import YulSemnaticsZoo.Yul.Syntax.WellFormed
import YulSemnaticsZoo.Yul.Semantics.Clocked.Interp
import YulSemnaticsZoo.EVM.Syntax.Syntax

set_option doc.verso true

/-!
# Compiler: Yul to EVM

{lit}`compile` translates the code of the top object of a Yul program in the EVM dialect to EVM
bytecode. It is a pure function. It gives {lit}`none` if the object is not well-formed, if the
code calls a builtin outside the 8 builtins of the clocked semantics, or if it cannot make the
code: a variable or a return variable is more than 16 words deep in the stack, or the code is
larger than {lit}`2 ^ 16` bytes.

## Design

* *Variables* are on the stack. The compiler keeps the names of the variables in scope in the
  order of the {lit}`Vars` of the Yul semantics: the last declaration is first, and it is the top
  of the stack. Above the variables are the values of the expressions that are not used yet. A
  variable is read with {lit}`DUPn` and set with {lit}`SWAPn POP`. At the end of a block,
  {lit}`POP` removes the variables of the block.
* *Expressions* put their values on the stack, the first value on top. The arguments of a call
  are compiled from the last to the first, as the Yul semantics evaluates them. Thus each
  {lit}`gas()` becomes one {lit}`GAS`, in the same order.
* *Functions* are code with a {lit}`JUMPDEST` at their start. A call pushes the return label, a
  0 for each return variable, then the arguments, and jumps to the function. The function then
  has its parameters and return variables on the stack, in the order of the Yul semantics, with
  the return label below them. At its end, it removes the parameters, moves the return label
  above the return values ({lit}`SWAP1` … {lit}`SWAPm`), and jumps back. The code of a function
  is at its definition, with a jump over it.
* *Control flow*: {lit}`if` and {lit}`for` use {lit}`PUSH0 EQ` and {lit}`JUMPI`. {lit}`break`,
  {lit}`continue` and {lit}`leave` remove the variables of the blocks that they leave, and jump.
  {lit}`return(off, size)` becomes {lit}`RETURN`, and the end of the code becomes {lit}`STOP`.
* *Labels* are symbolic in the compiled code: the path of the AST node and a number. One layout
  pass then gives each label its position. A jump target is always a {lit}`PUSH2`, thus the
  positions are known before the layout pass.

Each loop iteration of the Yul semantics starts at a {lit}`JUMPDEST`, and each call runs a
{lit}`JUMP`. Thus each tick of the Yul clock is at least one EVM instruction.

The compiler checks only some of the rules of well-formed code again (each name is bound, each
expression has the number of values that its place needs, and {lit}`break`, {lit}`continue` and
{lit}`leave` have a target). The proof of correctness uses these checks, and not
{lit}`Object.WellFormed`.
-/

namespace Compiler
open Yul Semantics

/-- the reason why the compiler gives no code -/
inductive Error where
  /-- the object is not well-formed in the EVM dialect -/
  | notWellFormed
  /-- a builtin outside the 8 builtins of the clocked semantics -/
  | unsupported
  /-- an expression without the number of values that its place needs, or a call with the wrong
  number of arguments -/
  | arity
  /-- a variable or function that is not in scope -/
  | unbound
  /-- {lit}`break` or {lit}`continue` outside a loop body, or {lit}`leave` outside a function -/
  | misplaced
  /-- two functions of a block, or two parameters or return variables of a function, with the
  same name -/
  | duplicate
  /-- a variable more than 16 words deep in the stack, or more than 16 return variables -/
  | stackTooDeep
  /-- code larger than {lit}`2 ^ 16` bytes: a {lit}`PUSH2` cannot give each position -/
  | tooLarge
  /-- two labels with the same name; the paths of the AST nodes are different, thus this does
  not occur -/
  | duplicateLabel
  deriving DecidableEq, Repr

/-! ## Compiled code -/

/-- a label: the path of an AST node, and a number for each label of the node -/
abbrev Label := List Nat × Nat

/-- an item of the compiled code -/
inductive Item where
  | op (i : EVM.Instr)
  /-- a {lit}`JUMPDEST` with a label -/
  | label (l : Label)
  /-- a {lit}`PUSH2` of the position of the label -/
  | push (l : Label)
  deriving DecidableEq, Repr

abbrev Code := List Item

/-- the {lit}`n` bytes of {lit}`v` in big-endian order, the low bytes -/
def toBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, v => toBytes n (v / 256) ++ [(v % 256).toUInt8]

theorem toBytes_length : (toBytes n v).length = n := by
  induction n generalizing v <;> simp_all [toBytes]

/-- {lit}`PUSHn` of the low {name}`n` bytes of {name}`v` -/
def pushNat (n : Fin 33) (v : Nat) : EVM.Instr :=
  .Push n ⟨(toBytes n v).toArray, by simp [toBytes_length]⟩

def push0 : Item := .op (pushNat 0 0)

def pops (k : Nat) : Code := List.replicate k (.op .Pop)

def dup (n : Nat) : Except Error Item :=
  if h : 0 < n ∧ n ≤ 16 then .ok (.op (.Dup n h)) else .error .stackTooDeep

def swap (n : Nat) : Except Error Item :=
  if h : 0 < n ∧ n ≤ 16 then .ok (.op (.Swap n h)) else .error .stackTooDeep

/-- {lit}`SWAP1` … {lit}`SWAPm`: the word below {name}`m` words goes to the top, and the {name}`m`
words keep their order -/
def rotate (m : Nat) : Except Error Code := (List.range m).mapM fun j => swap (j + 1)

/-! ## The context of the compiler -/

/-- what the compiler knows of a function in scope -/
structure FunInfo where
  label : Label
  params : Nat
  rets : Nat

/-- the functions in scope, as the {lit}`Funs` of the Yul semantics: for each block around the
code, the innermost first, the functions of the block -/
abbrev CFuns := List (List (Identifier × FunInfo))

/-- the function {name}`f` in scope, and the functions in scope at its definition -/
def CFuns.find? (f : Identifier) : CFuns → Option (FunInfo × CFuns)
  | [] => none
  | l :: ls =>
    match l.lookup f with
    | some i => some (i, l :: ls)
    | none => find? f ls

structure Ctx where
  /-- the names of the variables in scope; the last declaration is first -/
  vars : List Identifier
  funs : CFuns
  /-- in the body of a loop: the label after the loop, the label of the post block, and the
  number of variables at the loop -/
  loop : Option (Label × Label × Nat) := none
  /-- in a function: the label of the end of the function, and the number of its parameters and
  return variables -/
  leave : Option (Label × Nat) := none

/-- the instruction of a builtin of the clocked semantics, its number of arguments and its number
of values -/
def builtinOp : Yul.EVM.Builtin → Option (EVM.Instr × Nat × Nat)
  | .Add => some (.Add, 2, 1)
  | .Lt => some (.Lt, 2, 1)
  | .Eq => some (.Eq, 2, 1)
  | .Calldataload => some (.Calldataload, 1, 1)
  | .Mload => some (.Mload, 1, 1)
  | .Mstore => some (.Mstore, 2, 0)
  | .Gas => some (.Gas, 0, 1)
  | .Return => some (.Return, 2, 0)
  | _ => none

/-- the functions that the statements define, as {lit}`defs` of the Yul semantics; the function
of statement {lit}`j` has the label {lit}`(q ++ [j], 0)` -/
def cdefs (q : List Nat) : Nat → List Statement → List (Identifier × FunInfo)
  | _, [] => []
  | j, .FunctionDefinition f ps rs _ :: ss =>
    (f, ⟨(q ++ [j], 0), ps.length, rs.length⟩) :: cdefs q (j + 1) ss
  | j, _ :: ss => cdefs q (j + 1) ss

/-- the context with the functions of the statements in scope -/
def scope (ctx : Ctx) (q : List Nat) (ss : List Statement) : Except Error Ctx :=
  let fs := cdefs q 0 ss
  if (fs.map (·.1)).Nodup then .ok { ctx with funs := fs :: ctx.funs } else .error .duplicate

/-- remove the variables above the first {name}`n`, and jump to {name}`l` -/
def jumpOut (vars : List Identifier) (n : Nat) (l : Label) : Code :=
  pops (vars.length - n) ++ [.push l, .op .Jump]

/-- set the variables {lit}`xs` to the values on the stack, the first value on top -/
def assign (vars : List Identifier) : List Identifier → Except Error Code
  | [] => .ok []
  | x :: xs => do
    let some j := vars.idxOf? x | throw .unbound
    return [← swap (xs.length + 1 + j), .op .Pop] ++ (← assign vars xs)

/-! ## Expressions

{lit}`compileExpr ctx q d e k`: the code of the expression {lit}`e` at the path {lit}`q`, with
{lit}`d` values above the variables. The code puts {lit}`k` values on the stack, or the compiler
gives an error.
-/

mutual

def compileExpr (ctx : Ctx) (q : List Nat) (d : Nat) : Expression → Nat → Except Error Code
  | .Literal l, k => do
    unless k = 1 do throw .arity
    return [.op (pushNat 32 (Clocked.literalValue l).toNat)]
  | .Identifier x, k => do
    unless k = 1 do throw .arity
    let some j := ctx.vars.idxOf? x | throw .unbound
    return [← dup (d + j + 1)]
  | .FunctionCall f args, k =>
    match Yul.EVM.dialect.builtin f with
    | some (kinds, mk) => do
      let some b := mk (literalArgs kinds args) | throw .unsupported
      let some (i, n, outs) := builtinOp b | throw .unsupported
      unless args.length = n ∧ k = outs do throw .arity
      return (← compileArgs ctx q d args) ++ [.op i]
    | none => do
      let some (fn, _) := ctx.funs.find? f | throw .unbound
      unless args.length = fn.params ∧ k = fn.rets do throw .arity
      let args ← compileArgs ctx q (d + 1 + fn.rets) args
      return [.push (q, 0)] ++ List.replicate fn.rets push0 ++ args ++
        [.push fn.label, .op .Jump, .label (q, 0)]

/-- the arguments, from the last to the first; the argument {lit}`j` is at the path
{lit}`q ++ [j]` -/
def compileArgs (ctx : Ctx) (q : List Nat) (d : Nat) : List Expression → Except Error Code
  | [] => .ok []
  | e :: es => do
    let c ← compileArgs ctx q d es
    return c ++ (← compileExpr ctx (q ++ [es.length]) (d + es.length) e 1)

end

/-! ## Statements

{lit}`compileStmt ctx q s`: the code of the statement {lit}`s` at the path {lit}`q`, and the
names of the variables after it.
-/

/-- the context of the body of a function with the parameters {name}`ps` and the return
variables {name}`rs`, in the scope {name}`funs` of its definition; the end of the function has
the label {lit}`(q, 2)` -/
def funCtx (funs : CFuns) (q : List Nat) (ps rs : List Identifier) : Ctx :=
  { vars := ps ++ rs, funs, leave := some ((q, 2), ps.length + rs.length) }

/-- the code of a function with the label {lit}`(q, 0)`, {name}`n` parameters, {name}`m` return
variables and the code {name}`body` of its body -/
def funCode (q : List Nat) (n m : Nat) (body : Code) : Except Error Code := do
  return [.label (q, 0)] ++ body ++ [.label (q, 2)] ++ pops n ++ (← rotate m) ++ [.op .Jump]

/-- the iterations of a loop at the path {lit}`q`, with the code {name}`cond` of the condition,
{name}`body` of the body and {name}`post` of the post block. The labels {lit}`(q, 0)`,
{lit}`(q, 1)` and {lit}`(q, 2)` are the start of an iteration, the post block ({lit}`continue`)
and the end of the loop ({lit}`break`). -/
def loopCode (q : List Nat) (cond body post : Code) : Code :=
  [.label (q, 0)] ++ cond ++ [push0, .op .Eq, .push (q, 2), .op .Jumpi] ++ body ++
    [.label (q, 1)] ++ post ++ [.push (q, 0), .op .Jump, .label (q, 2)]

mutual

def compileStmt (ctx : Ctx) (q : List Nat) : Statement → Except Error (Code × List Identifier)
  | .Block b => return (← compileBlock ctx q b, ctx.vars)
  | .FunctionDefinition _ ps rs body => do
    unless (ps ++ rs).Nodup do throw .duplicate
    let cb ← compileBlock (funCtx ctx.funs q ps rs) (q ++ [0]) body
    let c ← funCode q ps.length rs.length cb
    return ([.push (q, 1), .op .Jump] ++ c ++ [.label (q, 1)], ctx.vars)
  | .VariableDeclaration xs none => return (List.replicate xs.length push0, xs ++ ctx.vars)
  | .VariableDeclaration xs (some e) => return (← compileExpr ctx q 0 e xs.length, xs ++ ctx.vars)
  | .Assignment xs e => do
    let c ← compileExpr ctx q 0 e xs.length
    return (c ++ (← assign ctx.vars xs), ctx.vars)
  | .If c b => do
    let cc ← compileExpr ctx (q ++ [0]) 0 c 1
    let cb ← compileBlock ctx (q ++ [1]) b
    return (cc ++ [push0, .op .Eq, .push (q, 0), .op .Jumpi] ++ cb ++ [.label (q, 0)], ctx.vars)
  | .Expression e => return (← compileExpr ctx q 0 e 0, ctx.vars)
  | .ForLoop ⟨init⟩ c post body => do
    let ctxi ← scope { ctx with loop := none } (q ++ [0]) init
    let (ci, vars) ← compileStmts ctxi (q ++ [0]) 0 init
    let ctxi := { ctxi with vars }
    let cc ← compileExpr ctxi (q ++ [1]) 0 c 1
    let cb ← compileBlock { ctxi with loop := some ((q, 2), (q, 1), vars.length) } (q ++ [2]) body
    let cp ← compileBlock ctxi (q ++ [3]) post
    return (ci ++ loopCode q cc cb cp ++ pops (vars.length - ctx.vars.length), ctx.vars)
  | .Break =>
    match ctx.loop with
    | some (exit, _, n) => .ok (jumpOut ctx.vars n exit, ctx.vars)
    | none => .error .misplaced
  | .Continue =>
    match ctx.loop with
    | some (_, cont, n) => .ok (jumpOut ctx.vars n cont, ctx.vars)
    | none => .error .misplaced
  | .Leave =>
    match ctx.leave with
    | some (exit, n) => .ok (jumpOut ctx.vars n exit, ctx.vars)
    | none => .error .misplaced

/-- a block: its functions are in scope in all of it, and {lit}`POP` removes its variables at
its end -/
def compileBlock (ctx : Ctx) (q : List Nat) : Block → Except Error Code
  | ⟨ss⟩ => do
    let (c, vars) ← compileStmts (← scope ctx q ss) q 0 ss
    return c ++ pops (vars.length - ctx.vars.length)

/-- the statements; the statement {name}`j` is at the path {lit}`q ++ [j]` -/
def compileStmts (ctx : Ctx) (q : List Nat) (j : Nat) :
    List Statement → Except Error (Code × List Identifier)
  | [] => .ok ([], ctx.vars)
  | s :: ss => do
    let (c, vars) ← compileStmt ctx (q ++ [j]) s
    let (cs, vars) ← compileStmts { ctx with vars } q (j + 1) ss
    return (c ++ cs, vars)

end

/-! ## Layout -/

/-- the number of bytes of an item -/
def Item.size : Item → Nat
  | .op i => i.encode.length
  | .label _ => 1
  | .push _ => 3

/-- the labels of the code and their positions, from the position {lit}`p` -/
def offsets : Code → Nat → List (Label × Nat)
  | [], _ => []
  | .label l :: c, p => (l, p) :: offsets c (p + 1)
  | it :: c, p => offsets c (p + it.size)

/-- the instruction of an item, with the positions {name}`pos` of the labels -/
def Item.resolve (pos : Label → Nat) : Item → EVM.Instr
  | .op i => i
  | .label _ => .Jumpdest
  | .push l => pushNat 2 (pos l)

/-- the bytes of the code: each label at its position -/
def layout (prog : Code) : List UInt8 :=
  let tbl := offsets prog 0
  (prog.map (Item.resolve fun l => (tbl.lookup l).getD 0)).flatMap EVM.Instr.encode

/-- the bytecode of the code, if each label is unique and each position fits in 2 bytes -/
def assemble (prog : Code) : Except Error (List UInt8) := do
  unless ((offsets prog 0).map (·.1)).Nodup do throw .duplicateLabel
  unless (prog.map Item.size).sum ≤ 2 ^ 16 do throw .tooLarge
  return layout prog

/-! ## The compiler -/

/-- the bytecode of the code of the top object, or the reason why there is none -/
def compileE (P : Object) : Except Error (List UInt8) := do
  unless decide (P.WellFormed Yul.EVM.dialect) do throw .notWellFormed
  let c ← compileBlock { vars := [], funs := [] } [] P.code
  assemble (c ++ [.op .Stop])

def compile (P : Object) : Option (List UInt8) := (compileE P).toOption

end Compiler

import Fuzz.Gen
import YulSemnaticsZoo.Yul.Printer
import YulSemnaticsZoo.Yul.WellFormed

/-!
# Random Yul objects, and random text for them

`object` makes objects that are well-formed in the EVM dialect of the tiny Yul, so that the
analysis of solc accepts them: each name is in scope and new, each call has the right number of
arguments and results, `break` and `continue` are in a loop body, `leave` is in a function, and
`datasize` and `dataoffset` refer to sub-objects and data. `mutateObject` changes an object so
that it can break one of these rules. `text` prints the tokens of an object with random
spellings that the printer does not use: comments, white space, hex numbers, escapes and hex
literals.
-/

namespace Fuzz.Yul
open Fuzz _root_.Yul

/-- a random generator with a counter for new names -/
abbrev YGen := StateT Nat Gen

def fresh (p : String) : YGen String := modifyGet fun k => (p ++ toString k, k + 1)

/-- builtins of the EVM dialect with no literal arguments and one result: name and number of
arguments -/
def builtins1 : List (String × Nat) :=
  [("add", 2), ("eq", 2), ("mload", 1), ("gas", 0), ("create", 3), ("call", 7)]

/-- builtins of the EVM dialect with no literal arguments and no result -/
def builtins0 : List (String × Nat) :=
  [("mstore", 2), ("codecopy", 3), ("extcodecopy", 4), ("return", 2), ("datacopy", 3)]

structure Env where
  /-- the variables in scope -/
  vars : List Identifier := []
  /-- the functions in scope: name, number of arguments, number of results -/
  funs : List (Identifier × Nat × Nat) := []
  /-- the names that `datasize` and `dataoffset` can refer to -/
  paths : List String := []
  inLoop : Bool := false
  inFun : Bool := false

instance : Inhabited Env := ⟨{}⟩
instance : Inhabited Block := ⟨⟨[]⟩⟩
instance : Inhabited Statement := ⟨.Break⟩
instance : Inhabited Object := ⟨{ name := "", code := ⟨[]⟩, objects := [], data := [] }⟩

def literal : Gen Literal := do
  match ← nat 0 5 with
  | 0 => return .NumberLiteral (← nat 0 255)
  | 1 => return .NumberLiteral (← nat 0 (2 ^ 256 - 1))
  | 2 => return .NumberLiteral (2 ^ 256 - 1)
  | 3 => return .StringLiteral (← list (← nat 0 32) byte)
  | 4 => return .TrueLiteral
  | _ => return .FalseLiteral

def str (s : String) : Expression := .Literal (.StringLiteral s.toUTF8.toList)

/-- `verbatim_<ins>i_<outs>o` with code that can be longer than 32 bytes -/
def verbatim (outs : Nat) (arg : Gen Expression) : Gen Expression := do
  let ins ← nat 0 2
  let code ← list (← nat 1 40) byte
  return .FunctionCall s!"verbatim_{ins}i_{outs}o" (.Literal (.StringLiteral code) :: (← list ins arg))

/-- a call of a builtin with literal arguments and `outs` results; not `setimmutable` and
`loadimmutable`, which solc assembles only for an immutable that the creation code sets and the
deployed code loads -/
def literalCall (env : Env) (outs : Nat) (arg : Gen Expression) : Gen Expression := do
  match outs with
  | 0 => verbatim 0 arg
  | 1 =>
    match ← nat 0 3, env.paths with
    | 0, ps@(_ :: _) =>
      return .FunctionCall (← pick ["datasize", "dataoffset"] "") [str (← pick ps "")]
    | 1, _ => return .FunctionCall "linkersymbol" [str "L"]
    | 2, _ => return .FunctionCall "memoryguard" [.Literal (.NumberLiteral (← nat 0 (2 ^ 256 - 1)))]
    | _, _ => verbatim 1 arg

  | n => verbatim n arg

/-- an expression with one value -/
def expr (env : Env) : Nat → Gen Expression
  | 0 => leaf
  | d + 1 => do
    match ← nat 0 4 with
    | 0 => leaf
    | 1 =>
      let (f, k) ← pick builtins1 ("gas", 0)
      return .FunctionCall f (← list k (expr env d))
    | 2 =>
      match env.funs.filter (·.2.2 == 1) with
      | [] => leaf
      | fs =>
        let (f, k, _) ← pick fs ("", 0, 0)
        return .FunctionCall f (← list k (expr env d))
    | 3 => literalCall env 1 (expr env d)
    | _ => leaf
where
  leaf : Gen Expression := do
    if !env.vars.isEmpty && (← coin) then return .Identifier (← pick env.vars "")
    else return .Literal (← literal)

/-- a call with no value -/
def callStmt (env : Env) (d : Nat) : Gen Statement := do
  match ← nat 0 2, env.funs.filter (·.2.2 == 0) with
  | 0, fs@(_ :: _) =>
    let (f, k, _) ← pick fs ("", 0, 0)
    return .Expression (.FunctionCall f (← list k (expr env d)))
  | 1, _ => return .Expression (← literalCall env 0 (expr env d))
  | _, _ =>
    let (f, k) ← pick builtins0 ("return", 2)
    return .Expression (.FunctionCall f (← list k (expr env d)))

mutual

/-- a block; `funs` allows function definitions in it -/
partial def block (env : Env) (funs : Bool) (d : Nat) : YGen Block := do
  let decls ← if funs && d > 0 then
      (List.range (← nat 0 2)).mapM fun _ => do return (← fresh "f", ← nat 0 3, ← nat 0 2)
    else pure []
  let env := { env with funs := env.funs ++ decls }
  let defs ← decls.mapM fun (f, np, nr) => do
    let ps ← (List.range np).mapM fun _ => fresh "p"
    let rs ← (List.range nr).mapM fun _ => fresh "r"
    let body ← block { env with vars := ps ++ rs, inLoop := false, inFun := true } true (d - 1)
    return Statement.FunctionDefinition f ps rs body
  let (ss, _) ← stmts env funs (← nat 0 4) d
  -- the functions of a block are in scope in all of it, so they can be anywhere in it
  let at_ ← nat 0 ss.length
  return ⟨ss.take at_ ++ defs ++ ss.drop at_⟩

/-- `k` statements, and the scope after them -/
partial def stmts (env : Env) (funs : Bool) : Nat → Nat → YGen (List Statement × Env)
  | 0, _ => return ([], env)
  | k + 1, d => do
    let (s, env) ← stmt env funs d
    let (ss, env) ← stmts env funs k d
    return (s :: ss, env)

/-- a statement, and the scope after it -/
partial def stmt (env : Env) (funs : Bool) (d : Nat) : YGen (Statement × Env) := do
  let e := fun (_ : Unit) => (expr env (min d 2) : Gen Expression)
  let multi := env.funs.filter (·.2.2 ≥ 2)
  match ← nat 0 (if d = 0 then 3 else 9) with
  | 0 =>
    let x ← fresh "v"
    if ← coin then
      return (.VariableDeclaration [x] (some (← e ())), { env with vars := x :: env.vars })
    else return (.VariableDeclaration [x] none, { env with vars := x :: env.vars })
  | 1 =>
    match env.vars with
    | [] => return (← callStmt env (min d 2), env)
    | vs => return (.Assignment [← pick vs ""] (← e ()), env)
  | 2 =>
    -- a call with more than one result: of a function, or of verbatim
    let (call, n) ← match multi, ← coin with
      | fs@(_ :: _), true => do
        let (f, k, n) ← pick fs ("", 0, 0)
        pure (Expression.FunctionCall f (← list k (expr env (min d 2))), n)
      | _, _ => do
        let n ← nat 2 3
        pure (← verbatim n (expr env (min d 2)), n)
    let xs ← (List.range n).mapM fun _ => fresh "v"
    if (← coin) && env.vars.length ≥ n then
      return (.Assignment (env.vars.take n) call, env)
    return (.VariableDeclaration xs (some call), { env with vars := xs ++ env.vars })
  | 3 => return (← callStmt env (min d 2), env)
  | 4 => return (.If (← e ()) (← block env funs (d - 1)), env)
  | 5 =>
    let (init, env') ← stmts { env with inLoop := false } false (← nat 0 2) (d - 1)
    let env' := { env' with inLoop := env.inLoop }
    let cond ← expr env' (min d 2)
    let post ← block { env' with inLoop := false } false (d - 1)
    let body ← block { env' with inLoop := true } funs (d - 1)
    return (.ForLoop ⟨init⟩ cond post body, env)
  | 6 => return (.Block (← block env funs (d - 1)), env)
  | 7 =>
    if env.inLoop then return (if ← coin then .Break else .Continue, env)
    else return (← callStmt env (min d 2), env)
  | 8 =>
    if env.inFun then return (.Leave, env) else return (← callStmt env (min d 2), env)
  | _ => return (← callStmt env (min d 2), env)

end

/-- a name for an object or data; some have a `.`, which `datasize` cannot refer to -/
def objectName (p : String) : YGen String := do
  let n ← fresh p
  if (← nat 0 4) == 0 then return n ++ ".x" else return n

/-- the paths to the data of the sub-objects of an object -/
partial def subData (o : Object) : List String :=
  o.objects.flatMap fun c => (c.data.map (·.name) ++ subData c).map (c.name ++ "." ++ ·)

partial def object (d : Nat) : YGen Object := do
  let name ← objectName "O"
  let objects ← if d = 0 then pure [] else (List.range (← nat 0 2)).mapM fun _ => object (d - 1)
  let data ← (List.range (← nat 0 2)).mapM fun _ => do
    return ({ name := ← objectName "D", value := ← list (← nat 0 8) byte } : Data)
  let o : Object := { name, code := ⟨[]⟩, objects, data }
  -- not the data of a sub-object: solc analyses `datasize("O.D")`, but it fails to assemble it
  return { o with code := ← block { paths := o.dataNames.filter (!(subData o).contains ·) } true 3 }


/-! ## Mutations -/

/-- the paths from an object to its sub-objects and data, and to theirs -/
partial def allPaths (o : Object) : List String :=
  o.data.map (·.name) ++ o.objects.flatMap fun c => c.name :: (allPaths c).map (c.name ++ "." ++ ·)

/-- the names in a block, of variables, functions and parameters, each with whether it is the
name of a call -/
partial def blockNames : Block → List (Identifier × Bool)
  | ⟨ss⟩ => ss.flatMap stmtNames
where
  names (xs : List Identifier) := xs.map (·, false)
  exprNames : Expression → List (Identifier × Bool)
    | .FunctionCall f args => (f, true) :: args.flatMap exprNames
    | .Identifier x => [(x, false)]
    | .Literal _ => []
  stmtNames : Statement → List (Identifier × Bool)
    | .Block b => blockNames b
    | .FunctionDefinition f ps rs b => names (f :: ps ++ rs) ++ blockNames b
    | .VariableDeclaration xs v => names xs ++ (v.map exprNames).getD []
    | .Assignment xs e => names xs ++ exprNames e
    | .If c b => exprNames c ++ blockNames b
    | .Expression e => exprNames e
    | .ForLoop i c p b => blockNames i ++ exprNames c ++ blockNames p ++ blockNames b
    | .Break | .Continue | .Leave => []

/-- the block with the `k`th name (as `blockNames` counts them) replaced by `f` of it; the state
counts the names before -/
partial def mapName (k : Nat) (f : Identifier → Identifier) : Block → StateM Nat Block
  | ⟨ss⟩ => return ⟨← ss.mapM stmt⟩
where
  name (x : Identifier) : StateM Nat Identifier :=
    modifyGet fun i => (if i == k then f x else x, i + 1)
  expr : Expression → StateM Nat Expression
    | .FunctionCall g args => return .FunctionCall (← name g) (← args.mapM expr)
    | .Identifier x => return .Identifier (← name x)
    | .Literal l => return .Literal l
  stmt : Statement → StateM Nat Statement
    | .Block b => return .Block (← mapName k f b)
    | .FunctionDefinition g ps rs b =>
      return .FunctionDefinition (← name g) (← ps.mapM name) (← rs.mapM name) (← mapName k f b)
    | .VariableDeclaration xs v => return .VariableDeclaration (← xs.mapM name) (← v.mapM expr)
    | .Assignment xs e => return .Assignment (← xs.mapM name) (← expr e)
    | .If c b => return .If (← expr c) (← mapName k f b)
    | .Expression e => return .Expression (← expr e)
    | .ForLoop i c p b =>
      return .ForLoop (← mapName k f i) (← expr c) (← mapName k f p) (← mapName k f b)
    | s => return s

/-- the block with `f` applied to its `k`th list of statements (in the order of the lists'
starts); the state counts the lists before -/
partial def mapList (k : Nat) (f : List Statement → List Statement) :
    Block → StateM Nat Block
  | ⟨ss⟩ => do
    let i ← modifyGet fun i => (i, i + 1)
    let ss ← ss.mapM stmt
    return ⟨if i == k then f ss else ss⟩
where
  stmt : Statement → StateM Nat Statement
    | .Block b => return .Block (← mapList k f b)
    | .FunctionDefinition g ps rs b => return .FunctionDefinition g ps rs (← mapList k f b)
    | .If c b => return .If c (← mapList k f b)
    | .ForLoop i c p b => return .ForLoop (← mapList k f i) c (← mapList k f p) (← mapList k f b)
    | s => return s

/-- a statement that often breaks a rule: with a name of `ns` (which can be in scope or not),
the wrong number of values, or a literal that is too large -/
def wrongStmt (ns : List Identifier) : Gen Statement := do
  let n ← pick ns "x"
  let arg : Gen Expression := return .Literal (.NumberLiteral 1)
  match ← nat 0 9 with
  | 0 => return .Break
  | 1 => return .Continue
  | 2 => return .Leave
  | 3 => return .FunctionDefinition n (← list (← nat 0 1) (pick ns "x")) [] ⟨[]⟩
  | 4 => return .VariableDeclaration [n] (some (← pick [.Identifier (← pick ns "x"),
      .FunctionCall (← pick ns "x") [], .Literal (.NumberLiteral (2 ^ 256)),
      .Literal (.StringLiteral (List.replicate 33 0x61))] (.Identifier "x")))
  | 5 =>
    if ← coin then return .Assignment (← list (← nat 1 2) (pick ns "x")) (← arg)
    else return .Assignment [n, n] (.FunctionCall "verbatim_0i_2o" [str "c"])
  | 6 => return .Expression (.FunctionCall n (← list (← nat 0 3) arg))
  | 7 => return .Expression (.FunctionCall "verbatim_0i_0o" [.Literal (.StringLiteral [])])
  | 8 => return .If (.FunctionCall n (← list (← nat 0 2) arg)) ⟨[]⟩
  | _ => return .Expression (.FunctionCall "mstore"
      [← arg, .FunctionCall (← pick ["datasize", "dataoffset"] "") [str (← pick ns "x")]])

/-- the object with a random change to its code that can break a rule: a name replaced with
another name of the code, a statement deleted, or a statement inserted -/
def mutateObject (o : Object) : Gen Object := do
  let ns := (blockNames o.code).map (·.1)
  let lists := ((mapList 0 id o.code).run 0).2
  let code ← match ← nat 0 2 with
    | 0 =>
      let n ← pick ns "x"
      pure ((mapName (← nat 0 (ns.length - 1)) (fun _ => n) o.code).run' 0)
    | 1 =>
      let i ← nat 0 99
      pure ((mapList (← nat 0 (lists - 1)) (fun ss => ss.eraseIdx (i % (ss.length + 1))) o.code)
        |>.run' 0)
    | _ =>
      let i ← nat 0 99
      -- with names that solc reserves
      let s ← wrongStmt (ns ++ o.name :: allPaths o ++ ["sub", "jump", "verbatim", "verbatimx"])

      pure ((mapList (← nat 0 (lists - 1)) (fun ss =>
        ss.take (i % (ss.length + 1)) ++ s :: ss.drop (i % (ss.length + 1))) o.code).run' 0)
  return { o with code }

/-! ## Text -/

def hexDigitCase (k : Nat) : Gen Char := do
  let c := hexDigit k
  return if (← coin) then c.toUpper else c

def hexText (k : Nat) : Gen String := do
  let ds := Nat.toDigits 16 k
  return String.ofList (← ds.mapM fun d => do return if (← coin) then d.toUpper else d)

/-- a byte in a string literal, with one of the spellings that mean it -/
def byteText (b : UInt8) : Gen String := do
  let x := s!"\\x{String.ofList [← hexDigitCase (b.toNat / 16), ← hexDigitCase (b.toNat % 16)]}"
  let u := s!"\\u00{String.ofList [← hexDigitCase (b.toNat / 16), ← hexDigitCase (b.toNat % 16)]}"
  let c := Char.ofNat b.toNat
  let spellings :=
    if b = 0x22 then ["\\\""]
    else if b = 0x5c then ["\\\\"]
    else if b = 0x27 then ["'", "\\'", x, u]
    else if b = 0x0a then ["\\n", x, u]
    else if b = 0x0d then ["\\r", x, u]
    else if b = 0x09 then ["\\t", x, u]
    else if 0x20 ≤ b ∧ b < 0x7f then [c.toString, x, u]
    else if b < 0x80 then [x, u]
    else [x]
  pick spellings x

/-- a string literal; a hex literal if `hex` -/
def strText (bs : List UInt8) (hex : Bool) : Gen String := do
  if hex then
    let ds ← bs.mapM fun b => do
      return String.ofList [← hexDigitCase (b.toNat / 16), ← hexDigitCase (b.toNat % 16)]
    -- one `_` can be between two pairs of digits
    let ds ← ds.mapIdxM fun i d => do return if i > 0 && (← coin) then "_" ++ d else d
    return "hex\"" ++ String.join ds ++ "\""
  else
    -- a backslash before a new line is no character
    let parts ← bs.mapM fun b => do
      let cont ← pick ["", "", "", "", "", "\\\n", "\\\r\n", "\\\r"] ""
      return cont ++ (← byteText b)
    return "\"" ++ String.join parts ++ "\""

def tokenText (prev : Option Token) : Token → Gen String
  | .Word s => return s
  | .Number n => do if ← coin then return toString n else return "0x" ++ (← hexText n)
  | .Str bs => do
    -- the name of an object or data is a string literal; a value can be a hex literal
    let name := prev == some (.Word "object") || prev == some (.Word "data")
    strText bs (!name && (← coin))
  | t => return String.ofList t.chars

def wordish : Token → Bool
  | .Word _ | .Number _ => true
  | _ => false

/-- text between two tokens; it must separate a word or number from a word, a number or a
string, which can be a hex literal -/
def gapText (needed : Bool) : Gen String :=
  pick ([" ", "\n", "\t ", "   ", " /* c */ ", " // c\n"] ++ if needed then [] else ["", "/**/"])
    " "

/-- `hist`: the tokens before, the last first; `params`: in the parameters of a function, which
can end with a comma -/
def text (ts : List Token) : Gen String := go [] false ts
where
  go (hist : List Token) (params : Bool) : List Token → Gen String
    | [] => return ""
    | t :: ts => do
      let params' := match t, hist with
        | .Sym .LParen, .Word _ :: .Word "function" :: _ => true
        | .Sym .RParen, _ => false
        | _, _ => params
      let comma ← if t == .Sym .RParen && params && (hist.head? matches some (.Word _)) then
          pick ["", ","] ""
        else pure ""
      let g ← match ts with
        | u :: _ => gapText (wordish t && (wordish u || u matches .Str _))
        | [] => pure ""
      return comma ++ (← tokenText hist.head? t) ++ g ++ (← go (t :: hist) params' ts)

end Fuzz.Yul

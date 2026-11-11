import YulSemnaticsZoo.Yul.Dialect
import YulSemnaticsZoo.Yul.Parser

set_option doc.verso true

/-!
# Yul: well-formed ASTs

Reference: [Restrictions on the Grammar](https://docs.soliditylang.org/en/v0.8.38/yul.html#restrictions-on-the-grammar)
and [Scoping Rules](https://docs.soliditylang.org/en/v0.8.38/yul.html#scoping-rules)

The restrictions on ASTs that the grammar does not express, for a dialect:
* each name is in scope where it is used, and each declaration declares new names;
* each expression has the number of values that its place needs;
* {lit}`break` and {lit}`continue` are in the body of the innermost loop, {lit}`leave` is in a
  function, and no function is anywhere in the init block of a loop;
* the arguments and literal arguments of each builtin are as the dialect needs;
* each literal fits in a word: a number is less than 2^256, and a string has at most 32 bytes
  (but a literal argument of a builtin can be longer).

Where the docs and solc 0.8.38 differ, these are as in solc, but no function is anywhere in an
init block, as in the docs. A declaration cannot use the name of a builtin or a name that the
dialect reserves. The names that {lit}`datasize` and {lit}`dataoffset` can refer to are as in
{lit}`Object::Structure` of solc.

{lit}`lake test` fuzzes {lit}`Object.WellFormed` against the analysis of solc, and skips the
functions in init blocks that solc accepts.
-/

namespace Yul

-- What is in scope at a statement
structure Scope where
  -- the variables
  vars : List Identifier := []
  -- the functions: name, number of parameters, number of return variables
  funs : List (Identifier × Nat × Nat) := []
  -- the variables outside the function: they are not in scope, but a declaration cannot use them
  hidden : List Identifier := []
  -- in the body of the innermost loop, and not in a function in it: `break` and `continue` can be
  -- here
  inLoopBody : Bool := false
  -- in the init block of a loop, at any depth: no function can be here
  inInit : Bool := false
  inFunction : Bool := false

/-- a literal fits in a word -/
def Literal.WellFormed : Literal → Prop
  | .NumberLiteral n => n < 2 ^ 256
  | .StringLiteral bs => bs.length ≤ 32
  | .TrueLiteral | .FalseLiteral => True

instance : DecidablePred Literal.WellFormed := fun l => by
  cases l <;> unfold Literal.WellFormed <;> infer_instance

/-- a declaration in scope {lit}`Γ` can declare the names {lit}`xs`: they are different, and no
name is a builtin, reserved, in scope or hidden -/
def Scope.Declares (d : Dialect) (Γ : Scope) (xs : List Identifier) : Prop :=
  xs.Nodup ∧ ∀ x ∈ xs, (d.builtin x).isNone ∧ !d.reserved x ∧ x ∉ Γ.vars ∧
    x ∉ Γ.funs.map (·.1) ∧ x ∉ Γ.hidden

/-- the literals for the literal arguments of a builtin -/
def literalArgs : List Arg → List Expression → List Literal
  | .Literal :: ks, .Literal l :: es => l :: literalArgs ks es
  | _ :: ks, _ :: es => literalArgs ks es
  | _, _ => []

/-- the scope after the statement {lit}`s`: a {lit}`let` adds its variables -/
def Scope.after (Γ : Scope) : Statement → Scope
  | .VariableDeclaration xs _ => { Γ with vars := xs ++ Γ.vars }
  | _ => Γ

/-- the functions that the statements define: name, number of parameters, number of return
variables -/
def functions : List Statement → List (Identifier × Nat × Nat)
  | [] => []
  | .FunctionDefinition f ps rs _ :: ss => (f, ps.length, rs.length) :: functions ss
  | _ :: ss => functions ss

section

-- the dialect, and the names of the sub-objects and data that the code can refer to
variable (d : Dialect) (names : List String)

mutual

/-- {lit}`e` is well-formed in scope {lit}`Γ` and has {lit}`n` values -/
def Expression.WellFormed (Γ : Scope) : Expression → Nat → Prop
  | .Literal l, n => l.WellFormed ∧ n = 1
  | .Identifier x, n => x ∈ Γ.vars ∧ n = 1
  | .FunctionCall f args, n =>
    match d.builtin f with
    | some (kinds, mk) =>
      builtinArgsWellFormed Γ kinds args ∧
        match mk (literalArgs kinds args) with
        | some b => d.outs b = n ∧ (d.dataName b).all names.contains
        | none => False
    | none =>
      match Γ.funs.lookup f with
      | some (ps, rs) => args.length = ps ∧ argsWellFormed Γ args ∧ n = rs
      | none => False

/-- each expression is well-formed and has one value -/
def argsWellFormed (Γ : Scope) : List Expression → Prop
  | [] => True
  | e :: es => e.WellFormed Γ 1 ∧ argsWellFormed Γ es

/-- an argument for each of the arguments of a builtin: an expression with one value for
{name}`Arg.Expression`, and a literal for {name}`Arg.Literal` -/
def builtinArgsWellFormed (Γ : Scope) : List Arg → List Expression → Prop
  | [], [] => True
  | .Expression :: ks, e :: es => e.WellFormed Γ 1 ∧ builtinArgsWellFormed Γ ks es
  | .Literal :: ks, e :: es => (e matches .Literal _) ∧ builtinArgsWellFormed Γ ks es
  | [], _ :: _ | _ :: _, [] => False

end

mutual

/-- the functions of a block are in scope in all of it -/
def Block.WellFormed (Γ : Scope) : Block → Prop
  | ⟨ss⟩ =>
    Γ.Declares d ((functions ss).map (·.1)) ∧
      statementsWellFormed { Γ with funs := functions ss ++ Γ.funs } ss

/-- each statement is well-formed in the scope after the statements before it -/
def statementsWellFormed (Γ : Scope) : List Statement → Prop
  | [] => True
  | s :: ss => s.WellFormed Γ ∧ statementsWellFormed (Γ.after s) ss

def Statement.WellFormed (Γ : Scope) : Statement → Prop
  | .Block b => b.WellFormed Γ
  | .FunctionDefinition _ ps rs body =>
    -- the name is in scope already: it is a function of the block
    !Γ.inInit ∧ Γ.Declares d (ps ++ rs) ∧
      body.WellFormed
        { vars := ps ++ rs, funs := Γ.funs, hidden := Γ.vars ++ Γ.hidden, inFunction := true }
  | .VariableDeclaration xs v =>
    Γ.Declares d xs ∧
      match v with
      | some e => e.WellFormed d names Γ xs.length
      | none => True
  | .Assignment xs e => xs.Nodup ∧ (∀ x ∈ xs, x ∈ Γ.vars) ∧ e.WellFormed d names Γ xs.length
  | .If c b => c.WellFormed d names Γ 1 ∧ b.WellFormed Γ
  | .Expression e => e.WellFormed d names Γ 0
  -- the variables of the init block are in scope in the rest of the loop
  | .ForLoop ⟨init⟩ c post body =>
    let Γi := { Γ with inLoopBody := false, inInit := true }
    let Γ' := { init.foldl Scope.after Γi with inInit := Γ.inInit }
    statementsWellFormed Γi init ∧ c.WellFormed d names Γ' 1 ∧
      body.WellFormed { Γ' with inLoopBody := true } ∧ post.WellFormed Γ'
  | .Break | .Continue => Γ.inLoopBody
  | .Leave => Γ.inFunction

end

end

/-- the paths in an object: the name of each sub-object and data, and for each sub-object its
name, a {lit}`.` and each path in it. A name with {lit}`.` has no paths. -/
def Object.paths : Object → List String
  | ⟨_, _, objects, data⟩ => go objects ++ (data.map (·.name)).filter (!·.contains '.')
where
  go : List Object → List String
    | [] => []
    | o :: os =>
      (if o.name.contains '.' then [] else o.name :: o.paths.map (o.name ++ "." ++ ·)) ++ go os

/-- the names that the code of an object can give to {lit}`datasize` and {lit}`dataoffset`: the
name of the object if it has no {lit}`.`, and its paths -/
def Object.dataNames (o : Object) : List String :=
  (if o.name.contains '.' then [] else [o.name]) ++ o.paths

mutual

def Object.WellFormed (d : Dialect) : Object → Prop
  | o@⟨_, code, objects, _⟩ => code.WellFormed d o.dataNames {} ∧ objectsWellFormed d objects

def objectsWellFormed (d : Dialect) : List Object → Prop
  | [] => True
  | o :: os => o.WellFormed d ∧ objectsWellFormed d os

end

/-! ## Deciding well-formedness -/

instance {d : Dialect} {Γ : Scope} {xs : List Identifier} : Decidable (Γ.Declares d xs) := by
  unfold Scope.Declares; infer_instance

section

variable (d : Dialect) (names : List String)

mutual

def Expression.decWellFormed (Γ : Scope) :
    (e : Expression) → (n : Nat) → Decidable (e.WellFormed d names Γ n)
  | .Literal _, _ | .Identifier _, _ => by unfold Expression.WellFormed; infer_instance
  | .FunctionCall _ args, _ => by
    unfold Expression.WellFormed
    split
    · next kinds _ _ =>
      have := decBuiltinArgsWellFormed Γ kinds args
      split <;> infer_instance
    · split
      · have := decArgsWellFormed Γ args; infer_instance
      · infer_instance

def decArgsWellFormed (Γ : Scope) :
    (es : List Expression) → Decidable (argsWellFormed d names Γ es)
  | [] => by unfold argsWellFormed; infer_instance
  | e :: es => by
    unfold argsWellFormed
    have := Expression.decWellFormed Γ e 1
    have := decArgsWellFormed Γ es
    infer_instance

def decBuiltinArgsWellFormed (Γ : Scope) :
    (ks : List Arg) → (es : List Expression) → Decidable (builtinArgsWellFormed d names Γ ks es)
  | .Expression :: ks, e :: es => by
    unfold builtinArgsWellFormed
    have := Expression.decWellFormed Γ e 1
    have := decBuiltinArgsWellFormed Γ ks es
    infer_instance
  | .Literal :: ks, _ :: es => by
    unfold builtinArgsWellFormed
    have := decBuiltinArgsWellFormed Γ ks es
    infer_instance
  | [], [] | [], _ :: _ | _ :: _, [] => by simp only [builtinArgsWellFormed]; infer_instance

end

instance {Γ : Scope} {e : Expression} {n : Nat} : Decidable (e.WellFormed d names Γ n) :=
  Expression.decWellFormed d names Γ e n


mutual

def Block.decWellFormed (Γ : Scope) : (b : Block) → Decidable (b.WellFormed d names Γ)
  | ⟨ss⟩ => by
    unfold Block.WellFormed
    have := fun Γ => decStatementsWellFormed Γ ss
    infer_instance

def decStatementsWellFormed (Γ : Scope) :
    (ss : List Statement) → Decidable (statementsWellFormed d names Γ ss)
  | [] => by unfold statementsWellFormed; infer_instance
  | s :: ss => by
    unfold statementsWellFormed
    have := Statement.decWellFormed Γ s
    have := fun Γ => decStatementsWellFormed Γ ss
    infer_instance

def Statement.decWellFormed (Γ : Scope) : (s : Statement) → Decidable (s.WellFormed d names Γ)
  | .Block b => by unfold Statement.WellFormed; exact Block.decWellFormed Γ b
  | .FunctionDefinition _ ps rs body => by
    unfold Statement.WellFormed
    have := fun Γ => Block.decWellFormed Γ body
    infer_instance
  | .VariableDeclaration _ v => by unfold Statement.WellFormed; cases v <;> infer_instance
  | .Assignment .. | .Expression _ | .Break | .Continue | .Leave => by
    unfold Statement.WellFormed; infer_instance
  | .If _ b => by
    unfold Statement.WellFormed
    have := Block.decWellFormed Γ b
    infer_instance
  | .ForLoop ⟨init⟩ _ post body => by
    unfold Statement.WellFormed
    have := fun Γ => decStatementsWellFormed Γ init
    have := fun Γ => Block.decWellFormed Γ body
    have := fun Γ => Block.decWellFormed Γ post
    infer_instance

end

instance {Γ : Scope} {b : Block} : Decidable (b.WellFormed d names Γ) := Block.decWellFormed d names Γ b

end

mutual

def Object.decWellFormed (d : Dialect) : (o : Object) → Decidable (o.WellFormed d)
  | ⟨_, _, objects, _⟩ => by
    unfold Object.WellFormed
    have := decObjectsWellFormed d objects
    infer_instance

def decObjectsWellFormed (d : Dialect) : (os : List Object) → Decidable (objectsWellFormed d os)
  | [] => by unfold objectsWellFormed; infer_instance
  | o :: os => by
    unfold objectsWellFormed
    have := Object.decWellFormed d o
    have := decObjectsWellFormed d os
    infer_instance

end

instance {d : Dialect} {o : Object} : Decidable (o.WellFormed d) := Object.decWellFormed d o

/-- parse an object, and check that it is well-formed -/
def Object.parseWellFormed (d : Dialect) (s : String) :
    Except String { o : Object // o.WellFormed d } := do
  let o ← Object.parse s
  if h : o.WellFormed d then return ⟨o, h⟩ else throw "the object is not well-formed"

end Yul

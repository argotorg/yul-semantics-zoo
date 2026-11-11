set_option doc.verso true

/-!
# Yul: syntax

The abstract syntax of Yul.

Reference: [The formal specification of Yul](https://docs.soliditylang.org/en/v0.8.38/yul.html#formal-specification)

Differences from the specified grammar:
* There is no {lit}`Switch`.
* There are no types : a {lit}`TypedIdentifierList` is a list of {lit}`Identifier`s, and a {lit}`Literal` has no {lit}`TypeName`.
* In an {lit}`Object`, the sub-objects and the {lit}`Data` are in two lists.
-/

namespace Yul

abbrev Identifier := String

inductive Literal where
  | NumberLiteral (n : Nat)
  /-- {lit}`StringLiteral`: the bytes of the string, after escapes; also a `hex"…"` literal -/
  | StringLiteral (bytes : List UInt8)
  | TrueLiteral
  | FalseLiteral
  deriving DecidableEq, Repr

inductive Expression where
  | FunctionCall (f : Identifier) (args : List Expression)
  | Identifier (name : Identifier)
  | Literal (l : Literal)

mutual

inductive Block where
  | mk (statements : List Statement)

inductive Statement where
  | Block (b : Block)
  /-- {lit}`FunctionDefinition`: `function name(params) -> rets body` -/
  | FunctionDefinition (name : Identifier) (params rets : List Identifier) (body : Block)
  /-- {lit}`VariableDeclaration`: {lit}`let vars := val`, or `let vars` -/
  | VariableDeclaration (vars : List Identifier) (val : Option Expression)
  | Assignment (vars : List Identifier) (val : Expression)
  | If (cond : Expression) (body : Block)
  | Expression (e : Expression)
  /-- {lit}`ForLoop`: `for init cond post body` -/
  | ForLoop (init : Block) (cond : Expression) (post body : Block)
  | Break
  | Continue
  | Leave

end

structure Data where
  name : String
  value : List UInt8

/-- A Yul object: code, the sub-objects it can deploy, and data. The code refers to sub-objects
and data by name (in the EVM dialect: {lit}`dataoffset`, {lit}`datasize`). -/
structure Object where
  name : String
  code : Block
  objects : List Object
  data : List Data

end Yul

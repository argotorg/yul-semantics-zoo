set_option doc.verso true

/-!
# Yul: syntax

The abstract syntax of Yul.

## Core Syntax

Reference: [The formal specification of Yul](https://docs.soliditylang.org/en/v0.8.38/yul.html#formal-specification)

Differences from the specified grammar:
* There is no {lit}`Switch`.
* There are no types : a {lit}`TypedIdentifierList` is a list of {lit}`Identifier`s, and a {lit}`Literal` has no {lit}`TypeName`.
* In an {lit}`Object`, the sub-objects and the {lit}`Data` are in two lists.
-/

namespace Yul

abbrev Identifier := String

/-!
Literals are numbers, strings, true or false
-/
inductive Literal where
  | NumberLiteral (n : Nat)
  -- the bytes of the string, after escapes; also a `hex"…"` literal
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
  -- `function name(params) -> rets body`
  | FunctionDefinition (name : Identifier) (params rets : List Identifier) (body : Block)
  -- `let vars := val`, or `let vars`
  | VariableDeclaration (vars : List Identifier) (val : Option Expression)
  | Assignment (vars : List Identifier) (val : Expression)
  | If (cond : Expression) (body : Block)
  | Expression (e : Expression)
  -- `for init cond post body`
  | ForLoop (init : Block) (cond : Expression) (post body : Block)
  | Break
  | Continue
  | Leave

end

/-!
## Yul Objects

Reference: [Specification of Yul Object](https://docs.soliditylang.org/en/v0.8.38/yul.html#specification-of-yul-object)

Yul objects are used to group named code and data sections. The functions
{lit}`datasize`, {lit}`dataoffset` and {lit}`datacopy` can be used to access these sections from
within code. Hex strings can be used to specify data in hex encoding, regular
strings in native encoding. For code, {lit}`datacopy` will access its assembled
binary representation.
-/

structure Data where
  name : String
  value : List UInt8

structure Object where
  name : String
  code : Block
  objects : List Object
  data : List Data

end Yul

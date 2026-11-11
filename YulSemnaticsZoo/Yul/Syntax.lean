/-!
# Yul: syntax

The abstract syntax of Yul. The names are the names of the grammar in the "Specification of
Yul" and "Specification of Yul Object" sections of the solidity docs. As in the grammar, the
syntax is the same for all dialects: a call of a builtin is a `FunctionCall`.

Differences from the grammar:
- There is no `Switch`. It can be written with `VariableDeclaration` and `If`.
- There are no types, as in the solc AST (`libyul/AST.h`): a `TypedIdentifierList` is a list
  of `Identifier`s, and a `Literal` has no `TypeName`.
- In an `Object`, the sub-objects and the `Data` are in two lists.

Nothing is checked: the syntax can express unbound variables, a `Break` out of a loop, a
builtin with a wrong number of arguments, and so on.
-/

namespace Yul

abbrev Identifier := String

inductive Literal where
  | NumberLiteral (n : Nat)
  /-- `StringLiteral`: the bytes of the string, after escapes; also a `hex"…"` literal -/
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
  /-- `FunctionDefinition`: `function name(params) -> rets body` -/
  | FunctionDefinition (name : Identifier) (params rets : List Identifier) (body : Block)
  /-- `VariableDeclaration`: `let vars := val`, or `let vars` -/
  | VariableDeclaration (vars : List Identifier) (val : Option Expression)
  | Assignment (vars : List Identifier) (val : Expression)
  | If (cond : Expression) (body : Block)
  | Expression (e : Expression)
  /-- `ForLoop`: `for init cond post body` -/
  | ForLoop (init : Block) (cond : Expression) (post body : Block)
  | Break
  | Continue
  | Leave

end

structure Data where
  name : String
  value : List UInt8

/-- A Yul object: code, the sub-objects it can deploy, and data. The code refers to sub-objects
and data by name (in the EVM dialect: `dataoffset`, `datasize`). -/
structure Object where
  name : String
  code : Block
  objects : List Object
  data : List Data

end Yul

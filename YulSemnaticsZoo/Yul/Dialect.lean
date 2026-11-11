import YulSemnaticsZoo.Yul.Syntax

set_option doc.verso true

/-!
# Yul: dialects

A dialect gives the builtins of Yul. In the syntax a builtin call is a {lit}`FunctionCall`; the
dialect tells which names are builtins, and which arguments of a builtin must be literals.
The values of the literal arguments are part of the builtin.
-/

namespace Yul

-- An argument of a builtin: an expression, or a literal that is part of the builtin
inductive Arg where
  | Expression
  | Literal
  deriving DecidableEq, Repr

structure Dialect where
  -- a builtin, with the values of its literal arguments
  Builtin : Type
  -- the number of values a builtin returns
  outs : Builtin → Nat
  -- if `f` is the name of a builtin, its arguments, and the builtin for the values of its literal
  -- arguments (`none` if the values are not valid)
  builtin : Identifier → Option (List Arg × (List Literal → Option Builtin))

end Yul

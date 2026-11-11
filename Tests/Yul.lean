import YulSemnaticsZoo.Yul.Quote
import YulSemnaticsZoo.Yul.Printer

/-! `Yul.Object.parse_print` and the others prove that parsing printed text gives the AST. These
tests are for the text that the printer does not print. -/

namespace Yul.Test
open Yul

def result : Except String String → Option String
  | .ok s => some s
  | .error _ => none

-- comments, hex numbers, escapes and hex literals
#guard result ((Expression.parse
    "f(0x1F, // a comment\n /* a\n comment */ \"\\n\\'\\u00e9\", hex\"dEaD\")").map (·.print))
  == some "f(31, \"\\x0a'\\xc3\\xa9\", \"\\xde\\xad\")"

-- not Yul: a keyword as an identifier, a number followed by a letter, a string without an
-- end, a type, an empty `let`
#guard ["let function := 1", "x := 12ab", "x := \"abc", "let x : u256 := 1", "let := 1"].all
  fun s => result ((Statement.parse s).map (·.print)) == none

example : ([yul| { let x := add(1, 2) } |] : Block) =
    ⟨[.VariableDeclaration ["x"] (some (.FunctionCall "add"
      [.Literal (.NumberLiteral 1), .Literal (.NumberLiteral 2)]))]⟩ := rfl

/-- error: Yul: expected an identifier, unexpected Yul.Token.Sym (Yul.Symbol.Assign) -/
#guard_msgs in
example : Statement := [yul| let := 1 |]

end Yul.Test

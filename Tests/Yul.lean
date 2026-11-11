import YulSemnaticsZoo.Yul.Quote
import YulSemnaticsZoo.Yul.Printer
import YulSemnaticsZoo.Yul.WellFormed
import YulSemnaticsZoo.Yul.EVM

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

-- where the docs grammar and solc 0.8.38 differ, as solc: only a call is an expression
-- statement, a decimal number has no leading zero, a declared name does not end with `.` and
-- has no `..`, a backslash before a new line in a string is no character, a hex literal can
-- have one `_` between two pairs of digits, and function parameters can end with a comma
#guard ["x", "\"abc\"", "let x := 024", "let x := 00", "let x. := 1", "let x..y := 1",
  "function f(a..b) {}", "f(1,)", "let x := 1_000",
  "let x := hex\"0_011\"", "let x := hex\"_0011\"", "let x := hex\"0011_\"",
  "let x := hex\"00__11\"",
  "function f(,) {}"].all fun s => result ((Statement.parse s).map (·.print)) == none
#guard ["f()", "let x := 0", "let x := 0x00", "let x.y := 1", "x. := 1", "x..y := 1", "f.()",
  "let s := \"a\\\nb\\\r\nc\\\rd\"", "let x := hex\"00_11_22\"",
  "function f(a,) {}"].map (fun s => result ((Statement.parse s).map (·.print))) ==
  ["f()", "let x := 0", "let x := 0", "let x.y := 1", "x. := 1", "x..y := 1", "f.()",
   "let s := \"abcd\"",
   "let x := \"\\x00\\x11\\\"\"",
   "function f(a) { }"].map some

-- as in solc: a name of an object or data is not empty and not the name of the object that
-- contains it, and the objects and data in an object have different names
#guard ["object \"\" { code { } }", "object \"A\" { code { } data \"\" \"\" }",
  "object \"A\" { code { } object \"A\" { code { } } }",
  "object \"A\" { code { } data \"A\" \"\" }",
  "object \"A\" { code { } object \"B\" { code { } } data \"B\" \"\" }"].all
  fun s => result ((Object.parse s).map (·.print)) == none
#guard result ((Object.parse
    "object \"A\" { code { } object \"B\" { code { } object \"A\" { code { } } } }").map (·.print))
  != none

example : ([yul| { let x := add(1, 2) } |] : Block) =
    ⟨[.VariableDeclaration ["x"] (some (.FunctionCall "add"
      [.Literal (.NumberLiteral 1), .Literal (.NumberLiteral 2)]))]⟩ := rfl

/-- error: Yul: expected an identifier, unexpected Yul.Token.Sym (Yul.Symbol.Assign) -/
#guard_msgs in
example : Statement := [yul| let := 1 |]

def wellFormed (code : String) : Bool :=
  (Object.parseWellFormed EVM.dialect s!"object \"A\" \{ code {code} }").toOption.isSome

-- as in the docs, no function is anywhere in an init block; solc 0.8.38 accepts the first two
-- (its test `function_defined_in_init_nested_1.yul` has the second)
#guard ["{ for { for {} 1 {} { function f() {} } } 1 {} {} }",
  "{ for { for {} 1 { function f() {} } {} } 1 {} {} }",
  "{ for { function f() {} } 1 {} {} }"].all (!wellFormed ·)
-- but `break` is in the body of the innermost loop
#guard wellFormed "{ for { for {} 1 {} { break } } 1 {} {} }"

end Yul.Test

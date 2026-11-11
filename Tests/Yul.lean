import YulSemnaticsZoo.Yul.Syntax

/-! A Yul object that uses every feature of the syntax. It is a test that the syntax can
express these programs: the file fails to build if it cannot. -/

namespace Yul.Test
open Yul

def v (x : Identifier) : Expression := .Identifier x
def n (k : Nat) : Expression := .Literal (.NumberLiteral k)
def s (str : String) : Expression := .Literal (.StringLiteral str.toUTF8.toList)
def f (name : Identifier) (args : List Expression) : Expression := .FunctionCall name args
def stmt (name : Identifier) (args : List Expression) : Statement := .Expression (f name args)

/-- runtime code of `Child`: return the gas plus an immutable -/
def childRuntime : Object where
  name := "Child_deployed"
  code := ⟨
    [ stmt "mstore" [n 0, f "add" [f "gas" [], f "loadimmutable" [s "k"]]]
    , stmt "return" [n 0, n 32] ]⟩
  objects := []
  data := []

/-- init code of `Child`: set the immutable, then return the runtime code -/
def child : Object where
  name := "Child"
  code := ⟨
    [ .VariableDeclaration ["size"] (some (f "datasize" [s "Child_deployed"]))
    , stmt "datacopy" [n 0, f "dataoffset" [s "Child_deployed"], v "size"]
    , stmt "setimmutable" [n 0, s "k", n 7]
    , stmt "return" [n 0, v "size"] ]⟩
  objects := [childRuntime]
  data := []

def factory : Object where
  name := "Factory"
  code := ⟨
    [ stmt "mstore" [n 64, f "memoryguard" [n 128]]
    -- recursion: f(k) = 0 if k = 0, else f(k - 1); r starts at 0; k - 1 is k + (2^256 - 1)
    , .FunctionDefinition "f" ["k"] ["r"] ⟨
        [ .If (f "eq" [f "eq" [v "k", n 0], n 0]) ⟨
            [.Assignment ["r"] (f "f" [f "add" [v "k", n (2 ^ 256 - 1)]])]⟩ ]⟩
    , .VariableDeclaration ["x"] (some (f "f" [n 3]))
    -- contract creation
    , stmt "codecopy" [n 0, f "dataoffset" [s "Child"], f "datasize" [s "Child"]]
    , .VariableDeclaration ["c"] (some (f "create" [n 0, n 0, f "datasize" [s "Child"]]))
    -- code reads: self and external
    , stmt "codecopy" [n 0, n 0, n 32]
    , stmt "extcodecopy" [v "c", n 0, n 0, n 32]
    -- external calls, gas
    , .VariableDeclaration ["ok"] (some (f "call" [f "gas" [], v "c", n 0, n 0, n 0, n 0, n 32]))
    , .If (f "eq" [v "ok", .Literal .FalseLiteral]) ⟨[stmt "return" [n 0, n 0]]⟩
    , .VariableDeclaration ["ok2"]
        (some (f "call" [f "gas" [], f "linkersymbol" [s "lib.sol:L"], n 0, n 0, n 0, n 0, n 0]))
    , .VariableDeclaration ["m"] (some (f "mload" [f "dataoffset" [s "meta"]]))
    , stmt "verbatim_1i_0o" [.Literal (.StringLiteral [0x50]), n 0]
    -- loops: an infinite loop, a loop with continue / break, a function with leave
    , .ForLoop ⟨[.VariableDeclaration ["i"] (some (n 0))]⟩ (.Literal .TrueLiteral)
        ⟨[.Assignment ["i"] (f "add" [v "i", n 1])]⟩
        ⟨[ .If (f "eq" [v "i", n 1]) ⟨[.Continue]⟩
         , .If (f "eq" [v "i", n 3]) ⟨[.Break]⟩ ]⟩
    , .FunctionDefinition "g" [] [] ⟨[.Leave]⟩
    , .Block ⟨[.Expression (f "g" [])]⟩
    , .ForLoop ⟨[]⟩ (n 1) ⟨[]⟩ ⟨[]⟩ ]⟩
  objects := [child]
  data := [⟨"meta", [0xde, 0xad]⟩]

end Yul.Test

import YulSemnaticsZoo.Yul.EVM

namespace Yul.EVM.Test
open Yul Yul.EVM

/-- the arguments of builtin `f`, and the builtin for the literal arguments `lits` -/
def resolve (f : Identifier) (lits : List Literal) : Option (List Arg × Option Builtin) :=
  (dialect.builtin f).map fun (args, mk) => (args, mk lits)

def str (s : String) : Literal := .StringLiteral s.toUTF8.toList

-- builtins without literal arguments: name, number of arguments, builtin, number of returns
#guard
  [ ("add", 2, Builtin.Add, 1), ("eq", 2, .Eq, 1)
  , ("codecopy", 3, .Codecopy, 0), ("extcodecopy", 4, .Extcodecopy, 0)
  , ("mload", 1, .Mload, 1), ("mstore", 2, .Mstore, 0), ("gas", 0, .Gas, 1)
  , ("create", 3, .Create, 1), ("call", 7, .Call, 1), ("return", 2, .Return, 0)
  , ("datacopy", 3, .Datacopy, 0) ].all fun (name, k, b, o) =>
    resolve name [] == some (List.replicate k .Expression, some b) && dialect.outs b == o

-- builtins with a string literal argument
#guard resolve "dataoffset" [str "A"] == some ([.Literal], some (.Dataoffset "A"))
#guard resolve "datasize" [str "A"] == some ([.Literal], some (.Datasize "A"))
#guard resolve "loadimmutable" [str "k"] == some ([.Literal], some (.Loadimmutable "k"))
#guard resolve "linkersymbol" [str "l.sol:L"] == some ([.Literal], some (.Linkersymbol "l.sol:L"))
#guard resolve "setimmutable" [str "k"]
  == some ([.Expression, .Literal, .Expression], some (.Setimmutable "k"))
#guard [Builtin.Dataoffset "A", .Datasize "A", .Loadimmutable "k", .Linkersymbol "L"].all
  (dialect.outs · == 1)
#guard dialect.outs (.Setimmutable "k") == 0
-- a name that is not a string literal, or not UTF-8
#guard resolve "dataoffset" [.NumberLiteral 1] == some ([.Literal], none)
#guard resolve "dataoffset" [.TrueLiteral] == some ([.Literal], none)
#guard resolve "dataoffset" [.StringLiteral [0xff]] == some ([.Literal], none)
#guard resolve "dataoffset" [] == some ([.Literal], none)
#guard resolve "dataoffset" [str "A", str "B"] == some ([.Literal], none)

-- memoryguard takes a number literal that fits in a word
#guard resolve "memoryguard" [.NumberLiteral 128] == some ([.Literal], some (.Memoryguard 128))
#guard resolve "memoryguard" [.NumberLiteral (2 ^ 256 - 1)]
  == some ([.Literal], some (.Memoryguard (BitVec.ofNat 256 (2 ^ 256 - 1))))
#guard resolve "memoryguard" [.NumberLiteral (2 ^ 256)] == some ([.Literal], none)
#guard resolve "memoryguard" [str "128"] == some ([.Literal], none)
#guard dialect.outs (.Memoryguard 0) == 1

-- verbatim_<i>i_<o>o takes a string literal, then i expressions
#guard resolve "verbatim_2i_1o" [.StringLiteral [0x50]]
  == some ([.Literal, .Expression, .Expression], some (.Verbatim 2 1 [0x50]))
#guard (resolve "verbatim_0i_0o" []).map (·.1) == some [.Literal]
#guard (resolve "verbatim_99i_99o" []).map (·.1.length) == some 100
#guard resolve "verbatim_1i_0o" [.NumberLiteral 1] == some ([.Literal, .Expression], none)
#guard dialect.outs (.Verbatim 2 7 []) == 7
-- names solc does not accept (`([1-9]?[0-9])i_([1-9]?[0-9])o`)
#guard ["verbatim_100i_0o", "verbatim_0i_100o", "verbatim_01i_0o", "verbatim_1_000i_0o",
  "verbatim_i_0o", "verbatim_1i_0", "verbatim_1o_1i", "verbatim_1i_1o_", "verbatim", "verbatim_",
  "Verbatim_1i_1o", "verbatim_+1i_0o"].all (resolve · [] == none)

-- names that are not builtins
#guard ["", "foo", "Add", "sub", "iszero", "sstore", "pop", "stop", "calldataload", "f"].all
  (resolve · [] == none)

end Yul.EVM.Test

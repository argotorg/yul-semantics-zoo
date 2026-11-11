import YulSemnaticsZoo.Yul.EVM

namespace Yul.EVM.Test
open Yul Yul.EVM

/-- the arguments of builtin `f`, and the builtin for the literal arguments `lits` -/
def resolve (f : Identifier) (lits : List Literal) : Option (List Arg × Option Builtin) :=
  (dialect.builtin f).map fun (args, mk) => (args, mk lits)

-- the literal of setimmutable is its middle argument
#guard resolve "setimmutable" [.StringLiteral [0x6b]]
  == some ([.Expression, .Literal, .Expression], some (.Setimmutable "k"))
-- a literal of the wrong kind, or a name that is not UTF-8
#guard resolve "dataoffset" [.NumberLiteral 1] == some ([.Literal], none)
#guard resolve "dataoffset" [.StringLiteral [0xff]] == some ([.Literal], none)
-- memoryguard takes a number that fits in a word
#guard resolve "memoryguard" [.NumberLiteral (2 ^ 256 - 1)]
  == some ([.Literal], some (.Memoryguard (BitVec.ofNat 256 (2 ^ 256 - 1))))
#guard resolve "memoryguard" [.NumberLiteral (2 ^ 256)] == some ([.Literal], none)
-- verbatim names as solc accepts them: `verbatim_([1-9]?[0-9])i_([1-9]?[0-9])o`
#guard resolve "verbatim_2i_1o" [.StringLiteral [0x50]]
  == some ([.Literal, .Expression, .Expression], some (.Verbatim 2 1 [0x50]))
#guard (resolve "verbatim_99i_99o" []).map (·.1.length) == some 100
#guard ["verbatim_100i_0o", "verbatim_01i_0o", "verbatim_1_000i_0o", "verbatim_i_0o"].all
  (resolve · [] == none)
-- as in solc: verbatim code is not empty
#guard resolve "verbatim_0i_0o" [.StringLiteral []] == some ([.Literal], none)

#guard [Builtin.Datasize "A", .Dataoffset "A", .Loadimmutable "A", .Gas].map dataName
  == [some "A", some "A", none, none]

-- the names of solc 0.8.33 that a declaration cannot use: instructions (not the ones only in EOF),
-- builtins, and the names that start with `verbatim`
#guard ["sub", "jump", "dup16", "push0", "pc", "datasize", "verbatim", "verbatimx"].all reserved
#guard !["rjump", "eofcreate", "dataload", "x", "verbatix", "Add"].any reserved

end Yul.EVM.Test

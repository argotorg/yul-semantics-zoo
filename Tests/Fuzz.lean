import Fuzz.Solc

namespace Fuzz.Test
open EVM Fuzz

-- the bytes that the fuzzer does not give to solc decode to `none`
#guard eofImmediate.all (decode ·.toUInt8 [] == none)

-- `agrees` is false on a different instruction, and on a byte without an instruction that
-- solc prints as one of ours (solc output from solc 0.8.33)
#guard agrees (disassemble [0x02, 0x01]) "MUL ADD "
#guard !agrees (disassemble [0x01]) "MUL "
#guard !agrees (disassemble [0x02]) "ADD "

end Fuzz.Test

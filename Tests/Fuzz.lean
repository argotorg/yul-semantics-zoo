import Fuzz.Solc
import Fuzz.YulGen
import YulSemnaticsZoo.Yul.EVM
import YulSemnaticsZoo.Yul.Subset

namespace Fuzz.Test
open EVM Fuzz

-- `agrees` is false on a different instruction, and on a byte without an instruction that
-- solc prints as one of ours (solc output from solc 0.8.38)
#guard agrees (disassemble [0x02, 0x01]) "MUL ADD "
#guard !agrees (disassemble [0x01]) "MUL "
#guard !agrees (disassemble [0x02]) "ADD "

/-- `f` is a builtin of the EVM dialect with `k` arguments that are not literals, and `outs`
results -/
def isBuiltin (outs : Nat) (f : String) (k : Nat) : Bool :=
  match Yul.EVM.builtin f with
  | some (args, mk) =>
    args == List.replicate k .Expression && (mk []).map Yul.EVM.outs == some outs
  | none => false

-- the Yul fuzzer skips a call of a solc builtin that is not in the EVM dialect
-- (`Fuzz.Yul.otherBuiltins`), so it does not find a name in these lists that the dialect does not
-- have
#guard Yul.builtins1.all fun (f, k) => isBuiltin 1 f k
#guard Yul.builtins0.all fun (f, k) => isBuiltin 0 f k

/-- `f` is a builtin of the subset dialect with `k` arguments and `outs` results, as in the EVM
dialect -/
def isSubsetBuiltin (outs : Nat) (f : String) (k : Nat) : Bool :=
  match Yul.Subset.builtin? f with
  | some b => Yul.Subset.ins b == k && Yul.Subset.outs b == outs && isBuiltin outs f k
  | none => false

-- the clocked fuzzer calls each of the 8 builtins of the subset dialect, and no other builtin
#guard Yul.subset1.all fun (f, k) => isSubsetBuiltin 1 f k
#guard Yul.subset0.all fun (f, k) => isSubsetBuiltin 0 f k
#guard (Yul.subset1 ++ Yul.subset0).length == 8

end Fuzz.Test

import Fuzz.Solc
import Fuzz.YulGen
import YulSemnaticsZoo.Yul.Semantics.Clocked.Interp

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

/-- `f` is a builtin of the EVM dialect with `k` arguments that are not literals and `outs`
results, and the clocked semantics defines it: it does not halt with `unsupported` -/
def isClockedBuiltin (outs : Nat) (f : String) (k : Nat) : Bool :=
  isBuiltin outs f k &&
    match Yul.EVM.dialect.builtin f with
    | some (_, mk) =>
      (Yul.Clocked.builtin [] (fun _ => 0) (mk []) (List.replicate k 0) (Yul.Clocked.start 0)).val
        != .halt .unsupported
    | none => false

-- the clocked fuzzer calls each of the 8 builtins that the clocked semantics defines, and no
-- other builtin
#guard Yul.subset1.all fun (f, k) => isClockedBuiltin 1 f k
#guard Yul.subset0.all fun (f, k) => isClockedBuiltin 0 f k
#guard ((Yul.subset1 ++ Yul.subset0).map (·.1)).eraseDups.length == 8

end Fuzz.Test

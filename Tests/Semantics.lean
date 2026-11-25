import YulSemnaticsZoo.Semantics
import Fuzz.Gen

namespace Semantics.Test
open Semantics Fuzz

/-- a word near 0, near 2 ^ 256, or any word -/
def word : Gen Word := do
  match ← nat 0 2 with
  | 0 => return BitVec.ofNat 256 (← nat 0 64)
  | 1 => return BitVec.ofNat 256 (2 ^ 256 - 1 - (← nat 0 64))
  | _ => return BitVec.ofNat 256 (← nat 0 (2 ^ 256 - 1))

/-- for random values: mload after mstore at the same offset gives the value; mstore changes no
byte before or after its 32 bytes; calldataload gives the 32 bytes at the offset, with zeros
after the end of the calldata -/
def prop : Gen Bool := do
  let (a, b, v, w) := (← word, ← word, ← word, ← word)
  let m := mstore Memory.empty b w
  -- an address near the 32 bytes at `a`
  let x := a.toNat + (← nat 0 96) - 32
  let i ← list (← nat 0 64) Fuzz.byte
  let off ← if ← coin then pure (BitVec.ofNat 256 (← nat 0 70)) else word
  return mload (mstore m a v) a == v
    && (a.toNat ≤ x && x < a.toNat + 32 || mstore m a v x == m x)
    && calldataload i off == ofBytes ((i.drop off.toNat ++ List.replicate 32 0).take 32)

#guard ((list 1000 prop).run' (mkStdGen 0)).all id

-- big-endian: the last byte of the word is at the highest address
#guard read (mstore Memory.empty 0 1) 0 33 == List.replicate 31 0 ++ [1, 0]

end Semantics.Test

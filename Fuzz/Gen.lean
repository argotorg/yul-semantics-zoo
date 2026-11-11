/-!
# Random generation for the fuzzers
-/

namespace Fuzz

abbrev Gen := StateM StdGen

def nat (lo hi : Nat) : Gen Nat := modifyGet fun g => randNat g lo hi

def byte : Gen UInt8 := return (← nat 0 255).toUInt8

def list (k : Nat) (x : Gen α) : Gen (List α) := (List.range k).mapM fun _ => x

def pick (xs : List α) (d : α) : Gen α := return xs.getD (← nat 0 (xs.length - 1)) d

def coin : Gen Bool := return (← nat 0 1) == 0

end Fuzz

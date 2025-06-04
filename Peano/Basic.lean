inductive MyNat where
  | zero : MyNat
  | succ : MyNat -> MyNat

namespace MyNat

def natToMyNat : Nat → MyNat
  | 0 => MyNat.zero
  | Nat.succ n => MyNat.succ (natToMyNat n)

instance : OfNat MyNat n where
  ofNat := natToMyNat n

def add (x y : MyNat) :=
  match y with
  | zero => x
  | succ n => succ (add x n)

infixl:65 "+" => add

theorem add_zero : x + zero = x := by rfl
theorem add_succ : x + succ n = succ (x + n) := by rfl


theorem zero_add : zero + x = x := by
  induction x with
  | zero => rw [add_zero]
  | succ d ih => rw [add_succ, ih]

end MyNat

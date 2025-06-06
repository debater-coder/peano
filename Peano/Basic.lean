import Mathlib

inductive MyNat where
  | zero : MyNat
  | succ : MyNat -> MyNat

namespace MyNat

def natToMyNat : Nat → MyNat
  | 0 => MyNat.zero
  | Nat.succ n => MyNat.succ (natToMyNat n)

instance : OfNat MyNat n where
  ofNat := natToMyNat n

def pred (n : MyNat) :=
  match n with
  | zero => zero
  | succ n => n

theorem pred_succ (n : MyNat) : n = pred (succ n) := by rfl

theorem one_eq_succ_zero : (1:MyNat) = succ zero := by rfl

theorem succ_ne_zero (n : MyNat) : succ n ≠ zero := by tauto

end MyNat

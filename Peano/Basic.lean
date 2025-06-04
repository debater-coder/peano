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

def add (x y : MyNat) :=
  match y with
  | zero => x
  | succ n => succ (add x n)

infixl:65 "+" => add


@[simp] theorem add_zero : x + zero = x := by rfl
theorem add_succ : x + succ n = succ (x + n) := by rfl


@[simp] theorem zero_add : zero + x = x := by
  induction x with
  | zero => rfl
  | succ d ih => rw [add_succ, ih]

theorem succ_add : succ n + x = succ (n + x) := by
  induction x with
  | zero => rfl
  | succ d ih => rw [add_succ, add_succ, ih]

theorem succ_eq_add_one (n : MyNat): succ n = n + (1:MyNat) := by rfl

theorem succ_inj (a b : MyNat) : succ a = succ b → a = b := by
  sorry

theorem add_right_cancel (a b n : MyNat) : a + n = b + n → a = b := by
  intro h
  induction n with
  | zero => exact h
  | succ d ih =>
    repeat rw [add_succ] at h
    apply succ_inj at h
    exact ih h


end MyNat

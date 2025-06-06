import Peano.Basic

open MyNat

namespace MyAdd

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

theorem succ_inj (a b : MyNat) (h: succ a = succ b) : a = b := by
  rw [pred_succ a, pred_succ b, h]

theorem add_comm (a b : MyNat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ d ih => rw [add_succ, succ_add, ih]

theorem add_assoc (a b c : MyNat) : a + b + c = a + (b + c) := by
  induction c with
  | zero => simp
  | succ d ih =>
    repeat rw [add_succ]
    rw [ih]

theorem add_right_cancel (a b n : MyNat) (h: a + n = b + n): a = b := by
  induction n with
  | zero => exact h
  | succ d ih =>
    repeat rw [add_succ] at h
    apply succ_inj at h
    exact ih h

theorem add_left_cancel (a b n : MyNat) (h: n + a = n + b) : a = b := by
  rw [add_comm n a, add_comm n b] at h
  exact add_right_cancel a b n h

end MyAdd

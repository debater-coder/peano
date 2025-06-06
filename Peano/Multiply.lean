import Peano.Basic
import Peano.Add

namespace MyMul

open MyNat
open MyAdd


def multiply (x y : MyNat) :=
  match y with
  | zero => zero
  | succ n => add (multiply x n) x

infixl:70 "*" => multiply

@[simp] theorem mul_zero (x : MyNat) : x * zero = zero := by rfl

theorem mul_succ (x y : MyNat) : x * succ y = x * y + x := by rfl

@[simp] theorem mul_one (x : MyNat) : x * (1:MyNat) = x := by
    rw [one_eq_succ_zero, mul_succ]
    simp

@[simp] theorem zero_mul (x : MyNat) : zero * x = zero := by
  induction x with
  | zero => simp
  | succ d ih =>
    rw [mul_succ, ih]
    simp

theorem succ_mul (x y : MyNat) : succ x * y = x * y + y := by
  induction y with
  | zero => simp
  | succ d ih =>
    rw [mul_succ, mul_succ, ih, add_succ, add_succ]
    rw [add_assoc, add_assoc, add_comm x d]


theorem two_mul (x : MyNat) : (2:MyNat) * x = x + x := by
  have h : (2:MyNat) = succ (succ zero) := by rfl
  rw [h, succ_mul, succ_mul]
  simp

theorem mul_comm (x y : MyNat) : x * y = y * x := by
  induction y with
  | zero => rw [zero_mul, mul_zero]
  | succ d ih => rw [mul_succ, succ_mul, ih]

theorem one_mul (x : MyNat) : (1:MyNat) * x = x := by
  rw [mul_comm, mul_one]

theorem add_mul (x y z : MyNat) : (x + y) * z = x * z + y * z := by
  induction z with
  | zero => simp
  | succ d ih =>
    repeat rw [mul_succ]
    rw [add_comm (y*d) y]
    nth_rw 2 [← add_assoc]
    rw [add_assoc (x*d) x]
    rw [add_assoc (x*d) (x+y)]
    rw [add_comm (x+y)]
    repeat rw [← add_assoc]
    rw [ih]

theorem mul_add (x y z : MyNat) : z * (x + y) = z * x + z * y := by
  rw [mul_comm, mul_comm z x, mul_comm z y]
  exact add_mul x y z

theorem mul_assoc (x y z : MyNat) : x * y * z = x * (y * z) := by
  induction z with
  | zero => simp
  | succ d ih =>
    repeat rw [mul_succ]
    rw [ih, mul_add]

theorem mul_left_ne_zero (a b : MyNat) (h: a * b ≠ zero) : b ≠ zero := by
  contrapose! h
  rw [h, mul_zero a]

theorem mul_eq_zero (a b : MyNat) (h : a * b = zero) : a = zero ∨ b = zero := by
  induction a with
  | zero =>
    left
    simp
  | succ d ih =>
    cases b with
    | zero =>
      right
      rfl
    | succ n => tauto

lemma mul_eq_zero_xor (a b : MyNat) (ha: a ≠ zero) (h: a * b = zero) : b = zero := by
  cases mul_eq_zero a b h with
  | inl => tauto
  | inr h1 => exact h1


theorem mul_left_cancel (a b c : MyNat) (h : a * b = a * c) (hx: a ≠ zero) : b = c := by
  induction b generalizing c with -- since b = c, c needs to change when b changes
  | zero =>
    rw [mul_zero] at h
    exact symm (mul_eq_zero_xor a c hx (symm h))
  | succ d ih =>
    cases c with
    | zero =>
      exact mul_eq_zero_xor a d.succ hx h
    | succ e =>
       rw [mul_succ, mul_succ] at h
       apply MyAdd.add_right_cancel at h
       exact congrArg succ (ih e h)

theorem mul_right_cancel (a b c : MyNat) (h: b * a = c * a) (hx: a ≠ zero) : b = c := by
  rw [mul_comm b a, mul_comm c a] at h
  exact mul_left_cancel a b c h hx
end MyMul

import Peano.Basic
import Peano.Add
import Peano.Multiply

namespace MyPow
open MyNat
open MyAdd
open MyMul

def pow (x y : MyNat) :=
  match y with
  | zero => (1 : MyNat)
  | succ n => pow x n * x

infix:75 "^" => pow

@[simp] theorem zero_pow_zero : zero ^ zero = 1 := by rfl
@[simp] theorem pow_zero (n : MyNat) : n ^ zero = 1 := by rfl
theorem pow_succ (x n : MyNat) : x ^ succ n = x ^ n * x := by rfl

theorem zero_pow (n : MyNat) : zero ^ succ n = zero := by
  rw [pow_succ]
  simp

theorem pow_two (n : MyNat) : n ^ (2:MyNat) = n * n := by
  have h : (2:MyNat) = succ (succ zero) := by rfl
  rw [h, pow_succ, pow_succ, pow_zero, one_mul]

theorem binomial_square (a b : MyNat)
  : (a + b) ^ (2:MyNat) = a ^ (2:MyNat) + (2:MyNat) * a * b + b ^ (2:MyNat) := by
  rw [pow_two, add_mul, mul_add, mul_add, ← add_assoc, add_assoc (a*a) (a*b) (b*a)]
  rw [mul_comm b a, ← two_mul (a*b), ←mul_assoc]
  repeat rw [← pow_two]

end MyPow

import LeanCourse.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases lt_or_ge x 0 with h0 | h1
  · linarith [abs_of_neg h0]
  · linarith [abs_of_nonneg h1]

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
 linarith [abs_neg x, le_abs_self (-x)]


theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases lt_or_ge x 0 with h0 | h1
  · rcases lt_or_ge y 0 with p0 | p1
    · have : |x| = -x := by linarith [abs_of_neg h0]
      have : |y| = -y := by linarith [abs_of_neg p0]
      have : -(x+y)=|x|+|y| := by linarith
      have : x + y < 0 := by linarith
      have : -(x+y)=|x+y| := by linarith [abs_of_neg this]
      have : |x+y|=|x|+|y| := by linarith
      apply le_of_eq
      exact this
    · sorry

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · intro h
    rcases lt_or_ge y 0 with h0 | h1
    · right
      have : |y|=-y := by rw[abs_of_neg h0]
      linarith
    · left
      have : |y|=y := by rw[abs_of_nonneg h1]
      linarith
  · intro h
    rcases h with h0 | h1
    · linarith [le_abs_self y]
    · linarith [neg_le_abs_self y]

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  sorry

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, h'⟩
  rcases h' with h0 | h1
  · linarith [sq_nonneg x, sq_nonneg y]
  · linarith [sq_nonneg x, sq_nonneg y]


example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1 : (x-1)*(x+1)=0 := by linarith
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1
  rcases h1 with p0 | p1
  · left;linarith
  · right;linarith


example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · by_cases h : P
    · intro q
      right; apply q h
    · intro q
      left
      exact h
  · intro q1 q2
    rcases q1 with h0 | h1
    · contradiction
    · exact h1

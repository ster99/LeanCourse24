import LeanCourse.Common
open Real Function Set
open Finset BigOperators

example {a r : ℝ} (n : ℕ) (h : r ≠ 1)
: ∑ i ∈ range (n + 1), a * r ^ i = (a * r ^ (n + 1) - a) / (r - 1) := by
  induction n with
  | zero =>
  simp
  rw [Eq.symm (mul_sub_one a r), mul_div_cancel_right₀ a]
  exact sub_ne_zero_of_ne h

  | succ n hi =>
  rw [sum_range_succ (fun x ↦ a * r ^ x) (n + 1), hi, div_add', div_left_inj']
  have hh: r ^ (n + 1) * (r - 1)= r ^ (n + 1 + 1) - r ^ (n + 1) := by
    calc
    r ^ (n + 1) * (r - 1) = r ^ (n + 1) * r - r ^ (n + 1) := by exact mul_sub_one (r ^ (n + 1)) r
    _ = r ^ (n + 1 + 1) - r ^ (n + 1) := by rfl
  rw[mul_assoc a (r ^ (n + 1)) (r - 1), hh, mul_sub_left_distrib a (r ^ (n + 1 + 1)) (r ^ (n + 1))]
  simp
  exact sub_ne_zero_of_ne h
  exact sub_ne_zero_of_ne h

--
/-
Let $n$ and $k$ be nonnegative integers with $k \leqslant n$. Then
(i ) $\binom{n}{0}=\binom{n}{n}=1$
(ii) $\binom{n}{k}=\binom{n}{n-k}$.
-/

def binom (n k : ℕ) (h: k ≤ n): ℕ := n.factorial / (k.factorial * (n - k).factorial)
--one has to feed in the function binom  n, k and the proof that k ≤ n

example (n k: ℕ) (h: k ≤ n): binom n k h = binom n (n - k) (Nat.sub_le n k) ∧ binom n 0 (Nat.zero_le n) = 1  ∧ binom n n (Nat.le_refl n) = 1 := by
  constructor
  · unfold binom
    rw [Nat.mul_comm, Nat.sub_sub_self h]
  · constructor
    · unfold binom
      simp
      refine Nat.div_self ?right.left.H
      exact Nat.factorial_pos n
    · unfold binom
      simp
      refine Nat.div_self ?right.left.H

/--if you want it done with choose of mathlib then it hard to show steps because as soon
as you simp you automatically get the claim by lemmas in mathlib-/
example (n k: ℕ) (h: k ≤ n) : n.choose k = n.choose (n - k) ∧ n.choose 0 = 1 ∧ n.choose n = 1 := by
  constructor
  · exact Eq.symm (Nat.choose_symm h)
  · constructor
    · simp
    · simp


/-- I defined an extended f with the value 0 => 2 for convenience. Otherwise one should have
created a lemma merging Nat.le_induction and Nat.twoStepInduction. Not optimal in terms of time
-/
def f : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | (n + 1) => f n + 2 * f (n - 1)

#check Nat.le_induction
#check Nat.twoStepInduction

example (n : ℕ) : f n = (2 : ℤ)^n + (-1) ^ n := by
  induction' n using Nat.twoStepInduction with k h₁ h₂
  · simp
    rw [f]
  · simp
    rw [f]
  · rw [f]
    simp
    rw [h₁, h₂]
    ring
    intro h
    contradiction

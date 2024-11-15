import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real Function Set Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 2, 3, 5, 6.
  Read chapter 4, section 1.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 29.10.2023.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


example {p : ℝ → Prop} (h : ∀ x, p x) : ∃ x, p x := by {
  sorry
  }


example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by {
  sorry
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by {
  sorry
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by {
  sorry
  }

/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by {
  sorry
  }

def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (a : ℝ) : SequentialLimit (fun n : ℕ ↦ a) a := by {
  sorry
  }

/-
`(n)!` denotes the factorial function on the natural numbers.
The parentheses are mandatory when writing.
Use `calc` to prove this.
You can use `exact?` to find lemmas from the library,
such as the fact that factorial is monotone. -/
example (n m k : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by {
  sorry
  }

section Set

variable {α β : Type*} {s t : Set α}

/- Prove the following statements about sets. -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by {
  sorry
  }

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by {
  sorry
  }

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by {
  sorry
  }

example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by {
  sorry
  }

example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by {
  sorry
  }

end Set

/-! # Exercises to hand-in. -/


/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by {
  constructor
  · intro h
    obtain ⟨ x , hx ⟩ := h
    obtain hc1|hc2 := hx
    · left
      use x
    · right
      use x
  · intro h
    obtain hpx|hqx := h
    obtain ⟨ x, k ⟩ := hpx
    use x
    · left
      assumption
    obtain ⟨ y, j ⟩ := hqx
    use y
    · right
      assumption
  }

section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by {
  constructor
  · unfold SurjectiveFunction
    intro h
    intro y
    specialize h y
    obtain ⟨ x, hx ⟩ := h
    simp at hx
    use f x
  · unfold SurjectiveFunction
    unfold SurjectiveFunction at hf
    intro hg y₁
    simp
    specialize hg y₁
    obtain ⟨ x₁, hx₁ ⟩ := hg
    specialize hf x₁
    obtain ⟨ x₂, hx₂ ⟩ := hf
    use x₂
    rw [hx₂]
    exact hx₁
  }

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by {

  unfold SurjectiveFunction at hf
  unfold SurjectiveFunction
  intro y
  simp
  ring
  specialize hf ( (y - 1) / 2)
  obtain ⟨ x₁, hx₁ ⟩ := hf
  use (x₁ - 12) / 3
  ring
  rw[hx₁]
  ring
  }

/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by {
  let R := {x | x ∉ f x}
  sorry
  }

end Surjectivity

/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by {

  intro ε hε
  unfold SequentialLimit at hs ht
  have hε₂ : ε/2 > 0 := by linarith
  specialize hs (ε/2) hε₂
  specialize ht (ε/2) hε₂
  obtain ⟨ N, hN ⟩ := hs
  obtain ⟨ N', hN' ⟩ := ht
  let N₀ := max N N'
  simp
  use N₀
  intro m
  specialize hN m
  specialize hN' m
  intro hmax
  rw[add_comm, ← sub_sub, add_sub_assoc, add_sub_right_comm]
  have hmN : m ≥ N := by exact le_of_max_le_left hmax
  have hmN' : m ≥ N' := by exact le_of_max_le_right hmax
  specialize hN hmN
  specialize hN' hmN'
  calc
    |t m - b + (s m - a)| ≤  |t m - b| + |s m - a| := by apply abs_add_le
    _ < ε/2 + ε/2 := by gcongr
    _ = ε := by linarith
  }

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by {

  unfold SequentialLimit at hs
  unfold SequentialLimit
  intro ε εp
  by_cases h : c=0
  · use 0
    intro n
    simp
    refine abs_sub_lt_of_nonneg_of_lt ?h.a_nonneg ?h.a_lt_n ?h.b_nonneg ?h.b_lt_n
    · calc
      c * s n = 0 * s n := by rw[h]
      _ = 0 := by exact zero_mul (s n)
      0 ≥ 0 := by exact Preorder.le_refl 0
    · calc
      c * s n = 0 * s n := by rw[h]
      _ = 0 := by exact zero_mul (s n)
      0 < ε := by assumption
    · calc
      0 = 0 * a := by exact Eq.symm (zero_mul a)
      _ = c * a := by rw[← h]
      _ ≤ c * a := by rfl
    · calc
      c * a = 0 * a := by rw[h]
      _ = 0 := by exact zero_mul (a)
      0 < ε := by assumption
  · specialize hs (ε/|c|)
    have hc : |c| > 0 := by exact abs_pos.mpr h
    have hεc : (ε/|c|) > 0 := by exact div_pos εp hc
    specialize hs hεc
    obtain ⟨ N₁, hN₁ ⟩ := hs
    use N₁
    simp
    intro n
    specialize hN₁ n
    intro hn
    specialize hN₁ hn
    calc
      |c * s n - c * a| = |c * (s n - a)| := by rw[mul_sub]
      _  = |c| * |s n - a| := by exact abs_mul c (s n - a)
      _  <  |c| *  (ε/ |c|) := by gcongr
      _ = ε := by rw[mul_div, mul_div_right_comm, div_self, one_mul]; exact abs_ne_zero.mpr h
  }





section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by {

  unfold EventuallyGrowsFaster
  simp
  intro k
  use k
  intro n h₁
  gcongr
  }

/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by {

  unfold EventuallyGrowsFaster at h₁ h₂
  unfold EventuallyGrowsFaster
  simp
  intro k
  specialize h₁ k
  specialize h₂ k
  obtain ⟨ N, hN ⟩ := h₁
  obtain ⟨ N', hN' ⟩ := h₂
  let N₀ := max N N'
  use N₀
  intro m
  intro hmax
  specialize hN m
  specialize hN' m
  have hmN : m ≥ N := by exact le_of_max_le_left hmax
  have hmN' : m ≥ N' := by exact le_of_max_le_right hmax
  specialize hN hmN
  specialize hN' hmN'
  calc
    k * (t₁ m + t₂ m) = k * t₁ m + k * t₂ m := by ring
    _ ≤ s₁ m + s₂ m := by linarith
  }

/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by {

      let g : ℕ → ℕ := (fun n ↦ factorial n)
      unfold EventuallyGrowsFaster
      use g
      constructor
      · intro k
        use k
        simp
        intro n hp
        simp[g]
        calc
        k * (factorial n) ≤ (n+1) * (factorial n) := by gcongr; sorry
        _ = factorial (n+1) := by exact rfl
      · intro n
        simp[g]
        exact factorial_ne_zero n
  }

end Growth

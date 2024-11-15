import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Set Nat
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 4, sections 2, 3.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 5.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- Do the exercises about sets from last exercise set, if you haven't done them because
we didn't cover the material in class yet. -/


variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by {
  sorry
  }


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by {
  sorry
  }

/- `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal.
You can use the `ext` tactic to show that two pairs are equal.
`simp` can simplify `(a, b).1` to `a`.
This is true by definition, so calling `assumption` below also works directly. -/

example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff
example (a a' : α) (b b' : β) (ha : a = a') (hb : b = b') : (a, b) = (a', b') := by
  ext
  · simp
    assumption
  · assumption

/- To practice, show the equality of the following pair. What is the type of these pairs? -/
example (x y : ℝ) : (123 + 32 * 3, (x + y) ^ 2) = (219, x ^ 2 + 2 * x * y + y ^ 2) := by {
  sorry
  }

/- `A ≃ B` means that there is a bijection from `A` to `B`.
So in this exercise you are asked to prove that there is a bijective correspondence between
  functions from `ℤ × ℕ` to `ℤ × ℤ`
and
  functions from `ℕ` to `ℕ`
This is an exercise about finding lemmas from the library.
Your proof is supposed to only combine results from the library,
you are not supposed to define the bijection yourself.
If you want, you can use `calc` blocks with `≃`. -/
example : (ℤ × ℕ → ℤ × ℤ) ≃ (ℕ → ℕ) := by {
  sorry
  }

/- Prove a version of the axiom of choice Lean's `Classical.choose`. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by {
  sorry
  }


/-! # Exercises to hand-in. -/


/- ## Converging sequences

Prove two more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma sequentialLimit_reindex {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by {

  unfold SequentialLimit
  unfold SequentialLimit at hs
  intro ε εpos
  specialize hs ε εpos
  obtain ⟨ bN , hN ⟩ := hs
  specialize hr bN
  obtain ⟨ M , hM ⟩ := hr
  use M
  simp at hN hM
  simp
  /- From here I feel like I am overcomplicating things
    but I really don't see the cleaner way to go, I may ask you at lecture -/
  intro n
  specialize hM n
  intro h
  specialize hM h
  specialize hN (r n)
  specialize hN hM
  exact hN

  }


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma sequentialLimit_squeeze {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by {

  unfold SequentialLimit at hs₁ hs₃
  unfold SequentialLimit
  intro ε εpos
  specialize hs₁ ε εpos
  specialize hs₃ ε εpos
  obtain ⟨ N₁ , hN₁ ⟩ := hs₁
  obtain ⟨ N₃ , hN₃ ⟩ := hs₃
  let N₀ := max N₁ N₃
  use N₀
  intro n
  specialize hN₁ n
  specialize hN₃ n
  specialize hs₁s₂ n
  specialize hs₂s₃ n
  intro h
  have h₁ : n ≥ N₁ := by {
    calc
    n ≥ N₀ := h
    _ ≥ N₁ := by exact Nat.le_max_left N₁ N₃
  }
  have h₃ : n ≥ N₃ := by {
    calc
    n ≥ N₀ := h
    _ ≥ N₃ := by exact Nat.le_max_right N₁ N₃
  }
  specialize hN₁ h₁
  specialize hN₃ h₃
  have hh₁ : -ε < s₁ n - a ∧ s₁ n - a < ε := by exact abs_lt.mp hN₁
  have hh₃ : -ε < s₃ n - a ∧ s₃ n - a < ε := by exact abs_lt.mp hN₃
  obtain ⟨ h1 , h2 ⟩ := hh₁
  obtain ⟨ g1, g2 ⟩ := hh₃
  have k1 : -ε < s₂ n - a := by {
    calc
    -ε < s₁ n - a := by exact h1
    _ ≤ s₂ n -a := by gcongr
  }
  have k2 : s₂ n - a < ε := by {
    calc
    s₂ n - a ≤ s₃ n - a := by gcongr
    _ < ε := by exact g2
  }
  have hh₂ : |s₂ n - a| < ε := by {
    refine abs_sub_lt_iff.mpr ?_
    constructor
    · exact k2
    · rw[Eq.symm (neg_sub a (s₂ n) )] at k1
      exact lt_of_neg_lt_neg k1;
  }
  assumption
  }


example ( a b : ℝ ) : a-b = -(b-a) := by exact Eq.symm (neg_sub b a)

/- ## Sets -/

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by {

    ext x
    constructor
    · intro h
      obtain ⟨ a , b ⟩ := h
      simp at a
      obtain ⟨ x₁, hx₁ ⟩ := a
      simp
      use x₁
      constructor
      · constructor
        · exact hx₁.1
        · have j : f x₁ ∈ t := by exact mem_of_eq_of_mem (id hx₁.2) b
          assumption
      · exact hx₁.2
    · intro h
      simp at h
      obtain ⟨ x₁, hx₁ ⟩ := h
      simp
      constructor
      · use x₁
        constructor
        · exact hx₁.1.1
        · exact hx₁.2
      · have  j : x ∈ t := by exact mem_of_eq_of_mem (id (Eq.symm hx₁.2)) hx₁.1.2
        assumption

  }

/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by {

  ext x
  constructor
  · simp
    intro h
    by_cases hpos : x ≥ 0
    · right
      have tau : 4 * 4 ≤ x * x := by {
      calc
      4 * 4 = 16 := by ring
      _ ≤ x^2 := by exact h
      x^2 = x * x := by apply pow_two x
      }
      sorry
    . left
      simp at hpos
      have tau : 4 * 4 ≤ x * x := by {
      calc
      4 * 4 = 16 := by ring
      _ ≤ x^2 := by exact h
      x^2 = x * x := by apply pow_two x
      }
      sorry
  · simp
    intro h
    rw[pow_two x]
    by_cases hm : x ≥ 4
    · calc
      16 = 4 * 4 := by ring
      _ ≤ x * x := by gcongr
    · simp at hm
      obtain hc1|hc2:=h
      · have hh : -x ≥ 4 := by exact le_neg_of_le_neg hc1
        calc
        16 = 4 * 4 := by ring
        _ ≤ (-x) * (-x) := by gcongr
        _ = x * x := by exact neg_mul_neg x x
      . have : @OfNat.ofNat ℝ 4 instOfNatAtLeastTwo < @OfNat.ofNat ℝ 4 instOfNatAtLeastTwo := by {
        calc
        4 ≤ x := hc2
        _ < 4 := hm
        }
        norm_num at this

  }

/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/

def conditionalInverse (y : β)
  (h : ∃ x : α, x ∈ s ∧ f x = y) : α :=
  Classical.choose h


lemma invFun_spec (y : β) (h : ∃ x, x ∈ s ∧ f x = y) :
    f (conditionalInverse f s y h) = y := by {
      have k := Classical.choose_spec h
      exact k.2
    }

lemma invFun_spec' (y : β) (h : ∃ x, x ∈ s ∧ f x = y) :
    conditionalInverse f s y h ∈ s := by {
      have k := Classical.choose_spec h
      exact k.1
    }


lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by {

  unfold LeftInvOn
  unfold InjOn at hf

  let g : β → α := fun y ↦ if h : ∃ x : α, x ∈ s ∧ f x = y then
    conditionalInverse f s y h else default

  use g
  intro x hx
  have hxpreim : ∃ y ∈ s, f y = f x := by use x
  have : g (f x) = conditionalInverse f s (f x) (by use x) := by simp[g, hxpreim]

  rw[this]
  have hgf : conditionalInverse f s (f x) (by use x) ∈ s := invFun_spec' f s (f x) (by use x)
  specialize hf hgf hx
  apply hf
  have := invFun_spec f s (f x) (by use x)
  assumption
  }


/- Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

To help you along the way, some potentially useful ways to reformulate the hypothesis are given. -/

-- This lemma might be useful.
#check Injective.eq_iff

lemma set_bijection_of_partition {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by {
  -- h1' and h1'' might be useful later as arguments of `simp` to simplify your goal.
  simp[range] at h1 h2
  unfold Injective at hf hg
  have h1' : ∀ x y, f x ≠ g y := sorry
  have h1'' : ∀ y x, g y ≠ f x := by sorry
  have h2' : ∀ x, x ∈ range f ∪ range g := by sorry
  let L : Set α × Set β → Set γ := sorry
  let R : Set γ → Set α × Set β := sorry
  sorry
  }

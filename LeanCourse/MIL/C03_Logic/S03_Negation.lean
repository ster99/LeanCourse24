import LeanCourse.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨a, fa⟩
  rcases h a with ⟨x, hl⟩
  have : f x ≥ a := fa x
  linarith

example : ¬FnHasUb fun x ↦ x := by
intro fnub
rcases fnub with ⟨a, hf⟩
have : (fun x ↦ x) (a+1) = a+1 := by norm_num
have : (fun x ↦ x) (a+1) ≤ a := hf (a+1)
linarith

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  have con : ¬a ≥ b := by
   intro nanb
   have : f b ≤ f a := by apply h nanb
   linarith
  apply lt_of_not_ge at con
  exact con

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro as
  have : f a ≤ f b := as h
  apply not_le_of_gt at h'
  linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by {
    unfold Monotone
    intro a b h
    simp
  }
  have h' : f 1 ≤ f 0 := le_refl _
  apply h at monof

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  have p : ¬x > 0 := by
   intro xg
   have hr : x > x/2 := by linarith
   have xt : (x/2)>0 := by linarith
   apply h at xt
   linarith
  apply le_of_not_gt
  exact p
end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
 intro y h1
 have : ∃ x, P x := ⟨y, h1⟩
 exact h this


example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro h2
  rcases h2 with ⟨x₀,q⟩
  have h3 : ¬ P x₀ := by apply h x₀
  exact h x₀ q

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h1
  rcases h with ⟨y, h2⟩
  have h3 : P y := h1 y
  exact h2 h3


example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra h1
  apply h h1

example (h : Q) : ¬¬Q := by
  apply not_not.mpr h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro y
  by_contra h1
  have h2 : ∀ x, f x ≤ y := by push_neg at h1; exact h1
  have h3 : FnUb f y := h2
  have h4 : FnHasUb f := ⟨y,h3⟩
  exact h h4

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  rw[Monotone] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end

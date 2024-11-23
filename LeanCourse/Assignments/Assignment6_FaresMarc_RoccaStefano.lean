import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8.1.
  Chapter 7 explains some of the design decisions for classes in Mathlib.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 19.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


/- Prove the following exercises about functions where the domain/codomain are
subtypes. -/

abbrev PosReal : Type := {x : ℝ // x > 0}

/- Codomain is a subtype (usually not recommended). -/
example (f : ℝ → PosReal) (hf : Monotone f) :
    Monotone (fun x ↦ log (f x)) := by {
  sorry
  }

/- Specify that the range is a subset of a given set (recommended). -/
example (f : ℝ → ℝ) (hf : range f ⊆ {x | x > 0}) (h2f : Monotone f) :
  Monotone (log ∘ f) := by {
  sorry
  }

/- Domain is a subtype (not recommended). -/
example (f : PosReal → ℝ) (hf : Monotone f) :
    Monotone (fun x ↦ f ⟨exp x, exp_pos x⟩) := by {
  sorry
  }

/- Only specify that a function is well-behaved on a subset of its domain (recommended). -/
example (f : ℝ → ℝ) (hf : MonotoneOn f {x | x > 0}) :
    Monotone (fun x ↦ f (exp x)) := by {
  sorry
  }



variable {G H K : Type*} [Group G] [Group H] [Group K]
open Subgroup


/- State and prove that the preimage of `U` under the composition of `φ` and `ψ` is a preimage
of a preimage of `U`. This should be an equality of subgroups! -/
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : sorry := sorry

/- State and prove that the image of `S` under the composition of `φ` and `ψ`
is a image of an image of `S`. -/
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : sorry := sorry



/- Define the conjugate of a subgroup, as the elements of the form `xhx⁻¹` for `h ∈ H`. -/
def conjugate (x : G) (H : Subgroup G) : Subgroup G := sorry


/- Now let's prove that a group acts on its own subgroups by conjugation. -/

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by {
  sorry
  }

lemma conjugate_mul (x y : G) (H : Subgroup G) :
    conjugate (x * y) H = conjugate x (conjugate y H) := by {
  sorry
  }


/- Saying that a group `G` acts on a set `X` can be done with `MulAction`.
The two examples below show the two properties that a group action must satisfy. -/
#print MulAction

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
example (g g' : G) (x : X) : (g * g') • x = g • (g' • x) := by exact?
example (x : X) : (1 : G) • x = x := by exact?

/- Now show that `conjugate` specifies a group action from `G` onto its subgroups. -/
instance : MulAction G (Subgroup G) := sorry



/-! # Exercises to hand-in. -/


/- A `Setoid` is the name for an equivalence relation in Lean.
Let's define the smallest equivalence relation on a type `X`. -/
def myEquivalenceRelation (X : Type*) : Setoid X where
  r x y := x = y
  iseqv := {
    refl := by {
      intro x
      rfl
    }
    symm := by{
      intro x y hxy
      rw[hxy]
    }
    trans := by{
      intro x y z hxy hyz
      rw[← hxy] at hyz
      exact hyz
    }
  }

/- This simp-lemma will simplify `x ≈ y` to `x = y` in the lemma below. -/
@[simp] lemma equiv_iff_eq (X : Type*) (x y : X) :
  letI := myEquivalenceRelation X; x ≈ y ↔ x = y := by rfl

/-
Now let's prove that taking the quotient w.r.t. this equivalence relation is
equivalent to the original type.

Use `Quotient.mk` to define a map into a quotient (or its notation `⟦_⟧`)
Use `Quotient.lift` to define a map out of a quotient.
Use `Quotient.sound` to prove that two elements of the quotient are equal.
Use `Quotient.ind` to prove something for all elements of a quotient.
You can use this using the induction tactic: `induction x using Quotient.ind; rename_i x`.
-/

def quo (y : Quotient (myEquivalenceRelation X))
  (h : ∃ x : X, ⟦x⟧ = y) : X :=
  Classical.choose h

def quotient_equiv_subtype (X : Type*) :

    Quotient (myEquivalenceRelation X) ≃ X where

    toFun := Quotient.lift (fun (x : X) ↦ x) (by
      intro a b h
      simp at h
      tauto
    )

    invFun := Quotient.mk (myEquivalenceRelation X)

    left_inv := by {
      unfold LeftInverse
      intro y
      have hh: ⟦Classical.choose (Quotient.exists_rep y)⟧ = y := by
        exact Classical.choose_spec (Quotient.exists_rep y)
      rw[← hh]
      --I wanted to use quo but didn't work...have hh : quo y (Quotient.exists_rep y)
      apply Quotient.sound
      rfl
    }

    right_inv := by {
      unfold Function.RightInverse
      unfold LeftInverse
      intro y
      simp
    }

section GroupActions

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/- Below is the orbit of an element `x ∈ X` w.r.t. a group action by `G`.
Prove that the orbits of two elements are equal
precisely when one element is in the orbit of the other. -/
def orbitOf (x : X) : Set X := range (fun g : G ↦ g • x)

lemma orbitOf_eq_iff (x y : X) : orbitOf G x = orbitOf G y ↔ y ∈ orbitOf G x := by {
  constructor
  · intro h
    have ytriv : ∃ e, (fun g : G ↦ g • y) e = y := by use 1, MulAction.one_smul y
    have yorby : y ∈ orbitOf G y := by exact ytriv
    have yorbx : y ∈ orbitOf G x := by apply Set.mem_of_mem_of_subset yorby (Eq.subset (symm h))
    exact yorbx
  · rintro ⟨k,hk⟩; simp at hk
    have xy : k⁻¹ • y = x := by exact inv_smul_eq_iff.mpr (id (Eq.symm hk))
    ext z
    constructor
    · rintro ⟨l,hl⟩; simp at hl
      have zy : (l * k⁻¹) • y = z := by {
        calc
        (l * k⁻¹) • y = l • k⁻¹ • y := by exact mul_smul l k⁻¹ y
                    _ = l • x := by exact congrArg (HSMul.hSMul l) xy
                    _ = z := by exact hl
      }
      use (l*k⁻¹)
    · rintro ⟨l,hl⟩
      have zx : (l * k) • x = z := by {
        calc
        (l * k) • x = l • k • x := by exact mul_smul l k x
                  _ = l • (y) := by exact congrArg (HSMul.hSMul l) hk
                  _ = z := by exact hl
      }
      use (l*k)
  }
/- Define the stabilizer of an element `x` as the subgroup of elements
`g ∈ G` that satisfy `g • x = x`. -/
def stabilizerOf (x : X) : Subgroup G where
  carrier := {g : G | g • x = x}
  mul_mem' := by{
    intro g k gg kk
    calc
    (g * k) • x = g • k • x := by exact mul_smul g k x
              _ = g • x := by exact congrArg (HSMul.hSMul g) kk
              _ = x := by exact gg
  }
  one_mem' := by{
    calc
    1 • x = x := by exact MulAction.one_smul x
  }
  inv_mem' := by{
    simp
    intro g gg
    calc
    g⁻¹ • x = g⁻¹ • (g • x) := by exact congrArg (HSMul.hSMul g⁻¹) (id (Eq.symm gg))
          _ = (g⁻¹ * g) • x := by exact smul_smul g⁻¹ g x
          _ = (1:G) • x := by exact congrFun (congrArg HSMul.hSMul (inv_mul_cancel g)) x
          _ = x := by exact MulAction.one_smul x
  }
-- This is a lemma that allows `simp` to simplify `x ≈ y` in the proof below.
@[simp] theorem leftRel_iff {x y : G} {s : Subgroup G} :
    letI := QuotientGroup.leftRel s; x ≈ y ↔ x⁻¹ * y ∈ s :=
  QuotientGroup.leftRel_apply

/- Let's probe the orbit-stabilizer theorem.

Hint: Only define the forward map (as a separate definition),
and use `Equiv.ofBijective` to get an equivalence.
(Note that we are coercing `orbitOf G x` to a (sub)type in the right-hand side) -/

def toFun (x : X) (k: G ⧸ stabilizerOf G x): orbitOf G x :=
⟨Classical.choose (Quotient.exists_rep k) • x, by
  unfold orbitOf
  simp
  ⟩

def orbit_stabilizer_theorem (x : X) : G ⧸ stabilizerOf G x ≃ orbitOf G x := by {

  have htoFun : Bijective (toFun G x) := by {
    unfold Bijective
    constructor
    · unfold Injective
      intro k₁ k₂ h
      sorry
      --probably I defined the function toFun in a way which is badly managable, so I have
      --troubles handling it to prove the property. I couldn't find a neater way, sorry.
    · unfold Surjective
      intro y
      have h := y.2
      unfold orbitOf at h
      unfold Set.range at h
      obtain ⟨g, hg⟩ := h
      simp at hg
      use Quotient.mk _ g
      sorry
  }
  apply Equiv.ofBijective (toFun G x) htoFun
  }

end GroupActions

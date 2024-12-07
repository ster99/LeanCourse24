import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Nat.Choose.Dvd
noncomputable section
open Function Ideal Polynomial Classical
open scoped Matrix
-- This is removed intentionally and should not be used manually in the exercises
attribute [-ext] LinearMap.prod_ext


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 8.2 and 9.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 26.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice.
Feel free to skip these exercises-/

example (n m : ℤ) : span {n} ⊔ span {m} = span {gcd n m} := by {
  sorry
  }

example (n m : ℤ) : span {n} ⊓ span {m} = span {lcm n m} := by {
  sorry
  }

/- Show that transposing a matrix gives rise to a linear equivalence. -/
example {R M m n : Type*} [Ring R] [AddCommGroup M] [Module R M] :
  Matrix m n M ≃ₗ[R] Matrix n m M where
    toFun := fun M ↦ Mᵀ
    map_add' := by sorry
    map_smul' := by sorry
    invFun := by sorry
    left_inv := by sorry
    right_inv := by sorry

/- A ring has characteristic `p` if `1 + ⋯ + 1 = 0`, where we add `1` `p` times to itself.
This is written `CharP` in Lean.
In a module over a ring with characteristic 2, for every element `m` we have `m + m = 0`. -/
example {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [CharP R 2] (m : M) :
    m + m = 0 := by {
  sorry
  }

section Frobenius
variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p]
/- Let's define the Frobenius morphism `x ↦ x ^ p`.
You can use lemmas from the library.
We state that `p` is prime using `Fact p.Prime`.
This allows type-class inference to see that this is true.
You can access the fact that `p` is prime using `hp.out`. -/

def frobeniusMorphism (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p] :
  R →+* R := sorry

@[simp] lemma frobeniusMorphism_def (x : R) : frobeniusMorphism p R x = x ^ p := sorry

/- Prove the following equality for iterating the frobenius morphism. -/
lemma iterate_frobeniusMorphism (n : ℕ) (x : R) : (frobeniusMorphism p R)^[n] x = x ^ p ^ n := by {
  sorry
  }

/- Show that the Frobenius morphism is injective on a domain. -/
lemma frobeniusMorphism_injective [IsDomain R] :
    Function.Injective (frobeniusMorphism p R) := by {
  sorry
  }

/- Show that the Frobenius morphism is bijective on a finite domain. -/
lemma frobeniusMorphism_bijective [IsDomain R] [Finite R] :
    Function.Bijective (frobeniusMorphism p R) := by {
  sorry
  }

example [IsDomain R] [Finite R] (k : ℕ) (x : R) : x ^ p ^ k = 1 ↔ x = 1 := by {
  sorry
  }

example {R : Type*} [CommRing R] [IsDomain R] [Finite R] [CharP R 2] (x : R) : IsSquare x := by {
  sorry
  }

end Frobenius


section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
prove that the units of a ring form a group.
Hint: I recommend that you first prove that the product of two units is again a unit,
and that you define the inverse of a unit separately using `Exists.choose`.
Hint 2: to prove associativity, use something like `intros; ext; apply mul_assoc`
(`rw` doesn't work well because of the casts) -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1

def IsAUnit.mul {x y : R} (hx : IsAUnit x) (hy : IsAUnit y) : IsAUnit (x * y) := by {
  sorry
  }

instance groupUnits : Group {x : R // IsAUnit x} := sorry

-- you have the correct group structure if this is true by `rfl`
example (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := by sorry

end Ring

/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
To prove this we have to additionally assume that `M` contains at least two elements, and
`smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).-/
#check exists_ne
lemma commutative_of_module {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by {
  sorry
  }


/-! # Exercises to hand-in. -/

/- The Frobenius morphism in a domain of characteristic `p` is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. A proof sketch is given, and the following results will be useful. -/

#check add_pow
#check CharP.cast_eq_zero_iff

variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [IsDomain R] [CharP R p] in
open Nat Finset in
lemma add_pow_eq_pow_add_pow (x y : R) : (x + y) ^ p = x ^ p + y ^ p := by {
  have hp' : p.Prime := hp.out
  have range_eq_insert_Ioo : range p = insert 0 (Ioo 0 p)
  · ext n
    simp
    constructor
    intro h
    by_cases q: n=0
    · left
      exact q
    · right
      exact ⟨zero_lt_of_ne_zero q,h⟩
    · rintro (h0|⟨h1,h2⟩)
      · rw[h0]
        exact pos_of_neZero p
      · exact h2

  have dvd_choose : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by {
  simp
  have hi : ∀ i : ℕ, (i ≤ p) →  p.choose i = p.factorial / (i.factorial * (p - i).factorial) := by exact fun i a ↦ choose_eq_factorial_div_factorial a
  sorry
  }
  have h6 : ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
  calc
    _ =  ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by {
      have : ∀ i ∈ Ioo 0 p, ∃ k ∈ ℕ, Nat.choose p i = p * k := by
        apply CharP.cast_eq_zero_iff.mpr dvd_choose
    }
    _ = 0 := by sorry
  sorry
  }
  #leansearch "(R : Type*) [CommRing R] [IsDomain R] [CharP R p], ∀ y ∈ R, y * p = 0."
#check Nat.factorial_mul_factorial_dvd_factorial
#check Nat.choose_eq_factorial_div_factorial
#check Nat.factorial_dvd_descFactorial
#leansearch "sum between two integers."
section LinearMap

variable {R M₁ M₂ N M' : Type*} [CommRing R]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N] [AddCommGroup M']
  [Module R M₁] [Module R M₂] [Module R N] [Module R M']

/- Define the coproduct of two linear maps, and prove the characterization below.
Note that this proof works exactly the same for vector spaces over a field as it works
for modules over a ring, so feel free to think of `M₁`, `M₂`, `N` and `M'` as vector spaces.
You might recognize this as the characterization of a *coproduct* in category theory. -/

def coproduct (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) : M₁ × M₂ →ₗ[R] N where
  toFun x := f x.1 + g x.2
  map_add' x y := by {
    simp
    exact add_add_add_comm (f x.1) (f y.1) (g x.2) (g y.2)
  }
  map_smul' r x := by simp

-- this can be useful to have as a simp-lemma, and should be proven by `rfl`
@[simp] lemma coproduct_def (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) (x : M₁) (y : M₂) :
  coproduct f g (x, y) = f x + g y := by{
    unfold coproduct
    simp
  }



lemma coproduct_unique {f : M₁ →ₗ[R] N} {g : M₂ →ₗ[R] N} {l : M₁ × M₂ →ₗ[R] N} :
    l = coproduct f g ↔
    l.comp (LinearMap.inl R M₁ M₂) = f ∧
    l.comp (LinearMap.inr R M₁ M₂) = g := by {
      let p : M₁ → M₁ × M₂ := fun x₁ => (x₁,0)
      have : IsLinearMap R p :={
        map_add := by {
        intro x y
        calc
        p (x + y) = (x + y,0) := by rfl
                _ = (x,0) + (y,0) := by exact Eq.symm (Prod.mk_zero_add_mk_zero x y)
                _ = p x + p y := by rfl
        }
        map_smul := by{
          intro a x
          calc
          p (a • x) = (a • x,0) := by rfl
                  _ = a • (x,0) := by exact Eq.symm (Prod.smul_mk_zero a x)
                  _ = a • p x := by rfl
        }
      }
      constructor
      · intro h
        constructor
        · ext x
          simp
          have : l (x,0) = coproduct f g (x,0) := by exact congrFun (congrArg DFunLike.coe h) (x, 0)
          have qq : coproduct f g (x,0) = f x := by simp
          rw[this,qq]
        · ext y
          simp
          have : l (0,y) = coproduct f g (0,y) := by exact congrFun (congrArg DFunLike.coe h) (0,y)
          have qq : coproduct f g (0,y) = g y := by simp
          rw[this,qq]
      · rintro ⟨h1,h2⟩
        ext x
        unfold coproduct
        simp
        have : x = ((x.1,0) + (0,x.2)) := by exact Eq.symm (Prod.fst_add_snd x)
        have : l x = l ((x.1,0) + (0,x.2)) := by exact congrArg (⇑l) this
        have : l ((x.1,0) + (0,x.2)) = l (x.1,0) + l (0,x.2) := by exact LinearMap.map_add l (x.1, 0) (0, x.2)
        have : l (x.1,0) = l (p (x.1)) := by exact rfl
        have : l (p (x.1)) = f x.1 := by apply h1 x.1
    }

end LinearMap

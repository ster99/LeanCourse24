import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Nat BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 5 (mostly section 2) and 6 (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 12.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- A note on definitions -/

lemma my_lemma : 3 + 1 = 4 := rfl
def myThree : ℕ := 3

/-
Tactics like `simp` and `rw` will not unfold definitions unless instructed to.
Tactics like `exact` and `apply` will unfold definitions if needed.
Uncomment the following lines one-by-one to see the difference. -/

example : myThree + 1 = 4 := by
  -- rw [my_lemma] -- fails
  -- simp [my_lemma] -- fails to use `my_lemma`
  -- exact my_lemma -- works
  -- apply my_lemma -- works
  -- rw [myThree, my_lemma] -- works after instructing `rw` to unfold the definition
  -- simp [myThree] -- works after instructing `simp` to unfold the definition
                    -- (it doesn't need `my_lemma` to then prove the goal)
  sorry


/- The following exercises are to practice with casts. -/
example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by {
  norm_cast at h
  rw[h]
  }

example (n m : ℕ) (h : (n : ℚ) + 3 ≤ 2 * m) : (n : ℝ) + 1 < 2 * m := by {
  norm_cast at *
  linarith
  }

example (n m : ℕ) (h : (n : ℚ) = m ^ 2 - 2 * m) : (n : ℝ) + 1 = (m - 1) ^ 2 := by {
  have h' : (n : ℝ) = m ^ 2 - 2 * m := by norm_cast at *
  rw [h']
  ring
  }

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by {
  norm_cast
  }

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by {
  norm_cast
  }

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by {
  gcongr
  norm_cast
  }

example (n : ℤ) (h : 0 < n) : 0 < Real.sqrt n := by {
  have : 0 < (n : ℝ) := by norm_cast
  exact sqrt_pos_of_pos this
  }

/- Working with `Finset` is very similar to working with `Set`.
However, some notation, such as `f '' s` or `𝒫 s` doesn't exist for `Finset`. -/
example (s t : Finset ℕ) : (s ∪ t) ∩ t = (s ∩ t) ∪ t := by {
  ext x
  simp
  }

example {α β : Type*} (f : α → β) (s : Finset α) (y : β) : y ∈ s.image f ↔ ∃ x ∈ s, f x = y := by {
  sorry
  }

/- `Disjoint` can be used to state that two (fin)sets are disjoint.
Use `Finset.disjoint_left` (or `Set.disjoint_left`) to unfold its definition.
If you have `x ∈ t \ s` apply `simp` first to get a conjunction of two conditions.
-/
example {α : Type*} (s t : Finset α) : Disjoint s (t \ s) := by {
  sorry
  }


/- Let's define the Fibonacci sequence -/
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibonacci (n + 1) + fibonacci n

/- Prove the following exercises by induction. -/

example (n : ℕ) : ∑ i in range n, fibonacci (2 * i + 1) = fibonacci (2 * n) := by {
  sorry
  }

example (n : ℕ) : ∑ i in range n, (fibonacci i : ℤ) = fibonacci (n + 1) - 1 := by {
  sorry
  }

example (n : ℕ) : 6 * ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by {
  sorry
  }

def fac : ℕ → ℕ
  | 0       => 1
  | (n + 1) => (n + 1) * fac n

theorem pow_two_le_fac (n : ℕ) : 2 ^ n ≤ fac (n + 1) := by {
  sorry
  }

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by {
  sorry
  }

example (n : ℕ) : fac (2 * n) = fac n * 2 ^ n * ∏ i in range n, (2 * i + 1) := by {
  sorry
  }





/- **Exercise**.
Define scalar multiplication of a real number and a `Point`. -/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

-- give definition here


/- **Exercise**.Define Pythagorean triples, i.e. triples `a b c : ℕ` with `a^2 + b^2 = c^2`.
Give an example of a Pythagorean triple, and show that multiplying a Pythagorean triple by a
constant gives another Pythagorean triple. -/

-- give definition here



/- Prove that triples of equivalent types are equivalent. -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

example (α β : Type*) (e : α ≃ β) : Triple α ≃ Triple β := sorry



/- 5. Show that if `G` is an abelian group then triples from elements of `G` is an abelian group. -/

class AbelianGroup' (G : Type*) where
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

example (G : Type*) [AbelianGroup' G] : AbelianGroup' (Triple G) := sorry



/-! # Exercises to hand-in. -/

/- **Exercise**.
Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any element of a strict bipointed type we have
`∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/

structure StrictBiPoint (α : Type*) where
  x₀ : α
  x₁ : α
  strict : x₀ ≠ x₁

namespace StrictBiPoint
lemma strictness {α : Type*} (x : StrictBiPoint α) (z : α) : z ≠ x.x₀ ∨ z ≠ x.x₁ := by{
  have strict : x.x₀ ≠ x.x₁ := by exact x.strict
  by_cases h : z= x.x₀
  · right
    exact ne_of_eq_of_ne h strict
  · have : z ≠ x.x₀ := by exact h
    left
    exact this
}

end StrictBiPoint
lemma SumofFirstn (n : ℕ) : ∑ i in range (n + 1), (i : ℚ) = n * (n + 1) / 2 := by {
  induction n with
  | zero => simp
  | succ n ih =>
    rw[Finset.sum_range_succ,ih]
    field_simp
    ring
  }

/- Prove by induction that `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/
open Finset in
lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i in range (n + 1), (i : ℚ) ^ 3) = (∑ i in range (n + 1), (i : ℚ)) ^ 2 := by{
  induction n with
  | zero => simp
  | succ n ih => {
    rw [Finset.sum_range_succ, ih]
    have sumn : (∑ i ∈ Finset.range (n + 1), (i : ℚ)) = (n:ℚ) * (n + 1:ℚ) / 2  := by apply SumofFirstn
    have sumcube : (∑ i ∈ Finset.range (n + 1), (i : ℚ))^2 + (n+1:ℚ)^3 = ((∑ i ∈ Finset.range (n + 1), (i : ℚ))+ (n+1:ℚ))^2 := by {
    calc
    (∑ i ∈ Finset.range (n + 1), (i : ℚ))^2 + (n+1:ℚ)^3 = ((n:ℚ) * (n + 1:ℚ)/2)^2 + (n+1:ℚ)^3 := by exact congrFun (congrArg HAdd.hAdd (congrFun (congrArg HPow.hPow sumn) 2)) ((n + 1:ℚ) ^ 3)
                                                       _ = (((n:ℚ)*(n + 1:ℚ)/2) + (n+1:ℚ))^2 := by ring
                                                       _ = ((∑ i ∈ Finset.range (n + 1), (i : ℚ))+ (n+1:ℚ))^2 := by exact congrFun (congrArg HPow.hPow (congrFun (congrArg HAdd.hAdd (id (Eq.symm sumn))) (n + 1:ℚ))) 2
    }
    let T : ℕ → ℚ := fun x => (x:ℚ)
    have ht : (n+1:ℚ) = T (n+1) := by exact Eq.symm (Mathlib.Tactic.Ring.inv_add rfl rfl)
    have hq : (∑ i ∈ Finset.range (n + 1), (i : ℚ))+ (n+1:ℚ) = (∑ i ∈ Finset.range (n + 1 + 1), (i : ℚ)) := by {
      calc
      (∑ i ∈ Finset.range (n + 1), (i : ℚ))+ (n+1:ℚ) = (∑ i ∈ Finset.range (n + 1), T i)+ (n + 1 :ℚ) := by rfl
                                                    _ = (∑ i ∈ Finset.range (n + 1), T i)+ T (n+1) := by exact congrArg (HAdd.hAdd (∑ i ∈ Finset.range (n + 1), T i)) ht
                                                    _ = (∑ i ∈ Finset.range (n + 1 + 1), T i) := by rw[sum_range_succ T (n+1)]
                                                    _ = (∑ i ∈ Finset.range (n + 1 + 1), (i : ℚ)) := by rfl

    }
    have hp : ((∑ i ∈ Finset.range (n + 1), (i : ℚ))+ (n+1:ℚ))^2 = (∑ i ∈ Finset.range (n + 1 + 1), (i : ℚ))^2 := by exact congrFun (congrArg HPow.hPow hq) 2
    have conc : (∑ i ∈ Finset.range (n + 1), (i : ℚ))^2 + (n+1:ℚ)^3 = (∑ i ∈ Finset.range (n + 1 + 1), (i : ℚ))^2 := by exact Eq.symm (Mathlib.Tactic.Ring.pow_congr (id (Eq.symm hq)) rfl (id (Eq.symm sumcube)))
    norm_cast at *
  }
    }
/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
induction m, h using Nat
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
      rw[fac]
      exact Dvd.dvd.mul_left ih (k + 1)
lemma disjoint_unions {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by {
  have disjoint : ∀ i j, i<j→ Disjoint (C i) (C j) := by{
  · intro i j hij
    simp [Set.disjoint_left, hC]
    tauto
  }
  constructor
  · intro i j hij
    obtain h|h := hij.lt_or_lt
    · exact disjoint i j h
    · exact Disjoint.symm (disjoint j i h)
  · apply subset_antisymm
    · gcongr with i
      rw [hC]
      exact diff_subset
    · simp [Set.subset_def]
      intro x i mem
      induction i using wf.induction with | _ i ih =>
      by_cases hx : ∃ j<i, x∈ A j
      · obtain ⟨j,h1,h2⟩ := hx
        exact ih j h1 h2
      · simp at hx
        simp [hC]
        use i
  }



/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

lemma not_prime_iff (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by {
      have one_less_than_two: 1<2 := by norm_num
      constructor
      · intro h
        by_cases hr : (n = 0)
        · left; exact hr
        · by_cases h1 : (n=1)
          right;left;exact h1
          · apply Or.rotate
            left
            have none : n>1 := by exact Nat.lt_of_le_of_ne (zero_lt_of_ne_zero hr) fun a ↦ h1 (id (Eq.symm a))
            have exp : ∃ m : ℕ, m ∣ n ∧ m ≠ 1 ∧ m ≠ n := by exact (not_prime_iff_exists_dvd_ne none).mp h
            rcases exp with ⟨p,⟨⟨c,d⟩ ,⟨hp31,hp32⟩⟩⟩
            use p, c
            constructor
            · by_contra r
              have f : p = 0 ∨ p = 1 := by exact le_one_iff_eq_zero_or_eq_one.mp (le_of_lt_succ (gt_of_not_le r))
              rcases f with (f1|f2)
              · have : p * c = 0 := by exact mul_eq_zero_of_left f1 c
                rw[this] at d; apply hr d
              · apply hp31 f2
            constructor
            · by_contra j
              have f : c=0 ∨ c=1 := by exact le_one_iff_eq_zero_or_eq_one.mp (le_of_lt_succ (gt_of_not_le j))
              rcases f with (f1|f2)
              · have : p * c = 0 := by exact mul_eq_zero_of_right p f1
                rw[this] at d; apply hr d
              · have : p * c = p := by  {
                calc p * c = p * 1 := by exact congrArg (HMul.hMul p) f2
                         _ = p := by exact mul_one p
              }
                rw[this] at d; symm at d; apply hp32 d
            · exact d
      rintro (h1|h2|h3)
      · exact Eq.mpr_not (congrArg Nat.Prime h1) not_prime_zero
      · exact Eq.mpr_not (congrArg Nat.Prime h2) not_prime_one
      · rcases h3 with ⟨a,⟨b,⟨h31,h32,h33⟩⟩⟩
        by_contra c
        have bi : a=1 ∨ a=n := by apply (Prime.eq_one_or_self_of_dvd c) a (Dvd.intro b (id (Eq.symm h33)))
        rcases bi with (bi1|bi2)
        · rw[bi1] at h31
          have two_less_two : 2<2 := by exact lt_of_le_of_lt h31 one_less_than_two
          exact (Nat.ne_of_lt two_less_two) rfl
        · rw[bi2] at h33
          have : b = 1 := by apply Nat.mul_left_cancel (zero_lt_of_ne_zero (Nat.Prime.ne_zero c));ring;symm;exact h33
          rw[this] at h32
          have two_less_two : 2<2 := by exact lt_of_le_of_lt h32 one_less_than_two
          exact (Nat.ne_of_lt two_less_two) rfl
          }
lemma prime_of_prime_two_pow_sub_one (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by {
  by_contra h2n
  rw [not_prime_iff] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · have : 2^0-1=0 := by norm_num
    rw[this] at hn ; exact Nat.not_prime_zero hn
  · have : 2^1-1=1 := by norm_num
    rw[this] at hn ; exact Nat.not_prime_one hn
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by exact congrFun (congrArg HMod.hMod (congrFun (congrArg HSub.hSub (pow_mul 2 a b)) 1)) (2 ^ a - 1)
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by exact Int.ModEq.sub (Int.ModEq.pow b (Int.modEq_sub (2 ^ a) 1)) rfl
      _ ≡ 1 - 1 [ZMOD (2 : ℤ) ^ a - 1] := by exact congrFun (congrArg HMod.hMod (congrFun (congrArg HSub.hSub (one_pow b)) 1)) (2 ^ a - 1)
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by exact rfl
  have hy : 1 < 2 := by norm_num
  have h2 : 2 ^ 2 ≤ 2 ^ a := by apply Nat.pow_le_pow_of_le hy ha
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [Nat.one_le_two_pow]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by {
  apply tsub_lt_tsub_right_of_le Nat.one_le_two_pow
  exact Nat.pow_lt_pow_of_lt hy ((Nat.lt_mul_iff_one_lt_right (zero_lt_of_lt ha)).mpr hb)
  }
  have q : 0 ≤ a * b := by exact Nat.zero_le (a * b)
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by
    have hu : 1<2 := by norm_num
    apply Nat.pow_le_pow_of_le hu q
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1 := by exact nat_pow_one_sub_dvd_pow_mul_sub_one 2 a b
  rw [Nat.prime_def_lt] at hn
  rcases hn with ⟨hn1,hn2⟩
  have : (2 ^ a - 1) = 1 := by exact hn2 (2 ^ a - 1) h5 h'
  exact h4 this
  }
/- Prove that for positive `a` and `b`, `a^2 + b` and `b^2 + a` cannot both be squares.
Prove it on paper first! -/
lemma not_isSquare_sq_add_or (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by {
  sorry
  }


/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers. -/

abbrev PosReal : Type := {x : ℝ // 0 < x}

structure PosReal' where
  x : ℝ
  pos : 0 < x
namespace PosReal'
def PosReal_div (a b : PosReal') : PosReal' :=
{ x := (a.x / b.x)
  pos := by apply div_pos a.pos b.pos
}

def groupPosReal : Group PosReal' where
mul a b := a * b
one := 1
inv a := PosReal_div b a
mul_assoc := by sorry
mul_one := by sorry
one_mul := by sorry
inv_mul_cancel := by sorry
#check commMonoid.proof_1
#leansearch "(a : PosReal)*(b:PosReal)*(c:PosReal)=(a : PosReal)*((b:PosReal)*(c:PosReal))."
#leansearch "inverse of a positive real number."
#leansearch "division of positive is positive."
end PosReal'
/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
#loogle "Finset.card."
attribute [-simp] card_powerset
#check Finset.induction

lemma fintype_card_powerset (α : Type*) (s : Finset α) :
    Finset.card (powerset s) = 2 ^ Finset.card s := by {
      induction s using Finset.induction with
  | empty => simp
  | @insert x s hxs ih => sorry
  }

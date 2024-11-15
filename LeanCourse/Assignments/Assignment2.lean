import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 2, sections 2, 3, 4 and 5
  Read chapter 3, sections 1, 4.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 22.10.2023.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by {
  linarith
  }

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 := by {
  calc
  u ^ 2 + 3 * u + 1 = u*u + u + u + u + 1 := by ring
                  _ = (u+0)*(u+0) + (u+0) + (u+0) + (u+0) + 1 := by ring
                  _ = (u+1-1)*(u+1-1) + (u+1-1) + (u+1-1) + (u+1-1) + 1 := by ring
                  _ = (v-1)*(v-1) + (v-1) + (v-1) + (v-1) + 1 := by rw[h1]
                  _ = v*v + 1 - v - v + v + v + v - 1 - 1 -1 + 1 := by ring
                  _ = v ^ 2 + v - 1 := by ring
  }

example (a b c x y : ℝ) (h : a ≤ b) (h2 : b < c) (h3 : x ≤ y) :
    a + exp x ≤ c + exp (y + 2) := by {
    apply add_le_add
    have p : b ≤ c := by linarith [h2]
    · apply le_trans
      · apply h
      · apply p
    have q : x ≤ y+2 := by linarith [h3]
    · apply exp_le_exp.mpr q
  }

/-- Prove the following using `linarith`.
Note that `linarith` cannot deal with implication or if and only if statements. -/
example (a b c : ℝ) : a + b ≤ c ↔ a ≤ c - b := by {
  constructor
  · intro h
    linarith
  · intro p
    linarith
  }

/- Note: for purely numerical problems, you can use `norm_num`
(although `ring` or `linarith` also work in some cases). -/
example : 2 + 3 * 4 + 5 ^ 6 ≤ 7 ^ 8 := by norm_num
example (x : ℝ) : (1 + 1) * x + (7 ^ 2 - 35 + 1) = 2 * x + 15 := by norm_num

/- You can prove many equalities and inequalities by being smart with calculations.
In this case `linarith` can also prove this, but `calc` can be a lot more flexible. -/
example {x y : ℝ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by gcongr
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by gcongr
    _ > 3 := by norm_num

/-- It can be useful to add a `+ 0` in a calculational proof for `gcongr` -/
example {m n : ℤ} : n ≤ n + m ^ 2 := by
  -- gcongr doesn't make progress here
  calc
    n = n + 0 := by ring
    _ ≤ n + m ^ 2 := by gcongr; exact sq_nonneg m

/- Sometimes `congr`/`gcongr` goes too deep into a term.
In that case, you can give `gcongr` a pattern with how deep it should enter the terms.
When the pattern contains `?_`, it creates a subgoal with the corresponding terms
on each side of the inequality.
For `congr` you can also do this using the tactic `congrm`. -/
example {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (hab : a₁ + a₂ = b₁ + b₂) (hbc : b₁ + b₂ ≤ c₁ + c₂) :
    a₁ + a₂ + 1 ≤ c₁ + c₂ + 1 := by
  calc a₁ + a₂ + 1 = b₁ + b₂ + 1 := by congrm ?_ + 1; exact hab
    _ ≤ c₁ + c₂ + 1 := by gcongr ?_ + 1 -- gcongr automatically applies `hbc`.


example (x : ℝ) (hx : x = 3) : x ^ 2 + 3 * x - 5 = 13 := by
  rw [hx]
  norm_num

example {m n : ℤ} : n - m ^ 2 ≤ n + 3 := by {
  calc
    n - m ^ 2 = n - m^2 + 0 := by rw[add_zero]
            _ ≤ n - m^2 + m^2 := by gcongr; apply sq_nonneg m
            _ = n+ (m^2-m^2) := by ring
            _ = n + 0 := by ring
            _ ≤ n + 3 := by gcongr; norm_num
  }

example {a: ℝ} (h : ∀ b : ℝ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  calc
  a ≥ -3 + 4 * b - b ^ 2 := by exact h
  _ ≥ -4 + 4 * b - b ^ 2 := by gcongr; norm_num
  _ = -2^2 + 2*2-b^2 := by norm_num
  _ = -(2^2-2*2+b^2) := by ring


example {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ} (h₁₂ : a₁ + a₂ + 1 ≤ b₁ + b₂) (h₃ : a₃ + 2 ≤ b₃) :
  exp (a₁ + a₂) + a₃ + 1 ≤ exp (b₁ + b₂) + b₃ + 1 := by {
  sorry
  }


/- Divisibility also gives an order. Warning: divisibility uses a unicode character,
which can be written using `\|`. -/

/-- Prove this using calc. -/
lemma exercise_division (n m k l : ℕ) (h₁ : n ∣ m) (h₂ : m = k) (h₃ : k ∣ l) : n ∣ l := by {
  sorry
  }


/- We can also work with abstract partial orders. -/

section PartialOrder

variable {X : Type*} [PartialOrder X]
variable (x y z : X)

/- A partial order is defined to be an order relation `≤` with the following axioms -/
#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

/- every preorder comes automatically with an associated strict order -/
example : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

/- the reverse order `≥`/`>` is defined from `≤`/`<`.
In Mathlib we usually state lemmas using `≤`/`<` instead of `≥`/`>`. -/
example : x ≥ y ↔ y ≤ x := by rfl
example : x > y ↔ y < x := by rfl


example (hxy : x ≤ y) (hyz : y ≤ z) (hzx : z ≤ x) : x = y ∧ y = z ∧ x = z := by {
  sorry
  }


end PartialOrder


/-! # Exercises to hand-in. -/

/- Prove this using a calculation. -/
lemma exercise_calc_real {t : ℝ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by {
  calc
  t ^ 2 - 3 * t - 17 = t * (t - 3) -17 := by ring
                   _ ≥ 10 * (10 - 3) - 17 := by gcongr
                   _ = 53 := by norm_num
                   _ ≥ 5 := by norm_num
  }

/- Prove this using a calculation.
The arguments `{R : Type*} [CommRing R] {t : R}` mean
"let `t` be an element of an arbitrary commutative ring `R`." -/
lemma exercise_calc_ring {R : Type*} [CommRing R] {t : R}
    (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by {
     have h : t ^ 2 = 4 := by{
        calc
        t ^ 2 = t ^ 2 + 0 := by rw[add_zero]
            _ = t ^ 2 + (- 4 + 4) := by ring
            _ = t ^ 2 - 4 + 4 := by ring
            _ = 0 + 4 := by rw[ht]
            _ = 4 := by rw[zero_add]
      }
     calc
     t^4+3*t^3-3*t^2-2*t-2= (t^2)*(t^2) + 3 *t* (t^2)-3*t^2-2*t-2:= by ring
                                             _ = 4*4+3*t*4-3*4-2*t-2 := by rw[h]
                                             _ = 10*t+2 := by ring
  }

/-- Prove this using a calculation. -/
lemma exercise_square {m n k : ℤ} (h : m ^ 2 + n ≤ 2) : n + 1 ≤ 3 + k ^ 2 := by {
  have hq : -m ^ 2 ≤ 0 := by
    refine Int.neg_nonpos_of_nonneg ?h
    · apply sq_nonneg m

  have hp : n ≤ 2 := by{
    calc
    n = 0 + n := by rw[zero_add]
    _ = -m^2 + m^2 + n := by rw[neg_add_cancel]
    _ = -m^2 + (m^2 + n) := by rw[add_assoc]
    _ ≤ -m^2 + 2 := by gcongr
    _ ≤ 0 + 2 := by gcongr
    _ = 2 := by rw[zero_add]
  }
  calc
  n + 1 ≤ 2 + 1 := by gcongr
      _ = 3 := by norm_num
      _ = 3 + 0 := by rw[add_zero]
      _ ≤ 3 + k^2 := by gcongr; apply sq_nonneg k
  }



section Min
variable (a b c : ℝ)

/- The following theorems characterize `min`.
Let's this characterization it to prove that `min` is commutative and associative.
Don't use other lemmas about `min` from Mathlib! -/
#check (min : ℝ → ℝ → ℝ)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

lemma exercise_min_comm : min a b = min b a := by {
  have h1 : min a b ≤ min b a := by apply le_min (min_le_right a b) (min_le_left a b)
  have h2 : min b a ≤ min a b := by apply le_min (min_le_right b a) (min_le_left b a)

  apply eq_of_le_of_le h1 h2
  }

lemma exercise_min_assoc : min a (min b c) = min (min a b) c := by {
  have h5 : min a (min b c) ≤ b := le_trans (min_le_right a (min b c)) (min_le_left b c)
  have h6 : min a (min b c) ≤ c := le_trans (min_le_right a (min b c)) (min_le_right b c)
  have h7 : min a (min b c) ≤ min a b := le_min (min_le_left a (min b c)) h5
  have h8 : min a (min b c) ≤ min (min a b) c := le_min h7 h6

  have p5 : min (min a b) c ≤ b := le_trans (min_le_left (min a b) c) (min_le_right a b)
  have p6 : min (min a b) c ≤ a := le_trans (min_le_left (min a b) c) (min_le_left a b)
  have p7 : min (min a b) c ≤ min b c := le_min p5 (min_le_right (min a b) c)
  have p8 : min (min a b) c ≤ min a (min b c) := le_min p6 p7

  apply eq_of_le_of_le h8 p8
  }

end Min

/- Prove that the following function is continuous.
You can use `Continuous.div` as the first step,
and use the search techniques to find other relevant lemmas.
`ne_of_lt`/`ne_of_gt` will be useful to prove the inequality. -/

#check ne_of_lt
#check Continuous.div
lemma exercise_continuity : Continuous (fun x ↦ (sin (x ^ 5) * cos x) / (x ^ 2 + 1)) := by {
  apply Continuous.div
  · apply Continuous.mul
    · apply Continuous.comp'
      · exact continuous_sin
      · exact continuous_pow 5
    · exact continuous_cos
  · apply Continuous.add
    · exact continuous_pow 2
    · exact continuous_const
  · intro x
    have hp : x^2+1>0 := by{
    calc
    x ^ 2 + 1 ≥ 0 + 1 := by sorry
            _ = 1 := by norm_num
            _ > 0 := by norm_num
    }
    apply ne_of_gt hp
  }

/- Prove this only using `intro`/`constructor`/`obtain`/`exact` -/
lemma exercise_and_comm : ∀ (p q : Prop), p ∧ q ↔ q ∧ p := by {
  intro p q
  constructor
  · intro h
    obtain ⟨hp,hq⟩ := h
    constructor
    · exact hq
    · exact hp
  · intro h
    obtain ⟨hq,hp⟩ := h
    constructor
    · exact hp
    · exact hq
  }

/-- Prove the following properties of nondecreasing functions. -/
def Nondecreasing (f : ℝ → ℝ) : Prop := ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → f x₁ ≤ f x₂

lemma exercise_nondecreasing_comp (f g : ℝ → ℝ) (hg : Nondecreasing g) (hf : Nondecreasing f) :
    Nondecreasing (g ∘ f) := by {
  intro x y h
  dsimp
  have h1 : f x ≤ f y := by apply hf x y h
  apply hg (f x) (f y) h1
  }

/-- Note: `f + g` is the function defined by `(f + g)(x) := f(x) + g(x)`.
  `simp` can simplify `(f + g) x` to `f x + g x`. -/
lemma exercise_nondecreasing_add (f g : ℝ → ℝ) (hf : Nondecreasing f) (hg : Nondecreasing g) :
    Nondecreasing (f + g) := by {
  intro x y h
  simp
  apply add_le_add
  · apply hf x y h
  · apply hg x y h
  }



/-- Prove the following property of even. -/
def EvenFunction (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

lemma exercise_even_iff (f g : ℝ → ℝ) (hf : EvenFunction f) :
    EvenFunction (f + g) ↔ EvenFunction g := by {
  constructor
  · intro hfg x
    have h0 : f x = f (-x) := by apply hf x
    have h : f x + g x = f x + g (-x) := by {
      calc
      f x + g x = f (-x) + g (-x) := by apply hfg x
              _ = f x + g (-x) := by linarith
    }
    apply add_left_cancel at h
    exact h
  · intro hg x
    simp
    rw[hf x,hg x]
  }

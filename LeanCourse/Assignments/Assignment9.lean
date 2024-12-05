import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution
import Mathlib.Data.Real.Irrational
import Mathlib.MeasureTheory.Function.Jacobian
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval Convolution ENNReal
noncomputable section

noncomputable section
open BigOperators Function Set Real Filter Classical Topology TopologicalSpace


/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 11 & 12.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 10.12.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/
section

variable (α : Type*)
 [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]

/-
In the next three exercises we will show that every continuous injective function `ℝ → ℝ` is
either strictly monotone or strictly antitone.

We start by proving a slightly harder version of the exercise in class.
We generalize the real numbers to an arbitrary type `α`
that satisfies all the conditions required for the intermediate value theorem.
If you want to prove this by using the intermediate value theorem only once,
then use `intermediate_value_uIcc`.
`uIcc a b` is the unordered interval `[min a b, max a b]`.
-/
lemma mono_exercise_part1 {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by {
     sorry
    }
/- Now use this and the intermediate value theorem again
to prove that `f` is at least monotone on `[a, ∞)`. -/
lemma mono_exercise_part2 {f : α → α} (hf : Continuous f) (h2f : Injective f)
    {a b : α} (hab : a ≤ b) (h2ab : f a < f b) : StrictMonoOn f (Ici a) := by {
  sorry
  }

/-
Now we can finish just by using the previous exercise multiple times.
In this proof we take advantage that we did the previous exercise for an arbitrary order,
because that allows us to apply it to `ℝ` with the reversed order `≥`.
This is called `OrderDual ℝ`. This allows us to get that `f` is also strictly monotone on
`(-∞, b]`.
Now finish the proof yourself.
You do not need to apply the intermediate value theorem in this exercise.
-/
lemma mono_exercise_part3 (f : ℝ → ℝ) (hf : Continuous f) (h2f : Injective f) :
    StrictMono f ∨ StrictAnti f := by {
  have : ∀ {a b : ℝ} (hab : a ≤ b) (h2ab : f a < f b), StrictMonoOn f (Iic b)
  · intro a b hab h2ab
    have := mono_exercise_part2 (OrderDual ℝ) hf h2f hab h2ab
    rw [strictMonoOn_dual_iff.symm] at this
    exact this
  by_contra h
  simp [not_or, StrictMono, StrictAnti] at h
  obtain ⟨⟨a, b, hab, h2ab⟩, ⟨c, d, hcd, h2cd⟩⟩ := h
  have h3cd : f c < f d := h2cd.lt_of_ne (h2f.ne hcd.ne)
  have h1 : a < c
  · by_contra h
    simp at h
    exact mono_exercise_part2 ℝ hf h2f hcd.le h3cd h (h.trans hab.le) hab |>.not_le h2ab
  have h2 : f c ≤ f a
  · by_contra h
    simp at h
    exact mono_exercise_part2 ℝ hf h2f h1.le h left_mem_Ici hab.le hab |>.not_le h2ab
  exact this hcd.le h3cd (h1.le.trans hcd.le) hcd.le h1 |>.not_le h2
  }

end

/-
Let's prove that the absolute value function is not differentiable at 0.
You can do this by showing that the left derivative and the right derivative do exist,
but are not equal. We can state this with `HasDerivWithinAt`
To make the proof go through, we need to show that the intervals have unique derivatives.
An example of a set that doesn't have unique derivatives is the set `ℝ × {0}`
as a subset of `ℝ × ℝ`, since that set doesn't contains only points in the `x`-axis,
so within that set there is no way to know what the derivative of a function should be
in the direction of the `y`-axis.

The following lemmas will be useful
* `HasDerivWithinAt.congr`
* `uniqueDiffWithinAt_convex`
* `HasDerivWithinAt.derivWithin`
* `DifferentiableAt.derivWithin`.
-/
#check HasDerivWithinAt.congr
#check uniqueDiffWithinAt_convex
#check HasDerivWithinAt.derivWithin

example : ¬ DifferentiableAt ℝ (fun x : ℝ ↦ |x|) 0 := by {
  intro h
  have h1 : HasDerivWithinAt (fun x : ℝ ↦ |x|) 1 (Ici 0) 0 := by {
    have hh2 : HasDerivWithinAt (fun x : ℝ ↦ x) 1 (Ici 0) 0 := by exact HasDerivAt.hasDerivWithinAt (hasDerivAt_id' 0)
    have hhh3 : ∀ x ∈ Ici (0 : ℝ), |x| = x := by exact fun x a ↦ abs_of_nonneg a
    apply HasDerivWithinAt.congr hh2 hhh3
    simp
    }
  have h2 : HasDerivWithinAt (fun x : ℝ ↦ |x|) (-1) (Iic 0) 0 := by {
    have hh2 : HasDerivWithinAt (fun x : ℝ ↦ -x) (-1) (Iic 0) 0 := by exact hasDerivWithinAt_neg 0 (Iic 0)
    have hhh3 : ∀ x ∈ Iic (0 : ℝ), |x| = -x := by exact fun x a ↦ abs_of_nonpos a
    apply HasDerivWithinAt.congr hh2 hhh3
    simp
    }
  have h3 : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 := by {
  apply uniqueDiffWithinAt_convex
  · exact convex_Ici 0
  · simp
  · simp
  }
  have h4 : UniqueDiffWithinAt ℝ (Iic (0 : ℝ)) 0 := by {
  apply uniqueDiffWithinAt_convex
  · exact convex_Iic 0
  · simp
  · simp
  }
  have h5 := h.derivWithin h3
  rw [← h.derivWithin h4, h1.derivWithin h3, h2.derivWithin h4] at h5
  norm_num at h5
  }

/- There are special cases of the change of variables theorems for affine transformations
(but you can also use the change of variable theorem from the lecture) -/
example (a b : ℝ) :
    ∫ x in a..b, sin (x / 2 + 3) =
    2 * cos (a / 2 + 3) - 2 * cos (b / 2  + 3) := by {
      sorry
  }

/- Use the change of variables theorem for this exercise. -/
example (f : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ x in s, exp x * f (exp x) = ∫ y in exp '' s, f y := by {
  sorry
  }

example (x : ℝ) : ∫ t in (0)..x, t * exp t = (x - 1) * exp x + 1 := by {
  sorry
  }

example (a b : ℝ) : ∫ x in a..b, 2 * x * exp (x ^ 2) =
    exp (b ^ 2) - exp (a ^ 2) := by {
  sorry
  }


/-! # Exercises to hand-in. -/

/- This is a copy of `mono_exercise_part1` above. See the comments there for more info. -/
variable (α : Type*) [ConditionallyCompleteLinearOrder α]
  [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] in
lemma mono_exercise_part1_copy {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by {
      by_cases h : a < x ∧ x < b ∧ a < b
      rcases h with ⟨hh1,hh2,hh3⟩
      · by_contra q
        have q3 : f x ≤ f a ∧ f a ≤ f b ∨ f b ≤ f a ∧ f a ≤ f x := by left; exact ⟨le_of_lt (lt_of_not_ge q),le_of_lt h2ab⟩
        have q5 : ∃ y ∈ [[x, b]], f y = f a := by apply (mem_image f [[x, b]] (f a)).1 (Set.mem_of_mem_of_subset (mem_uIcc.mpr q3) (intermediate_value_uIcc (Continuous.continuousOn hf)))
        rcases q5 with ⟨y,⟨hy1,hy2⟩⟩
        have q6 : x ≤ y ∧ y ≤ b ∨ b ≤ y ∧ y ≤ x := by apply mem_uIcc.mp hy1
        have q7 : y > a := by {
          rcases q6 with (q61|q62)
          · exact gt_of_ge_of_gt q61.1 hh1
          · exact gt_of_ge_of_gt q62.1 hh3
        }
        exact (Ne.symm (ne_of_lt q7)) (h2f (h2f (congrArg f hy2)))
      · by_cases q : x = a
        · have fax : f x = f a := by exact h2f (congrArg f (congrArg f q))
          exact le_of_eq (h2f (h2f (congrArg f (congrArg f (id (Eq.symm fax))))))
        · have ax : a < x := by exact lt_of_le_of_ne hx fun a_1 ↦ q (h2f (congrArg f (id (Eq.symm a_1))))
          by_cases qq : x < b
          · simp at h; exact False.elim ((ne_of_lt (gt_of_ge_of_gt (h ax qq) (lt_of_le_of_lt hx qq))) (h2f (h2f (h2f rfl))))
          · simp at qq
            by_cases qq': x = b
            · rw[h2f (congrArg f (congrArg f qq'))]; exact le_of_lt h2ab
            · have yeuh : b < x := by exact lt_of_le_of_ne qq fun a ↦ qq' (h2f (congrArg f (id (Eq.symm a))))
              by_contra q
              simp at q
              have ba : a < b := by {
                by_contra o; simp at o
                exact (ne_of_lt h2ab) (h2f (congrArg f (h2f (congrArg f (congrArg f (LE.le.antisymm hab o))))))
              }
              have q3 : f x ≤ f a ∧ f a ≤ f b ∨ f b ≤ f a ∧ f a ≤ f x := by left; exact ⟨le_of_lt q,le_of_lt h2ab⟩
              have q5 : ∃ y ∈ [[x, b]], f y = f a := by apply (mem_image f [[x, b]] (f a)).1 (Set.mem_of_mem_of_subset (mem_uIcc.mpr q3) (intermediate_value_uIcc (Continuous.continuousOn hf)))
              rcases q5 with ⟨y,⟨hy1,hy2⟩⟩
              have q6 : x ≤ y ∧ y ≤ b ∨ b ≤ y ∧ y ≤ x := by apply mem_uIcc.mp hy1
              have q7 : y > a := by {
                rcases q6 with (q61|q62)
                · apply gt_of_ge_of_gt q61.1 ax
                · exact gt_of_ge_of_gt q62.1 ba
              }
              exact (Ne.symm (ne_of_lt q7)) (h2f (h2f (congrArg f hy2)))
  }

/- Prove the following using the change of variables theorem. -/
lemma change_of_variables_exercise (f : ℝ → ℝ) :
    ∫ x in (0)..π, sin x * f (cos x) = ∫ y in (-1)..1, f y := by {
      have hs : MeasurableSet (Ioc 0 π) := by exact measurableSet_Ioc
      have hh : ∀ x ∈ (Ioc 0 π), HasDerivWithinAt cos (-sin x) (Ioc 0 π) x := by exact fun x a ↦ HasDerivAt.hasDerivWithinAt ((fun x a ↦ hasDerivAt_cos x) x a)
      have hhh' : InjOn cos (Ioc 0 π) := by apply Set.InjOn.mono Ioc_subset_Icc_self injOn_cos
      have leq' : (-1 : ℝ) ≤ (1 : ℝ) := by norm_num
      have leq'' : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
      have cocosim : cos '' (Ioc 0 π) = (Ico (-1) 1) := by{
        ext x
        constructor
        · simp; intro y h1 h2 h3
          constructor
          · rw [← h3]; apply Real.neg_one_le_cos
          · have hihi : cos y < 1 := by exact lt_of_lt_of_eq (Real.cos_lt_cos_of_nonneg_of_le_pi leq'' h2 h1) cos_zero
            rw[← h3]; exact hihi
        · simp; intro h h1; use arccos x
          constructor
          · constructor
            · simp; exact h1
            · exact arccos_le_pi x
          · apply cos_arccos h (le_of_lt h1)
      }
      have huh : ∀ x ∈ [[0,π]], sin x • f (cos x) = |- sin x| • f (cos x) := by{
        intro x h; simp; left
        exact Eq.symm (abs_of_nonneg (sin_nonneg_of_mem_Icc (Set.mem_of_mem_of_subset h (Eq.subset (id (Eq.symm (Eq.symm (uIcc_of_le pi_nonneg))))))))
      }
      calc
      ∫ (x : ℝ) in (0)..π, sin x • f (cos x) = ∫ (x : ℝ) in (0)..π, |-(sin x)| • f (cos x) := by apply intervalIntegral.integral_congr huh
                                           _ = ∫ (x : ℝ) in Ioc 0 π, |(-sin x)| • f (cos x) := by exact intervalIntegral.integral_of_le pi_nonneg
                                           _ = ∫ (x : ℝ) in cos '' Ioc 0 π, f x  := by exact id (Eq.symm (integral_image_eq_integral_abs_deriv_smul hs hh hhh' f))
                                           _ = ∫ (y : ℝ) in Ico (-1) 1, f y := by exact congrFun (congrArg integral (congrArg volume.restrict cocosim)) fun x ↦ f x
                                           _ = ∫ (y : ℝ) in Icc (-1) 1, f y := by exact Eq.symm integral_Icc_eq_integral_Ico
                                           _ = ∫ (y : ℝ) in Ioc (-1) 1, f y := by exact integral_Icc_eq_integral_Ioc
                                           _ = ∫ (y : ℝ) in (-1)..1, f y := by exact Eq.symm (intervalIntegral.integral_of_le leq')
      }

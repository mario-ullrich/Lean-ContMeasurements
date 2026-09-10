/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A continuous injection of the line into the unit interval

The logistic function `s ↦ eˢ / (1 + eˢ)` maps `ℝ` continuously and injectively onto
a subset of the open interval `(0,1)`, and `logisticInv` inverts it on its image.

Nothing here is specific to measurements.  The gadget is used once, in the upper
bound: a measurement whose value is an *integer* has a free fractional part, and this
map puts one more real coordinate into it, saving one measurement.
-/

namespace ContMeasurements

/-- The logistic function `s ↦ eˢ / (1 + eˢ)`, a continuous injection `ℝ → (0,1)`. -/
noncomputable def logistic (s : ℝ) : ℝ := Real.exp s / (1 + Real.exp s)

/-- The logistic function is continuous; its denominator never vanishes. -/
theorem continuous_logistic : Continuous logistic := by
  unfold logistic
  exact Real.continuous_exp.div (continuous_const.add Real.continuous_exp) fun s => by
    positivity

/-- The logistic function takes values in the open unit interval. -/
theorem logistic_mem_Ioo (s : ℝ) : logistic s ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpos := Real.exp_pos s
  have hden : 0 < 1 + Real.exp s := by positivity
  refine ⟨div_pos hpos hden, ?_⟩
  show Real.exp s / (1 + Real.exp s) < 1
  rw [div_lt_one hden]
  linarith

/-- The logistic function is injective, since `t ↦ t / (1 + t)` is injective on `(0, ∞)`
and the exponential is injective. -/
theorem injective_logistic : Function.Injective logistic := by
  intro a b hab
  have hda : 0 < 1 + Real.exp a := by positivity
  have hdb : 0 < 1 + Real.exp b := by positivity
  have hab' : Real.exp a / (1 + Real.exp a) = Real.exp b / (1 + Real.exp b) := hab
  have hcross : Real.exp a * (1 + Real.exp b) = Real.exp b * (1 + Real.exp a) :=
    (div_eq_div_iff hda.ne' hdb.ne').1 hab'
  have hexp : Real.exp a = Real.exp b := by nlinarith [hcross]
  exact Real.exp_eq_exp.1 hexp

/-- A left inverse of `logistic`, used to read the smuggled coordinate back off. -/
noncomputable def logisticInv : ℝ → ℝ := Function.invFun logistic

/-- `logisticInv` undoes `logistic`. -/
@[simp]
theorem logisticInv_logistic (s : ℝ) : logisticInv (logistic s) = s :=
  Function.leftInverse_invFun injective_logistic s

end ContMeasurements

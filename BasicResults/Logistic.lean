/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The logistic function and its inverse

The logistic function `s ↦ eˢ / (1 + eˢ)` maps `ℝ` continuously and injectively into
the open interval `(0,1)`, and the logit `p ↦ log (p / (1 - p))` inverts it.

Nothing here is specific to measurements.  The pair is used once, in the upper bound:
a measurement whose value is an *integer* has a free fractional part, and the logistic
function puts one more real coordinate into it, saving one measurement.
-/

namespace Real

/-- The logistic function `s ↦ eˢ / (1 + eˢ)`, a continuous injection `ℝ → (0,1)`. -/
noncomputable def logistic (s : ℝ) : ℝ := exp s / (1 + exp s)

/-- The logit function `p ↦ log (p / (1 - p))`, inverse to the logistic function. -/
noncomputable def logit (p : ℝ) : ℝ := log (p / (1 - p))

/-- The logistic function is continuous; its denominator never vanishes. -/
theorem continuous_logistic : Continuous logistic :=
  continuous_exp.div (continuous_const.add continuous_exp) fun _ => by positivity

/-- The logistic function takes values in the open unit interval. -/
theorem logistic_mem_Ioo (s : ℝ) : logistic s ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpos := exp_pos s
  have hden : 0 < 1 + exp s := by positivity
  refine ⟨div_pos hpos hden, ?_⟩
  show exp s / (1 + exp s) < 1
  rw [div_lt_one hden]
  linarith

/-- The logit undoes the logistic function.  The computation behind it is
`logistic s / (1 - logistic s) = eˢ`. -/
@[simp]
theorem logit_logistic (s : ℝ) : logit (logistic s) = s := by
  have key : logistic s / (1 - logistic s) = exp s := by
    have h : (1 : ℝ) + exp s ≠ 0 := by positivity
    rw [logistic]
    field_simp
    ring
  rw [logit, key, log_exp]

/-- The logistic function is injective, having a left inverse. -/
theorem logistic_injective : Function.Injective logistic :=
  Function.LeftInverse.injective logit_logistic

end Real

/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import BasicResults
public import ContMeasurements.Scheme
public import ContMeasurements.LowerBound
public import ContMeasurements.Bisection
public import ContMeasurements.Identification
public import ContMeasurements.UpperBound
public import ContMeasurements.Complexity

/-!
# Adaptive continuous measurements

How many measurements does one need to recover a vector of a `d`-dimensional normed
space to within a prescribed accuracy, if every measurement may be an arbitrary
continuous functional and may be chosen on the basis of the values already observed?

With **linear** measurements, even adaptively chosen, fewer than `d` achieve nothing
at all, and the same is true of **nonadaptive continuous** measurements, by the
Borsuk–Ulam theorem.  Combining adaptivity with nonlinearity changes the answer
completely: `k + 1` measurements suffice whenever `d ≤ 2ᵏ`, and `n` measurements fail
whenever `2ⁿ ≤ d`.  In dimension `d = 2ᵏ` exactly `k + 1` are needed.

## Layout

The general ingredients (Borsuk–Ulam, split covers, the halving lemma, colored
covers, the Lebesgue cover of `ℝᵐ`) live in the separate `BasicResults` library.
Nothing there mentions measurements. This library holds the theory itself.

* `ContMeasurements.Scheme`: the model: `AdaptiveScheme`, its information map, and
  the combinators `tail`, `comap`, `const`, `branch`.
* `ContMeasurements.LowerBound`: `n` measurements separating antipodes force
  `2ⁿ ≥ d + 1`, hence an error of at least `R` on the sphere of radius `R` when
  `2ⁿ ≤ d`.
* `ContMeasurements.Bisection`: finding a color among at most `2ᴸ` costs `L`
  measurements.
* `ContMeasurements.Identification`: one measurement names a piece within a color,
  with an integer value whose fractional part is free to carry one more coordinate.
* `ContMeasurements.UpperBound`: if `d ≤ 2ᵏ`, then `k + 1` measurements recover any
  vector of a `d`-dimensional real normed space to any accuracy.
* `ContMeasurements.Complexity`: the minimal number `n*`, the sandwich
  `⌈log₂(d+1)⌉ ≤ n* ≤ ⌈log₂ d⌉ + 1`, and equality `n* = k + 1` in dimension `2ᵏ`.
-/

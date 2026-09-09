/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import ContMeasurements.Scheme
import ContMeasurements.SplitCover
import ContMeasurements.Halving
import ContMeasurements.BorsukUlam
import ContMeasurements.LowerBound
import ContMeasurements.ColoredCover
import ContMeasurements.Bisection
import ContMeasurements.Identification
import ContMeasurements.BrickPartition
import ContMeasurements.UpperBound
import ContMeasurements.Complexity

/-!
# Adaptive continuous measurements

How many measurements does one need to recover a vector of a `d`-dimensional normed
space to within a prescribed accuracy, if every measurement may be an arbitrary
continuous functional and may be chosen on the basis of the values already observed?

With **linear** measurements — even adaptively chosen — fewer than `d` achieve nothing
at all, and the same is true of **nonadaptive continuous** measurements, by the
Borsuk–Ulam theorem.  Combining adaptivity with nonlinearity changes the answer
completely: `⌈log₂ d⌉ + 1` measurements suffice, and `⌈log₂(d+1)⌉` are necessary.

## Layout

* `ContMeasurements.Scheme` — the model: `AdaptiveScheme`, its information map, and
  the combinators `tail`, `comap`, `single`, `branch`.

**The lower bound.**

* `ContMeasurements.SplitCover` — split sets, covers by them, and the sign functions
  turning such a cover into an odd map without zeros.
* `ContMeasurements.Halving` — one measurement costs at most a factor of two.
* `ContMeasurements.BorsukUlam` — the Borsuk–Ulam theorem, the **only `sorry`** of the
  development, plus its transfer to an arbitrary norm and radius.
* `ContMeasurements.LowerBound` — `n` measurements separating antipodes force
  `2ⁿ ≥ d + 1`, hence an error of at least `R` on the sphere of radius `R` when
  `2ⁿ ≤ d`.

**The upper bound.**

* `ContMeasurements.ColoredCover` — covers with few colours and separated pieces.
* `ContMeasurements.Bisection` — finding a colour costs `⌈log₂ (number of colours)⌉`
  measurements.
* `ContMeasurements.Identification` — one measurement names a piece within a colour,
  with an integer value whose fractional part is free to carry one more coordinate.
* `ContMeasurements.BrickPartition` — the coloured cover of `ℝᵐ` with `m + 1` colours.
* `ContMeasurements.UpperBound` — `⌈log₂ d⌉ + 1` measurements recover any vector of a
  `d`-dimensional real normed space to any accuracy.

**Both together.**

* `ContMeasurements.Complexity` — the minimal number `n*`, the sandwich
  `⌈log₂(d+1)⌉ ≤ n* ≤ ⌈log₂ d⌉ + 1`, and equality `n* = k + 1` in dimension `2ᵏ`.
-/

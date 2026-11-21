/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ContMeasurements.LowerBound
public import ContMeasurements.UpperBound
public import ContMeasurements.Complexity

/-!
# A Borsuk–Ulam theorem for adaptive continuous measurements: proofs

This module is the *Solution* of a Palomar submission. Comparator checks that every
declaration named in `comparator.json` has, in this module's environment, exactly the same
name and type as its counterpart in `Palomar.AdaptiveMeasurements.Challenge`, and that it
uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. The definitions the
statements use, `ContMeasurements.AdaptiveScheme` with `first`, `tail` and `info`, and
`ContMeasurements.minMeasurements`, are not holes: Comparator checks that each is the same
declaration, body included, in both modules.

Nothing is declared here. The advertised statements

* `ContMeasurements.exists_norm_eq_and_info_eq_info_neg`: if `2ⁿ ≤ dim E`, every adaptive
  scheme gives some antipodal pair on every sphere the same `n` values,
* `ContMeasurements.exists_recovery_scheme`: if `0 < dim E ≤ 2ᵏ`, then `k + 1` measurements
  recover every vector to within any `ε > 0`,
* `ContMeasurements.clog_le_minMeasurements_and_le`: the two bounds on the least number of
  measurements,
* `ContMeasurements.minMeasurements_eq_of_finrank_eq_two_pow`: equality when `dim E = 2ᵏ`,

and the definitions they rest on arrive through the imports above, under their own names in
the development: from `ContMeasurements/LowerBound.lean`, `ContMeasurements/UpperBound.lean`,
`ContMeasurements/Complexity.lean` and `ContMeasurements/Scheme.lean`. The Challenge module
restates exactly those, which is why no wrapper is needed.

The lower bound runs through a covering proposition: if `n` measurements separate antipodes
on a compact symmetric set, a halving lemma covers that set by `2ⁿ - 1` split sets, and the
Borsuk–Ulam theorem forbids such a cover of the sphere of a space of dimension `m ≥ 2ⁿ`. The
Borsuk–Ulam theorem is proved in `BasicResults/`, combinatorially, from Tucker's lemma on the
Kuhn triangulation of the integer cube. The upper bound combines a Lebesgue cover of `ℝᵈ⁻¹`
by `d` colors, one measurement that names a piece of a given color by an integer and carries
the last coordinate in its fractional part, and bisection over the color classes.
-/

@[expose] public section

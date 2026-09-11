/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.BorsukUlam
import BasicResults.SplitCover
import BasicResults.Halving
import BasicResults.ColoredCover
import BasicResults.GridSimplex
import BasicResults.LebesgueCover
import BasicResults.Logistic
import BasicResults.Tucker

/-!
# Basic results

General mathematics that the theory of adaptive continuous measurements consumes.
None of the statements in this library mentions measurements; each is about metric
geometry, equivariant topology or the real line, and each is a candidate for Mathlib.
They live in root namespaces, as a Mathlib contribution would.

Keeping them apart has a second purpose: the development's **only** `sorry` — the
Borsuk–Ulam theorem — lives here, so it is visibly a classical result imported from
outside rather than a gap in the theory itself.

## Contents

* `BasicResults.BorsukUlam` — the Borsuk–Ulam theorem in odd-map form (**the only
  `sorry`**), and its transfer to the sphere of any radius in any finite-dimensional
  real normed space.
* `BasicResults.SplitCover` — split sets, covers by them, and the sign functions
  turning such a cover into a continuous odd map without zeros. This is the covering
  form of the Krasnosel'skiĭ genus.
* `BasicResults.Halving` — level sets of an even function on a compact symmetric set:
  if each is covered by `h` split sets, the whole set needs only `2h`.
* `BasicResults.ColoredCover` — covers of a metric space by pieces of small diameter,
  colored so that distinct pieces of one color are separated, and their rescaling.
* `BasicResults.GridSimplex` — the Kuhn triangulation of an integer cube, described by
  the coordinatewise order, with the signs and directions of a simplex and the count of
  the ways of extending one by a vertex.
* `BasicResults.LebesgueCover` — such a cover of `ℝᵐ` with `m + 1` colors, built from
  the skeleta of the integer grid. The number `m + 1` is the Lebesgue covering
  dimension bound and cannot be lowered.
* `BasicResults.Logistic` — the logistic function, a continuous injection `ℝ → (0,1)`,
  and the logit inverting it.
* `BasicResults.Tucker` — Tucker's lemma: a labelling of the grid that is antipodal on
  the boundary gives one simplex two opposite labels.  This is the combinatorial form of
  the Borsuk–Ulam theorem.
-/

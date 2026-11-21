/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

/-!
# Palomar submissions

Root module of the `Palomar` library, which collects the submission surfaces for the
[Palomar registry](https://palomar-registry.org): one directory per result, holding a
`Challenge` module (the audited statements), a `Solution` module (the proofs, drawn from
the development in `ContMeasurements/` and `BasicResults/`), a `comparator.json` and a
`formalization.yaml`.

The `sorry`s in the `Challenge` modules are placeholders required by the submission format:
a Challenge advertises statements and imports only Mathlib, so that a reader can audit what
is claimed without reading the development. The mathematical development itself is
`sorry`-free.

A `Challenge` and its `Solution` are **separate roots**, never imported into one another or
into a common module: the Challenge repeats the definitions the statements rest on, while
the Solution receives the very same definitions through `ContMeasurements`, so a shared
environment would see each of them twice. Comparator compiles the two against separate
environments for exactly this reason. Hence this module imports nothing, and the library is
built from the glob `Palomar.+`.

This library is deliberately absent from `defaultTargets`, so a plain `lake build` behaves
exactly as it does without it. Build these modules with `lake build Palomar`.

## Entries

* `Palomar/AdaptiveMeasurements/`: a Borsuk–Ulam theorem for adaptive continuous
  measurements and the matching upper bound: if `2ⁿ ≤ d`, every adaptive scheme of `n`
  continuous measurements on a `d`-dimensional real normed space gives some antipodal pair
  on every sphere the same values, while `k + 1` measurements recover every vector to any
  accuracy when `d ≤ 2ᵏ`; hence `⌈log₂(d+1)⌉ ≤ n* ≤ ⌈log₂ d⌉ + 1` for the least number
  `n*`, with equality `n* = k + 1` when `d = 2ᵏ`; advertising
  `ContMeasurements.exists_norm_eq_and_info_eq_info_neg`,
  `ContMeasurements.exists_recovery_scheme`,
  `ContMeasurements.clog_le_minMeasurements_and_le` and
  `ContMeasurements.minMeasurements_eq_of_finrank_eq_two_pow`.
-/

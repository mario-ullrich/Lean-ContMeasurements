# Candidates for Mathlib

Everything in `BasicResults` is general mathematics that mentions no measurements, and none
of it is in Mathlib. The results live in root namespaces, as a Mathlib contribution would
have them.

* **The Borsuk–Ulam theorem** itself, in any of its forms (`borsukUlam_cube`, `borsukUlam`,
  `Function.Odd.exists_norm_eq_and_eq_zero_of_lt_finrank`), together with **Tucker's lemma**
  (`GridSimplex.tucker`) and the Kuhn triangulation of the integer cube it runs on
  (`BasicResults/GridSimplex.lean`).
* `Metric.infDist` under negation: there is an extended-distance `infEDist_neg` but no
  real-valued `infDist_neg`; here it is derived from `Metric.infDist_image isometry_neg`.
* The passage from level sets to slabs by a Lebesgue-number argument
  (`HasSplitCover.exists_pos_inter_preimage_ball`), which is generic.
* The bisection lemma (`exists_bisection_scheme`): a finite family of "membership
  oracles" realised by distance functionals. This one is stated for adaptive schemes and
  lives in `ContMeasurements`, so upstreaming it means restating it without them.
* The Lebesgue cover (`ColoredCover.lebesgue`): a colored covering of `ℝᵐ` with
  `m + 1` colors and separated pieces of the same color.
* The logistic function and the logit (`Real.logistic`, `Real.logit`), which Mathlib
  does not have.

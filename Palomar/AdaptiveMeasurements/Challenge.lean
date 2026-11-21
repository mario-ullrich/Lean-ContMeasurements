/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Nat.Log

/-!
# A Borsuk–Ulam theorem for adaptive continuous measurements: statement surface

This module is the *Challenge* of a Palomar submission: the small, auditable surface
carrying the advertised statements. It imports nothing beyond Mathlib, so every notion it
uses is either standard or written out here. The proofs live in
`Palomar.AdaptiveMeasurements.Solution`, which supplies them from the development in
`ContMeasurements/` and `BasicResults/`; the `sorry`s below are the placeholders required by
that format.

## The question

A vector `x` of a `d`-dimensional real normed space `E` is to be recovered up to an error
`ε` in the norm, from `n` real numbers `λ₁(x), …, λₙ(x)`. Each `λᵢ` is a continuous function
of `x`, and it may be chosen after the values `λ₁(x), …, λᵢ₋₁(x)` have been seen. How large
must `n` be?

With linear measurements, or with continuous measurements fixed in advance, `d` are needed.
Adaptively chosen continuous measurements need far fewer: `⌈log₂ d⌉ + 1` suffice for every
accuracy, and `⌈log₂(d+1)⌉` are necessary. The two bounds meet when `d` is a power of two.

## The model

An *adaptive scheme* on a topological space `X` is a family of functionals
`fct k y : X → ℝ`, one for each number `k` of values already observed and each vector
`y : Fin k → ℝ` of those values. Each functional is continuous in the point measured; its
dependence on the observed values `y` is arbitrary, and that freedom is what makes the
scheme adaptive. The information map `S.info n x : Fin n → ℝ` evaluates the first `n`
measurements in sequence, each selected by the values before it. An algorithm is
`Φ ∘ S.info n` with an arbitrary reconstruction map `Φ`, and errors are stated pointwise.
`minMeasurements E R ε` is the least `n` for which some scheme and some reconstruction
recover every `x` of the closed ball of radius `R` to within `ε`.

## The statements

1. **Borsuk–Ulam for adaptive schemes.** If `2ⁿ ≤ d`, then for every scheme and every
   `R > 0` some `x` with `‖x‖ = R` satisfies `S.info n x = S.info n (-x)`. The information
   map is in general discontinuous, so the classical theorem does not apply to it directly.
2. **The upper bound.** If `0 < d ≤ 2ᵏ`, then for every `ε > 0` there are a scheme and a
   reconstruction with `‖x - Φ (S.info (k + 1) x)‖ ≤ ε` for every `x ∈ E`, with no bound on
   the norm of `x`.
3. **Both bounds.** For `d > 0` and `0 < ε < R`,
   `⌈log₂(d+1)⌉ ≤ minMeasurements E R ε ≤ ⌈log₂ d⌉ + 1`.
4. **Powers of two.** If `d = 2ᵏ` and `0 < ε < R`, then `minMeasurements E R ε = k + 1`.

`Nat.clog 2 d` is Mathlib's `⌈log₂ d⌉`.

## The definitions restated here

* `ContMeasurements.AdaptiveScheme`: an adaptive scheme of continuous measurements;
* `ContMeasurements.AdaptiveScheme.first`, `ContMeasurements.AdaptiveScheme.tail`: its first
  functional, and the scheme of the remaining measurements once a first value is observed;
* `ContMeasurements.AdaptiveScheme.info`: the information map of the first `n` measurements;
* `ContMeasurements.minMeasurements`: the least number of measurements.

They are reproduced verbatim from `ContMeasurements/Scheme.lean` and
`ContMeasurements/Complexity.lean`, under the same names and with the same variable
declarations, so that Comparator can match them against their counterparts there. The four
theorems likewise carry the names they have in the development.
-/

@[expose] public section

namespace ContMeasurements

universe u

/-- An **adaptive scheme of continuous measurements** on `X`.

After `k` values `y : Fin k → ℝ` have been observed, the next functional to be
evaluated is `fct k y : X → ℝ`.  Each such functional is continuous in the point
being measured; the dependence of `fct k y` on `y` is arbitrary, and that dependence
is precisely what "adaptive" means.

The scheme carries no length: a scheme of any length is obtained by reading off only
the first `n` measurements, see `AdaptiveScheme.info`. -/
structure AdaptiveScheme (X : Type u) [TopologicalSpace X] where
  /-- The functional asked after the values `y : Fin k → ℝ` have been observed. -/
  fct : (k : ℕ) → (Fin k → ℝ) → X → ℝ
  /-- Every functional of the scheme is continuous. -/
  continuous_fct : ∀ k y, Continuous (fct k y)

namespace AdaptiveScheme

variable {X : Type u} [TopologicalSpace X]

/-- The first functional `λ₁` of a scheme, asked before anything has been observed. -/
def first (S : AdaptiveScheme X) : X → ℝ :=
  S.fct 0 Fin.elim0

/-- The scheme governing the remaining measurements once the value `y` has been
observed: its `k`-th functional is the `(k+1)`-st functional of `S`, asked after the
values `y, ys`. -/
def tail (S : AdaptiveScheme X) (y : ℝ) : AdaptiveScheme X where
  fct k ys := S.fct (k + 1) (Fin.cons y ys)
  continuous_fct _ _ := S.continuous_fct _ _

/-- The **information map** `N : X → ℝⁿ` of the first `n` measurements of a scheme:
`N x = (λ₁ x, λ₂^{(y₁)} x, …)`, each functional being selected by the values already
produced. -/
def info : (n : ℕ) → AdaptiveScheme X → X → (Fin n → ℝ)
  | 0, _, _ => Fin.elim0
  | n + 1, S, x => Fin.cons (S.first x) (info n (S.tail (S.first x)) x)

end AdaptiveScheme

section LowerBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]

/-- **Borsuk–Ulam for adaptive measurements.**  If `2ⁿ ≤ m = dim E`, then no matter how
the `n` continuous measurements are chosen, adaptively and with no regularity in the
observed values, some antipodal pair on the sphere of radius `R` produces exactly the
same information. -/
theorem exists_norm_eq_and_info_eq_info_neg {m n : ℕ} (hm : Module.finrank ℝ E = m)
    (S : AdaptiveScheme E) (hn : 2 ^ n ≤ m) {R : ℝ} (hR : 0 < R) :
    ∃ x : E, ‖x‖ = R ∧ S.info n x = S.info n (-x) :=
  sorry

end LowerBound

/-- **The upper bound.**  If `0 < d = dim E ≤ 2ᵏ`, then `k + 1` adaptive continuous
measurements recover every vector of `E` to within any `ε > 0`, with no bound on its
norm. -/
theorem exists_recovery_scheme {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {d k : ℕ} (hd : Module.finrank ℝ E = d) (hd0 : 0 < d)
    (hk : d ≤ 2 ^ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : AdaptiveScheme E) (Φ : (Fin (k + 1) → ℝ) → E),
      ∀ x : E, ‖x - Φ (S.info (k + 1) x)‖ ≤ ε :=
  sorry

section Complexity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The least number of adaptive continuous measurements that suffice to recover every
vector of the closed ball of radius `R` to within `ε`.

`Nat.sInf` returns `0` when no such number exists; the bounds below always come with
hypotheses that exclude this. -/
noncomputable def minMeasurements (E : Type*) [NormedAddCommGroup E] (R ε : ℝ) : ℕ :=
  sInf {n | ∃ (S : AdaptiveScheme E) (Φ : (Fin n → ℝ) → E),
    ∀ x ∈ Metric.closedBall (0 : E) R, ‖x - Φ (S.info n x)‖ ≤ ε}

variable [FiniteDimensional ℝ E]

/-- **Both bounds.**  For `d = dim E > 0` and `0 < ε < R`, the least number of
measurements satisfies `⌈log₂(d+1)⌉ ≤ minMeasurements E R ε ≤ ⌈log₂ d⌉ + 1`. -/
theorem clog_le_minMeasurements_and_le {d : ℕ} (hd : Module.finrank ℝ E = d) (hd0 : 0 < d)
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    Nat.clog 2 (d + 1) ≤ minMeasurements E R ε ∧
      minMeasurements E R ε ≤ Nat.clog 2 d + 1 :=
  sorry

/-- **Powers of two.**  If `dim E = 2ᵏ` and `0 < ε < R`, exactly `k + 1` measurements are
needed: `minMeasurements E R ε = k + 1`. -/
theorem minMeasurements_eq_of_finrank_eq_two_pow {k : ℕ} (hd : Module.finrank ℝ E = 2 ^ k)
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) : minMeasurements E R ε = k + 1 :=
  sorry

end Complexity

end ContMeasurements

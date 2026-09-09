/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import ContMeasurements.LowerBound
import ContMeasurements.UpperBound

/-!
# The exact number of measurements

Putting the two bounds together: writing `n*(d, R, ε)` for the least number of
adaptive continuous measurements with which every vector of the ball of radius `R` in
a `d`-dimensional real normed space can be recovered to within `ε < R`,

  `⌈log₂(d+1)⌉ ≤ n*(d, R, ε) ≤ ⌈log₂ d⌉ + 1`.

The two bounds coincide when `d` is a power of two, where `n* = log₂ d + 1` exactly,
and differ by one otherwise.

Both are remarkable next to the classical situation: with linear — or with
nonadaptive continuous — measurements, fewer than `d` of them achieve nothing at all.
Adaptivity together with nonlinearity is what buys the exponential saving, and neither
alone does.

## Main results

* `ContMeasurements.minMeasurements` — the quantity `n*`.
* `ContMeasurements.minMeasurements_le` — the upper bound. Proved unconditionally.
* `ContMeasurements.clog_le_minMeasurements` — the lower bound. Depends on
  `borsukUlam_euclidean`, hence on its `sorry`.
* `ContMeasurements.minMeasurements_eq_of_two_pow` — equality in dimension `2ᵏ`.
  Depends on the same `sorry`.
-/

namespace ContMeasurements

open Metric AdaptiveScheme

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The least number of adaptive continuous measurements that suffice to recover every
vector of the closed ball of radius `R` to within `ε`.

`Nat.sInf` returns `0` when no such number exists; the bounds below always come with
hypotheses that exclude this. -/
noncomputable def minMeasurements (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R ε : ℝ) : ℕ :=
  sInf {n | ∃ (S : AdaptiveScheme E) (Φ : (Fin n → ℝ) → E),
    ∀ x ∈ Metric.closedBall (0 : E) R, ‖x - Φ (S.info n x)‖ ≤ ε}

variable [FiniteDimensional ℝ E]

/-- **The upper bound.**  `⌈log₂ d⌉ + 1` measurements are enough, for every accuracy
and every radius.  Proved unconditionally. -/
theorem minMeasurements_le {d : ℕ} (hd : Module.finrank ℝ E = d) (hd0 : 0 < d)
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) : minMeasurements E R ε ≤ Nat.clog 2 d + 1 := by
  refine Nat.sInf_le ?_
  obtain ⟨S, Φ, hSΦ⟩ := exists_recovery_scheme hd hd0 hε
  exact ⟨S, Φ, fun x _ => hSΦ x⟩

/-- **The lower bound, in counting form.**  An algorithm accurate to within `ε < R` on
the ball of radius `R` uses `n` measurements with `2ⁿ ≥ d + 1`.

Depends on `borsukUlam_euclidean`, hence on its `sorry`. -/
theorem succ_le_two_pow_minMeasurements {d : ℕ} (hd : Module.finrank ℝ E = d)
    (hd0 : 0 < d) {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    d + 1 ≤ 2 ^ minMeasurements E R ε := by
  have hne : {n | ∃ (S : AdaptiveScheme E) (Φ : (Fin n → ℝ) → E),
      ∀ x ∈ Metric.closedBall (0 : E) R, ‖x - Φ (S.info n x)‖ ≤ ε}.Nonempty := by
    refine ⟨Nat.clog 2 d + 1, ?_⟩
    obtain ⟨S, Φ, hSΦ⟩ := exists_recovery_scheme hd hd0 hε
    exact ⟨S, Φ, fun x _ => hSΦ x⟩
  obtain ⟨S, Φ, hSΦ⟩ :
      ∃ (S : AdaptiveScheme E) (Φ : (Fin (minMeasurements E R ε) → ℝ) → E),
        ∀ x ∈ Metric.closedBall (0 : E) R,
          ‖x - Φ (S.info (minMeasurements E R ε) x)‖ ≤ ε := Nat.sInf_mem hne
  by_contra hcon
  have hn : 2 ^ minMeasurements E R ε ≤ d := by omega
  have hR : 0 < R := hε.trans hεR
  obtain ⟨x, hxn, hxerr⟩ := exists_error_ge hd S hn hR Φ
  have hmem : x ∈ Metric.closedBall (0 : E) R := by
    rw [Metric.mem_closedBall, dist_zero_right, hxn]
  have hle := hSΦ x hmem
  linarith

/-- **The lower bound.**  At least `⌈log₂(d+1)⌉` measurements are needed.

Depends on `borsukUlam_euclidean`, hence on its `sorry`. -/
theorem clog_le_minMeasurements {d : ℕ} (hd : Module.finrank ℝ E = d) (hd0 : 0 < d)
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    Nat.clog 2 (d + 1) ≤ minMeasurements E R ε :=
  (Nat.clog_le_iff_le_pow one_lt_two).2 (succ_le_two_pow_minMeasurements hd hd0 hε hεR)

/-- **The sandwich.**  `⌈log₂(d+1)⌉ ≤ n* ≤ ⌈log₂ d⌉ + 1`.

Depends on `borsukUlam_euclidean` through its lower half. -/
theorem clog_le_minMeasurements_le {d : ℕ} (hd : Module.finrank ℝ E = d) (hd0 : 0 < d)
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    Nat.clog 2 (d + 1) ≤ minMeasurements E R ε ∧
      minMeasurements E R ε ≤ Nat.clog 2 d + 1 :=
  ⟨clog_le_minMeasurements hd hd0 hε hεR, minMeasurements_le hd hd0 R hε⟩

/-- **In dimension a power of two the two bounds meet:** `n*(2ᵏ) = k + 1`.

Depends on `borsukUlam_euclidean`, hence on its `sorry`. -/
theorem minMeasurements_eq_of_two_pow {k : ℕ} (hd : Module.finrank ℝ E = 2 ^ k)
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) : minMeasurements E R ε = k + 1 := by
  have hd0 : 0 < 2 ^ k := Nat.one_le_two_pow
  have hle : minMeasurements E R ε ≤ k + 1 := by
    have h := minMeasurements_le hd hd0 R hε
    rwa [Nat.clog_pow 2 k one_lt_two] at h
  have hge : k + 1 ≤ minMeasurements E R ε := by
    have h := succ_le_two_pow_minMeasurements hd hd0 hε hεR
    by_contra hcon
    rw [not_le] at hcon
    have hmono : 2 ^ minMeasurements E R ε ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  omega

end ContMeasurements

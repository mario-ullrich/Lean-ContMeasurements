/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import ContMeasurements.Bisection
import ContMeasurements.Identification
import BasicResults.LebesgueCover
import BasicResults.Logistic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Nat.Log

/-!
# The upper bound

Whenever `d ≤ 2ᵏ`, `k + 1` adaptively chosen continuous measurements recover every
vector of a `d`-dimensional real normed space to within any prescribed accuracy; in
particular `⌈log₂ d⌉ + 1` do, exponentially fewer than the `d` measurements that linear
(or nonadaptive continuous) information needs.

## The algorithm

Fix the target accuracy `ε > 0` and write the dimension as `d = m + 1`.

1. Take the Lebesgue cover of `ℝᵐ` (`ColoredCover.lebesgue`), rescaled so that its pieces have
   diameter well below `ε`.  It has `m + 1 = d` colors.
2. Spend `k` measurements on a bisection over the `d ≤ 2ᵏ` colors (`Bisection.lean`).
   Each measurement is the distance to the union of the color classes of one half, a
   continuous functional whose vanishing decides the half.
3. Spend **one** further measurement to pin down the piece inside the chosen color
   class (`Identification.lean`).  Because pieces of one color are separated, a
   single continuous functional can take a different **integer** value near each of
   them.

The first `d - 1` coordinates are now known to within `ε`.  The last coordinate comes
for free: the identification functional is integer-valued, so adding a continuous
injection of the last coordinate into `(0,1)` leaves the integer part intact while the
fractional part carries that coordinate exactly.  This is the trick that brings the
count down from `⌈log₂(d+1)⌉ + 1` to `⌈log₂ d⌉ + 1`.

## Main results

* `ContMeasurements.exists_recovery_scheme_pi`: the theorem for `ℝᵈ` with the maximum
  norm.
* `ContMeasurements.exists_recovery_scheme`: the theorem for an arbitrary
  finite-dimensional real normed space, obtained by transporting along a linear
  homeomorphism.  Since all norms on a finite-dimensional space are equivalent, this
  is the statement "for any norm" of the paper.
* `ContMeasurements.exists_recovery_scheme_clog`: the closed form, `⌈log₂ d⌉ + 1`
  measurements.

Both are proved **unconditionally**; Borsuk–Ulam is not involved.
-/

namespace ContMeasurements

open Metric Set AdaptiveScheme

/-- **Recovery in `ℝ^{m+1}` with the maximum norm.**

If `m + 1 ≤ 2ᵏ`, then for every accuracy `ε > 0` there is a scheme of `k + 1` adaptive
continuous measurements together with a reconstruction map recovering every vector of
`ℝ^{m+1}` to within `ε`. -/
theorem exists_recovery_scheme_pi (m k : ℕ) (hk : m + 1 ≤ 2 ^ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : AdaptiveScheme (Fin (m + 1) → ℝ)) (Φ : (Fin (k + 1) → ℝ) → (Fin (m + 1) → ℝ)),
      ∀ x, dist x (Φ (S.info (k + 1) x)) ≤ ε := by
  classical
  -- The projection onto the first `m` coordinates.
  set π : (Fin (m + 1) → ℝ) → (Fin m → ℝ) := fun x i => x i.castSucc with hπdef
  have hπ : Continuous π := continuous_pi fun i => continuous_apply i.castSucc
  -- The Lebesgue cover of `ℝᵐ`, rescaled to the target accuracy.
  have hs : (0 : ℝ) < ε / 2 := by linarith
  set cc := (ColoredCover.lebesgue m).scale hs with hccdef
  have hc : 0 < ε / 2 * LebesgueCover.sep m := mul_pos hs (LebesgueCover.sep_pos m)
  have haccuracy : ε / 2 * (3 / 2) + ε / 2 * LebesgueCover.sep m / 8 ≤ ε := by
    have h1 := LebesgueCover.sep_le_one m
    have h2 := (LebesgueCover.sep_pos m).le
    nlinarith
  -- For each color, the identification functional and its decoder.
  choose fct dec hfctc hfct using fun r => exists_identification cc hc r
  -- The leaf algorithms: the identification functional of the first `m` coordinates,
  -- offset by an injective encoding of the last coordinate into `(0,1)`.
  set leafFun : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ :=
    fun r x => fct r (π x) + Real.logistic (x (Fin.last m)) with hleafFun
  have hleafc : ∀ r, Continuous (leafFun r) := fun r =>
    ((hfctc r).comp hπ).add (Real.continuous_logistic.comp (continuous_apply (Fin.last m)))
  set leaf : Fin (m + 1) → AdaptiveScheme (Fin (m + 1) → ℝ) :=
    fun r => AdaptiveScheme.const (leafFun r) (hleafc r) with hleafdef
  set out : Fin (m + 1) → (Fin 1 → ℝ) → (Fin (m + 1) → ℝ) :=
    fun r y => Fin.snoc (dec r ⌊y 0⌋) (Real.logit (Int.fract (y 0))) with houtdef
  -- The color classes, pulled back to `ℝ^{m+1}`.
  set A : Fin (m + 1) → Set (Fin (m + 1) → ℝ) := fun r => π ⁻¹' cc.colorClass r with hAdef
  -- Each leaf is accurate on the closure of its color class.
  have hleafspec : ∀ r, ∀ x ∈ closure (A r),
      dist x (out r ((leaf r).info 1 x)) ≤ ε := by
    intro r x hx
    have hπx : π x ∈ closure (cc.colorClass r) := hπ.closure_preimage_subset _ hx
    obtain ⟨n, hn, hdec⟩ := hfct r (π x) hπx
    -- The measured value is the integer `n` plus something in `(0,1)`.
    have hval : (leaf r).info 1 x 0 = (n : ℝ) + Real.logistic (x (Fin.last m)) := by
      have h1 : (leaf r).info 1 x = Fin.cons (leafFun r x) Fin.elim0 :=
        AdaptiveScheme.info_const_one _ _ _
      rw [h1, Fin.cons_zero]
      show fct r (π x) + Real.logistic (x (Fin.last m))
        = (n : ℝ) + Real.logistic (x (Fin.last m))
      rw [hn]
    obtain ⟨hlo, hhi⟩ := Real.logistic_mem_Ioo (x (Fin.last m))
    have hfl : ⌊(leaf r).info 1 x 0⌋ = n := by
      rw [hval, Int.floor_intCast_add, Int.floor_eq_zero_iff.2 ⟨hlo.le, hhi⟩, add_zero]
    have hfr : Int.fract ((leaf r).info 1 x 0) = Real.logistic (x (Fin.last m)) := by
      rw [hval, Int.fract_intCast_add, Int.fract_eq_self.2 ⟨hlo.le, hhi⟩]
    have hout : out r ((leaf r).info 1 x) = Fin.snoc (dec r n) (x (Fin.last m)) := by
      rw [houtdef]
      simp only [hfl, hfr, Real.logit_logistic]
    rw [hout, dist_pi_le_iff hε.le]
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [Fin.snoc_last, dist_self]
      exact hε.le
    · intro j
      rw [Fin.snoc_castSucc]
      have hcoord : dist (x j.castSucc) (dec r n j) = dist (π x j) (dec r n j) := rfl
      rw [hcoord]
      exact le_trans (dist_le_pi_dist (π x) (dec r n) j) (le_trans hdec haccuracy)
  -- Bisection over the `m + 1 ≤ 2ᵏ` colors costs `k` measurements.
  have hcard : (Finset.univ : Finset (Fin (m + 1))).card ≤ 2 ^ k := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact hk
  obtain ⟨S, Φ, hSΦ⟩ := exists_bisection_scheme hleafspec k Finset.univ hcard
  -- Every point has a color, so the guarantee is global.
  have huniv : ∀ x : Fin (m + 1) → ℝ,
      x ∈ closure (⋃ r ∈ (Finset.univ : Finset (Fin (m + 1))), A r) := by
    intro x
    refine subset_closure ?_
    obtain ⟨r, hr⟩ := cc.exists_mem_colorClass (π x)
    exact Set.mem_iUnion₂.2 ⟨r, Finset.mem_univ r, hr⟩
  have key : ∃ (S : AdaptiveScheme (Fin (m + 1) → ℝ))
      (Φ : (Fin (1 + k) → ℝ) → (Fin (m + 1) → ℝ)),
      ∀ x, dist x (Φ (S.info (1 + k) x)) ≤ ε :=
    ⟨S, Φ, fun x => hSΦ x (huniv x)⟩
  rwa [Nat.add_comm 1 k] at key

/-- **Recovery in an arbitrary finite-dimensional real normed space.**

If `d ≤ 2ᵏ`, then for every `ε > 0` a scheme of `k + 1` adaptive continuous
measurements recovers every vector of a `d`-dimensional real normed space to within
`ε`. The case `k = ⌈log₂ d⌉` is `exists_recovery_scheme_clog`.

All norms on a finite-dimensional space are equivalent, so this is the "for any norm
on `ℝᵈ`" statement of the paper; the proof transports the coordinate algorithm along a
linear homeomorphism and rescales the accuracy by the norm of its inverse. -/
theorem exists_recovery_scheme {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {d k : ℕ} (hd : Module.finrank ℝ E = d) (hd0 : 0 < d)
    (hk : d ≤ 2 ^ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : AdaptiveScheme E) (Φ : (Fin (k + 1) → ℝ) → E),
      ∀ x : E, ‖x - Φ (S.info (k + 1) x)‖ ≤ ε := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  let e : E ≃L[ℝ] (Fin (m + 1) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (hd.trans (Module.finrank_fin_fun ℝ).symm)
  set C : ℝ := ‖(e.symm : (Fin (m + 1) → ℝ) →L[ℝ] E)‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  have hεC : (0 : ℝ) < ε / (C + 1) := by positivity
  obtain ⟨Sp, Φp, hSp⟩ := exists_recovery_scheme_pi m k hk hεC
  have hfin : C * (ε / (C + 1)) ≤ ε := by
    have hpos : (0 : ℝ) < C + 1 := by linarith
    rw [mul_comm, div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith
  refine ⟨Sp.comap e e.continuous, fun y => e.symm (Φp y), ?_⟩
  intro x
  rw [AdaptiveScheme.info_comap]
  calc ‖x - e.symm (Φp (Sp.info (k + 1) (e x)))‖
      = ‖e.symm (e x - Φp (Sp.info (k + 1) (e x)))‖ := by
        rw [map_sub, e.symm_apply_apply]
    _ ≤ C * ‖e x - Φp (Sp.info (k + 1) (e x))‖ :=
        (e.symm : (Fin (m + 1) → ℝ) →L[ℝ] E).le_opNorm _
    _ ≤ C * (ε / (C + 1)) := by
        have hpi := hSp (e x)
        rw [dist_eq_norm] at hpi
        exact mul_le_mul_of_nonneg_left hpi hC0
    _ ≤ ε := hfin

/-- **The closed form:** `⌈log₂ d⌉ + 1` measurements suffice, the case `k = ⌈log₂ d⌉`
of `exists_recovery_scheme`, since `d ≤ 2^⌈log₂ d⌉` (`Nat.le_pow_clog`). -/
theorem exists_recovery_scheme_clog {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {d : ℕ} (hd : Module.finrank ℝ E = d) (hd0 : 0 < d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : AdaptiveScheme E) (Φ : (Fin (Nat.clog 2 d + 1) → ℝ) → E),
      ∀ x : E, ‖x - Φ (S.info (Nat.clog 2 d + 1) x)‖ ≤ ε :=
  exists_recovery_scheme hd hd0 (Nat.le_pow_clog one_lt_two d) hε

end ContMeasurements

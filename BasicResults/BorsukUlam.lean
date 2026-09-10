/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Algebra.Group.EvenFunction

/-!
# The Borsuk–Ulam theorem

The odd-map form of the Borsuk–Ulam theorem states that a continuous odd map from the
sphere `S^{m-1}` into `ℝᵏ` with `k < m` must vanish somewhere.  Equivalently, a
continuous map `S^{m-1} → ℝᵏ` with `k < m` takes the same value at some antipodal
pair.

**This theorem is not available in Mathlib** (as of the pinned release there is no
Borsuk–Ulam theorem, and neither Brouwer's fixed point theorem nor Sperner's or
Tucker's lemma, from which it is usually derived).  It is therefore stated here with
a `sorry`, and it is the **only** `sorry` in this development.

If Borsuk–Ulam enters Mathlib, only `borsukUlam` has to be replaced by an
`exact` of the library result; nothing downstream changes.

The cases `k ≤ 1` are elementary and are proved below, in `borsukUlam_of_le_one`.

## Main statements

* `borsukUlam` — the theorem itself, on the unit sphere of
  `EuclideanSpace ℝ (Fin m)`. **Contains the project's only `sorry`.**
* `borsukUlam_of_le_one` — the same statement for `k ≤ 1`, proved.
* `Function.Odd.exists_norm_eq_and_eq_zero_of_lt_finrank` — the form actually used: on
  *any* finite-dimensional real normed space `E` of dimension `m`, and on the sphere
  of *any* radius `R > 0`, a continuous odd map `E → ℝᵏ` with `k < m` has a zero.
  This is proved from the Euclidean case by transporting along a linear
  homeomorphism and rescaling radially, and it is what makes the lower bound valid
  for an arbitrary norm.
-/

open Metric

/-- The Euclidean space `ℝᵐ` is nontrivial as soon as `m ≥ 1`. -/
theorem EuclideanSpace.nontrivial_of_pos {m : ℕ} (hm : 0 < m) :
    Nontrivial (EuclideanSpace ℝ (Fin m)) :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)

/-- The unit sphere of `ℝᵐ` is nonempty as soon as `m ≥ 1`. -/
theorem EuclideanSpace.unitSphere_nonempty {m : ℕ} (hm : 0 < m) :
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1).Nonempty :=
  haveI := EuclideanSpace.nontrivial_of_pos hm
  NormedSpace.sphere_nonempty.2 zero_le_one

/-- The rank of `ℝᵐ` exceeds one as soon as `m ≥ 2`; this is what the connectedness of
its spheres needs. -/
theorem EuclideanSpace.one_lt_rank {m : ℕ} (hm : 1 < m) :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin m)) := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast hm

/-- **Borsuk–Ulam theorem** (odd-map form).  A map into `ℝᵏ` with `k < m` that is odd
and continuous on the unit sphere of `ℝᵐ` vanishes at some point of that sphere.

Equivalently: `k < m` continuous functionals cannot separate all antipodal pairs of
`S^{m-1}`.

**This is the only `sorry` of the development.** -/
theorem borsukUlam {m k : ℕ} (hk : k < m)
    (f : EuclideanSpace ℝ (Fin m) → (Fin k → ℝ))
    (hf : ContinuousOn f (Metric.sphere 0 1)) (hodd : Function.Odd f) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1, f x = 0 :=
  sorry

/-- **Borsuk–Ulam for at most one functional**, proved unconditionally.

With no functional the conclusion is empty and only needs a point on the sphere.  With
one functional it is the intermediate value theorem: the sphere of `ℝᵐ` is connected
for `m ≥ 2`, and an odd function takes opposite values at an antipodal pair, so it
takes the value `0` in between. -/
theorem borsukUlam_of_le_one {m k : ℕ} (hk1 : k ≤ 1) (hk : k < m)
    (f : EuclideanSpace ℝ (Fin m) → (Fin k → ℝ))
    (hf : ContinuousOn f (Metric.sphere 0 1)) (hodd : Function.Odd f) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1, f x = 0 := by
  rcases Nat.lt_or_ge k 1 with hk0 | hk1'
  · -- No functional at all: every point of the sphere works, and there is one.
    obtain ⟨x, hx⟩ := EuclideanSpace.unitSphere_nonempty (m := m) (by omega)
    exact ⟨x, hx, funext fun i => absurd i.2 (by omega)⟩
  · -- One functional: the intermediate value theorem on the connected sphere.
    obtain rfl : k = 1 := le_antisymm hk1 hk1'
    have hm : 1 < m := hk
    set g : EuclideanSpace ℝ (Fin m) → ℝ := fun x => f x 0 with hg
    have hgc : ContinuousOn g (Metric.sphere 0 1) :=
      (continuous_apply (0 : Fin 1)).comp_continuousOn hf
    have hpre : IsPreconnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :=
      isPreconnected_sphere (EuclideanSpace.one_lt_rank hm) 0 1
    obtain ⟨a, ha⟩ := EuclideanSpace.unitSphere_nonempty (m := m) (by omega)
    have hna : -a ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 := by
      rw [mem_sphere_zero_iff_norm] at ha ⊢
      rwa [norm_neg]
    have hgodd : g (-a) = -g a := by rw [hg]; simp [hodd a]
    -- `0` lies between the two antipodal values, hence is attained on the sphere.
    have hzero : ∃ y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1, g y = 0 := by
      rcases le_total (g a) 0 with hga | hga
      · have h0 : (0 : ℝ) ∈ Set.Icc (g a) (g (-a)) := ⟨hga, by rw [hgodd]; linarith⟩
        exact hpre.intermediate_value ha hna hgc h0
      · have h0 : (0 : ℝ) ∈ Set.Icc (g (-a)) (g a) := ⟨by rw [hgodd]; linarith, hga⟩
        exact hpre.intermediate_value hna ha hgc h0
    obtain ⟨y, hy, hgy⟩ := hzero
    exact ⟨y, hy, funext fun i => by rw [Subsingleton.elim i 0]; exact hgy⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Borsuk–Ulam for an arbitrary norm and an arbitrary radius.**

On a real normed space of finite dimension `m`, every continuous odd map
`Ψ : E → ℝᵏ` with `k < m` vanishes at some point of norm `R`, for every `R > 0`.

The reduction to the Euclidean unit sphere is purely formal: a linear homeomorphism
`EuclideanSpace ℝ (Fin m) ≃L[ℝ] E` carries the Euclidean unit sphere onto a compact
symmetric set, and the radial map `u ↦ (R / ‖e u‖) • e u` sends it onto the sphere of
radius `R` of `E` oddly and continuously.  No property of the norm of `E` is used
beyond homogeneity, which is why the lower bound holds for *any* norm.

Depends on `borsukUlam`, hence on its `sorry`. -/
theorem Function.Odd.exists_norm_eq_and_eq_zero_of_lt_finrank {m k : ℕ}
    (hm : Module.finrank ℝ E = m) (hk : k < m) {R : ℝ} (hR : 0 < R)
    (Ψ : E → (Fin k → ℝ)) (hΨc : Continuous Ψ) (hΨo : Function.Odd Ψ) :
    ∃ x : E, ‖x‖ = R ∧ Ψ x = 0 := by
  -- A linear homeomorphism from the Euclidean model space.
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin.trans hm.symm)
  -- The radial map onto the sphere of radius `R`, introduced with a pointwise defining
  -- equation so that rewriting under it stays straightforward.
  obtain ⟨g, hg⟩ :
      ∃ g : EuclideanSpace ℝ (Fin m) → E, ∀ u, g u = (R / ‖e u‖) • e u :=
    ⟨_, fun _ => rfl⟩
  have hne : ∀ u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1, ‖e u‖ ≠ 0 := by
    intro u hu
    rw [norm_ne_zero_iff]
    intro h0
    have hu0 : u = 0 := by simpa using congrArg e.symm h0
    rw [mem_sphere_zero_iff_norm, hu0, norm_zero] at hu
    exact zero_ne_one hu
  -- `g` is odd, since `e` is linear and the norm is even.
  have hgodd : Function.Odd g := by
    intro u
    rw [hg, hg, map_neg, norm_neg, smul_neg]
  -- `g` is continuous away from the origin, in particular on the unit sphere.
  have hgcont : ContinuousOn g (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) := by
    have hgfun : g = fun u => (R / ‖e u‖) • e u := funext hg
    rw [hgfun]
    exact (continuousOn_const.div e.continuous.norm.continuousOn hne).smul
      e.continuous.continuousOn
  have hcont : ContinuousOn (Ψ ∘ g) (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    hΨc.comp_continuousOn hgcont
  have hodd : Function.Odd (Ψ ∘ g) := by
    intro u
    show Ψ (g (-u)) = -Ψ (g u)
    rw [hgodd u, hΨo]
  -- Borsuk–Ulam produces a zero on the unit sphere; rescaling gives the point wanted.
  obtain ⟨u₀, hu₀, hzero⟩ := borsukUlam hk (Ψ ∘ g) hcont hodd
  refine ⟨g u₀, ?_, hzero⟩
  have h1 : ‖e u₀‖ ≠ 0 := hne u₀ hu₀
  have h2 : (0 : ℝ) < ‖e u₀‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h1)
  rw [hg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_cancel₀ _ h1]

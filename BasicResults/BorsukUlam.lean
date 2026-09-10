/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
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

Everything else in the project is proved unconditionally.  The results that use
Borsuk–Ulam are exactly the lower bounds; they are marked as such in the README, and
`#print axioms` distinguishes them: the statements depending on this file report
`sorryAx`, all others do not.

If Borsuk–Ulam enters Mathlib, only `borsukUlam` has to be replaced by an
`exact` of the library result; nothing downstream changes.

## Main statements

* `borsukUlam` — the theorem itself, on the unit sphere of
  `EuclideanSpace ℝ (Fin m)`. **Contains the project's only `sorry`.**
* `Function.Odd.exists_norm_eq_and_eq_zero_of_lt_finrank` — the form actually used: on
  *any* finite-dimensional real normed space `E` of dimension `m`, and on the sphere
  of *any* radius `R > 0`, a continuous odd map `E → ℝᵏ` with `k < m` has a zero.
  This is proved from the Euclidean case by transporting along a linear
  homeomorphism and rescaling radially, and it is what makes the lower bound valid
  for an arbitrary norm.
-/

open Metric

/-- **Borsuk–Ulam theorem** (odd-map form).  A map into `ℝᵏ` with `k < m` that is odd
and continuous on the unit sphere of `ℝᵐ` vanishes at some point of that sphere.

Equivalently: `k < m` continuous functionals cannot separate all antipodal pairs of
`S^{m-1}`.

**This is the only `sorry` of the development.**  Mathlib does not provide
Borsuk–Ulam, and proving it would require a substantial piece of algebraic topology
(or a combinatorial route through Tucker's lemma), which is outside the scope of this
project. -/
theorem borsukUlam {m k : ℕ} (hk : k < m)
    (f : EuclideanSpace ℝ (Fin m) → (Fin k → ℝ))
    (hf : ContinuousOn f (Metric.sphere 0 1)) (hodd : Function.Odd f) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1, f x = 0 :=
  sorry

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

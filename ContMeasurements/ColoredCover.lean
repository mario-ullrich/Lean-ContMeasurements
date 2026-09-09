/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Coloured covers

A *coloured cover* of a metric space is a family of pieces `D i` covering the space,
each of diameter at most `ε`, together with a colouring `t` of the index set by
finitely many colours such that **two distinct pieces of the same colour are at
distance at least `c > 0`**.

This is the combinatorial input of the recovery algorithm of Krieg, Novak and
Ullrich.  Knowing the colour of the piece containing `x` costs `⌈log₂ K⌉` measurements
by bisection, because the union of the pieces of a given set of colours is a closed
set and the distance to it is a continuous functional.  Knowing the colour then
*locates* `x` up to `ε`, because within one colour the pieces are separated, so a
single further continuous functional can name the piece.

The number of colours cannot be smaller than `m + 1` in `ℝᵐ`; this is the Lebesgue
covering dimension of `ℝᵐ`.  The concrete cover with `m + 1` colours is built in
`BrickPartition.lean`.

## Main definitions

* `ContMeasurements.ColoredCover` — the structure above.
* `ContMeasurements.ColoredCover.colourSet` — the union `E_r` of all pieces of
  colour `r`.
* `ContMeasurements.ColoredCover.scale` — rescaling by a factor `s > 0`, which scales
  both `ε` and `c`.  This is how an arbitrary target accuracy is reached from a
  single cover of unit scale.
-/

open Metric Set

namespace ContMeasurements

/-- A **coloured cover** of the metric space `X` with `K` colours, pieces of diameter
at most `ε`, and distinct pieces of equal colour at distance at least `c`.

Diameters are stated pointwise (`dist_le`) rather than through `Metric.diam`, so that
no boundedness side conditions are needed and empty pieces are harmless. -/
structure ColoredCover (X : Type*) [PseudoMetricSpace X] (ι : Type*) (K : ℕ) (ε c : ℝ) where
  /-- The pieces of the cover. -/
  D : ι → Set X
  /-- The colour of each piece. -/
  t : ι → Fin K
  /-- The pieces cover the space. -/
  cover : ∀ x : X, ∃ i, x ∈ D i
  /-- Each piece has diameter at most `ε`. -/
  dist_le : ∀ i, ∀ x ∈ D i, ∀ y ∈ D i, dist x y ≤ ε
  /-- Distinct pieces of the same colour are `c`-separated. -/
  separated : ∀ i j, i ≠ j → t i = t j → ∀ x ∈ D i, ∀ y ∈ D j, c ≤ dist x y

namespace ColoredCover

variable {X : Type*} [PseudoMetricSpace X] {ι : Type*} {K : ℕ} {ε c : ℝ}

/-- The set `E_r` of points of colour `r`: the union of all pieces coloured `r`. -/
def colourSet (cc : ColoredCover X ι K ε c) (r : Fin K) : Set X :=
  {x | ∃ i, cc.t i = r ∧ x ∈ cc.D i}

@[simp]
theorem mem_colourSet {cc : ColoredCover X ι K ε c} {r : Fin K} {x : X} :
    x ∈ cc.colourSet r ↔ ∃ i, cc.t i = r ∧ x ∈ cc.D i := Iff.rfl

/-- Every point has a colour. -/
theorem exists_mem_colourSet (cc : ColoredCover X ι K ε c) (x : X) :
    ∃ r, x ∈ cc.colourSet r := by
  obtain ⟨i, hi⟩ := cc.cover x
  exact ⟨cc.t i, i, rfl, hi⟩

/-- The colour sets cover the space. -/
theorem iUnion_colourSet (cc : ColoredCover X ι K ε c) :
    (Set.univ : Set X) ⊆ ⋃ r, cc.colourSet r := by
  intro x _
  obtain ⟨r, hr⟩ := cc.exists_mem_colourSet x
  exact mem_iUnion.2 ⟨r, hr⟩

section Scale

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Scaling a vector scales distances by the absolute value of the factor. -/
private theorem dist_smul_eq (a : ℝ) (u v : V) : dist (a • u) (a • v) = ‖a‖ * dist u v := by
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul]

/-- Rescaling a coloured cover by a factor `s > 0`: the piece `D i` becomes `s • D i`,
so both the diameter bound and the separation constant are multiplied by `s`.

Applying this to the unit-scale brick partition of `ℝᵐ` produces covers of arbitrarily
small diameter, which is what turns the recovery algorithm into one of arbitrary
accuracy. -/
def scale (cc : ColoredCover V ι K ε c) {s : ℝ} (hs : 0 < s) :
    ColoredCover V ι K (s * ε) (s * c) where
  D i := (fun x => s⁻¹ • x) ⁻¹' cc.D i
  t := cc.t
  cover x := cc.cover (s⁻¹ • x)
  dist_le i x hx y hy := by
    have h := cc.dist_le i _ hx _ hy
    rw [dist_smul_eq, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)] at h
    have h2 := mul_le_mul_of_nonneg_left h hs.le
    rwa [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at h2
  separated i j hij hcol x hx y hy := by
    have h := cc.separated i j hij hcol _ hx _ hy
    rw [dist_smul_eq, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)] at h
    have h2 := mul_le_mul_of_nonneg_left h hs.le
    rwa [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at h2

@[simp]
theorem mem_scale_D {cc : ColoredCover V ι K ε c} {s : ℝ} (hs : 0 < s) {i : ι} {x : V} :
    x ∈ (cc.scale hs).D i ↔ s⁻¹ • x ∈ cc.D i := Iff.rfl

@[simp]
theorem scale_t {cc : ColoredCover V ι K ε c} {s : ℝ} (hs : 0 < s) :
    (cc.scale hs).t = cc.t := rfl

@[simp]
theorem mem_scale_colourSet {cc : ColoredCover V ι K ε c} {s : ℝ} (hs : 0 < s)
    {r : Fin K} {x : V} :
    x ∈ (cc.scale hs).colourSet r ↔ s⁻¹ • x ∈ cc.colourSet r := Iff.rfl

end Scale

end ColoredCover

end ContMeasurements

/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Colored covers

A *colored cover* of a metric space is a family of pieces covering the space,
each of diameter at most `ε`, together with a coloring of the index set by
finitely many colors such that **two distinct pieces of the same color are at
distance at least `c > 0`**.

This is the combinatorial input of the recovery algorithm of Krieg, Novak and
Ullrich.  Knowing the color of the piece containing `x` costs `⌈log₂ K⌉` measurements
by bisection, because the union of the pieces of a given set of colors is a closed
set and the distance to it is a continuous functional.  Knowing the color then
*locates* `x` up to `ε`, because within one color the pieces are separated, so a
single further continuous functional can name the piece.

The number of colors cannot be smaller than `m + 1` in `ℝᵐ`; this is the Lebesgue
covering dimension of `ℝᵐ`.  The concrete cover with `m + 1` colors is built in
`LebesgueCover.lean`.

## Main definitions

* `ColoredCover`: the structure above.
* `ColoredCover.colorClass`: the union `E_r` of all pieces of
  color `r`.
* `ColoredCover.scale`: rescaling by a factor `s > 0`, which scales
  both `ε` and `c`.  This is how an arbitrary target accuracy is reached from a
  single cover of unit scale.
-/

open Metric Set

/-- A **colored cover** of the metric space `X` with `K` colors, pieces of diameter
at most `ε`, and distinct pieces of equal color at distance at least `c`.

Diameters are stated pointwise (`dist_le_of_mem`) rather than through `Metric.diam`,
so that no boundedness side conditions are needed and empty pieces are harmless. -/
structure ColoredCover (X : Type*) [PseudoMetricSpace X] (ι : Type*) (K : ℕ) (ε c : ℝ) where
  /-- The pieces of the cover. -/
  piece : ι → Set X
  /-- The color of each piece. -/
  color : ι → Fin K
  /-- The pieces cover the space. -/
  exists_mem_piece : ∀ x : X, ∃ i, x ∈ piece i
  /-- Each piece has diameter at most `ε`. -/
  dist_le_of_mem : ∀ i, ∀ x ∈ piece i, ∀ y ∈ piece i, dist x y ≤ ε
  /-- Distinct pieces of the same color are `c`-separated. -/
  le_dist_of_color_eq :
    ∀ i j, i ≠ j → color i = color j → ∀ x ∈ piece i, ∀ y ∈ piece j, c ≤ dist x y

namespace ColoredCover

variable {X : Type*} [PseudoMetricSpace X] {ι : Type*} {K : ℕ} {ε c : ℝ}

/-- The set `E_r` of points of color `r`: the union of all pieces colored `r`. -/
def colorClass (cc : ColoredCover X ι K ε c) (r : Fin K) : Set X :=
  {x | ∃ i, cc.color i = r ∧ x ∈ cc.piece i}

/-- Membership in a color set, unfolded. -/
@[simp]
theorem mem_colorClass {cc : ColoredCover X ι K ε c} {r : Fin K} {x : X} :
    x ∈ cc.colorClass r ↔ ∃ i, cc.color i = r ∧ x ∈ cc.piece i := Iff.rfl

/-- Every point has a color. -/
theorem exists_mem_colorClass (cc : ColoredCover X ι K ε c) (x : X) :
    ∃ r, x ∈ cc.colorClass r := by
  obtain ⟨i, hi⟩ := cc.exists_mem_piece x
  exact ⟨cc.color i, i, rfl, hi⟩

/-- The color sets cover the space. -/
theorem iUnion_colorClass (cc : ColoredCover X ι K ε c) :
    (Set.univ : Set X) ⊆ ⋃ r, cc.colorClass r := by
  intro x _
  obtain ⟨r, hr⟩ := cc.exists_mem_colorClass x
  exact mem_iUnion.2 ⟨r, hr⟩

section Scale

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Scaling two vectors by `s⁻¹` with `s > 0` scales their distance by `s⁻¹`. -/
private theorem dist_inv_smul {s : ℝ} (hs : 0 < s) (u v : V) :
    dist (s⁻¹ • u) (s⁻¹ • v) = s⁻¹ * dist u v := by
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]

/-- Rescaling a colored cover by a factor `s > 0`: each piece `A` becomes `s • A`, so
both the diameter bound and the separation constant are multiplied by `s`.

Applying this to the unit-scale Lebesgue cover of `ℝᵐ` produces covers of arbitrarily
small diameter, which is what turns the recovery algorithm into one of arbitrary
accuracy. -/
noncomputable def scale (cc : ColoredCover V ι K ε c) {s : ℝ} (hs : 0 < s) :
    ColoredCover V ι K (s * ε) (s * c) where
  piece i := (fun x => s⁻¹ • x) ⁻¹' cc.piece i
  color := cc.color
  exists_mem_piece x := cc.exists_mem_piece (s⁻¹ • x)
  dist_le_of_mem i x hx y hy := by
    have h := cc.dist_le_of_mem i _ hx _ hy
    rwa [dist_inv_smul hs, inv_mul_le_iff₀ hs] at h
  le_dist_of_color_eq i j hij hcol x hx y hy := by
    have h := cc.le_dist_of_color_eq i j hij hcol _ hx _ hy
    rwa [dist_inv_smul hs, le_inv_mul_iff₀ hs] at h

/-- Membership in a rescaled piece, unfolded. -/
@[simp]
theorem mem_scale_piece {cc : ColoredCover V ι K ε c} {s : ℝ} (hs : 0 < s) {i : ι} {x : V} :
    x ∈ (cc.scale hs).piece i ↔ s⁻¹ • x ∈ cc.piece i := Iff.rfl

/-- Rescaling keeps the colors. -/
@[simp]
theorem scale_color {cc : ColoredCover V ι K ε c} {s : ℝ} (hs : 0 < s) :
    (cc.scale hs).color = cc.color := rfl

/-- Membership in a rescaled color set, unfolded.  Not a `simp` lemma: `simp` reaches
the same normal form through `mem_colorClass`, `scale_color` and `mem_scale_piece`. -/
theorem mem_scale_colorClass {cc : ColoredCover V ι K ε c} {s : ℝ} (hs : 0 < s)
    {r : Fin K} {x : V} :
    x ∈ (cc.scale hs).colorClass r ↔ s⁻¹ • x ∈ cc.colorClass r := Iff.rfl

end Scale

end ColoredCover

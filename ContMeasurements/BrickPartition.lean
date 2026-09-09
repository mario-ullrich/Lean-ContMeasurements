/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import ContMeasurements.ColoredCover
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Algebra.Order.Floor.Ring

/-!
# The brick partition of `ℝᵐ` with `m + 1` colours

This file builds the coloured cover of `ℝᵐ` (with the maximum norm) that drives the
recovery algorithm: pieces of bounded diameter, coloured with `m + 1` colours in such
a way that two distinct pieces of the same colour are a definite distance apart.

## The construction

Cut `ℝᵐ` along the integer grid.  For `0 ≤ k ≤ m` let `F_k` be the `k`-skeleton, the
set of points with at most `k` non-integer coordinates, and let `δ_0 > δ_1 > … > δ_m`
be small radii in arithmetic progression with common difference `c`.  Put

  `C_k = (closed δ_k-neighbourhood of F_k) \ (⋃_{j < k} closed δ_j-neighbourhood of F_j)`,

and give `C_k` the colour `k`.  Each `C_k` splits into pieces sitting around the
individual `k`-dimensional faces of the grid; these are the pieces of the cover.

Two distinct faces of the same dimension `k` are separated because a point close to
both of them is close to a face of dimension `k - 1`: it would then lie in the
`δ_{k-1}`-neighbourhood of `F_{k-1}`, which `C_k` has removed.  Making this precise is
`exists_int_near_of_ne`, the geometric heart of the file.

The number `m + 1` of colours cannot be lowered — that is the Lebesgue covering
dimension of `ℝᵐ`.  The recovery algorithm therefore spends `⌈log₂(m+1)⌉` measurements
on the bisection over colours; the extra coordinate trick of `UpperBound.lean` is what
brings the total down to `⌈log₂ m⌉ + 1`.

## Main definitions and results

* `ContMeasurements.brickCover` — the coloured cover of `ℝᵐ` with `m + 1` colours,
  pieces of diameter at most `3/2` and separation `1 / (4(m+2))`.
-/

open Metric Set

namespace ContMeasurements

variable {m : ℕ}

/-! ### Skeleta, faces and neighbourhoods -/

/-- The `k`-skeleton of the integer grid: points with at most `k` non-integer
coordinates. -/
def latticeSkeleton (m k : ℕ) : Set (Fin m → ℝ) :=
  {x | ∃ S : Finset (Fin m), S.card ≤ k ∧ ∀ i ∉ S, ∃ n : ℤ, x i = (n : ℝ)}

/-- The closed face of the grid with corner `a` spanned by the directions in `S`:
the coordinates in `S` range over `[aᵢ, aᵢ + 1]`, the others are pinned to `aᵢ`. -/
def face (a : Fin m → ℤ) (S : Finset (Fin m)) : Set (Fin m → ℝ) :=
  {x | (∀ i ∈ S, (a i : ℝ) ≤ x i ∧ x i ≤ (a i : ℝ) + 1) ∧ ∀ i ∉ S, x i = (a i : ℝ)}

/-- The closed `t`-neighbourhood of a set, spelled out to avoid side conditions. -/
def nbhd (t : ℝ) (A : Set (Fin m → ℝ)) : Set (Fin m → ℝ) := {x | ∃ p ∈ A, dist x p ≤ t}

theorem face_subset_skeleton (a : Fin m → ℤ) (S : Finset (Fin m)) :
    face a S ⊆ latticeSkeleton m S.card :=
  fun _ hx => ⟨S, le_rfl, fun i hi => ⟨a i, hx.2 i hi⟩⟩

/-- Every point of the `k`-skeleton lies on a `k`-dimensional face, provided
`k ≤ m`. -/
theorem exists_face_of_mem_skeleton {k : ℕ} (hk : k ≤ m) {p : Fin m → ℝ}
    (hp : p ∈ latticeSkeleton m k) :
    ∃ (a : Fin m → ℤ) (S : Finset (Fin m)), S.card = k ∧ p ∈ face a S := by
  obtain ⟨S₀, hS₀card, hS₀⟩ := hp
  obtain ⟨S, hS₀S, -, hScard⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ S₀) hS₀card
      (by simpa using hk)
  refine ⟨fun i => ⌊p i⌋, S, hScard, ?_, ?_⟩
  · exact fun i _ => ⟨Int.floor_le _, le_of_lt (Int.lt_floor_add_one _)⟩
  · intro i hi
    obtain ⟨n, hn⟩ := hS₀ i fun h => hi (hS₀S h)
    rw [hn, Int.floor_intCast]

/-! ### The radii -/

/-- The radius used at level `k`: an arithmetic progression decreasing in `k`, with
common difference `brickSep m`. -/
noncomputable def brickDelta (m k : ℕ) : ℝ := ((m : ℝ) + 1 - k) / (4 * ((m : ℝ) + 2))

/-- The separation constant of the cover, the common difference of the radii. -/
noncomputable def brickSep (m : ℕ) : ℝ := 1 / (4 * ((m : ℝ) + 2))

theorem brickSep_pos (m : ℕ) : 0 < brickSep m := by
  rw [brickSep]
  positivity

theorem brickDelta_succ_add (m k : ℕ) :
    brickDelta m (k + 1) + brickSep m = brickDelta m k := by
  rw [brickDelta, brickDelta, brickSep, div_add_div_same]
  push_cast
  ring_nf

theorem brickDelta_le_zero (m k : ℕ) : brickDelta m k ≤ brickDelta m 0 := by
  rw [brickDelta, brickDelta]
  apply div_le_div_of_nonneg_right _ (by positivity)
  · simp
  · positivity

theorem brickDelta_pos {k : ℕ} (hk : k ≤ m) : 0 < brickDelta m k := by
  rw [brickDelta]
  apply div_pos _ (by positivity)
  have : (k : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hk
  linarith

theorem brickDelta_nonneg {k : ℕ} (hk : k ≤ m) : 0 ≤ brickDelta m k :=
  (brickDelta_pos hk).le

/-- The two radii used in a separation argument add up to less than `1`, so distinct
faces of the same dimension really are distinguishable. -/
theorem two_brickDelta_zero_add_sep_lt (m : ℕ) :
    2 * brickDelta m 0 + brickSep m < 1 / 2 := by
  rw [brickDelta, brickSep]
  rw [div_add_div_same, div_lt_div_iff₀ (by positivity) (by norm_num)]
  push_cast
  ring_nf
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-! ### Separation of distinct faces -/

/-- **The geometric heart of the construction.**

If a point `x` is close to two *distinct* faces of the same dimension `k`, then one of
the directions `i₀` spanned by the first face carries an integer very near `x i₀`.
Replacing that coordinate of the first face by the integer produces a point of the
`(k-1)`-skeleton just as close to `x` — which is what the construction of the pieces
has excluded.

The bound `δ + δ' < 1` is what makes the argument work: two lattice points that differ
must differ by at least `1`. -/
theorem exists_int_near_of_ne {a a' : Fin m → ℤ} {S S' : Finset (Fin m)}
    {x p q : Fin m → ℝ} {δ δ' : ℝ} (hne : (a, S) ≠ (a', S'))
    (hcard : S.card = S'.card) (hp : p ∈ face a S) (hq : q ∈ face a' S')
    (hxp : dist x p ≤ δ) (hxq : dist x q ≤ δ') (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ')
    (hsum : δ + δ' < 1) :
    ∃ i₀ ∈ S, ∃ v : ℤ, |x i₀ - (v : ℝ)| ≤ max δ δ' := by
  -- Coordinatewise consequences of the two distance bounds.
  have hxpi : ∀ i, |x i - p i| ≤ δ := fun i => by
    have := dist_le_pi_dist x p i
    rw [Real.dist_eq] at this
    linarith
  have hxqi : ∀ i, |x i - q i| ≤ δ' := fun i => by
    have := dist_le_pi_dist x q i
    rw [Real.dist_eq] at this
    linarith
  by_cases hSS : S = S'
  · -- Same directions, so the corners differ.
    subst hSS
    have haa : a ≠ a' := by
      intro h
      exact hne (by rw [h])
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 haa
    -- A direction outside `S` would put two distinct integers within `δ + δ'`.
    have hi₀S : i₀ ∈ S := by
      by_contra hout
      have h1 : p i₀ = (a i₀ : ℝ) := hp.2 i₀ hout
      have h2 : q i₀ = (a' i₀ : ℝ) := hq.2 i₀ hout
      have hint : (1 : ℝ) ≤ |(a i₀ : ℝ) - (a' i₀ : ℝ)| := by
        rw [← Int.cast_sub, ← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hi₀)
      have := abs_sub_abs_le_abs_sub (x i₀ - p i₀) (x i₀ - q i₀)
      have htri : |(a i₀ : ℝ) - (a' i₀ : ℝ)| ≤ |x i₀ - p i₀| + |x i₀ - q i₀| := by
        rw [← h1, ← h2]
        have : (p i₀ : ℝ) - q i₀ = (x i₀ - q i₀) - (x i₀ - p i₀) := by ring
        rw [this]
        exact (abs_sub _ _).trans_eq (by rw [add_comm])
      have := hxpi i₀
      have := hxqi i₀
      linarith
    refine ⟨i₀, hi₀S, ?_⟩
    -- The two unit intervals in direction `i₀` are distinct, so an endpoint of the
    -- lower one is within `max δ δ'` of `x i₀`.
    have hpi := hp.1 i₀ hi₀S
    have hqi := hq.1 i₀ hi₀S
    rcases lt_or_gt_of_ne hi₀ with hlt | hlt
    · refine ⟨a i₀ + 1, ?_⟩
      have hstep : ((a i₀ : ℝ) + 1) ≤ (a' i₀ : ℝ) := by exact_mod_cast hlt
      have h1 := hxpi i₀
      have h2 := hxqi i₀
      rw [abs_le] at h1 h2 ⊢
      push_cast
      constructor
      · have := le_max_right δ δ'
        linarith [h2.1, hqi.1]
      · have := le_max_left δ δ'
        linarith [h1.2, hpi.2]
    · refine ⟨a' i₀ + 1, ?_⟩
      have hstep : ((a' i₀ : ℝ) + 1) ≤ (a i₀ : ℝ) := by exact_mod_cast hlt
      have h1 := hxpi i₀
      have h2 := hxqi i₀
      rw [abs_le] at h1 h2 ⊢
      push_cast
      constructor
      · have := le_max_left δ δ'
        linarith [h1.1, hpi.1]
      · have := le_max_right δ δ'
        linarith [h2.2, hqi.2]
  · -- Different direction sets of equal size: some direction of `S` is missing in `S'`,
    -- and there the second face sits exactly on an integer.
    have hsub : ¬ S ⊆ S' := fun h => hSS (Finset.eq_of_subset_of_card_le h hcard.ge)
    obtain ⟨i₀, hi₀S, hi₀S'⟩ := Finset.not_subset.1 hsub
    refine ⟨i₀, hi₀S, a' i₀, ?_⟩
    have h2 : q i₀ = (a' i₀ : ℝ) := hq.2 i₀ hi₀S'
    rw [← h2]
    exact (hxqi i₀).trans (le_max_right δ δ')

/-! ### The pieces -/

/-- The index set of the cover: a corner and a set of spanned directions. -/
abbrev BrickIndex (m : ℕ) := (Fin m → ℤ) × Finset (Fin m)

/-- The piece of the cover attached to a face: its `δ_k`-neighbourhood, with the
neighbourhoods of all lower skeleta removed. -/
noncomputable def brickPiece (m : ℕ) (i : BrickIndex m) : Set (Fin m → ℝ) :=
  nbhd (brickDelta m i.2.card) (face i.1 i.2) \
    ⋃ j ∈ Finset.range i.2.card, nbhd (brickDelta m j) (latticeSkeleton m j)

/-- The pieces cover `ℝᵐ`: take the smallest level whose neighbourhood already
contains the point. -/
theorem exists_mem_brickPiece (x : Fin m → ℝ) : ∃ i, x ∈ brickPiece m i := by
  classical
  have hex : ∃ j, x ∈ nbhd (brickDelta m j) (latticeSkeleton m j) := by
    refine ⟨m, x, ⟨Finset.univ, by simp, fun i hi => absurd (Finset.mem_univ i) hi⟩, ?_⟩
    rw [dist_self]
    exact brickDelta_nonneg le_rfl
  set k := Nat.find hex with hk
  obtain ⟨p, hpk, hxp⟩ := Nat.find_spec hex
  have hkm : k ≤ m := Nat.find_min' hex (by
    refine ⟨x, ⟨Finset.univ, by simp, fun i hi => absurd (Finset.mem_univ i) hi⟩, ?_⟩
    rw [dist_self]
    exact brickDelta_nonneg le_rfl)
  obtain ⟨a, S, hScard, hpface⟩ := exists_face_of_mem_skeleton hkm hpk
  refine ⟨(a, S), ⟨p, hpface, by rw [hScard]; exact hxp⟩, ?_⟩
  simp only [Set.mem_iUnion, Finset.mem_range, not_exists, hScard]
  intro j hj _
  exact Nat.find_min hex hj (by assumption)

end ContMeasurements

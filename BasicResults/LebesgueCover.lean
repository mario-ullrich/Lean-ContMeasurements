/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.ColoredCover
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Algebra.Order.Floor.Ring

/-!
# A colored cover of `ℝᵐ` with `m + 1` colors

This file builds the colored cover of `ℝᵐ` (with the maximum norm) that drives the
recovery algorithm: pieces of bounded diameter, colored with `m + 1` colors in such
a way that two distinct pieces of the same color are a definite distance apart.

## The construction

Cut `ℝᵐ` along the integer grid.  For `0 ≤ k ≤ m` let `F_k` be the `k`-skeleton, the
set of points with at most `k` non-integer coordinates, and let `δ_0 > δ_1 > … > δ_m`
be small radii in arithmetic progression with common difference `c`.  Put

  `C_k = (closed δ_k-neighbourhood of F_k) \ (⋃_{j < k} closed δ_j-neighbourhood of F_j)`,

and give `C_k` the color `k`.  Each `C_k` splits into pieces sitting around the
individual `k`-dimensional faces of the grid; these are the pieces of the cover.

Two distinct faces of the same dimension `k` are separated because a point close to
both of them is close to a face of dimension `k - 1`: it would then lie in the
`δ_{k-1}`-neighbourhood of `F_{k-1}`, which `C_k` has removed.  Making this precise is
`LebesgueCover.exists_int_abs_sub_le_of_ne`, the geometric heart of the file.

The number `m + 1` of colors cannot be lowered — that is the Lebesgue covering
dimension of `ℝᵐ`.  The recovery algorithm therefore spends `⌈log₂(m+1)⌉` measurements
on the bisection over colors; the extra coordinate trick of `UpperBound.lean` is what
brings the total down to `⌈log₂ m⌉ + 1`.

## Main definitions and results

* `ColoredCover.lebesgue` — the colored cover of `ℝᵐ` with `m + 1` colors, pieces of
  diameter at most `3/2` and separation `1 / (4(m+2))`.  Its ingredients live in the
  namespace `LebesgueCover`.
-/

open Metric Set

namespace LebesgueCover

variable {m : ℕ}

/-! ### Skeleta, faces and neighbourhoods -/

/-- The `k`-skeleton of the integer grid: points with at most `k` non-integer
coordinates. -/
def skeleton (m k : ℕ) : Set (Fin m → ℝ) :=
  {x | ∃ S : Finset (Fin m), S.card ≤ k ∧ ∀ i ∉ S, ∃ n : ℤ, x i = (n : ℝ)}

/-- The closed face of the grid with corner `a` spanned by the directions in `S`:
the coordinates in `S` range over `[aᵢ, aᵢ + 1]`, the others are pinned to `aᵢ`. -/
def face (a : Fin m → ℤ) (S : Finset (Fin m)) : Set (Fin m → ℝ) :=
  {x | (∀ i ∈ S, (a i : ℝ) ≤ x i ∧ x i ≤ (a i : ℝ) + 1) ∧
    ∀ i ∉ S, x i = (a i : ℝ)}

/-- The closed `t`-neighbourhood of a set, spelled out to avoid side conditions. -/
def closedNbhd (t : ℝ) (A : Set (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  {x | ∃ p ∈ A, dist x p ≤ t}

/-- A face spanned by `k` directions lies in the `k`-skeleton. -/
theorem face_subset_skeleton (a : Fin m → ℤ) (S : Finset (Fin m)) :
    face a S ⊆ skeleton m S.card :=
  fun _ hx => ⟨S, le_rfl, fun i hi => ⟨a i, hx.2 i hi⟩⟩

/-- Every point of the `k`-skeleton lies on a `k`-dimensional face, provided
`k ≤ m`. -/
theorem exists_face_of_mem_skeleton {k : ℕ} (hk : k ≤ m) {p : Fin m → ℝ}
    (hp : p ∈ skeleton m k) :
    ∃ (a : Fin m → ℤ) (S : Finset (Fin m)), S.card = k ∧ p ∈ face a S := by
  obtain ⟨S₀, hS₀card, hS₀⟩ := hp
  obtain ⟨S, hS₀S, -, hScard⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ S₀) hS₀card
      (by simpa using hk)
  refine ⟨fun i => ⌊p i⌋, S, hScard, ?_, ?_⟩
  · exact fun i _ => ⟨Int.floor_le _, le_of_lt (Int.lt_floor_add_one _)⟩
  · intro i hi
    obtain ⟨n, hn⟩ := hS₀ i fun h => hi (hS₀S h)
    show p i = ((⌊p i⌋ : ℤ) : ℝ)
    rw [hn, Int.floor_intCast]

/-! ### The radii -/

/-- The separation constant of the cover, and the common difference of the radii. -/
noncomputable def sep (m : ℕ) : ℝ := 1 / (4 * ((m : ℝ) + 2))

/-- The radius used at level `k`: an arithmetic progression decreasing in `k`, with
common difference `sep m`. -/
noncomputable def radius (m k : ℕ) : ℝ := ((m : ℝ) + 1 - k) * sep m

/-- The separation constant is positive. -/
theorem sep_pos (m : ℕ) : 0 < sep m := by
  rw [sep]
  positivity

/-- The separation constant is at most `1`. -/
theorem sep_le_one (m : ℕ) : sep m ≤ 1 := by
  rw [sep, div_le_one (by positivity)]
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- Consecutive radii differ by the separation constant. -/
theorem radius_succ_add_sep (m k : ℕ) :
    radius m (k + 1) + sep m = radius m k := by
  rw [radius, radius]
  push_cast
  ring

/-- The radii decrease with the level. -/
theorem radius_le_radius_zero (m k : ℕ) : radius m k ≤ radius m 0 := by
  rw [radius, radius]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hs := (sep_pos m).le
  push_cast
  nlinarith [mul_nonneg hk hs]

/-- The radii are positive up to level `m`. -/
theorem radius_pos {k : ℕ} (hk : k ≤ m) : 0 < radius m k := by
  rw [radius]
  have hkm : (k : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hk
  exact mul_pos (by linarith) (sep_pos m)

/-- The radii are nonnegative up to level `m`. -/
theorem radius_nonneg {k : ℕ} (hk : k ≤ m) : 0 ≤ radius m k :=
  (radius_pos hk).le

/-- The two radii used in a separation argument add up to less than `1`, so distinct
faces of the same dimension really are distinguishable. -/
theorem two_mul_radius_zero_add_sep_lt (m : ℕ) :
    2 * radius m 0 + sep m < 1 / 2 := by
  have hpos : (0 : ℝ) < 4 * ((m : ℝ) + 2) := by positivity
  have hkey : 2 * radius m 0 + sep m
      = (2 * (m : ℝ) + 3) * (1 / (4 * ((m : ℝ) + 2))) := by
    rw [radius, sep]
    push_cast
    ring
  rw [hkey, mul_one_div, div_lt_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-! ### Separation of distinct faces -/

/-- **The geometric heart of the construction.**

If a point `x` is close to two *distinct* faces of the same dimension `k`, then one of
the directions `i₀` spanned by the first face carries an integer very near `x i₀`.
Replacing that coordinate of the first face by the integer produces a point of the
`(k-1)`-skeleton just as close to `x` — which is what the construction of the pieces
has excluded.

The bound `δ + δ' < 1` is what makes the argument work: two lattice points that differ
must differ by at least `1`. -/
theorem exists_int_abs_sub_le_of_ne {a a' : Fin m → ℤ} {S S' : Finset (Fin m)}
    {x p q : Fin m → ℝ} {δ δ' : ℝ} (hne : (a, S) ≠ (a', S'))
    (hcard : S.card = S'.card) (hp : p ∈ face a S) (hq : q ∈ face a' S')
    (hxp : dist x p ≤ δ) (hxq : dist x q ≤ δ') (hsum : δ + δ' < 1) :
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
abbrev Index (m : ℕ) := (Fin m → ℤ) × Finset (Fin m)

/-- The piece of the cover attached to a face: its `δ_k`-neighbourhood, with the
neighbourhoods of all lower skeleta removed. -/
noncomputable def piece (m : ℕ) (i : Index m) : Set (Fin m → ℝ) :=
  closedNbhd (radius m i.2.card) (face i.1 i.2) \
    ⋃ j ∈ Finset.range i.2.card, closedNbhd (radius m j) (skeleton m j)

/-- The pieces cover `ℝᵐ`: take the smallest level whose neighbourhood already
contains the point. -/
theorem exists_mem_piece (x : Fin m → ℝ) : ∃ i, x ∈ piece m i := by
  classical
  have huniv : x ∈ closedNbhd (radius m m) (skeleton m m) := by
    refine ⟨x, ⟨Finset.univ, by simp, fun i hi => absurd (Finset.mem_univ i) hi⟩, ?_⟩
    rw [dist_self]
    exact radius_nonneg le_rfl
  have hex : ∃ j, x ∈ closedNbhd (radius m j) (skeleton m j) := ⟨m, huniv⟩
  obtain ⟨p, hpk, hxp⟩ := Nat.find_spec hex
  have hkm : Nat.find hex ≤ m := Nat.find_min' hex huniv
  obtain ⟨a, S, hScard, hpface⟩ := exists_face_of_mem_skeleton hkm hpk
  refine ⟨(a, S), ⟨p, hpface, by rw [hScard]; exact hxp⟩, ?_⟩
  intro hmem
  obtain ⟨jj, hjj, hx'⟩ := Set.mem_iUnion₂.1 hmem
  rw [hScard, Finset.mem_range] at hjj
  exact Nat.find_min hex hjj hx'

/-! ### The colored cover -/

/-- Two points of one face differ by at most `1` in every coordinate. -/
theorem dist_le_one_of_mem_face {a : Fin m → ℤ} {S : Finset (Fin m)} {p q : Fin m → ℝ}
    (hp : p ∈ face a S) (hq : q ∈ face a S) : dist p q ≤ 1 := by
  rw [dist_pi_le_iff zero_le_one]
  intro i
  rw [Real.dist_eq, abs_le]
  by_cases hi : i ∈ S
  · obtain ⟨hp1, hp2⟩ := hp.1 i hi
    obtain ⟨hq1, hq2⟩ := hq.1 i hi
    constructor <;> linarith
  · rw [hp.2 i hi, hq.2 i hi]
    constructor <;> linarith

/-- Each piece has diameter at most `3/2`: it sits within `δ_k` of a face, and a face
has diameter `1`. -/
theorem dist_le_of_mem_piece (i : Index m) {x y : Fin m → ℝ}
    (hx : x ∈ piece m i) (hy : y ∈ piece m i) : dist x y ≤ 3 / 2 := by
  obtain ⟨p, hp, hxp⟩ := hx.1
  obtain ⟨q, hq, hyq⟩ := hy.1
  have hpq : dist p q ≤ 1 := dist_le_one_of_mem_face hp hq
  have hd : radius m i.2.card ≤ radius m 0 := radius_le_radius_zero m _
  have hsum := two_mul_radius_zero_add_sep_lt m
  have hsp := sep_pos m
  have h1 := dist_triangle x p y
  have h2 := dist_triangle p q y
  rw [dist_comm q y] at h2
  linarith

/-- **Distinct pieces of the same color are `sep m` apart.**

If they were closer, the point `x` would be within `δ_{k-1}` of the two faces at once,
and replacing one coordinate of the first face by the nearby integer would produce a
point of the `(k-1)`-skeleton just as close — but the piece of `x` was built by
*removing* the `δ_{k-1}`-neighbourhood of that skeleton. -/
theorem sep_le_dist_of_ne (i j : Index m) (hij : i ≠ j)
    (hcard : i.2.card = j.2.card) {x y : Fin m → ℝ}
    (hx : x ∈ piece m i) (hy : y ∈ piece m j) :
    sep m ≤ dist x y := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨p, hp, hxp⟩ := hx.1
  obtain ⟨q, hq, hyq⟩ := hy.1
  have hkm : i.2.card ≤ m := by simpa using Finset.card_le_univ i.2
  have hd0 : 0 ≤ radius m i.2.card := radius_nonneg hkm
  have hsp := sep_pos m
  have hle0 : radius m i.2.card ≤ radius m 0 := radius_le_radius_zero m _
  have hsum := two_mul_radius_zero_add_sep_lt m
  -- `x` is close to the second face as well.
  have hxq : dist x q ≤ radius m i.2.card + sep m := by
    have h1 := dist_triangle x y q
    have h2 : dist y q ≤ radius m i.2.card := by rw [hcard]; exact hyq
    linarith
  obtain ⟨i₀, hi₀, v, hv⟩ :=
    exists_int_abs_sub_le_of_ne hij hcard hp hq hxp hxq (by linarith)
  rw [max_eq_right (by linarith)] at hv
  -- The face has a direction, so its dimension is positive.
  have hkpos : 0 < i.2.card := Finset.card_pos.2 ⟨i₀, hi₀⟩
  obtain ⟨k', hk'⟩ : ∃ k', i.2.card = k' + 1 := ⟨i.2.card - 1, by omega⟩
  have hk'm : k' ≤ m := by omega
  -- Replacing the coordinate `i₀` of `p` by the integer `v` drops the dimension.
  have hz : Function.update p i₀ (v : ℝ) ∈ skeleton m k' := by
    refine ⟨i.2.erase i₀, ?_, ?_⟩
    · rw [Finset.card_erase_of_mem hi₀]; omega
    · intro l hl
      by_cases hli : l = i₀
      · exact ⟨v, by rw [hli, Function.update_self]⟩
      · have hlS : l ∉ i.2 := fun h => hl (Finset.mem_erase.2 ⟨hli, h⟩)
        exact ⟨i.1 l, by rw [Function.update_of_ne hli, hp.2 l hlS]⟩
  have hdist : dist x (Function.update p i₀ (v : ℝ)) ≤ radius m k' := by
    rw [dist_pi_le_iff (radius_nonneg hk'm)]
    intro l
    rw [Real.dist_eq]
    by_cases hli : l = i₀
    · subst hli
      rw [Function.update_self]
      calc |x l - (v : ℝ)| ≤ radius m i.2.card + sep m := hv
        _ = radius m k' := by rw [hk', radius_succ_add_sep]
    · rw [Function.update_of_ne hli]
      have h1 : |x l - p l| ≤ radius m i.2.card := by
        have hle := dist_le_pi_dist x p l
        rw [Real.dist_eq] at hle
        linarith
      have h2 : radius m i.2.card ≤ radius m k' := by
        rw [hk', ← radius_succ_add_sep m k']
        linarith
      linarith
  exact hx.2 (Set.mem_iUnion₂.2 ⟨k', Finset.mem_range.2 (by omega), _, hz, hdist⟩)

end LebesgueCover

namespace ColoredCover

/-- **The Lebesgue cover of `ℝᵐ`.**

`ℝᵐ` with the maximum norm is covered by pieces of diameter at most `3/2`, colored
with `m + 1` colors, such that two distinct pieces of the same color are at distance
at least `1 / (4(m+2))`.

Rescaling (`ColoredCover.scale`) turns this into covers of arbitrarily small diameter,
which is what the recovery algorithm consumes. -/
noncomputable def lebesgue (m : ℕ) :
    ColoredCover (Fin m → ℝ) (LebesgueCover.Index m) (m + 1) (3 / 2)
      (LebesgueCover.sep m) where
  piece := LebesgueCover.piece m
  color i := ⟨i.2.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ i.2)⟩
  exists_mem_piece := LebesgueCover.exists_mem_piece
  dist_le_of_mem i x hx y hy := LebesgueCover.dist_le_of_mem_piece i hx hy
  le_dist_of_color_eq i j hij hcol x hx y hy := by
    refine LebesgueCover.sep_le_dist_of_ne i j hij ?_ hx hy
    simpa using congrArg Fin.val hcol

end ColoredCover

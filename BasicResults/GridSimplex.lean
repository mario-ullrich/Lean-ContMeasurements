/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Order.Preorder.Chain
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Simplices of the Kuhn triangulation of an integer grid

The cube `[-N, N]ⁿ` carries a standard triangulation, due to Kuhn and Freudenthal, whose
vertices are the integer points and whose simplices are described purely by the order
relation: a set of integer points spans a simplex exactly when it is a **chain** for the
coordinatewise order and any two of its points differ by at most one in every coordinate.
This file sets up that description and the elementary facts a combinatorial argument on
the triangulation needs.

Two quantities are attached to a simplex `s`.  A label `(i, true)` is a **sign** of `s`
when some vertex has positive `i`-th coordinate, and `(i, false)` when some vertex has
negative `i`-th coordinate; the **directions** of `s` are the coordinates occurring in its
signs.  Since all vertices of a simplex differ by at most one in each coordinate, a
simplex never carries both signs in the same coordinate, so it has as many signs as
directions.

## Main results

* `IsSimplex.not_mem_signs_negLabel` — a simplex lies in one closed orthant: its signs
  contain no pair of opposite labels.
* `IsSimplex.card_le_card_directions_succ` — a simplex has at most one more vertex than it
  has directions.  This is what makes the counting argument finite.
* `IsSimplex.neg`, `mem_signs_neg` — reflection in the origin maps simplices to simplices
  and reverses every sign.
-/

open Finset
open scoped Pointwise

namespace GridSimplex

variable {n N : ℕ} {s : Finset (Fin n → ℤ)}

/-! ### The grid -/

/-- The integer points of the cube `[-N, N]ⁿ`. -/
def grid (n N : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

/-- Membership in the grid, coordinatewise. -/
@[simp]
theorem mem_grid {v : Fin n → ℤ} :
    v ∈ grid n N ↔ ∀ i, -(N : ℤ) ≤ v i ∧ v i ≤ (N : ℤ) := by
  simp only [grid, Fintype.mem_piFinset, Finset.mem_Icc]

/-- The grid is symmetric under reflection in the origin. -/
theorem neg_mem_grid {v : Fin n → ℤ} (hv : v ∈ grid n N) : -v ∈ grid n N := by
  rw [mem_grid] at hv ⊢
  intro i
  have := hv i
  simp only [Pi.neg_apply]
  omega

/-- The origin belongs to the grid. -/
theorem zero_mem_grid : (0 : Fin n → ℤ) ∈ grid n N := by simp

/-- A grid point lies on the boundary of the cube when one of its coordinates is
extremal. -/
def IsBoundary (N : ℕ) (v : Fin n → ℤ) : Prop := ∃ i, v i = (N : ℤ) ∨ v i = -(N : ℤ)

/-- Reflection preserves the boundary. -/
theorem isBoundary_neg {v : Fin n → ℤ} (hv : IsBoundary N v) : IsBoundary N (-v) := by
  obtain ⟨i, hi⟩ := hv
  refine ⟨i, ?_⟩
  simp only [Pi.neg_apply]
  omega

/-! ### Labels -/

/-- A coordinate together with a sign: `true` stands for `+`, `false` for `−`. -/
abbrev Label (n : ℕ) := Fin n × Bool

/-- The opposite label. -/
def negLabel (p : Label n) : Label n := (p.1, !p.2)

/-- Reversing a label twice does nothing. -/
@[simp]
theorem negLabel_negLabel (p : Label n) : negLabel (negLabel p) = p := by
  simp [negLabel]

/-- Reversing a label keeps its coordinate. -/
@[simp]
theorem negLabel_fst (p : Label n) : (negLabel p).1 = p.1 := rfl

/-- `negLabel` has no fixed point. -/
theorem negLabel_ne (p : Label n) : negLabel p ≠ p := by
  simp [negLabel, Prod.ext_iff]

/-- Membership in a set of labels closed under nothing: reflecting the label instead of the
set. -/
theorem mem_image_negLabel {t : Finset (Label n)} {p : Label n} :
    p ∈ t.image negLabel ↔ negLabel p ∈ t := by
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h
    rwa [negLabel_negLabel]
  · intro h
    exact Finset.mem_image.2 ⟨negLabel p, h, negLabel_negLabel p⟩

/-! ### Simplices -/

/-- A simplex of the Kuhn triangulation of the grid: a nonempty set of grid points that is
a chain for the coordinatewise order and whose points differ by at most one in every
coordinate.

These are exactly the faces of the triangulation; a top-dimensional one is a chain
`v < v + e_{i₁} < v + e_{i₁} + e_{i₂} < …`. -/
structure IsSimplex (N : ℕ) (s : Finset (Fin n → ℤ)) : Prop where
  /-- A simplex has a vertex. -/
  nonempty : s.Nonempty
  /-- Its vertices are grid points. -/
  subset_grid : s ⊆ grid n N
  /-- Its vertices are comparable. -/
  chain : IsChain (· ≤ ·) (s : Set (Fin n → ℤ))
  /-- Its vertices differ by at most one in every coordinate. -/
  sub_le_one : ∀ x ∈ s, ∀ y ∈ s, ∀ i, y i - x i ≤ 1

/-- A simplex lies in one closed orthant: no coordinate is positive at one vertex and
negative at another. -/
theorem IsSimplex.not_lt_zero_of_pos (hs : IsSimplex N s) {x y : Fin n → ℤ} (hx : x ∈ s)
    (hy : y ∈ s) {i : Fin n} (hxi : 0 < x i) : ¬ y i < 0 := by
  intro hyi
  have h := hs.sub_le_one y hy x hx i
  omega

/-- A nonempty subset of a simplex is a simplex. -/
theorem IsSimplex.subset {t : Finset (Fin n → ℤ)} (hs : IsSimplex N s) (hts : t ⊆ s)
    (ht : t.Nonempty) : IsSimplex N t where
  nonempty := ht
  subset_grid := hts.trans hs.subset_grid
  chain := hs.chain.mono (by exact_mod_cast hts)
  sub_le_one x hx y hy i := hs.sub_le_one x (hts hx) y (hts hy) i

/-! ### Signs and directions -/

/-- The signs of `s`: the label `(i, true)` occurs when some vertex has positive `i`-th
coordinate, and `(i, false)` when some vertex has negative `i`-th coordinate. -/
def signs (s : Finset (Fin n → ℤ)) : Finset (Label n) :=
  Finset.univ.filter fun p => ∃ x ∈ s, if p.2 then 0 < x p.1 else x p.1 < 0

/-- The positive sign in a coordinate occurs when some vertex is positive there. -/
@[simp]
theorem mem_signs_true {i : Fin n} : (i, true) ∈ signs s ↔ ∃ x ∈ s, 0 < x i := by
  simp [signs]

/-- The negative sign in a coordinate occurs when some vertex is negative there. -/
@[simp]
theorem mem_signs_false {i : Fin n} : (i, false) ∈ signs s ↔ ∃ x ∈ s, x i < 0 := by
  simp [signs]

/-- The directions of `s`: the coordinates occurring in its signs. -/
def directions (s : Finset (Fin n → ℤ)) : Finset (Fin n) := (signs s).image Prod.fst

/-- A coordinate is a direction exactly when some vertex is nonzero there. -/
@[simp]
theorem mem_directions {i : Fin n} : i ∈ directions s ↔ ∃ x ∈ s, x i ≠ 0 := by
  constructor
  · intro hi
    obtain ⟨p, hp, hpi⟩ := Finset.mem_image.1 hi
    obtain ⟨j, b⟩ := p
    simp only at hpi
    subst hpi
    cases b
    · obtain ⟨x, hx, hxj⟩ := mem_signs_false.1 hp
      exact ⟨x, hx, by omega⟩
    · obtain ⟨x, hx, hxj⟩ := mem_signs_true.1 hp
      exact ⟨x, hx, by omega⟩
  · rintro ⟨x, hx, hxi⟩
    rcases lt_or_gt_of_ne hxi with h | h
    · exact Finset.mem_image.2 ⟨(i, false), mem_signs_false.2 ⟨x, hx, h⟩, rfl⟩
    · exact Finset.mem_image.2 ⟨(i, true), mem_signs_true.2 ⟨x, hx, h⟩, rfl⟩

/-- Signs of a subset are signs. -/
theorem signs_subset {t : Finset (Fin n → ℤ)} (hts : t ⊆ s) : signs t ⊆ signs s := by
  rintro ⟨i, b⟩ hp
  cases b
  · obtain ⟨x, hx, hxi⟩ := mem_signs_false.1 hp
    exact mem_signs_false.2 ⟨x, hts hx, hxi⟩
  · obtain ⟨x, hx, hxi⟩ := mem_signs_true.1 hp
    exact mem_signs_true.2 ⟨x, hts hx, hxi⟩

/-- Directions of a subset are directions. -/
theorem directions_subset {t : Finset (Fin n → ℤ)} (hts : t ⊆ s) :
    directions t ⊆ directions s :=
  Finset.image_subset_image (signs_subset hts)

/-- A simplex lies in one closed orthant: its signs contain no pair of opposite labels. -/
theorem IsSimplex.not_mem_signs_negLabel (hs : IsSimplex N s) {p : Label n}
    (hp : p ∈ signs s) : negLabel p ∉ signs s := by
  obtain ⟨i, b⟩ := p
  cases b
  · intro hq
    obtain ⟨x, hx, hxi⟩ := mem_signs_false.1 hp
    obtain ⟨y, hy, hyi⟩ := mem_signs_true.1 hq
    exact hs.not_lt_zero_of_pos hy hx hyi hxi
  · intro hq
    obtain ⟨x, hx, hxi⟩ := mem_signs_true.1 hp
    obtain ⟨y, hy, hyi⟩ := mem_signs_false.1 hq
    exact hs.not_lt_zero_of_pos hx hy hxi hyi

/-- On the signs of a simplex the coordinate determines the label, so a simplex has as many
signs as directions. -/
theorem IsSimplex.card_signs (hs : IsSimplex N s) :
    (signs s).card = (directions s).card := by
  refine (Finset.card_image_of_injOn ?_).symm
  rintro ⟨i, b⟩ hp ⟨j, c⟩ hq hij
  simp only at hij
  subst hij
  cases b <;> cases c
  · rfl
  · exact absurd hq (hs.not_mem_signs_negLabel hp)
  · exact absurd hq (hs.not_mem_signs_negLabel hp)
  · rfl

/-! ### The least vertex -/

/-- A nonempty finite chain of integer vectors has a least element: the one of smallest
coordinate sum. -/
theorem exists_isLeast_of_isChain {t : Finset (Fin n → ℤ)} (ht : t.Nonempty)
    (hc : IsChain (· ≤ ·) (t : Set (Fin n → ℤ))) : ∃ a ∈ t, ∀ x ∈ t, a ≤ x := by
  obtain ⟨a, ha, hmin⟩ := t.exists_min_image (fun x => ∑ i, x i) ht
  refine ⟨a, ha, fun x hx => ?_⟩
  rcases eq_or_ne a x with rfl | hne
  · exact le_rfl
  · rcases hc ha hx hne with h | h
    · exact h
    · exfalso
      obtain ⟨j, hj⟩ := Function.ne_iff.1 (Ne.symm hne)
      have hlt : ∑ i, x i < ∑ i, a i :=
        Finset.sum_lt_sum (fun i _ => h i) ⟨j, Finset.mem_univ j, lt_of_le_of_ne (h j) hj⟩
      exact absurd (hmin x hx) (not_le.2 hlt)

/-- A simplex has a least vertex. -/
theorem IsSimplex.exists_bot (hs : IsSimplex N s) : ∃ a ∈ s, ∀ x ∈ s, a ≤ x :=
  exists_isLeast_of_isChain hs.nonempty hs.chain

/-- Measured from the least vertex, every coordinate of every vertex is either the base
value or one more. -/
theorem IsSimplex.eq_or_eq_add_one (hs : IsSimplex N s) {a x : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ y ∈ s, a ≤ y) (hx : x ∈ s) (i : Fin n) : x i = a i ∨ x i = a i + 1 := by
  have h1 : a i ≤ x i := hbot x hx i
  have h2 : x i - a i ≤ 1 := hs.sub_le_one a ha x hx i
  omega

/-- The coordinates in which `x` exceeds the base point `a`. -/
def step (a x : Fin n → ℤ) : Finset (Fin n) := Finset.univ.filter fun i => a i < x i

/-- Membership in the step set, unfolded. -/
@[simp]
theorem mem_step {a x : Fin n → ℤ} {i : Fin n} : i ∈ step a x ↔ a i < x i := by
  simp [step]

/-- Along the chain the step set can only grow. -/
theorem step_subset_step {a x y : Fin n → ℤ} (hxy : x ≤ y) : step a x ⊆ step a y := by
  intro i hi
  rw [mem_step] at hi ⊢
  exact lt_of_lt_of_le hi (hxy i)

/-- Strictly along the chain the step set grows strictly: a coordinate where `x` and `y`
differ is at its base value in `x`. -/
theorem IsSimplex.step_ssubset (hs : IsSimplex N s) {a x y : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≤ y) (hne : x ≠ y) :
    step a x ⊂ step a y := by
  refine ⟨step_subset_step hxy, fun hsub => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := Function.ne_iff.1 hne
  have hlt : x j < y j := lt_of_le_of_ne (hxy j) hj
  have hax : a j ≤ x j := hbot x hx j
  have hxj : x j = a j := by
    rcases hs.eq_or_eq_add_one ha hbot hy j with h | h <;> omega
  have h1 : j ∉ step a x := by simp [hxj]
  have h2 : j ∈ step a y := by rw [mem_step, ← hxj]; exact hlt
  exact h1 (hsub h2)

/-- Every step set consists of directions: a coordinate that grows along the simplex is
nonzero at one of its ends. -/
theorem step_subset_directions {a x : Fin n → ℤ} (ha : a ∈ s) (hx : x ∈ s) :
    step a x ⊆ directions s := by
  intro i hi
  rw [mem_step] at hi
  rw [mem_directions]
  rcases lt_trichotomy (a i) 0 with h | h | h
  · exact ⟨a, ha, by omega⟩
  · exact ⟨x, hx, by omega⟩
  · exact ⟨a, ha, by omega⟩

/-- Every vertex is the least vertex raised by one in the coordinates of its step set. -/
theorem IsSimplex.eq_add_ite (hs : IsSimplex N s) {a x : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ y ∈ s, a ≤ y) (hx : x ∈ s) (j : Fin n) :
    x j = a j + (if j ∈ step a x then 1 else 0) := by
  rcases hs.eq_or_eq_add_one ha hbot hx j with h | h
  · rw [if_neg (by simp [h]), h, add_zero]
  · rw [if_pos (by simp [h]), h]

/-! ### Ranks -/

/-- The rank of a vertex relative to a base point: the number of coordinates in which it is
larger.  Measured from the least vertex of a simplex, the rank increases strictly along
that simplex, so it numbers the vertices. -/
def rank (a x : Fin n → ℤ) : ℕ := (step a x).card

/-- The rank increases strictly along a simplex. -/
theorem IsSimplex.rank_lt_rank (hs : IsSimplex N s) {a x y : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) :
    rank a x < rank a y :=
  Finset.card_lt_card (hs.step_ssubset ha hbot hx hy hxy.le hxy.ne)

/-- The rank is injective on a simplex. -/
theorem IsSimplex.injOn_rank (hs : IsSimplex N s) {a : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) : Set.InjOn (rank a) s := by
  intro x hx y hy hxy
  by_contra hne
  rcases hs.chain hx hy hne with h | h
  · exact absurd hxy (hs.rank_lt_rank ha hbot hx hy (lt_of_le_of_ne h hne)).ne
  · exact absurd hxy.symm
      (hs.rank_lt_rank ha hbot hy hx (lt_of_le_of_ne h (Ne.symm hne))).ne

/-- The rank reflects the order: a vertex of smaller rank is smaller. -/
theorem IsSimplex.lt_of_rank_lt (hs : IsSimplex N s) {a x y : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hx : x ∈ s) (hy : y ∈ s) (h : rank a x < rank a y) :
    x < y := by
  rcases eq_or_ne x y with rfl | hne
  · exact absurd h (lt_irrefl _)
  rcases hs.chain hx hy hne with hle | hle
  · exact lt_of_le_of_ne hle hne
  · exact absurd (hs.rank_lt_rank ha hbot hy hx (lt_of_le_of_ne hle (Ne.symm hne)))
      (by omega)

/-- **A simplex has at most one more vertex than it has directions.**

The rank is injective on the simplex and takes values between `0` and the number of
directions. -/
theorem IsSimplex.card_le_card_directions_succ (hs : IsSimplex N s) :
    s.card ≤ (directions s).card + 1 := by
  obtain ⟨a, ha, hbot⟩ := hs.exists_bot
  have himg : s.image (rank a) ⊆ Finset.range ((directions s).card + 1) := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.mem_range.2
      (Nat.lt_succ_of_le (Finset.card_le_card (step_subset_directions ha hx)))
  calc s.card = (s.image (rank a)).card :=
        (Finset.card_image_of_injOn (hs.injOn_rank ha hbot)).symm
    _ ≤ (Finset.range ((directions s).card + 1)).card := Finset.card_le_card himg
    _ = (directions s).card + 1 := Finset.card_range _

/-! ### Simplices of maximal length

A simplex with one more vertex than it has directions is as long as it can be.  Its ranks
then run through every value from `0` upwards, so consecutive vertices differ by a single
unit step.  This is what pins down the ways of extending such a simplex by one vertex. -/

/-- A simplex of maximal length realises every rank up to its number of directions. -/
theorem IsSimplex.image_rank (hs : IsSimplex N s) {a : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hcard : s.card = (directions s).card + 1) :
    s.image (rank a) = Finset.range ((directions s).card + 1) := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.mem_range.2
      (Nat.lt_succ_of_le (Finset.card_le_card (step_subset_directions ha hx)))
  · rw [Finset.card_range, Finset.card_image_of_injOn (hs.injOn_rank ha hbot), hcard]

/-- Hence every rank below the number of directions occurs at a vertex. -/
theorem IsSimplex.exists_rank_eq (hs : IsSimplex N s) {a : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hcard : s.card = (directions s).card + 1)
    {r : ℕ} (hr : r ≤ (directions s).card) : ∃ z ∈ s, rank a z = r := by
  have hmem : r ∈ s.image (rank a) := by
    rw [hs.image_rank ha hbot hcard]
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hr)
  obtain ⟨z, hz, hzr⟩ := Finset.mem_image.1 hmem
  exact ⟨z, hz, hzr⟩

/-- In a simplex of maximal length, consecutive vertices have consecutive ranks. -/
theorem IsSimplex.rank_eq_succ (hs : IsSimplex N s) {a x y : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hcard : s.card = (directions s).card + 1) (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x < y) (hcons : ∀ z ∈ s, ¬(x < z ∧ z < y)) :
    rank a y = rank a x + 1 := by
  have hlt : rank a x < rank a y := hs.rank_lt_rank ha hbot hx hy hxy
  by_contra hne
  have hle : rank a x + 1 ≤ (directions s).card := by
    have hy' : rank a y ≤ (directions s).card :=
      Finset.card_le_card (step_subset_directions ha hy)
    omega
  obtain ⟨z, hz, hzr⟩ := hs.exists_rank_eq ha hbot hcard hle
  exact hcons z hz ⟨hs.lt_of_rank_lt ha hbot hx hz (by omega),
    hs.lt_of_rank_lt ha hbot hz hy (by omega)⟩

/-- In a simplex of maximal length, the step set of the successor of a vertex adds exactly
one coordinate. -/
theorem IsSimplex.exists_step_eq_insert (hs : IsSimplex N s) {a x y : Fin n → ℤ}
    (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z) (hcard : s.card = (directions s).card + 1)
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) (hcons : ∀ z ∈ s, ¬(x < z ∧ z < y)) :
    ∃ i ∉ step a x, step a y = insert i (step a x) := by
  have hsub : step a x ⊆ step a y := step_subset_step hxy.le
  have hcards : (step a x).card + 1 = (step a y).card :=
    (hs.rank_eq_succ ha hbot hcard hx hy hxy hcons).symm
  obtain ⟨i, hi, hins⟩ := Finset.exists_eq_insert_iff.2 ⟨hsub, hcards⟩
  exact ⟨i, hi, hins.symm⟩

/-- **Consecutive vertices of a simplex of maximal length differ by one unit step.** -/
theorem IsSimplex.exists_eq_add_single (hs : IsSimplex N s) {a x y : Fin n → ℤ}
    (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z) (hcard : s.card = (directions s).card + 1)
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) (hcons : ∀ z ∈ s, ¬(x < z ∧ z < y)) :
    ∃ i, x i + 1 = y i ∧ ∀ j, j ≠ i → x j = y j := by
  obtain ⟨i, hi, hstep⟩ := hs.exists_step_eq_insert ha hbot hcard hx hy hxy hcons
  refine ⟨i, ?_, ?_⟩
  · rw [hs.eq_add_ite ha hbot hx i, hs.eq_add_ite ha hbot hy i, hstep]
    simp [hi]
  · intro j hj
    rw [hs.eq_add_ite ha hbot hx j, hs.eq_add_ite ha hbot hy j, hstep]
    simp [Finset.mem_insert, hj]

/-! ### Reflection -/

/-- The reflection of a simplex in the origin is a simplex. -/
theorem IsSimplex.neg (hs : IsSimplex N s) : IsSimplex N (-s) where
  nonempty := hs.nonempty.neg
  subset_grid := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.1 hx
    exact neg_mem_grid (hs.subset_grid hy)
  chain := by
    rintro x hx y hy hne
    obtain ⟨x', hx', rfl⟩ := Finset.mem_neg.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_neg.1 hy
    have hne' : x' ≠ y' := fun h => hne (by rw [h])
    rcases hs.chain hx' hy' hne' with h | h
    · refine Or.inr (Pi.le_def.2 fun i => ?_)
      have := Pi.le_def.1 h i
      simp only [Pi.neg_apply]
      omega
    · refine Or.inl (Pi.le_def.2 fun i => ?_)
      have := Pi.le_def.1 h i
      simp only [Pi.neg_apply]
      omega
  sub_le_one := by
    intro x hx y hy i
    obtain ⟨x', hx', rfl⟩ := Finset.mem_neg.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_neg.1 hy
    have h1 := hs.sub_le_one x' hx' y' hy' i
    have h2 := hs.sub_le_one y' hy' x' hx' i
    simp only [Pi.neg_apply]
    omega

/-- Reflection reverses every sign. -/
theorem mem_signs_neg {p : Label n} : p ∈ signs (-s) ↔ negLabel p ∈ signs s := by
  obtain ⟨i, b⟩ := p
  cases b
  · rw [mem_signs_false]
    show (∃ x ∈ -s, x i < 0) ↔ (i, true) ∈ signs s
    rw [mem_signs_true]
    constructor
    · rintro ⟨x, hx, hxi⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.1 hx
      exact ⟨y, hy, by simpa using hxi⟩
    · rintro ⟨y, hy, hyi⟩
      exact ⟨-y, Finset.mem_neg.2 ⟨y, hy, rfl⟩, by simpa using hyi⟩
  · rw [mem_signs_true]
    show (∃ x ∈ -s, 0 < x i) ↔ (i, false) ∈ signs s
    rw [mem_signs_false]
    constructor
    · rintro ⟨x, hx, hxi⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.1 hx
      exact ⟨y, hy, by simpa using hxi⟩
    · rintro ⟨y, hy, hyi⟩
      exact ⟨-y, Finset.mem_neg.2 ⟨y, hy, rfl⟩, by simpa using hyi⟩

/-- Reflection reverses the set of signs. -/
theorem signs_neg (s : Finset (Fin n → ℤ)) : signs (-s) = (signs s).image negLabel := by
  ext p
  rw [mem_signs_neg, mem_image_negLabel]

/-- Reflection preserves the directions. -/
theorem directions_neg (s : Finset (Fin n → ℤ)) : directions (-s) = directions s := by
  ext i
  simp only [mem_directions]
  constructor
  · rintro ⟨x, hx, hxi⟩
    obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.1 hx
    exact ⟨y, hy, by simpa using hxi⟩
  · rintro ⟨y, hy, hyi⟩
    exact ⟨-y, Finset.mem_neg.2 ⟨y, hy, rfl⟩, by simpa using hyi⟩

end GridSimplex

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

A simplex therefore has at most one more vertex than it has directions, and the
counting argument below runs over the ways of adding one vertex without adding a sign
outside a prescribed set of labels.  There are two, except at the boundary of the cube,
where one of them leaves the grid.

## Main results

* `IsSimplex.not_mem_signs_negLabel` — a simplex lies in one closed orthant: its signs
  contain no pair of opposite labels.
* `IsSimplex.card_le_card_directions_succ` — a simplex has at most one more vertex than it
  has directions.  This is what makes the counting argument finite.
* `card_extensions_eq_one` — with one more vertex than directions, a simplex extends in
  exactly one way when one further label is allowed.
* `extensions_eq_empty` — with one more vertex than directions, a simplex does not extend
  at all when no further label is allowed.
* `card_extensions_eq_two`, `card_extensions_eq_one_of_isExtremal` — with as many vertices
  as directions, a simplex extends in exactly two ways, or in one when a coordinate sits
  at the boundary of the cube.
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

/-- A single grid point is a simplex. -/
theorem isSimplex_singleton {v : Fin n → ℤ} (hv : v ∈ grid n N) :
    IsSimplex N ({v} : Finset (Fin n → ℤ)) where
  nonempty := Finset.singleton_nonempty v
  subset_grid := Finset.singleton_subset_iff.2 hv
  chain := by
    rintro x hx y hy hne
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
    exact absurd (hx.trans hy.symm) hne
  sub_le_one := by
    intro x hx y hy i
    rw [Finset.mem_singleton] at hx hy
    subst hx
    subst hy
    omega


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

/-- The origin alone carries no sign. -/
@[simp]
theorem signs_singleton_zero : signs ({0} : Finset (Fin n → ℤ)) = ∅ := by
  ext p
  obtain ⟨i, c⟩ := p
  cases c
  · simp [mem_signs_false]
  · simp [mem_signs_true]

/-- The origin alone has no direction. -/
@[simp]
theorem directions_singleton_zero : directions ({0} : Finset (Fin n → ℤ)) = ∅ := by
  rw [directions, signs_singleton_zero, Finset.image_empty]

/-- A simplex with no direction and a single vertex is the origin alone. -/
theorem eq_singleton_zero (hs : IsSimplex N s) (h1 : s.card = 1)
    (hd : (directions s).card = 0) : s = {0} := by
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h1
  have hzero : ∀ i, x i = 0 := by
    intro i
    by_contra hcon
    have hmem : i ∈ directions ({x} : Finset (Fin n → ℤ)) :=
      mem_directions.2 ⟨x, Finset.mem_singleton_self x, hcon⟩
    rw [Finset.card_eq_zero.1 hd] at hmem
    exact absurd hmem (Finset.notMem_empty i)
  have : x = 0 := by
    ext i
    exact hzero i
  rw [this]


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

/-- A nonempty finite chain of integer vectors has a greatest element. -/
theorem exists_isGreatest_of_isChain {t : Finset (Fin n → ℤ)} (ht : t.Nonempty)
    (hc : IsChain (· ≤ ·) (t : Set (Fin n → ℤ))) : ∃ b ∈ t, ∀ x ∈ t, x ≤ b := by
  obtain ⟨b, hb, hmax⟩ := t.exists_max_image (fun x => ∑ i, x i) ht
  refine ⟨b, hb, fun x hx => ?_⟩
  rcases eq_or_ne b x with rfl | hne
  · exact le_rfl
  · rcases hc hb hx hne with h | h
    · exfalso
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
      have hlt : ∑ i, b i < ∑ i, x i :=
        Finset.sum_lt_sum (fun i _ => h i) ⟨j, Finset.mem_univ j, lt_of_le_of_ne (h j) hj⟩
      exact absurd (hmax x hx) (not_le.2 hlt)
    · exact h

/-- A simplex has a least vertex. -/
theorem IsSimplex.exists_bot (hs : IsSimplex N s) : ∃ a ∈ s, ∀ x ∈ s, a ≤ x :=
  exists_isLeast_of_isChain hs.nonempty hs.chain

/-- A simplex has a greatest vertex. -/
theorem IsSimplex.exists_top (hs : IsSimplex N s) : ∃ b ∈ s, ∀ x ∈ s, x ≤ b :=
  exists_isGreatest_of_isChain hs.nonempty hs.chain

/-- The grid is an order interval: a point between two grid points is a grid point. -/
theorem mem_grid_of_le_of_le {u w v : Fin n → ℤ} (hu : u ∈ grid n N) (hv : v ∈ grid n N)
    (huw : u ≤ w) (hwv : w ≤ v) : w ∈ grid n N := by
  rw [mem_grid] at hu hv ⊢
  intro i
  have h1 := hu i
  have h2 := hv i
  have h3 : u i ≤ w i := Pi.le_def.1 huw i
  have h4 : w i ≤ v i := Pi.le_def.1 hwv i
  omega

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

/-- Lowering the base point can only enlarge the step set. -/
theorem step_subset_step_base {a w x : Fin n → ℤ} (hwa : w ≤ a) : step a x ⊆ step w x := by
  intro i hi
  rw [mem_step] at hi ⊢
  exact lt_of_le_of_lt (Pi.le_def.1 hwa i) hi

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
  · rw [ite_eq_right (by simp [h]), h, add_zero]
  · rw [ite_eq_left (by simp [h]), h]

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

/-- **A simplex has at most one more vertex than its total step set has coordinates.**

The rank is injective on the simplex and takes values between `0` and the number of
coordinates in which the greatest vertex exceeds the least one. -/
theorem IsSimplex.card_le_card_step_succ (hs : IsSimplex N s) {a b : Fin n → ℤ}
    (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z) (htop : ∀ z ∈ s, z ≤ b) :
    s.card ≤ (step a b).card + 1 := by
  have himg : s.image (rank a) ⊆ Finset.range ((step a b).card + 1) := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.mem_range.2
      (Nat.lt_succ_of_le (Finset.card_le_card (step_subset_step (htop x hx))))
  calc s.card = (s.image (rank a)).card :=
        (Finset.card_image_of_injOn (hs.injOn_rank ha hbot)).symm
    _ ≤ (Finset.range ((step a b).card + 1)).card := Finset.card_le_card himg
    _ = (step a b).card + 1 := Finset.card_range _

/-- **A simplex has at most one more vertex than it has directions.**

Every coordinate in which the greatest vertex exceeds the least one is a direction. -/
theorem IsSimplex.card_le_card_directions_succ (hs : IsSimplex N s) :
    s.card ≤ (directions s).card + 1 := by
  obtain ⟨a, ha, hbot⟩ := hs.exists_bot
  obtain ⟨b, hb, htop⟩ := hs.exists_top
  exact (hs.card_le_card_step_succ ha hbot htop).trans
    (Nat.succ_le_succ (Finset.card_le_card (step_subset_directions ha hb)))

/-! ### Saturated simplices

A simplex with one more vertex than its total step set has coordinates is as long as it
can be: its ranks then run through every value from `0` upwards, so consecutive vertices
differ by a single unit step.  This is what pins down the ways of extending it by one
vertex. -/

/-- A simplex with one more vertex than it has directions is saturated: every direction is
already a coordinate in which the greatest vertex exceeds the least one. -/
theorem IsSimplex.card_eq_card_step_succ (hs : IsSimplex N s) {a b : Fin n → ℤ}
    (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z) (hb : b ∈ s) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (directions s).card + 1) : s.card = (step a b).card + 1 := by
  have h1 := hs.card_le_card_step_succ ha hbot htop
  have h2 : (step a b).card ≤ (directions s).card :=
    Finset.card_le_card (step_subset_directions ha hb)
  omega

/-- A saturated simplex realises every rank up to the size of its total step set. -/
theorem IsSimplex.image_rank (hs : IsSimplex N s) {a b : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (step a b).card + 1) :
    s.image (rank a) = Finset.range ((step a b).card + 1) := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.mem_range.2
      (Nat.lt_succ_of_le (Finset.card_le_card (step_subset_step (htop x hx))))
  · rw [Finset.card_range, Finset.card_image_of_injOn (hs.injOn_rank ha hbot), hcard]

/-- Hence every rank below the size of the total step set occurs at a vertex. -/
theorem IsSimplex.exists_rank_eq (hs : IsSimplex N s) {a b : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (step a b).card + 1) {r : ℕ} (hr : r ≤ (step a b).card) :
    ∃ z ∈ s, rank a z = r := by
  have hmem : r ∈ s.image (rank a) := by
    rw [hs.image_rank ha hbot htop hcard]
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hr)
  obtain ⟨z, hz, hzr⟩ := Finset.mem_image.1 hmem
  exact ⟨z, hz, hzr⟩

/-- In a saturated simplex, consecutive vertices have consecutive ranks. -/
theorem IsSimplex.rank_eq_succ (hs : IsSimplex N s) {a b x y : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (step a b).card + 1) (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y)
    (hcons : ∀ z ∈ s, ¬(x < z ∧ z < y)) : rank a y = rank a x + 1 := by
  have hlt : rank a x < rank a y := hs.rank_lt_rank ha hbot hx hy hxy
  by_contra hne
  have hle : rank a x + 1 ≤ (step a b).card := by
    have hy' : rank a y ≤ (step a b).card :=
      Finset.card_le_card (step_subset_step (htop y hy))
    omega
  obtain ⟨z, hz, hzr⟩ := hs.exists_rank_eq ha hbot htop hcard hle
  exact hcons z hz ⟨hs.lt_of_rank_lt ha hbot hx hz (by omega),
    hs.lt_of_rank_lt ha hbot hz hy (by omega)⟩

/-- In a saturated simplex, the step set of the successor of a vertex adds exactly one
coordinate. -/
theorem IsSimplex.exists_step_eq_insert (hs : IsSimplex N s) {a b x y : Fin n → ℤ}
    (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (step a b).card + 1) (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y)
    (hcons : ∀ z ∈ s, ¬(x < z ∧ z < y)) :
    ∃ i ∉ step a x, step a y = insert i (step a x) := by
  have hsub : step a x ⊆ step a y := step_subset_step hxy.le
  have hcards : (step a x).card + 1 = (step a y).card :=
    (hs.rank_eq_succ ha hbot htop hcard hx hy hxy hcons).symm
  obtain ⟨i, hi, hins⟩ := Finset.exists_eq_insert_iff.2 ⟨hsub, hcards⟩
  exact ⟨i, hi, hins.symm⟩

/-- **Consecutive vertices of a saturated simplex differ by one unit step.** -/
theorem IsSimplex.exists_eq_add_single (hs : IsSimplex N s) {a b x y : Fin n → ℤ}
    (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (step a b).card + 1) (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y)
    (hcons : ∀ z ∈ s, ¬(x < z ∧ z < y)) :
    ∃ i, x i + 1 = y i ∧ ∀ j, j ≠ i → x j = y j := by
  obtain ⟨i, hi, hstep⟩ := hs.exists_step_eq_insert ha hbot htop hcard hx hy hxy hcons
  refine ⟨i, ?_, ?_⟩
  · rw [hs.eq_add_ite ha hbot hx i, hs.eq_add_ite ha hbot hy i, hstep]
    simp [hi]
  · intro j hj
    rw [hs.eq_add_ite ha hbot hx j, hs.eq_add_ite ha hbot hy j, hstep]
    simp [Finset.mem_insert, hj]

/-! ### Extending a simplex by one vertex

A vertex added to a simplex sits below all of it, above all of it, or strictly between two
consecutive vertices.  In each position the added vertex is adjacent in the chain to a
vertex of the original simplex, so in a saturated simplex it differs from that vertex by a
single unit step. -/

/-- Inserting a vertex that is comparable with every vertex of a simplex and differs from
each by at most one in every coordinate again gives a simplex. -/
theorem IsSimplex.insert_vertex (hs : IsSimplex N s) {w : Fin n → ℤ} (hw : w ∈ grid n N)
    (hcomp : ∀ z ∈ s, w ≤ z ∨ z ≤ w)
    (hspan : ∀ z ∈ s, ∀ i, z i - w i ≤ 1 ∧ w i - z i ≤ 1) :
    IsSimplex N (insert w s) where
  nonempty := Finset.insert_nonempty _ _
  subset_grid := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hxs
    · exact hw
    · exact hs.subset_grid hxs
  chain := by
    rintro x hx y hy hne
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
    rcases hx with rfl | hxs
    · rcases hy with rfl | hys
      · exact absurd rfl hne
      · exact hcomp y hys
    · rcases hy with rfl | hys
      · exact (hcomp x hxs).symm
      · exact hs.chain hxs hys hne
  sub_le_one := by
    intro x hx y hy i
    rcases Finset.mem_insert.1 hx with rfl | hxs
    · rcases Finset.mem_insert.1 hy with rfl | hys
      · omega
      · exact (hspan y hys i).1
    · rcases Finset.mem_insert.1 hy with rfl | hys
      · exact (hspan x hxs i).2
      · exact hs.sub_le_one x hxs y hys i

/-- A new vertex that is neither below some vertex nor above another lies strictly between
two consecutive vertices.  Applied to the least and the greatest vertex, this is the
trichotomy for the position of a new vertex in the chain. -/
theorem exists_between_of_insert {w a b : Fin n → ℤ}
    (hchain : IsChain (· ≤ ·) ((insert w s : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
    (hws : w ∉ s) (ha : a ∈ s) (hb : b ∈ s) (h1 : ¬ w < a) (h2 : ¬ b < w) :
    ∃ x ∈ s, ∃ y ∈ s, x < w ∧ w < y ∧ ∀ z ∈ s, ¬(x < z ∧ z < y) := by
  classical
  have hsub : (s : Set (Fin n → ℤ)) ⊆ ((insert w s : Finset (Fin n → ℤ)) : Set _) := by
    intro z hz
    exact_mod_cast Finset.mem_insert_of_mem (by exact_mod_cast hz)
  have hchain' : IsChain (· ≤ ·) (s : Set (Fin n → ℤ)) := hchain.mono hsub
  have hmemw : w ∈ (insert w s : Finset (Fin n → ℤ)) := Finset.mem_insert_self _ _
  have hcomp : ∀ z ∈ s, z < w ∨ w < z := by
    intro z hz
    have hzw : z ≠ w := fun h => hws (h ▸ hz)
    rcases hchain (hsub (by exact_mod_cast hz)) (by exact_mod_cast hmemw) hzw with h | h
    · exact Or.inl (lt_of_le_of_ne h hzw)
    · exact Or.inr (lt_of_le_of_ne h (Ne.symm hzw))
  -- `w` is above the least vertex and below the greatest one.
  have haw : a < w := by
    rcases hcomp a ha with h | h
    · exact h
    · exact absurd h h1
  have hwb : w < b := by
    rcases hcomp b hb with h | h
    · exact absurd h h2
    · exact h
  -- The largest vertex below `w` and the smallest one above it.
  set L : Finset (Fin n → ℤ) := s.filter (fun z => z < w) with hL
  set R : Finset (Fin n → ℤ) := s.filter (fun z => w < z) with hR
  have hLs : L ⊆ s := Finset.filter_subset _ _
  have hRs : R ⊆ s := Finset.filter_subset _ _
  have hLne : L.Nonempty := ⟨a, Finset.mem_filter.2 ⟨ha, haw⟩⟩
  have hRne : R.Nonempty := ⟨b, Finset.mem_filter.2 ⟨hb, hwb⟩⟩
  obtain ⟨x, hxL, hxmax⟩ :=
    exists_isGreatest_of_isChain hLne (hchain'.mono (by exact_mod_cast hLs))
  obtain ⟨y, hyR, hymin⟩ :=
    exists_isLeast_of_isChain hRne (hchain'.mono (by exact_mod_cast hRs))
  obtain ⟨hxs, hxw⟩ := Finset.mem_filter.1 hxL
  obtain ⟨hys, hwy⟩ := Finset.mem_filter.1 hyR
  refine ⟨x, hxs, y, hys, hxw, hwy, ?_⟩
  rintro z hz ⟨hxz, hzy⟩
  rcases hcomp z hz with h | h
  · exact absurd (lt_of_lt_of_le hxz (hxmax z (Finset.mem_filter.2 ⟨hz, h⟩))) (lt_irrefl x)
  · exact absurd (lt_of_lt_of_le hzy (hymin z (Finset.mem_filter.2 ⟨hz, h⟩))) (lt_irrefl z)

/-- A vertex above the whole simplex is one unit step above its greatest vertex. -/
theorem IsSimplex.exists_eq_top_add_single {w a b : Fin n → ℤ}
    (ht : IsSimplex N (insert w s)) (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z) (hb : b ∈ s)
    (htop : ∀ z ∈ s, z ≤ b) (hbw : b < w)
    (hcard : (insert w s).card = (step a w).card + 1) :
    ∃ i, b i + 1 = w i ∧ ∀ j, j ≠ i → b j = w j := by
  have hbot' : ∀ z ∈ insert w s, a ≤ z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_trans (hbot b hb) hbw.le
    · exact hbot z hzs
  have htop' : ∀ z ∈ insert w s, z ≤ w := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_rfl
    · exact le_trans (htop z hzs) hbw.le
  refine ht.exists_eq_add_single (Finset.mem_insert_of_mem ha) hbot' htop' hcard
    (Finset.mem_insert_of_mem hb) (Finset.mem_insert_self _ _) hbw ?_
  rintro z hz ⟨hbz, hzw⟩
  rcases Finset.mem_insert.1 hz with rfl | hzs
  · exact absurd hzw (lt_irrefl _)
  · exact absurd (lt_of_lt_of_le hbz (htop z hzs)) (lt_irrefl b)

/-- A vertex below the whole simplex is one unit step below its least vertex. -/
theorem IsSimplex.exists_eq_add_single_bot {w a b : Fin n → ℤ}
    (ht : IsSimplex N (insert w s)) (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z)
    (htop : ∀ z ∈ s, z ≤ b) (hwa : w < a)
    (hcard : (insert w s).card = (step w b).card + 1) :
    ∃ i, w i + 1 = a i ∧ ∀ j, j ≠ i → w j = a j := by
  have hbot' : ∀ z ∈ insert w s, w ≤ z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_rfl
    · exact le_of_lt (lt_of_lt_of_le hwa (hbot z hzs))
  have htop' : ∀ z ∈ insert w s, z ≤ b := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_trans hwa.le (htop a ha)
    · exact htop z hzs
  refine ht.exists_eq_add_single (Finset.mem_insert_self _ _) hbot' htop' hcard
    (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem ha) hwa ?_
  rintro z hz ⟨hwz, hza⟩
  rcases Finset.mem_insert.1 hz with rfl | hzs
  · exact absurd hwz (lt_irrefl _)
  · exact absurd (lt_of_lt_of_le hza (hbot z hzs)) (lt_irrefl z)

/-- A vertex added below a simplex lowers a coordinate that is constant on it. -/
theorem IsSimplex.const_of_insert_bot {w a : Fin n → ℤ} {p : Fin n}
    (ht : IsSimplex N (insert w s)) (hbot : ∀ z ∈ s, a ≤ z)
    (hwp : w p + 1 = a p) : ∀ z ∈ s, z p = a p := by
  intro z hz
  have h1 : z p - w p ≤ 1 :=
    ht.sub_le_one w (Finset.mem_insert_self _ _) z (Finset.mem_insert_of_mem hz) p
  have h2 : a p ≤ z p := Pi.le_def.1 (hbot z hz) p
  omega

/-- A vertex added above a simplex raises a coordinate that is constant on it. -/
theorem IsSimplex.const_of_insert_top {w b : Fin n → ℤ} {p : Fin n}
    (ht : IsSimplex N (insert w s)) (htop : ∀ z ∈ s, z ≤ b)
    (hwp : b p + 1 = w p) : ∀ z ∈ s, z p = b p := by
  intro z hz
  have h1 : w p - z p ≤ 1 :=
    ht.sub_le_one z (Finset.mem_insert_of_mem hz) w (Finset.mem_insert_self _ _) p
  have h2 : z p ≤ b p := Pi.le_def.1 (htop z hz) p
  omega

/-! ### Raising and lowering a coordinate

The vertices that extend a simplex differ from one of its vertices in a single coordinate,
by one. -/

/-- The point obtained from `x` by raising the coordinate `p` by one. -/
def raise (x : Fin n → ℤ) (p : Fin n) : Fin n → ℤ := Function.update x p (x p + 1)

/-- The point obtained from `x` by lowering the coordinate `p` by one. -/
def lower (x : Fin n → ℤ) (p : Fin n) : Fin n → ℤ := Function.update x p (x p - 1)

/-- Raising changes the chosen coordinate. -/
@[simp]
theorem raise_apply_self (x : Fin n → ℤ) (p : Fin n) : raise x p p = x p + 1 := by
  simp [raise]

/-- Raising leaves the other coordinates alone. -/
@[simp]
theorem raise_apply_of_ne (x : Fin n → ℤ) {p j : Fin n} (h : j ≠ p) : raise x p j = x j := by
  simp [raise, h]

/-- Lowering changes the chosen coordinate. -/
@[simp]
theorem lower_apply_self (x : Fin n → ℤ) (p : Fin n) : lower x p p = x p - 1 := by
  simp [lower]

/-- Lowering leaves the other coordinates alone. -/
@[simp]
theorem lower_apply_of_ne (x : Fin n → ℤ) {p j : Fin n} (h : j ≠ p) : lower x p j = x j := by
  simp [lower, h]

/-- Raising a coordinate increases the point. -/
theorem le_raise (x : Fin n → ℤ) (p : Fin n) : x ≤ raise x p := by
  refine Pi.le_def.2 fun j => ?_
  rcases eq_or_ne j p with rfl | h
  · simp
  · simp [h]

/-- Lowering a coordinate decreases the point. -/
theorem lower_le (x : Fin n → ℤ) (p : Fin n) : lower x p ≤ x := by
  refine Pi.le_def.2 fun j => ?_
  rcases eq_or_ne j p with rfl | h
  · simp
  · simp [h]

/-- Raising in different coordinates gives different points. -/
theorem raise_ne_raise {x : Fin n → ℤ} {p q : Fin n} (h : p ≠ q) : raise x p ≠ raise x q :=
  fun hcon => by simpa [h, raise_apply_of_ne x h] using congrFun hcon p

/-! ### Extremal faces

A simplex on which one coordinate takes the same extreme value `N` or `-N` at every vertex
lies in a face of the cube.  These are the simplices the parity argument pairs up by
reflection. -/

/-- One coordinate is constantly `N`, or constantly `-N`, on `s`. -/
def IsExtremal (N : ℕ) (s : Finset (Fin n → ℤ)) : Prop :=
  ∃ c, (∀ z ∈ s, z c = (N : ℤ)) ∨ ∀ z ∈ s, z c = -(N : ℤ)

/-- Reflection preserves extremality. -/
theorem IsExtremal.neg (h : IsExtremal N s) : IsExtremal N (-s) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rcases hc with hc | hc
  · refine Or.inr fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.1 hz
    simp [hc y hy]
  · refine Or.inl fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.1 hz
    simp [hc y hy]

/-- **Reflection has no fixed extremal face.**  An extremal face and its reflection differ,
because the extreme coordinate would have to take both values `N` and `-N`. -/
theorem IsExtremal.neg_ne (h : IsExtremal N s) (hs : s.Nonempty) (hN : 0 < N) : -s ≠ s := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨z, hz⟩ := hs
  intro hcon
  have hmem : -z ∈ s := hcon ▸ Finset.mem_neg.2 ⟨z, hz, rfl⟩
  have hN' : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  rcases hc with hc | hc
  · have h1 := hc z hz
    have h2 := hc (-z) hmem
    simp only [Pi.neg_apply] at h2
    omega
  · have h1 := hc z hz
    have h2 := hc (-z) hmem
    simp only [Pi.neg_apply] at h2
    omega

/-! ### Inserting a vertex

Three ways of extending a simplex by one vertex: between two consecutive vertices, one
unit step below the least, and one unit step above the greatest.  In each case the
resulting set is again a simplex, and under the stated conditions it carries no new
sign. -/

/-- Inserting a vertex between two consecutive vertices gives a simplex. -/
theorem IsSimplex.insert_between (hs : IsSimplex N s) {x y w : Fin n → ℤ} (hx : x ∈ s)
    (hy : y ∈ s) (hxw : x ≤ w) (hwy : w ≤ y) (hcons : ∀ z ∈ s, ¬(x < z ∧ z < y)) :
    IsSimplex N (insert w s) := by
  refine hs.insert_vertex
    (mem_grid_of_le_of_le (hs.subset_grid hx) (hs.subset_grid hy) hxw hwy) ?_ ?_
  · intro z hz
    rcases eq_or_ne z x with rfl | hzx
    · exact Or.inr hxw
    rcases hs.chain hz hx hzx with h | h
    · exact Or.inr (h.trans hxw)
    · have hxz : x < z := lt_of_le_of_ne h (Ne.symm hzx)
      rcases eq_or_ne z y with rfl | hzy
      · exact Or.inl hwy
      rcases hs.chain hz hy hzy with h' | h'
      · exact absurd ⟨hxz, lt_of_le_of_ne h' hzy⟩ (hcons z hz)
      · exact Or.inl (hwy.trans h')
  · intro z hz i
    refine ⟨?_, ?_⟩
    · have h1 : x i ≤ w i := Pi.le_def.1 hxw i
      have h2 : z i - x i ≤ 1 := hs.sub_le_one x hx z hz i
      omega
    · have h1 : w i ≤ y i := Pi.le_def.1 hwy i
      have h2 : y i - z i ≤ 1 := hs.sub_le_one z hz y hy i
      omega

/-- Inserting the least vertex with one constant coordinate lowered gives a simplex. -/
theorem IsSimplex.insert_lower (hs : IsSimplex N s) {a : Fin n → ℤ} {p : Fin n} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hconst : ∀ z ∈ s, z p = a p) (hgrid : -(N : ℤ) ≤ a p - 1) :
    IsSimplex N (insert (lower a p) s) := by
  refine hs.insert_vertex ?_ ?_ ?_
  · rw [mem_grid]
    intro i
    have hai := mem_grid.1 (hs.subset_grid ha) i
    rcases eq_or_ne i p with rfl | hne
    · rw [lower_apply_self]; omega
    · rw [lower_apply_of_ne _ hne]; omega
  · intro z hz
    refine Or.inl (Pi.le_def.2 fun i => ?_)
    have h1 : a i ≤ z i := Pi.le_def.1 (hbot z hz) i
    rcases eq_or_ne i p with rfl | hne
    · rw [lower_apply_self]; omega
    · rw [lower_apply_of_ne _ hne]; omega
  · intro z hz i
    have h1 : a i ≤ z i := Pi.le_def.1 (hbot z hz) i
    have h2 : z i - a i ≤ 1 := hs.sub_le_one a ha z hz i
    rcases eq_or_ne i p with rfl | hne
    · have h3 := hconst z hz
      rw [lower_apply_self]; omega
    · rw [lower_apply_of_ne _ hne]; omega

/-- Inserting the greatest vertex with one constant coordinate raised gives a simplex. -/
theorem IsSimplex.insert_raise (hs : IsSimplex N s) {b : Fin n → ℤ} {p : Fin n} (hb : b ∈ s)
    (htop : ∀ z ∈ s, z ≤ b) (hconst : ∀ z ∈ s, z p = b p) (hgrid : b p + 1 ≤ (N : ℤ)) :
    IsSimplex N (insert (raise b p) s) := by
  refine hs.insert_vertex ?_ ?_ ?_
  · rw [mem_grid]
    intro i
    have hbi := mem_grid.1 (hs.subset_grid hb) i
    rcases eq_or_ne i p with rfl | hne
    · rw [raise_apply_self]; omega
    · rw [raise_apply_of_ne _ hne]; omega
  · intro z hz
    refine Or.inr (Pi.le_def.2 fun i => ?_)
    have h1 : z i ≤ b i := Pi.le_def.1 (htop z hz) i
    rcases eq_or_ne i p with rfl | hne
    · rw [raise_apply_self]; omega
    · rw [raise_apply_of_ne _ hne]; omega
  · intro z hz i
    have h1 : z i ≤ b i := Pi.le_def.1 (htop z hz) i
    have h2 : b i - z i ≤ 1 := hs.sub_le_one z hz b hb i
    rcases eq_or_ne i p with rfl | hne
    · have h3 := hconst z hz
      rw [raise_apply_self]; omega
    · rw [raise_apply_of_ne _ hne]; omega

/-- Inserting a vertex that is positive only where the simplex already is, and negative
only where it already is, adds no sign. -/
theorem signs_insert_subset {w : Fin n → ℤ}
    (h : ∀ i, (0 < w i → ∃ z ∈ s, 0 < z i) ∧ (w i < 0 → ∃ z ∈ s, z i < 0)) :
    signs (insert w s) ⊆ signs s := by
  rintro ⟨i, c⟩ hp
  cases c
  · obtain ⟨x, hx, hxi⟩ := mem_signs_false.1 hp
    rcases Finset.mem_insert.1 hx with rfl | hxs
    · exact mem_signs_false.2 ((h i).2 hxi)
    · exact mem_signs_false.2 ⟨x, hxs, hxi⟩
  · obtain ⟨x, hx, hxi⟩ := mem_signs_true.1 hp
    rcases Finset.mem_insert.1 hx with rfl | hxs
    · exact mem_signs_true.2 ((h i).1 hxi)
    · exact mem_signs_true.2 ⟨x, hxs, hxi⟩

/-- A vertex inserted between two vertices of the simplex adds no sign. -/
theorem signs_insert_subset_of_between {x y w : Fin n → ℤ} (hx : x ∈ s) (hy : y ∈ s)
    (hxw : x ≤ w) (hwy : w ≤ y) : signs (insert w s) ⊆ signs s :=
  signs_insert_subset fun i =>
    ⟨fun hpos => ⟨y, hy, lt_of_lt_of_le hpos (Pi.le_def.1 hwy i)⟩,
      fun hneg => ⟨x, hx, lt_of_le_of_lt (Pi.le_def.1 hxw i) hneg⟩⟩

/-- Lowering a constant nonzero coordinate of the least vertex adds no sign. -/
theorem signs_insert_lower_subset {a : Fin n → ℤ} {p : Fin n} (ha : a ∈ s)
    (hconst : ∀ z ∈ s, z p = a p) (hne : a p ≠ 0) :
    signs (insert (lower a p) s) ⊆ signs s := by
  refine signs_insert_subset fun i => ?_
  rcases eq_or_ne i p with rfl | hne'
  · rw [lower_apply_self]
    exact ⟨fun h => ⟨a, ha, by omega⟩, fun h => ⟨a, ha, by omega⟩⟩
  · rw [lower_apply_of_ne _ hne']
    exact ⟨fun h => ⟨a, ha, h⟩, fun h => ⟨a, ha, h⟩⟩

/-- Raising a constant nonzero coordinate of the greatest vertex adds no sign. -/
theorem signs_insert_raise_subset {b : Fin n → ℤ} {p : Fin n} (hb : b ∈ s)
    (hconst : ∀ z ∈ s, z p = b p) (hne : b p ≠ 0) :
    signs (insert (raise b p) s) ⊆ signs s := by
  refine signs_insert_subset fun i => ?_
  rcases eq_or_ne i p with rfl | hne'
  · rw [raise_apply_self]
    exact ⟨fun h => ⟨b, hb, by omega⟩, fun h => ⟨b, hb, by omega⟩⟩
  · rw [raise_apply_of_ne _ hne']
    exact ⟨fun h => ⟨b, hb, h⟩, fun h => ⟨b, hb, h⟩⟩

/-! ### Excluding positions for a new vertex

Which of the three positions a new vertex can take is decided by the size of the total
step set, compared with the number of directions the enlarged simplex is allowed. -/

/-- A coordinate in which the greatest vertex does not exceed the least one is constant. -/
theorem const_of_not_mem_step {a b : Fin n → ℤ} (hbot : ∀ z ∈ s, a ≤ z)
    (htop : ∀ z ∈ s, z ≤ b) {p : Fin n} (hp : p ∉ step a b) : ∀ z ∈ s, z p = a p := by
  intro z hz
  have h1 : a p ≤ z p := Pi.le_def.1 (hbot z hz) p
  have h2 : z p ≤ b p := Pi.le_def.1 (htop z hz) p
  have h3 : ¬ a p < b p := by simpa [mem_step] using hp
  omega

/-- If the enlarged simplex has no more directions than the total step set has
coordinates, no vertex can be added below the least one. -/
theorem IsSimplex.not_lt_of_insert {w a b : Fin n → ℤ} (ht : IsSimplex N (insert w s))
    (ha : a ∈ s) (hb : b ∈ s) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : (directions (insert w s)).card ≤ (step a b).card) : ¬ w < a := by
  intro hwa
  obtain ⟨p, hp⟩ : ∃ p, w p < a p := by
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hwa.ne
    exact ⟨p, lt_of_le_of_ne (Pi.le_def.1 hwa.le p) hp⟩
  have hab : a p ≤ b p := Pi.le_def.1 (htop a ha) p
  by_cases hmem : p ∈ step a b
  · rw [mem_step] at hmem
    have := ht.sub_le_one w (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb) p
    omega
  · have hsub : step a b ⊆ step w b := step_subset_step_base hwa.le
    have hpw : p ∈ step w b := mem_step.2 (by omega)
    have h1 : (step w b).card ≤ (directions (insert w s)).card :=
      Finset.card_le_card (step_subset_directions (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem hb))
    have h2 := Finset.card_lt_card (ssubset_iff_of_subset hsub |>.2 ⟨p, hpw, hmem⟩)
    omega

/-- If the enlarged simplex has no more directions than the total step set has
coordinates, no vertex can be added above the greatest one. -/
theorem IsSimplex.not_gt_of_insert {w a b : Fin n → ℤ} (ht : IsSimplex N (insert w s))
    (ha : a ∈ s) (hb : b ∈ s) (hbot : ∀ z ∈ s, a ≤ z)
    (hcard : (directions (insert w s)).card ≤ (step a b).card) : ¬ b < w := by
  intro hbw
  obtain ⟨p, hp⟩ : ∃ p, b p < w p := by
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hbw.ne
    exact ⟨p, lt_of_le_of_ne (Pi.le_def.1 hbw.le p) hp⟩
  have hab : a p ≤ b p := Pi.le_def.1 (hbot b hb) p
  by_cases hmem : p ∈ step a b
  · rw [mem_step] at hmem
    have := ht.sub_le_one a (Finset.mem_insert_of_mem ha) w (Finset.mem_insert_self _ _) p
    omega
  · have hsub : step a b ⊆ step a w := step_subset_step hbw.le
    have hpw : p ∈ step a w := mem_step.2 (by omega)
    have h1 : (step a w).card ≤ (directions (insert w s)).card :=
      Finset.card_le_card (step_subset_directions (Finset.mem_insert_of_mem ha)
        (Finset.mem_insert_self _ _))
    have h2 := Finset.card_lt_card (ssubset_iff_of_subset hsub |>.2 ⟨p, hpw, hmem⟩)
    omega

/-- A saturated simplex admits no new vertex between its least and its greatest. -/
theorem IsSimplex.not_between_of_saturated {w a b : Fin n → ℤ}
    (ht : IsSimplex N (insert w s)) (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z)
    (htop : ∀ z ∈ s, z ≤ b) (hws : w ∉ s) (haw : a ≤ w) (hwb : w ≤ b)
    (hcard : s.card = (step a b).card + 1) : False := by
  have hbot' : ∀ z ∈ insert w s, a ≤ z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact haw
    · exact hbot z hzs
  have htop' : ∀ z ∈ insert w s, z ≤ b := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact hwb
    · exact htop z hzs
  have h := ht.card_le_card_step_succ (Finset.mem_insert_of_mem ha) hbot' htop'
  rw [Finset.card_insert_of_notMem hws] at h
  omega

/-! ### Counting the extensions

How many vertices extend a simplex to a larger simplex whose signs stay inside a
prescribed set of labels.  The three counts below are the three shapes a simplex can have
relative to its number of directions. -/

open scoped Classical in
/-- The vertices extending `s` to a larger simplex all of whose signs lie in `t`. -/
noncomputable def extensions (N : ℕ) (s : Finset (Fin n → ℤ)) (t : Finset (Label n)) :
    Finset (Fin n → ℤ) :=
  (grid n N).filter fun w => w ∉ s ∧ IsSimplex N (insert w s) ∧ signs (insert w s) ⊆ t

/-- Membership in `extensions`, unfolded.  The grid condition is automatic. -/
theorem mem_extensions {t : Finset (Label n)} {w : Fin n → ℤ} :
    w ∈ extensions N s t ↔ w ∉ s ∧ IsSimplex N (insert w s) ∧ signs (insert w s) ⊆ t := by
  classical
  rw [extensions, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.2.1.subset_grid (Finset.mem_insert_self _ _), h⟩⟩

/-- An extension has no more directions than the allowed labels. -/
theorem card_directions_insert_le {t : Finset (Label n)} {w : Fin n → ℤ}
    (hw : w ∈ extensions N s t) : (directions (insert w s)).card ≤ t.card := by
  obtain ⟨-, ht, hsub⟩ := mem_extensions.1 hw
  rw [← ht.card_signs]
  exact Finset.card_le_card hsub

/-- **A simplex with one more vertex than it has directions has no extension keeping its
signs.**  This is the shape of a happy simplex with a repeated label. -/
theorem extensions_eq_empty (hs : IsSimplex N s)
    (hcard : s.card = (directions s).card + 1) : extensions N s (signs s) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  obtain ⟨hws, ht, -⟩ := mem_extensions.1 hw
  have h1 : (directions (insert w s)).card ≤ (signs s).card := card_directions_insert_le hw
  rw [hs.card_signs] at h1
  have h2 := ht.card_le_card_directions_succ
  rw [Finset.card_insert_of_notMem hws] at h2
  omega

/-- A coordinate carrying neither sign vanishes on the simplex. -/
theorem eq_zero_of_not_mem_signs {j : Fin n} (hpos : ((j, true) : Label n) ∉ signs s)
    (hneg : ((j, false) : Label n) ∉ signs s) : ∀ z ∈ s, z j = 0 := by
  intro z hz
  rcases lt_trichotomy (z j) 0 with h | h | h
  · exact absurd (mem_signs_false.2 ⟨z, hz, h⟩) hneg
  · exact h
  · exact absurd (mem_signs_true.2 ⟨z, hz, h⟩) hpos

/-- **Allowing one new positive label, a simplex with one more vertex than it has
directions extends only by raising that coordinate above its greatest vertex.** -/
theorem extensions_eq_singleton_raise (hs : IsSimplex N s) (hN : 0 < N)
    (hcard : s.card = (directions s).card + 1) {b : Fin n → ℤ} (hb : b ∈ s)
    (htop : ∀ z ∈ s, z ≤ b) {j : Fin n} (hpos : ((j, true) : Label n) ∉ signs s)
    (hneg : ((j, false) : Label n) ∉ signs s) :
    extensions N s (insert (j, true) (signs s)) = {raise b j} := by
  have hzero := eq_zero_of_not_mem_signs hpos hneg
  obtain ⟨a, ha, hbot⟩ := hs.exists_bot
  have hbj : b j = 0 := hzero b hb
  have hN' : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hmem : raise b j ∈ extensions N s (insert (j, true) (signs s)) := by
    refine mem_extensions.2 ⟨?_, ?_, ?_⟩
    · intro hcon
      have h := hzero _ hcon
      rw [raise_apply_self] at h
      omega
    · refine hs.insert_raise hb htop (fun z hz => by rw [hzero z hz, hbj]) ?_
      omega
    · rintro ⟨i, d⟩ hq
      by_cases hij : i = j
      · subst hij
        cases d
        · exfalso
          obtain ⟨z, hz, hzi⟩ := mem_signs_false.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · rw [raise_apply_self] at hzi; omega
          · rw [hzero z hzs] at hzi; omega
        · exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem ?_
        cases d
        · obtain ⟨z, hz, hzi⟩ := mem_signs_false.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · exact mem_signs_false.2 ⟨b, hb, by rwa [raise_apply_of_ne _ hij] at hzi⟩
          · exact mem_signs_false.2 ⟨z, hzs, hzi⟩
        · obtain ⟨z, hz, hzi⟩ := mem_signs_true.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · exact mem_signs_true.2 ⟨b, hb, by rwa [raise_apply_of_ne _ hij] at hzi⟩
          · exact mem_signs_true.2 ⟨z, hzs, hzi⟩
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨hmem, fun w hw => ?_⟩
  obtain ⟨hws, ht, hsub⟩ := mem_extensions.1 hw
  have hcardins : (insert w s).card = s.card + 1 := Finset.card_insert_of_notMem hws
  have hdle : (directions (insert w s)).card ≤ (directions s).card + 1 := by
    rw [← ht.card_signs]
    calc (signs (insert w s)).card ≤ (insert ((j, true) : Label n) (signs s)).card :=
          Finset.card_le_card hsub
      _ ≤ (signs s).card + 1 := Finset.card_insert_le _ _
      _ = (directions s).card + 1 := by rw [hs.card_signs]
  have hdge := ht.card_le_card_directions_succ
  have hdeq : (directions (insert w s)).card = (directions s).card + 1 := by omega
  have hwj : 0 < w j := by
    rcases lt_trichotomy (w j) 0 with h | h | h
    · exfalso
      have hq : ((j, false) : Label n) ∈ signs (insert w s) :=
        mem_signs_false.2 ⟨w, Finset.mem_insert_self _ _, h⟩
      rcases Finset.mem_insert.1 (hsub hq) with heq | hq'
      · exact absurd heq (by simp)
      · exact hneg hq'
    · exfalso
      have hsub' : signs (insert w s) ⊆ signs s := by
        intro q hq
        rcases Finset.mem_insert.1 (hsub hq) with heq | hq'
        · exfalso
          subst heq
          obtain ⟨z, hz, hzi⟩ := mem_signs_true.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · omega
          · rw [hzero z hzs] at hzi; omega
        · exact hq'
      have hdsub : directions (insert w s) ⊆ directions s :=
        Finset.image_subset_image hsub'
      have := Finset.card_le_card hdsub
      omega
    · exact h
  have hbw : b < w := by
    have hne : b ≠ w := by
      intro hcon
      rw [← hcon] at hwj
      omega
    rcases ht.chain (Finset.mem_insert_of_mem hb) (Finset.mem_insert_self _ _) hne with h | h
    · exact lt_of_le_of_ne h hne
    · exact absurd (Pi.le_def.1 h j) (by omega)
  have hbot' : ∀ z ∈ insert w s, a ≤ z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_trans (hbot b hb) hbw.le
    · exact hbot z hzs
  have htop' : ∀ z ∈ insert w s, z ≤ w := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_rfl
    · exact le_trans (htop z hzs) hbw.le
  have hstep : (insert w s).card = (step a w).card + 1 :=
    ht.card_eq_card_step_succ (Finset.mem_insert_of_mem ha) hbot'
      (Finset.mem_insert_self _ _) htop' (by omega)
  obtain ⟨i, hi1, hi2⟩ := ht.exists_eq_top_add_single ha hbot hb htop hbw hstep
  have hij : i = j := by
    by_contra hcon
    have h := hi2 j fun hjj => hcon hjj.symm
    omega
  subst hij
  refine funext fun j' => ?_
  rcases eq_or_ne j' i with rfl | hne
  · rw [raise_apply_self]; omega
  · rw [raise_apply_of_ne _ hne]; exact (hi2 j' hne).symm

/-- **Allowing one new negative label, a simplex with one more vertex than it has
directions extends only by lowering that coordinate below its least vertex.** -/
theorem extensions_eq_singleton_lower (hs : IsSimplex N s) (hN : 0 < N)
    (hcard : s.card = (directions s).card + 1) {a : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) {j : Fin n} (hpos : ((j, true) : Label n) ∉ signs s)
    (hneg : ((j, false) : Label n) ∉ signs s) :
    extensions N s (insert (j, false) (signs s)) = {lower a j} := by
  have hzero := eq_zero_of_not_mem_signs hpos hneg
  obtain ⟨b, hb, htop⟩ := hs.exists_top
  have haj : a j = 0 := hzero a ha
  have hN' : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hmem : lower a j ∈ extensions N s (insert (j, false) (signs s)) := by
    refine mem_extensions.2 ⟨?_, ?_, ?_⟩
    · intro hcon
      have h := hzero _ hcon
      rw [lower_apply_self] at h
      omega
    · refine hs.insert_lower ha hbot (fun z hz => by rw [hzero z hz, haj]) ?_
      omega
    · rintro ⟨i, d⟩ hq
      by_cases hij : i = j
      · subst hij
        cases d
        · exact Finset.mem_insert_self _ _
        · exfalso
          obtain ⟨z, hz, hzi⟩ := mem_signs_true.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · rw [lower_apply_self] at hzi; omega
          · rw [hzero z hzs] at hzi; omega
      · refine Finset.mem_insert_of_mem ?_
        cases d
        · obtain ⟨z, hz, hzi⟩ := mem_signs_false.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · exact mem_signs_false.2 ⟨a, ha, by rwa [lower_apply_of_ne _ hij] at hzi⟩
          · exact mem_signs_false.2 ⟨z, hzs, hzi⟩
        · obtain ⟨z, hz, hzi⟩ := mem_signs_true.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · exact mem_signs_true.2 ⟨a, ha, by rwa [lower_apply_of_ne _ hij] at hzi⟩
          · exact mem_signs_true.2 ⟨z, hzs, hzi⟩
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨hmem, fun w hw => ?_⟩
  obtain ⟨hws, ht, hsub⟩ := mem_extensions.1 hw
  have hcardins : (insert w s).card = s.card + 1 := Finset.card_insert_of_notMem hws
  have hdle : (directions (insert w s)).card ≤ (directions s).card + 1 := by
    rw [← ht.card_signs]
    calc (signs (insert w s)).card ≤ (insert ((j, false) : Label n) (signs s)).card :=
          Finset.card_le_card hsub
      _ ≤ (signs s).card + 1 := Finset.card_insert_le _ _
      _ = (directions s).card + 1 := by rw [hs.card_signs]
  have hdge := ht.card_le_card_directions_succ
  have hdeq : (directions (insert w s)).card = (directions s).card + 1 := by omega
  have hwj : w j < 0 := by
    rcases lt_trichotomy (w j) 0 with h | h | h
    · exact h
    · exfalso
      have hsub' : signs (insert w s) ⊆ signs s := by
        intro q hq
        rcases Finset.mem_insert.1 (hsub hq) with heq | hq'
        · exfalso
          subst heq
          obtain ⟨z, hz, hzi⟩ := mem_signs_false.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · omega
          · rw [hzero z hzs] at hzi; omega
        · exact hq'
      have hdsub : directions (insert w s) ⊆ directions s :=
        Finset.image_subset_image hsub'
      have := Finset.card_le_card hdsub
      omega
    · exfalso
      have hq : ((j, true) : Label n) ∈ signs (insert w s) :=
        mem_signs_true.2 ⟨w, Finset.mem_insert_self _ _, h⟩
      rcases Finset.mem_insert.1 (hsub hq) with heq | hq'
      · exact absurd heq (by simp)
      · exact hpos hq'
  have hwa : w < a := by
    have hne : w ≠ a := by
      intro hcon
      rw [hcon] at hwj
      omega
    rcases ht.chain (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem ha) hne with h | h
    · exact lt_of_le_of_ne h hne
    · exact absurd (Pi.le_def.1 h j) (by omega)
  have hbot' : ∀ z ∈ insert w s, w ≤ z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_rfl
    · exact le_trans hwa.le (hbot z hzs)
  have htop' : ∀ z ∈ insert w s, z ≤ b := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_trans hwa.le (htop a ha)
    · exact htop z hzs
  have hstep : (insert w s).card = (step w b).card + 1 :=
    ht.card_eq_card_step_succ (Finset.mem_insert_self _ _) hbot'
      (Finset.mem_insert_of_mem hb) htop' (by omega)
  obtain ⟨i, hi1, hi2⟩ := ht.exists_eq_add_single_bot ha hbot htop hwa hstep
  have hij : i = j := by
    by_contra hcon
    have h := hi2 j fun hjj => hcon hjj.symm
    omega
  subst hij
  refine funext fun j' => ?_
  rcases eq_or_ne j' i with rfl | hne
  · rw [lower_apply_self]; omega
  · rw [lower_apply_of_ne _ hne]; exact hi2 j' hne

/-- **A simplex with one more vertex than it has directions extends in exactly one way when
one further label is allowed.**

This is the shape of a happy simplex whose labels are distinct: it has one label beyond
its signs, and that label decides which end of the chain grows. -/
theorem card_extensions_eq_one (hs : IsSimplex N s) (hN : 0 < N)
    (hcard : s.card = (directions s).card + 1) {l : Label n} (hl : l ∉ signs s)
    (hl' : negLabel l ∉ signs s) : (extensions N s (insert l (signs s))).card = 1 := by
  obtain ⟨j, d⟩ := l
  have hpos : ((j, true) : Label n) ∉ signs s := by
    cases d
    · simpa [negLabel] using hl'
    · exact hl
  have hneg : ((j, false) : Label n) ∉ signs s := by
    cases d
    · exact hl
    · simpa [negLabel] using hl'
  cases d
  · obtain ⟨a, ha, hbot⟩ := hs.exists_bot
    rw [extensions_eq_singleton_lower hs hN hcard ha hbot hpos hneg, Finset.card_singleton]
  · obtain ⟨b, hb, htop⟩ := hs.exists_top
    rw [extensions_eq_singleton_raise hs hN hcard hb htop hpos hneg, Finset.card_singleton]

/-! ### Simplices with as many vertices as directions

The remaining shape.  Such a simplex is one vertex short of filling its chain, and the
missing vertex can be supplied in exactly two ways, unless one coordinate sits at the
boundary of the cube, which blocks one of them. -/

/-- A point has rank zero relative to itself. -/
@[simp]
theorem rank_self (a : Fin n → ℤ) : rank a a = 0 := by
  simp [rank, step]

/-- **A simplex whose total step set spans all of its directions has exactly two extensions
keeping its signs.**

Its ranks miss a single value; the two vertices on either side of the gap differ by two
unit steps, and the new vertex takes one of the two intermediate positions. -/
theorem card_extensions_eq_two_of_full (hs : IsSimplex N s) {a b : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hb : b ∈ s) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (directions s).card) (hfull : (step a b).card = s.card) :
    (extensions N s (signs s)).card = 2 := by
  classical
  -- the ranks of `s` miss exactly one value below `s.card`
  have hrsub : s.image (rank a) ⊆ Finset.range (s.card + 1) := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    refine Finset.mem_range.2 (Nat.lt_succ_of_le ?_)
    rw [← hfull]
    exact Finset.card_le_card (step_subset_step (htop x hx))
  have hrcard : (s.image (rank a)).card = s.card :=
    Finset.card_image_of_injOn (hs.injOn_rank ha hbot)
  have hmiss : (Finset.range (s.card + 1) \ s.image (rank a)).card = 1 := by
    rw [Finset.card_sdiff_of_subset hrsub, Finset.card_range, hrcard]
    omega
  obtain ⟨r, hr⟩ := Finset.card_eq_one.1 hmiss
  have hrmem : r ∈ Finset.range (s.card + 1) ∧ r ∉ s.image (rank a) :=
    Finset.mem_sdiff.1 (by rw [hr]; exact Finset.mem_singleton_self r)
  have hrothers : ∀ c, c ≤ s.card → c ≠ r → ∃ z ∈ s, rank a z = c := by
    intro c hc hcr
    have hcimg : c ∈ s.image (rank a) := by
      by_contra hcon
      have hmem : c ∈ Finset.range (s.card + 1) \ s.image (rank a) :=
        Finset.mem_sdiff.2 ⟨Finset.mem_range.2 (by omega), hcon⟩
      rw [hr] at hmem
      exact hcr (Finset.mem_singleton.1 hmem)
    obtain ⟨z, hz, hzc⟩ := Finset.mem_image.1 hcimg
    exact ⟨z, hz, hzc⟩
  have hr0 : r ≠ 0 := by
    intro h
    exact hrmem.2 (Finset.mem_image.2 ⟨a, ha, by rw [rank_self, h]⟩)
  have hrk : r ≠ s.card := by
    intro h
    exact hrmem.2 (Finset.mem_image.2 ⟨b, hb, by rw [h]; exact hfull⟩)
  have hrlt : r < s.card := by
    have := Finset.mem_range.1 hrmem.1
    omega
  -- the two vertices on either side of the gap
  obtain ⟨x, hx, hxr⟩ := hrothers (r - 1) (by omega) (by omega)
  obtain ⟨y, hy, hyr⟩ := hrothers (r + 1) (by omega) (by omega)
  have hxy : x < y := hs.lt_of_rank_lt ha hbot hx hy (by omega)
  have hcons : ∀ z ∈ s, ¬(x < z ∧ z < y) := by
    rintro z hz ⟨h1, h2⟩
    have h3 := hs.rank_lt_rank ha hbot hx hz h1
    have h4 := hs.rank_lt_rank ha hbot hz hy h2
    exact hrmem.2 (Finset.mem_image.2 ⟨z, hz, by omega⟩)
  -- they differ by two unit steps
  have hstepsub : step a x ⊆ step a y := step_subset_step hxy.le
  have hxc : (step a x).card = r - 1 := hxr
  have hyc : (step a y).card = r + 1 := hyr
  have hdiff : (step a y \ step a x).card = 2 := by
    rw [Finset.card_sdiff_of_subset hstepsub]
    omega
  obtain ⟨p, q, hpq, hpq2⟩ := Finset.card_eq_two.1 hdiff
  have hpmem : p ∈ step a y ∧ p ∉ step a x :=
    Finset.mem_sdiff.1 (by rw [hpq2]; exact Finset.mem_insert_self _ _)
  have hqmem : q ∈ step a y ∧ q ∉ step a x :=
    Finset.mem_sdiff.1 (by rw [hpq2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
  -- each of the two intermediate positions is an extension
  have hcand : ∀ p', p' ∈ step a y → p' ∉ step a x →
      raise x p' ∈ extensions N s (signs s) ∧ step a (raise x p') = insert p' (step a x) := by
    intro p' hp1 hp2
    have hxp : x p' = a p' := by
      have h := hs.eq_add_ite ha hbot hx p'
      rw [ite_eq_right hp2] at h
      omega
    have hyp : y p' = a p' + 1 := by
      have h := hs.eq_add_ite ha hbot hy p'
      rw [ite_eq_left hp1] at h
      omega
    have hle1 : x ≤ raise x p' := le_raise x p'
    have hle2 : raise x p' ≤ y := by
      refine Pi.le_def.2 fun j => ?_
      rcases eq_or_ne j p' with rfl | hne
      · rw [raise_apply_self]; omega
      · rw [raise_apply_of_ne _ hne]; exact Pi.le_def.1 hxy.le j
    have hstep' : step a (raise x p') = insert p' (step a x) := by
      ext j
      rcases eq_or_ne j p' with rfl | hne
      · refine ⟨fun _ => Finset.mem_insert_self _ _, fun _ => ?_⟩
        rw [mem_step, raise_apply_self]
        omega
      · rw [mem_step, raise_apply_of_ne _ hne, Finset.mem_insert]
        simp only [hne, false_or, mem_step]
    refine ⟨mem_extensions.2 ⟨?_, hs.insert_between hx hy hle1 hle2 hcons,
      signs_insert_subset_of_between hx hy hle1 hle2⟩, hstep'⟩
    intro hcon
    have hrank : rank a (raise x p') = r := by
      show (step a (raise x p')).card = r
      rw [hstep', Finset.card_insert_of_notMem hp2]
      omega
    exact hrmem.2 (Finset.mem_image.2 ⟨_, hcon, hrank⟩)
  obtain ⟨hpext, -⟩ := hcand p hpmem.1 hpmem.2
  obtain ⟨hqext, -⟩ := hcand q hqmem.1 hqmem.2
  -- and there are no others
  have hsetf : extensions N s (signs s) = {raise x p, raise x q} := by
    refine Finset.Subset.antisymm (fun w hw => ?_) (fun w hw => ?_)
    · obtain ⟨hws, ht, hsubs⟩ := mem_extensions.1 hw
      have hdle : (directions (insert w s)).card ≤ (step a b).card := by
        rw [← ht.card_signs]
        calc (signs (insert w s)).card ≤ (signs s).card := Finset.card_le_card hsubs
          _ = (directions s).card := hs.card_signs
          _ = (step a b).card := by omega
      obtain ⟨x', hx', y', hy', hx'w, hwy', hcons'⟩ :=
        exists_between_of_insert ht.chain hws ha hb (ht.not_lt_of_insert ha hb htop hdle)
          (ht.not_gt_of_insert ha hb hbot hdle)
      have hbot' : ∀ z ∈ insert w s, a ≤ z := by
        intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hzs
        · exact le_trans (hbot x' hx') hx'w.le
        · exact hbot z hzs
      have htop' : ∀ z ∈ insert w s, z ≤ b := by
        intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hzs
        · exact le_trans hwy'.le (htop y' hy')
        · exact htop z hzs
      -- the rank of the new vertex is the missing one
      have hrw : rank a w = r := by
        have hwle : rank a w ≤ s.card := by
          rw [← hfull]
          exact Finset.card_le_card (step_subset_step (htop' w (Finset.mem_insert_self _ _)))
        by_contra hcon
        obtain ⟨z, hz, hzr⟩ := hrothers (rank a w) hwle hcon
        have hwz : w = z := ht.injOn_rank (Finset.mem_insert_of_mem ha) hbot'
          (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hz) hzr.symm
        exact hws (by rw [hwz]; exact hz)
      have h3 : r < rank a y' := by
        rw [← hrw]
        exact ht.rank_lt_rank (Finset.mem_insert_of_mem ha) hbot'
          (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hy') hwy'
      have h1 : rank a x' < r := by
        rw [← hrw]
        exact ht.rank_lt_rank (Finset.mem_insert_of_mem ha) hbot'
          (Finset.mem_insert_of_mem hx') (Finset.mem_insert_self _ _) hx'w
      -- so the two neighbours are the two vertices on either side of the gap
      have hxx : x' = x := by
        by_contra hcon
        have h2 : rank a x' ≠ r - 1 := fun h =>
          hcon (hs.injOn_rank ha hbot hx' hx (by omega))
        obtain ⟨z, hz, hzr⟩ := hrothers (r - 1) (by omega) (by omega)
        exact hcons' z hz ⟨hs.lt_of_rank_lt ha hbot hx' hz (by omega),
          hs.lt_of_rank_lt ha hbot hz hy' (by omega)⟩
      have hyy : y' = y := by
        by_contra hcon
        have h2 : rank a y' ≠ r + 1 := fun h =>
          hcon (hs.injOn_rank ha hbot hy' hy (by omega))
        obtain ⟨z, hz, hzr⟩ := hrothers (r + 1) (by omega) (by omega)
        exact hcons' z hz ⟨hs.lt_of_rank_lt ha hbot hx' hz (by omega),
          hs.lt_of_rank_lt ha hbot hz hy' (by omega)⟩
      subst hxx
      subst hyy
      -- the new vertex adds exactly one of the two coordinates
      have hsub1 : step a x' ⊆ step a w := step_subset_step hx'w.le
      have hsub2 : step a w ⊆ step a y' := step_subset_step hwy'.le
      obtain ⟨i, hi1, hi2⟩ := Finset.exists_eq_insert_iff.2
        ⟨hsub1, show (step a x').card + 1 = (step a w).card by
          have : (step a w).card = r := hrw
          omega⟩
      have hiw : i ∈ step a w := by rw [← hi2]; exact Finset.mem_insert_self _ _
      have hi3 : i ∈ step a y' \ step a x' := Finset.mem_sdiff.2 ⟨hsub2 hiw, hi1⟩
      rw [hpq2] at hi3
      have hweq : w = raise x' i := by
        refine funext fun j => ?_
        have hwj := ht.eq_add_ite (Finset.mem_insert_of_mem ha) hbot'
          (Finset.mem_insert_self _ _) j
        have hxj := hs.eq_add_ite ha hbot hx' j
        rcases eq_or_ne j i with rfl | hne
        · rw [raise_apply_self, hwj, hxj, ite_eq_left hiw, ite_eq_right hi1]
          omega
        · rw [raise_apply_of_ne _ hne, hwj, hxj]
          have hiff : j ∈ step a w ↔ j ∈ step a x' := by
            rw [← hi2]
            simp only [Finset.mem_insert, hne, false_or]
          by_cases hj : j ∈ step a x'
          · rw [ite_eq_left (hiff.2 hj), ite_eq_left hj]
          · rw [ite_eq_right fun h => hj (hiff.1 h), ite_eq_right hj]
      rcases Finset.mem_insert.1 hi3 with rfl | hi4
      · rw [hweq]; exact Finset.mem_insert_self _ _
      · rw [Finset.mem_singleton] at hi4
        subst hi4
        rw [hweq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · rcases Finset.mem_insert.1 hw with rfl | hw'
      · exact hpext
      · rw [Finset.mem_singleton] at hw'
        subst hw'
        exact hqext
  rw [hsetf, Finset.card_insert_of_notMem (by simpa using raise_ne_raise hpq),
    Finset.card_singleton]

/-- A saturated simplex with as many vertices as directions has exactly one constant
direction, and it is nonzero there. -/
theorem exists_const_direction {a b : Fin n → ℤ}
    (hbot : ∀ z ∈ s, a ≤ z) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (directions s).card) (hsat : s.card = (step a b).card + 1)
    (hsub : step a b ⊆ directions s) :
    ∃ c, (∀ i, i ∈ directions s → i ∉ step a b → i = c) ∧ (∀ z ∈ s, z c = a c) ∧
      a c ≠ 0 := by
  have hcs : (directions s \ step a b).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  obtain ⟨c, hc⟩ := Finset.card_eq_one.1 hcs
  obtain ⟨hcd, hcstep⟩ : c ∈ directions s ∧ c ∉ step a b :=
    Finset.mem_sdiff.1 (by rw [hc]; exact Finset.mem_singleton_self c)
  refine ⟨c, ?_, const_of_not_mem_step hbot htop hcstep, ?_⟩
  · intro i hi1 hi2
    have hmem : i ∈ directions s \ step a b := Finset.mem_sdiff.2 ⟨hi1, hi2⟩
    rw [hc] at hmem
    exact Finset.mem_singleton.1 hmem
  · obtain ⟨z, hz, hzc⟩ := mem_directions.1 hcd
    rwa [const_of_not_mem_step hbot htop hcstep z hz] at hzc

/-- Lowering the constant direction below the least vertex is an extension. -/
theorem lower_mem_extensions (hs : IsSimplex N s) {a : Fin n → ℤ} {c : Fin n} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hconst : ∀ z ∈ s, z c = a c) (hne : a c ≠ 0)
    (hgrid : -(N : ℤ) ≤ a c - 1) : lower a c ∈ extensions N s (signs s) := by
  refine mem_extensions.2 ⟨?_, hs.insert_lower ha hbot hconst hgrid,
    signs_insert_lower_subset ha hconst hne⟩
  intro hcon
  have h := hconst _ hcon
  rw [lower_apply_self] at h
  omega

/-- Raising the constant direction above the greatest vertex is an extension. -/
theorem raise_mem_extensions (hs : IsSimplex N s) {b : Fin n → ℤ} {c : Fin n} (hb : b ∈ s)
    (htop : ∀ z ∈ s, z ≤ b) (hconst : ∀ z ∈ s, z c = b c) (hne : b c ≠ 0)
    (hgrid : b c + 1 ≤ (N : ℤ)) : raise b c ∈ extensions N s (signs s) := by
  refine mem_extensions.2 ⟨?_, hs.insert_raise hb htop hconst hgrid,
    signs_insert_raise_subset hb hconst hne⟩
  intro hcon
  have h := hconst _ hcon
  rw [raise_apply_self] at h
  omega

/-- **A saturated simplex with as many vertices as directions extends only at the two ends
of its chain, in its one constant direction.** -/
theorem extensions_subset_of_saturated (hs : IsSimplex N s) {a b : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hb : b ∈ s) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (directions s).card) (hsat : s.card = (step a b).card + 1)
    {c : Fin n} (huniq : ∀ i, i ∈ directions s → i ∉ step a b → i = c) :
    extensions N s (signs s) ⊆ {lower a c, raise b c} := by
  intro w hw
  obtain ⟨hws, ht, hsubs⟩ := mem_extensions.1 hw
  have hdle : (directions (insert w s)).card ≤ (step a b).card + 1 := by
    rw [← ht.card_signs]
    calc (signs (insert w s)).card ≤ (signs s).card := Finset.card_le_card hsubs
      _ = (directions s).card := hs.card_signs
      _ = (step a b).card + 1 := by omega
  have hcardins : (insert w s).card = s.card + 1 := Finset.card_insert_of_notMem hws
  -- the new vertex lies below the least or above the greatest one
  have hpos : w < a ∨ b < w := by
    by_cases h1 : w < a
    · exact Or.inl h1
    by_cases h2 : b < w
    · exact Or.inr h2
    exfalso
    obtain ⟨x, hx, y, hy, hxw, hwy, -⟩ :=
      exists_between_of_insert ht.chain hws ha hb h1 h2
    exact ht.not_between_of_saturated ha hbot htop hws
      (le_trans (hbot x hx) hxw.le) (le_trans hwy.le (htop y hy)) hsat
  rcases hpos with hwa | hbw
  · have hbot' : ∀ z ∈ insert w s, w ≤ z := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hzs
      · exact le_rfl
      · exact le_of_lt (lt_of_lt_of_le hwa (hbot z hzs))
    have htop' : ∀ z ∈ insert w s, z ≤ b := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hzs
      · exact le_trans hwa.le (htop a ha)
      · exact htop z hzs
    have hstepw : (insert w s).card = (step w b).card + 1 := by
      have h1 : step a b ⊆ step w b := step_subset_step_base hwa.le
      have h2 : (step w b).card ≤ (directions (insert w s)).card :=
        Finset.card_le_card (step_subset_directions (Finset.mem_insert_self _ _)
          (Finset.mem_insert_of_mem hb))
      have h3 := ht.card_le_card_step_succ (Finset.mem_insert_self _ _) hbot' htop'
      have h4 := Finset.card_le_card h1
      omega
    obtain ⟨i, hi1, hi2⟩ := ht.exists_eq_add_single_bot ha hbot htop hwa hstepw
    have hconsti : ∀ z ∈ s, z i = a i := ht.const_of_insert_bot hbot hi1
    have hai : a i ≠ 0 := by
      intro h0
      have hmem : ((i, false) : Label n) ∈ signs (insert w s) :=
        mem_signs_false.2 ⟨w, Finset.mem_insert_self _ _, by omega⟩
      obtain ⟨z, hz, hzi⟩ := mem_signs_false.1 (hsubs hmem)
      rw [hconsti z hz] at hzi
      omega
    have hic : i = c := by
      refine huniq i (mem_directions.2 ⟨a, ha, hai⟩) ?_
      simp only [mem_step]
      have := hconsti b hb
      omega
    subst hic
    have hweq : w = lower a i := by
      refine funext fun j => ?_
      rcases eq_or_ne j i with rfl | hne
      · rw [lower_apply_self]; omega
      · rw [lower_apply_of_ne _ hne]; exact hi2 j hne
    rw [hweq]
    exact Finset.mem_insert_self _ _
  · have hbot' : ∀ z ∈ insert w s, a ≤ z := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hzs
      · exact le_trans (hbot b hb) hbw.le
      · exact hbot z hzs
    have htop' : ∀ z ∈ insert w s, z ≤ w := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hzs
      · exact le_rfl
      · exact le_trans (htop z hzs) hbw.le
    have hstepw : (insert w s).card = (step a w).card + 1 := by
      have h1 : step a b ⊆ step a w := step_subset_step hbw.le
      have h2 : (step a w).card ≤ (directions (insert w s)).card :=
        Finset.card_le_card (step_subset_directions (Finset.mem_insert_of_mem ha)
          (Finset.mem_insert_self _ _))
      have h3 := ht.card_le_card_step_succ (Finset.mem_insert_of_mem ha) hbot' htop'
      have h4 := Finset.card_le_card h1
      omega
    obtain ⟨i, hi1, hi2⟩ := ht.exists_eq_top_add_single ha hbot hb htop hbw hstepw
    have hconsti : ∀ z ∈ s, z i = b i := ht.const_of_insert_top htop hi1
    have hbi : b i ≠ 0 := by
      intro h0
      have hmem : ((i, true) : Label n) ∈ signs (insert w s) :=
        mem_signs_true.2 ⟨w, Finset.mem_insert_self _ _, by omega⟩
      obtain ⟨z, hz, hzi⟩ := mem_signs_true.1 (hsubs hmem)
      rw [hconsti z hz] at hzi
      omega
    have hic : i = c := by
      refine huniq i (mem_directions.2 ⟨b, hb, hbi⟩) ?_
      simp only [mem_step]
      have := hconsti a ha
      omega
    subst hic
    have hweq : w = raise b i := by
      refine funext fun j => ?_
      rcases eq_or_ne j i with rfl | hne
      · rw [raise_apply_self]; omega
      · rw [raise_apply_of_ne _ hne]; exact (hi2 j hne).symm
    rw [hweq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- **A simplex with as many vertices as directions and no extremal coordinate has exactly
two extensions keeping its signs.** -/
theorem card_extensions_eq_two (hs : IsSimplex N s)
    (hcard : s.card = (directions s).card) (hext : ¬ IsExtremal N s) :
    (extensions N s (signs s)).card = 2 := by
  obtain ⟨a, ha, hbot⟩ := hs.exists_bot
  obtain ⟨b, hb, htop⟩ := hs.exists_top
  have hsub : step a b ⊆ directions s := step_subset_directions ha hb
  have hle : s.card ≤ (step a b).card + 1 := hs.card_le_card_step_succ ha hbot htop
  have hle2 : (step a b).card ≤ (directions s).card := Finset.card_le_card hsub
  rcases eq_or_lt_of_le hle2 with heq | hlt
  · exact card_extensions_eq_two_of_full hs ha hbot hb htop hcard (by omega)
  · have hsat : s.card = (step a b).card + 1 := by omega
    obtain ⟨c, huniq, hconst, hne⟩ :=
      exists_const_direction hbot htop hcard hsat hsub
    have hgrid := mem_grid.1 (hs.subset_grid ha) c
    have hbc : b c = a c := hconst b hb
    have hcN : a c ≠ (N : ℤ) := fun h =>
      hext ⟨c, Or.inl fun z hz => by rw [hconst z hz, h]⟩
    have hcN' : a c ≠ -(N : ℤ) := fun h =>
      hext ⟨c, Or.inr fun z hz => by rw [hconst z hz, h]⟩
    have h1 : lower a c ∈ extensions N s (signs s) :=
      lower_mem_extensions hs ha hbot hconst hne (by omega)
    have h2 : raise b c ∈ extensions N s (signs s) :=
      raise_mem_extensions hs hb htop (fun z hz => by rw [hconst z hz, hbc]) (by omega)
        (by omega)
    have hset : extensions N s (signs s) = {lower a c, raise b c} :=
      Finset.Subset.antisymm
        (extensions_subset_of_saturated hs ha hbot hb htop hcard hsat huniq) (by
          intro w hw
          rcases Finset.mem_insert.1 hw with rfl | hw'
          · exact h1
          · rw [Finset.mem_singleton] at hw'
            subst hw'
            exact h2)
    have hne2 : lower a c ∉ ({raise b c} : Finset (Fin n → ℤ)) := by
      simp only [Finset.mem_singleton]
      intro hcon
      have h := congrFun hcon c
      rw [lower_apply_self, raise_apply_self, hbc] at h
      omega
    rw [hset, Finset.card_insert_of_notMem hne2, Finset.card_singleton]

/-- **A simplex with as many vertices as directions and one extremal coordinate has exactly
one extension keeping its signs.**  The cube blocks the other one. -/
theorem card_extensions_eq_one_of_isExtremal (hs : IsSimplex N s) (hN : 0 < N)
    (hcard : s.card = (directions s).card) (hext : IsExtremal N s) :
    (extensions N s (signs s)).card = 1 := by
  obtain ⟨a, ha, hbot⟩ := hs.exists_bot
  obtain ⟨b, hb, htop⟩ := hs.exists_top
  obtain ⟨d, hd⟩ := hext
  have hN' : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hsub : step a b ⊆ directions s := step_subset_directions ha hb
  have hle : s.card ≤ (step a b).card + 1 := hs.card_le_card_step_succ ha hbot htop
  have hle2 : (step a b).card ≤ (directions s).card := Finset.card_le_card hsub
  have hda : a d = (N : ℤ) ∨ a d = -(N : ℤ) := by
    rcases hd with h | h
    · exact Or.inl (h a ha)
    · exact Or.inr (h a ha)
  have hdb : b d = a d := by
    rcases hd with h | h
    · rw [h a ha, h b hb]
    · rw [h a ha, h b hb]
  have hdd : d ∈ directions s := mem_directions.2 ⟨a, ha, by omega⟩
  have hds : d ∉ step a b := by
    simp only [mem_step]
    omega
  have hlt : (step a b).card < (directions s).card :=
    lt_of_le_of_ne hle2 fun hcon => hds (by
      rw [Finset.eq_of_subset_of_card_le hsub (le_of_eq hcon.symm)]
      exact hdd)
  have hsat : s.card = (step a b).card + 1 := by omega
  obtain ⟨c, huniq, hconst, hne⟩ := exists_const_direction hbot htop hcard hsat hsub
  have hdc : d = c := huniq d hdd hds
  subst hdc
  have hgrid := mem_grid.1 (hs.subset_grid ha) d
  have hsubset := extensions_subset_of_saturated hs ha hbot hb htop hcard hsat huniq
  rcases hda with hac | hac
  · -- the coordinate sits at `N`, so only lowering it is possible
    have h1 : lower a d ∈ extensions N s (signs s) :=
      lower_mem_extensions hs ha hbot hconst hne (by omega)
    have h2 : raise b d ∉ extensions N s (signs s) := by
      intro hcon
      obtain ⟨-, ht, -⟩ := mem_extensions.1 hcon
      have h := mem_grid.1 (ht.subset_grid (Finset.mem_insert_self _ _)) d
      rw [raise_apply_self] at h
      omega
    refine Finset.card_eq_one.2 ⟨lower a d, Finset.Subset.antisymm (fun w hw => ?_)
      (fun w hw => ?_)⟩
    · rcases Finset.mem_insert.1 (hsubset hw) with heq | heq
      · rw [heq]
        exact Finset.mem_singleton_self _
      · rw [Finset.mem_singleton] at heq
        subst heq
        exact absurd hw h2
    · rw [Finset.mem_singleton] at hw
      subst hw
      exact h1
  · -- the coordinate sits at `-N`, so only raising it is possible
    have h1 : raise b d ∈ extensions N s (signs s) :=
      raise_mem_extensions hs hb htop (fun z hz => by rw [hconst z hz, hdb]) (by omega)
        (by omega)
    have h2 : lower a d ∉ extensions N s (signs s) := by
      intro hcon
      obtain ⟨-, ht, -⟩ := mem_extensions.1 hcon
      have h := mem_grid.1 (ht.subset_grid (Finset.mem_insert_self _ _)) d
      rw [lower_apply_self] at h
      omega
    refine Finset.card_eq_one.2 ⟨raise b d, Finset.Subset.antisymm (fun w hw => ?_)
      (fun w hw => ?_)⟩
    · rcases Finset.mem_insert.1 (hsubset hw) with heq | heq
      · subst heq
        exact absurd hw h2
      · rw [Finset.mem_singleton] at heq
        rw [heq]
        exact Finset.mem_singleton_self _
    · rw [Finset.mem_singleton] at hw
      subst hw
      exact h1

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

/-- Reflection preserves the directions, since reversing a label keeps its coordinate. -/
theorem directions_neg (s : Finset (Fin n → ℤ)) : directions (-s) = directions s := by
  rw [directions, directions, signs_neg, Finset.image_image]
  exact Finset.image_congr fun p _ => negLabel_fst p

end GridSimplex

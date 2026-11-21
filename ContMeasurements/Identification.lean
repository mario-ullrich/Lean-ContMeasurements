/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import BasicResults.ColoredCover
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.Monoid

/-!
# Identifying a piece with a single measurement

Once the color `r` of the piece containing `x` is known, one further continuous
measurement pins down the piece itself.  The pieces of color `r` are `c`-separated,
so a *single* continuous functional can take a different constant value near each of
them without ever having to interpolate between two of them.

Concretely, write `Aᵢ` for the pieces of the cover, number those of color `r` by
natural numbers `e i` (possible because the index set is countable) and set
`λ(x) = Σᶠ i  (e i + 1) · φ(dist(x, Aᵢ))`,
where `φ` is a continuous collar function that equals `1` up to distance `c/8` and
vanishes from distance `c/4` on.  Near any point at most one summand is nonzero, since
two would put two pieces of the same color closer than `c`, so the sum is locally finite
and hence continuous, and its value at a point within `c/8` of the piece `i` is
exactly `e i + 1`.

The value is an **integer**, which is what makes the last trick of the upper bound
work: an extra coordinate can be smuggled into the fractional part of this
measurement, see `UpperBound.lean`.

## Main results

* `ContMeasurements.identify`: the functional itself, a locally finite sum.
* `ContMeasurements.exists_identification`: the functional and its decoder.
-/

@[expose] public section

open Metric Set

namespace ContMeasurements

/-! ### The collar function -/

/-- A continuous collar: `1` on `[0, c/8]`, `0` from `c/4` on, values in `[0,1]`. -/
noncomputable def collar (c s : ℝ) : ℝ := max 0 (min 1 (2 - 8 * s / c))

/-- The collar function is continuous. -/
theorem continuous_collar (c : ℝ) : Continuous (collar c) :=
  continuous_const.max (continuous_const.min
    (continuous_const.sub ((continuous_const.mul continuous_id).div_const c)))

/-- The collar equals `1` up to distance `c/8`. -/
theorem collar_eq_one {c s : ℝ} (hc : 0 < c) (hs : s ≤ c / 8) : collar c s = 1 := by
  have h8 : 8 * s / c ≤ 1 := by
    rw [div_le_one hc]
    linarith
  have h : (1 : ℝ) ≤ 2 - 8 * s / c := by linarith
  rw [collar, min_eq_left h, max_eq_right zero_le_one]

/-- The collar vanishes from distance `c/4` on. -/
theorem collar_eq_zero {c s : ℝ} (hc : 0 < c) (hs : c / 4 ≤ s) : collar c s = 0 := by
  have h8 : (2 : ℝ) ≤ 8 * s / c := by
    rw [le_div_iff₀ hc]
    linarith
  have h : 2 - 8 * s / c ≤ 0 := by linarith
  rw [collar, max_eq_left (le_trans (min_le_right _ _) h)]

/-- The only way the collar can be nonzero is close to the set. -/
theorem lt_of_collar_ne_zero {c s : ℝ} (hc : 0 < c) (h : collar c s ≠ 0) : s < c / 4 := by
  by_contra hs
  exact h (collar_eq_zero hc (not_lt.1 hs))

/-! ### The identification functional -/

variable {X : Type*} [PseudoMetricSpace X] {ι : Type*} {K : ℕ} {ε c : ℝ}

open Classical in
/-- The contribution of the piece `i` to the identification functional: the label
`e i + 1` damped by the collar, and `0` unless the piece is nonempty and has the
color under consideration.

The nonemptiness guard matters: `Metric.infDist x ∅ = 0`, so without it an empty
piece would contribute its full label everywhere. -/
noncomputable def identifyTerm (cc : ColoredCover X ι K ε c) (r : Fin K) (e : ι → ℕ) (i : ι)
    (x : X) : ℝ :=
  if cc.color i = r ∧ (cc.piece i).Nonempty then
    ((e i : ℝ) + 1) * collar c (Metric.infDist x (cc.piece i))
  else 0

/-- The **identification functional** of the color `r`. -/
noncomputable def identify (cc : ColoredCover X ι K ε c) (r : Fin K) (e : ι → ℕ)
    (x : X) : ℝ :=
  ∑ᶠ i, identifyTerm cc r e i x

open Classical in
/-- The decoder: from the value `n = e i + 1` of the identification functional it
returns some point of the piece `i`. -/
noncomputable def decodePoint [Nonempty X] (cc : ColoredCover X ι K ε c) (r : Fin K)
    (e : ι → ℕ) (n : ℤ) : X :=
  if h : ∃ y : X, ∃ i, cc.color i = r ∧ y ∈ cc.piece i ∧ (e i : ℤ) + 1 = n then h.choose
  else Classical.arbitrary X

/-- The decoder applied to the label of a nonempty piece returns a point of that piece. -/
theorem decodePoint_mem [Nonempty X] {cc : ColoredCover X ι K ε c} {r : Fin K}
    {e : ι → ℕ} (he : Function.Injective e) {i : ι} (hi : cc.color i = r) {p : X}
    (hp : p ∈ cc.piece i) : decodePoint cc r e ((e i : ℤ) + 1) ∈ cc.piece i := by
  classical
  have h : ∃ y : X, ∃ i', cc.color i' = r ∧ y ∈ cc.piece i' ∧
      (e i' : ℤ) + 1 = (e i : ℤ) + 1 :=
    ⟨p, i, hi, hp, rfl⟩
  rw [decodePoint, dite_eq_left h]
  obtain ⟨i', hi', hmem', hn'⟩ := h.choose_spec
  have hii : i' = i := he (by omega)
  subst hii
  exact hmem'

section Functional

variable {cc : ColoredCover X ι K ε c} {r : Fin K} {e : ι → ℕ}

/-- Each term of the sum is continuous. -/
theorem continuous_identifyTerm (i : ι) : Continuous (identifyTerm cc r e i) := by
  classical
  unfold identifyTerm
  by_cases h : cc.color i = r ∧ (cc.piece i).Nonempty
  · simp only [ite_eq_left h]
    exact continuous_const.mul ((continuous_collar c).comp (Metric.continuous_infDist_pt _))
  · simp only [ite_eq_right h]
    exact continuous_const

/-- If the term of a piece is nonzero somewhere in a small ball, the piece comes
close to the centre of that ball. -/
theorem exists_mem_of_identifyTerm_ne_zero (hc : 0 < c) {i : ι} {x₀ z : X}
    (hz : dist x₀ z < c / 8) (hw : identifyTerm cc r e i z ≠ 0) :
    cc.color i = r ∧ ∃ p ∈ cc.piece i, dist x₀ p < 3 * c / 8 := by
  classical
  unfold identifyTerm at hw
  by_cases h : cc.color i = r ∧ (cc.piece i).Nonempty
  · rw [ite_eq_left h] at hw
    have hcol : collar c (Metric.infDist z (cc.piece i)) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hw
      exact hw rfl
    obtain ⟨p, hp, hzp⟩ :=
      (Metric.infDist_lt_iff h.2).1 (lt_of_collar_ne_zero hc hcol)
    exact ⟨h.1, p, hp, by
      have := dist_triangle x₀ z p
      linarith⟩
  · rw [ite_eq_right h] at hw
    exact absurd rfl hw

/-- Near any point, at most one piece of the color `r` contributes a nonzero term:
two of them would be closer than the separation constant `c`. -/
theorem locallyFinite_identifyTerm (hc : 0 < c) :
    LocallyFinite fun i => Function.support (identifyTerm cc r e i) := by
  intro x₀
  refine ⟨Metric.ball x₀ (c / 8), Metric.ball_mem_nhds _ (by positivity), ?_⟩
  refine Set.Subsingleton.finite ?_
  rintro i ⟨z, hzs, hzb⟩ j ⟨z', hzs', hzb'⟩
  by_contra hij
  obtain ⟨hti, p, hp, hxp⟩ :=
    exists_mem_of_identifyTerm_ne_zero hc (Metric.mem_ball'.1 hzb) hzs
  obtain ⟨htj, q, hq, hxq⟩ :=
    exists_mem_of_identifyTerm_ne_zero hc (Metric.mem_ball'.1 hzb') hzs'
  have hsep := cc.le_dist_of_color_eq i j hij (hti.trans htj.symm) p hp q hq
  have := dist_triangle p x₀ q
  rw [dist_comm p x₀] at this
  linarith

/-- The identification functional is continuous: a locally finite sum of continuous
terms. -/
theorem continuous_identify (hc : 0 < c) : Continuous (identify cc r e) := by
  unfold identify
  exact continuous_finsum (fun i => continuous_identifyTerm i) (locallyFinite_identifyTerm hc)

/-- **The value of the identification functional.**  At a point within `c/8` of the
piece `i` of color `r`, the functional takes the value `e i + 1`; every other piece
of the same color is too far away to contribute. -/
theorem identify_eq (hc : 0 < c) {i : ι} (hi : cc.color i = r) {x p : X} (hp : p ∈ cc.piece i)
    (hxp : dist x p < c / 8) : identify cc r e x = (e i : ℝ) + 1 := by
  classical
  have hne : (cc.piece i).Nonempty := ⟨p, hp⟩
  have hzero : ∀ j, j ≠ i → identifyTerm cc r e j x = 0 := by
    intro j hji
    by_contra hw
    obtain ⟨htj, q, hq, hxq⟩ :=
      exists_mem_of_identifyTerm_ne_zero hc (by rw [dist_self]; positivity) hw
    have hsep := cc.le_dist_of_color_eq i j (Ne.symm hji) (hi.trans htj.symm) p hp q hq
    have := dist_triangle p x q
    rw [dist_comm p x] at this
    linarith
  rw [identify, finsum_eq_single _ i hzero, identifyTerm, ite_eq_left ⟨hi, hne⟩,
    collar_eq_one hc (le_of_lt (lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hp) hxp)),
    mul_one]

end Functional

/-- **The identification measurement.**

For every color `r` there is a continuous functional whose value on the closure of
the set of points of color `r` is an integer, together with a decoder turning that
integer into a point at distance at most `ε + c/8` from the measured point.

The functional is one measurement, and it is what the bisection over colors hands
over to. -/
theorem exists_identification [Nonempty X] [Countable ι] (cc : ColoredCover X ι K ε c)
    (hc : 0 < c) (r : Fin K) :
    ∃ (fct : X → ℝ) (dec : ℤ → X), Continuous fct ∧
      ∀ x ∈ closure (cc.colorClass r),
        ∃ n : ℤ, fct x = (n : ℝ) ∧ dist x (dec n) ≤ ε + c / 8 := by
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  refine ⟨identify cc r e, decodePoint cc r e, continuous_identify hc, ?_⟩
  intro x hx
  -- The point is within `c/8` of some piece of color `r`.
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (c / 8) (by positivity)
  obtain ⟨i, hi, hyi⟩ := hy
  refine ⟨(e i : ℤ) + 1, ?_, ?_⟩
  · rw [identify_eq hc hi hyi hxy]
    push_cast
    ring
  · -- The decoder returns a point of the same piece, of diameter at most `ε`.
    have hmem := decodePoint_mem (cc := cc) (r := r) he hi hyi
    have hdiam := cc.dist_le_of_mem i _ hyi _ hmem
    have := dist_triangle x y (decodePoint cc r e ((e i : ℤ) + 1))
    linarith

end ContMeasurements

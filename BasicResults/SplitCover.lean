/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Algebra.Group.EvenFunction

/-!
# Split sets and split covers

Throughout, `E` is a real normed space and the sets considered are **symmetric**,
that is, invariant under `x ↦ -x`.

A closed symmetric set `A` is called *split* if it decomposes as `A = A⁺ ∪ A⁻` with
`A⁺, A⁻` closed, disjoint, and exchanged by `x ↦ -x`.  On a split set one can name a
"sign" telling `x` from `-x` consistently, and by compactness the two halves are then
a positive distance apart.

Since `A⁻` is determined by `A⁺` as `-A⁺`, a split set is recorded here by its
positive half alone:

> a set `P` with `P` closed and `Disjoint P (-P)`; the split set it describes is
> `P ∪ -P`.

`HasSplitCover K k` says that `K` is covered by `k` such split sets.  This is the
covering form of the Krasnosel'skiĭ genus, and it is the quantity that one adaptive
continuous measurement can at most double (plus one); see `Halving.lean` and
`LowerBound.lean`.

## Main results

* `hasSplitCover_one_of_odd_ne_zero` — a closed symmetric set on which a continuous
  odd function has no zero is a single split set.  This is both the case `n = 1` of
  the induction and the "sign region of the odd part" contributed by each measurement.
* `HasSplitCover.biUnion_of_pairwise_disjoint` — pairwise disjoint compact symmetric
  pieces, each covered by `h` split sets, together need only `h` split sets: the
  pieces may **share** their sign regions.  This is where the factor `2` of the
  recursion `c(n) = 2 c(n-1) + 1` comes from, and nothing better is possible.
* `HasSplitCover.exists_cthickening` — a split cover of a compact symmetric set
  extends to a split cover of a closed neighbourhood of it.
* `HasSplitCover.exists_odd_continuous_ne_zero` — a cover by `k` split sets yields a
  continuous odd map into `ℝᵏ` without zeros on the covered set, via the sign
  functions `σ(x) = dist(x, P⁻) - dist(x, P⁺)`.  Feeding this into the Borsuk–Ulam
  theorem is the last step of the lower bound.
-/

open Metric Set

variable {E : Type*} [NormedAddCommGroup E]

/-- Finitely many positive numbers have a positive lower bound.  The empty family is
allowed, and then the bound is vacuous. -/
theorem exists_pos_forall_le_of_forall_pos {ι : Type*} [Finite ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ r > 0, ∀ i, r ≤ f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => (hι.false i).elim⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
    exact ⟨f i₀, hf i₀, hi₀⟩

/-- The positive half of a split set: a closed set disjoint from its own reflection.
The split set it describes is `P ∪ -P`, and a "sign" is available on it, namely `+`
on `P` and `-` on `-P`. -/
def IsSplitHalf (P : Set E) : Prop := IsClosed P ∧ Disjoint P (-P)

/-- `HasSplitCover K k` : the set `K` can be covered by `k` split sets, each given by
its positive half `P i`. -/
def HasSplitCover (K : Set E) (k : ℕ) : Prop :=
  ∃ P : Fin k → Set E, (∀ i, IsSplitHalf (P i)) ∧ K ⊆ ⋃ i, (P i ∪ -(P i))

/-- The empty set is covered by any number of split sets. -/
theorem hasSplitCover_empty (k : ℕ) : HasSplitCover (∅ : Set E) k :=
  ⟨fun _ => ∅, fun _ => ⟨isClosed_empty, by simp⟩, by simp⟩

namespace HasSplitCover

/-- A split cover of a set is a split cover of every subset. -/
theorem mono {K K' : Set E} {k : ℕ} (h : HasSplitCover K k) (hKK : K' ⊆ K) :
    HasSplitCover K' k := by
  obtain ⟨P, hP, hcov⟩ := h
  exact ⟨P, hP, hKK.trans hcov⟩

/-- Two split covers combine into one of the union, with the numbers added. -/
theorem union {K K' : Set E} {k l : ℕ} (h : HasSplitCover K k) (h' : HasSplitCover K' l) :
    HasSplitCover (K ∪ K') (k + l) := by
  obtain ⟨P, hP, hcov⟩ := h
  obtain ⟨Q, hQ, hcov'⟩ := h'
  refine ⟨Fin.append P Q, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hP i
    · rw [Fin.append_right]; exact hQ i
  · rintro x (hx | hx)
    · obtain ⟨-, ⟨i, rfl⟩, hxi⟩ := hcov hx
      exact mem_iUnion.2 ⟨Fin.castAdd l i, by rwa [Fin.append_left]⟩
    · obtain ⟨-, ⟨i, rfl⟩, hxi⟩ := hcov' hx
      exact mem_iUnion.2 ⟨Fin.natAdd k i, by rwa [Fin.append_right]⟩

/-- More split sets are never worse: pad the family with empty sets. -/
theorem of_le {K : Set E} {k l : ℕ} (hkl : k ≤ l) (h : HasSplitCover K k) :
    HasSplitCover K l := by
  have hu := h.union (hasSplitCover_empty (E := E) (l - k))
  rwa [Set.union_empty, Nat.add_sub_cancel' hkl] at hu

/-- Normalisation: on a compact symmetric set the halves of a split cover may be
taken compact and contained in the set. -/
theorem exists_isCompact_halves {K : Set E} {k : ℕ} (hK : IsCompact K)
    (hKs : ∀ x ∈ K, -x ∈ K) (h : HasSplitCover K k) :
    ∃ P : Fin k → Set E, (∀ i, IsCompact (P i) ∧ P i ⊆ K ∧ Disjoint (P i) (-(P i)))
      ∧ K ⊆ ⋃ i, (P i ∪ -(P i)) := by
  obtain ⟨P, hP, hcov⟩ := h
  refine ⟨fun i => K ∩ P i, fun i => ⟨hK.inter_right (hP i).1, inter_subset_left, ?_⟩, ?_⟩
  · exact Disjoint.mono inter_subset_right (fun x hx => (Set.mem_neg.1 hx).2) (hP i).2
  · intro x hx
    obtain ⟨-, ⟨i, rfl⟩, hxi⟩ := hcov hx
    refine mem_iUnion.2 ⟨i, ?_⟩
    rcases hxi with hxi | hxi
    · exact Or.inl ⟨hx, hxi⟩
    · exact Or.inr (Set.mem_neg.2 ⟨hKs x hx, Set.mem_neg.1 hxi⟩)

/-- **Pairwise disjoint pieces share their split sets.**

If compact symmetric sets `Z j` are pairwise disjoint and each is covered by `h`
split sets, then their union is covered by `h` split sets, not by `h` times the
number of pieces.  The `i`-th split set of the union is the union of the `i`-th split
sets of the pieces; it is again split because a point and its reflection lie in the
same piece.

Applied to the slabs of a measurement's level sets, this is exactly the step that
costs only a factor `2` (odd-numbered slabs and even-numbered slabs each form a
disjoint family). -/
theorem biUnion_of_pairwise_disjoint {ι : Type*} {s : Finset ι} {Z : ι → Set E} {h : ℕ}
    (hZc : ∀ j ∈ s, IsCompact (Z j)) (hZs : ∀ j ∈ s, ∀ x ∈ Z j, -x ∈ Z j)
    (hZd : ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → Disjoint (Z j) (Z j'))
    (hZ : ∀ j ∈ s, HasSplitCover (Z j) h) : HasSplitCover (⋃ j ∈ s, Z j) h := by
  classical
  -- Normalised halves for every index, taken empty outside `s`.
  have hall : ∀ j : ι, ∃ P : Fin h → Set E,
      (∀ i, IsCompact (P i) ∧ (j ∈ s → P i ⊆ Z j) ∧ Disjoint (P i) (-(P i)))
        ∧ (j ∈ s → Z j ⊆ ⋃ i, (P i ∪ -(P i))) := by
    intro j
    by_cases hj : j ∈ s
    · obtain ⟨P, hP, hcov⟩ := exists_isCompact_halves (hZc j hj) (hZs j hj) (hZ j hj)
      exact ⟨P, fun i => ⟨(hP i).1, fun _ => (hP i).2.1, (hP i).2.2⟩, fun _ => hcov⟩
    · exact ⟨fun _ => ∅, fun i => ⟨isCompact_empty, fun hj' => absurd hj' hj, by simp⟩,
        fun hj' => absurd hj' hj⟩
  choose P hP hcov using hall
  refine ⟨fun i => ⋃ j ∈ s, P j i, fun i => ⟨?_, ?_⟩, ?_⟩
  · exact s.finite_toSet.isClosed_biUnion fun j _ => (hP j i).1.isClosed
  · rw [Set.disjoint_left]
    rintro x hx hxneg
    obtain ⟨-, ⟨j, rfl⟩, -, ⟨hjs, rfl⟩, hxj⟩ := hx
    obtain ⟨-, ⟨j', rfl⟩, -, ⟨hjs', rfl⟩, hxj'⟩ := Set.mem_neg.1 hxneg
    have hxZ : x ∈ Z j := (hP j i).2.1 hjs hxj
    have hxZ' : x ∈ Z j' := by
      have hnx : -x ∈ Z j' := (hP j' i).2.1 hjs' hxj'
      simpa using hZs j' hjs' _ hnx
    have hjj' : j = j' := by
      by_contra hne
      exact (hZd j hjs j' hjs' hne).le_bot ⟨hxZ, hxZ'⟩
    subst hjj'
    exact (Set.disjoint_left.1 (hP j i).2.2 hxj) (Set.mem_neg.2 hxj')
  · rintro x ⟨-, ⟨j, rfl⟩, -, ⟨hjs, rfl⟩, hxj⟩
    obtain ⟨-, ⟨i, rfl⟩, hxi⟩ := hcov j hjs hxj
    refine mem_iUnion.2 ⟨i, ?_⟩
    rcases hxi with hxi | hxi
    · exact Or.inl (mem_biUnion hjs hxi)
    · exact Or.inr (Set.mem_neg.2 (mem_biUnion hjs (Set.mem_neg.1 hxi)))

/-- **Fattening.** A split cover of a compact symmetric set survives passing to a
closed neighbourhood of it: the halves are thickened by less than half their mutual
distance, so they stay disjoint.

This is what lets the induction of the lower bound cover, not just a level set, but a
whole slab around it. -/
theorem exists_cthickening {K : Set E} {k : ℕ} (hK : IsCompact K)
    (hKs : ∀ x ∈ K, -x ∈ K) (hc : HasSplitCover K k) :
    ∃ r > 0, HasSplitCover (Metric.cthickening r K) k := by
  obtain ⟨P, hP, hcov⟩ := exists_isCompact_halves hK hKs hc
  have hneg : ∀ i, IsClosed (-(P i)) := fun i => (hP i).1.isClosed.neg
  choose δ hδ0 hδ using fun i =>
    ((hP i).2.2).exists_cthickenings (hP i).1 (hneg i)
  obtain ⟨r, hr0, hr⟩ := exists_pos_forall_le_of_forall_pos δ hδ0
  refine ⟨r, hr0, fun i => Metric.cthickening r (P i),
    fun i => ⟨isClosed_cthickening, ?_⟩, ?_⟩
  · rw [neg_cthickening]
    exact (hδ i).mono (cthickening_mono (hr i) _) (cthickening_mono (hr i) _)
  · intro x hx
    rw [hK.cthickening_eq_biUnion_closedBall hr0.le] at hx
    obtain ⟨-, ⟨z, rfl⟩, -, ⟨hzK, rfl⟩, hxz⟩ := hx
    obtain ⟨-, ⟨i, rfl⟩, hzi⟩ := hcov hzK
    refine mem_iUnion.2 ⟨i, ?_⟩
    rcases hzi with hzi | hzi
    · exact Or.inl (mem_cthickening_of_dist_le _ _ _ _ hzi (mem_closedBall.1 hxz))
    · rw [neg_cthickening]
      exact Or.inr (mem_cthickening_of_dist_le _ _ _ _ hzi (mem_closedBall.1 hxz))

/-- **From a split cover to an odd map without zeros.**

Given `k` split sets covering `K`, the sign functions
`σ_i(x) = dist(x, -(P i)) - dist(x, P i)` assemble into a continuous odd map
`Ψ : E → ℝᵏ` that vanishes nowhere on `K`: each `x ∈ K` lies in some split set, and
there `σ_i(x) ≠ 0` because the two halves are closed and disjoint.

Together with the Borsuk–Ulam theorem this converts a covering count into a dimension
bound. -/
theorem exists_odd_continuous_ne_zero {K : Set E} {k : ℕ} (hc : HasSplitCover K k) :
    ∃ Ψ : E → (Fin k → ℝ),
      Continuous Ψ ∧ Function.Odd Ψ ∧ ∀ x ∈ K, Ψ x ≠ 0 := by
  obtain ⟨P, hP, hcov⟩ := hc
  -- `x ↦ dist (x, -S)` at `-x` is `x ↦ dist (x, S)`, because `x ↦ -x` is an isometry.
  have key : ∀ (S : Set E) (x : E), infDist (-x) (-S) = infDist x S := by
    intro S x
    rw [← Set.image_neg_eq_neg]
    exact Metric.infDist_image isometry_neg
  refine ⟨fun x i => infDist x (-(P i)) - infDist x (P i), ?_, ?_, ?_⟩
  · exact continuous_pi fun i =>
      (Metric.continuous_infDist_pt _).sub (Metric.continuous_infDist_pt _)
  · intro x
    funext i
    show infDist (-x) (-(P i)) - infDist (-x) (P i) = -(infDist x (-(P i)) - infDist x (P i))
    rw [key (P i) x, show (P i) = -(-(P i)) from (neg_neg _).symm, key (-(P i)) x, neg_neg]
    ring
  · intro x hx hΨ
    obtain ⟨-, ⟨i, rfl⟩, hxi⟩ := hcov hx
    have hΨi : infDist x (-(P i)) - infDist x (P i) = 0 := congrFun hΨ i
    rcases hxi with hxi | hxi
    · -- `x` lies in the positive half: its distance to the negative half is positive.
      have h0 : infDist x (P i) = 0 := infDist_zero_of_mem hxi
      have hne : (-(P i)).Nonempty := ⟨-x, Set.mem_neg.2 (by simpa using hxi)⟩
      have hpos : 0 < infDist x (-(P i)) := by
        refine (Metric.infDist_pos_iff_notMem_closure hne).1 ?_
        rw [(hP i).1.neg.closure_eq]
        exact fun hc => (Set.disjoint_left.1 (hP i).2 hxi) hc
      rw [h0, sub_zero] at hΨi
      exact hpos.ne' hΨi
    · -- `x` lies in the negative half: its distance to the positive half is positive.
      have h0 : infDist x (-(P i)) = 0 := infDist_zero_of_mem hxi
      have hne : (P i).Nonempty := ⟨-x, Set.mem_neg.1 hxi⟩
      have hpos : 0 < infDist x (P i) := by
        refine (Metric.infDist_pos_iff_notMem_closure hne).1 ?_
        rw [(hP i).1.closure_eq]
        exact fun hc => (Set.disjoint_left.1 (hP i).2 hc) hxi
      rw [h0, zero_sub, neg_eq_zero] at hΨi
      exact hpos.ne' hΨi

end HasSplitCover

/-- A closed symmetric set on which a continuous **odd** function has no zero is a
single split set: the sign of the function tells `x` from `-x`.

This is the elementary engine of the lower bound.  Applied to
`δ(x) = λ(x) - λ(-x)`, the odd part of a measurement `λ`, it says that wherever the
measurement actually separates an antipodal pair, one split set settles the matter. -/
theorem hasSplitCover_one_of_odd_ne_zero {W : Set E} {δ : E → ℝ} (hW : IsClosed W)
    (hWs : ∀ x ∈ W, -x ∈ W) (hδc : Continuous δ) (hδodd : Function.Odd δ)
    (hδ : ∀ x ∈ W, δ x ≠ 0) : HasSplitCover W 1 := by
  refine ⟨fun _ => W ∩ {x | 0 ≤ δ x},
    fun _ => ⟨hW.inter (isClosed_le continuous_const hδc), ?_⟩, ?_⟩
  · rw [Set.disjoint_left]
    rintro x ⟨hxW, hxδ⟩ hxneg
    obtain ⟨-, hxδ'⟩ : -x ∈ W ∩ {x | 0 ≤ δ x} := hxneg
    have hneg : (0 : ℝ) ≤ δ (-x) := hxδ'
    rw [hδodd x] at hneg
    have hpos : (0 : ℝ) ≤ δ x := hxδ
    exact hδ x hxW (le_antisymm (by linarith) hpos)
  · intro x hx
    refine mem_iUnion.2 ⟨0, ?_⟩
    rcases le_total 0 (δ x) with hδx | hδx
    · exact Or.inl ⟨hx, hδx⟩
    · refine Or.inr ⟨hWs x hx, ?_⟩
      show (0 : ℝ) ≤ δ (-x)
      rw [hδodd x]
      linarith

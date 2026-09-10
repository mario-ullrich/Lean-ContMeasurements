/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.SplitCover

/-!
# The halving lemma

Let `Z` be a compact symmetric set and `μ : E → ℝ` a continuous function that is
**even** on `Z`.  Its level sets `Z ∩ μ⁻¹{y}` are then symmetric as well, and they
partition `Z`.

The halving lemma says: if every level set can be covered by `h` split sets, then `Z`
itself can be covered by `2h` split sets.  Knowing a value of `μ` therefore costs at
most a factor of two, never more.

The mechanism is the one described in the introduction of the lower-bound paper.  A
level set carries its split cover over to a whole slab `Z ∩ μ⁻¹(I)` of nearby values
(`HasSplitCover.exists_pos_inter_preimage_ball`), by fattening the split sets
slightly.  Cutting the range of `μ` into closed slabs of a fixed small width, slabs
with an **even** index are
pairwise disjoint, and so are those with an **odd** index.  Pairwise disjoint pieces
share their split sets (`HasSplitCover.biUnion_of_pairwise_disjoint`), so the even slabs
together need `h` split sets and the odd slabs another `h`.

The factor `2` cannot be improved: it is exactly dual to the bisection over colors
performed by the recovery algorithm of the upper bound.
-/

open Metric Set

variable {E : Type*} [NormedAddCommGroup E]

/-- **From a level set to a slab.**

If the level set `Z ∩ μ⁻¹{y}` of an even function `μ` admits a cover by `h` split
sets, then so does `Z ∩ μ⁻¹(B(y, ρ))` for some `ρ > 0`.

The proof fattens the split sets of the level set to a closed neighbourhood of it
(`HasSplitCover.exists_cthickening`), and then uses compactness: the points of `Z` that
stay away from the level set have `μ`-values bounded away from `y`, because their
image is compact and misses `y`. -/
theorem HasSplitCover.exists_pos_inter_preimage_ball {Z : Set E} {μ : E → ℝ} {h : ℕ}
    (hZ : IsCompact Z) (hsymm : ∀ x ∈ Z, -x ∈ Z) (hμ : Continuous μ)
    (hμeven : ∀ x ∈ Z, μ (-x) = μ x) (y : ℝ)
    (hlevel : HasSplitCover (Z ∩ μ ⁻¹' {y}) h) :
    ∃ ρ > 0, HasSplitCover (Z ∩ μ ⁻¹' Metric.ball y ρ) h := by
  set L : Set E := Z ∩ μ ⁻¹' {y} with hL
  have hLc : IsCompact L := hZ.inter_right (isClosed_singleton.preimage hμ)
  have hLs : ∀ x ∈ L, -x ∈ L := by
    rintro x ⟨hxZ, hxy⟩
    exact ⟨hsymm x hxZ, by rw [Set.mem_preimage, hμeven x hxZ]; exact hxy⟩
  obtain ⟨r, hr0, hr⟩ := hlevel.exists_cthickening hLc hLs
  -- The points of `Z` at distance `≥ r` from the level set form a compact set whose
  -- image under `μ` misses `y`.
  have hCc : IsCompact (Z ∩ (Metric.thickening r L)ᶜ) :=
    hZ.inter_right Metric.isOpen_thickening.isClosed_compl
  have hy : y ∉ μ '' (Z ∩ (Metric.thickening r L)ᶜ) := by
    rintro ⟨z, ⟨hzZ, hzn⟩, hzy⟩
    exact hzn (Metric.self_subset_thickening hr0 L ⟨hzZ, hzy⟩)
  obtain ⟨ρ, hρ0, hρ⟩ :=
    Metric.isOpen_iff.1 (hCc.image hμ).isClosed.isOpen_compl y hy
  refine ⟨ρ, hρ0, hr.mono ?_⟩
  rintro x ⟨hxZ, hxb⟩
  refine Metric.thickening_subset_cthickening _ _ ?_
  by_contra hxn
  exact (hρ hxb) ⟨x, ⟨hxZ, hxn⟩, rfl⟩

/-- **Halving lemma.** If every level set of an even continuous function `μ` on a
compact symmetric set `Z` is covered by `h` split sets, then `Z` is covered by `2h`
split sets.

One real value therefore costs a factor of two, and this is sharp. -/
theorem hasSplitCover_two_mul_of_forall_fiber {Z : Set E} {μ : E → ℝ} {h : ℕ}
    (hZ : IsCompact Z) (hsymm : ∀ x ∈ Z, -x ∈ Z) (hμ : Continuous μ)
    (hμeven : ∀ x ∈ Z, μ (-x) = μ x)
    (hlevel : ∀ y : ℝ, HasSplitCover (Z ∩ μ ⁻¹' {y}) h) :
    HasSplitCover Z (2 * h) := by
  classical
  -- Every value has a ball of values whose slab is still covered by `h` split sets.
  choose ρ hρ0 hρ using fun y : ℝ =>
    HasSplitCover.exists_pos_inter_preimage_ball hZ hsymm hμ hμeven y (hlevel y)
  -- A Lebesgue number `η` for this cover of the compact set of attained values.
  obtain ⟨η, hη0, hη⟩ := lebesgue_number_lemma_of_metric (hZ.image hμ)
    (fun _ : ℝ => Metric.isOpen_ball)
    (fun t _ => mem_iUnion.2 ⟨t, Metric.mem_ball_self (hρ0 t)⟩)
  set w : ℝ := η / 2 with hw
  have hw0 : 0 < w := by rw [hw]; linarith
  -- The closed slabs of width `w` cut out of `Z` by `μ`.
  set Zs : ℤ → Set E :=
    fun j => Z ∩ μ ⁻¹' Set.Icc ((j : ℝ) * w) (((j : ℝ) + 1) * w) with hZsdef
  have hZsc : ∀ j, IsCompact (Zs j) := fun j =>
    hZ.inter_right (isClosed_Icc.preimage hμ)
  have hZss : ∀ j, ∀ x ∈ Zs j, -x ∈ Zs j := by
    rintro j x ⟨hxZ, hxI⟩
    exact ⟨hsymm x hxZ, by rw [Set.mem_preimage, hμeven x hxZ]; exact hxI⟩
  have hZsplit : ∀ j : ℤ, HasSplitCover (Zs j) h := by
    intro j
    rcases Set.eq_empty_or_nonempty (Zs j) with he | ⟨x, hx⟩
    · rw [he]; exact hasSplitCover_empty h
    · obtain ⟨y, hy⟩ := hη (μ x) ⟨x, hx.1, rfl⟩
      refine (hρ y).mono ?_
      rintro z ⟨hzZ, hz⟩
      refine ⟨hzZ, hy ?_⟩
      have hx2 := hx.2
      simp only [Set.mem_preimage, Set.mem_Icc] at hz hx2
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hz.1, hz.2, hx2.1, hx2.2]
  -- Slabs whose indices differ by at least two are disjoint.
  have hdisj2 : ∀ j j' : ℤ, j + 2 ≤ j' → Disjoint (Zs j) (Zs j') := by
    intro j j' hjj
    rw [Set.disjoint_left]
    rintro x ⟨-, hx⟩ ⟨-, hx'⟩
    simp only [Set.mem_preimage, Set.mem_Icc] at hx hx'
    have hlt : ((j : ℝ) + 1) < (j' : ℝ) := by exact_mod_cast (by omega : j + 1 < j')
    have : ((j : ℝ) + 1) * w < (j' : ℝ) * w := by
      exact mul_lt_mul_of_pos_right hlt hw0
    linarith [hx.2, hx'.1]
  -- Only finitely many slabs meet `Z`, since `μ` is bounded on `Z`.
  obtain ⟨M, hM⟩ := (hZ.image hμ).isBounded.subset_closedBall (0 : ℝ)
  set J : Finset ℤ := Finset.Icc ⌊-M / w⌋ ⌊M / w⌋ with hJ
  have hgrid : ∀ x ∈ Z, ∃ j ∈ J, x ∈ Zs j := by
    intro x hx
    have habs : |μ x| ≤ M := by
      have hmem : μ x ∈ Metric.closedBall (0 : ℝ) M := hM ⟨x, hx, rfl⟩
      rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem
    refine ⟨⌊μ x / w⌋,
      Finset.mem_Icc.2 ⟨Int.floor_mono ?_, Int.floor_mono ?_⟩, ⟨hx, ?_⟩⟩
    · exact div_le_div_of_nonneg_right (abs_le.1 habs).1 hw0.le
    · exact div_le_div_of_nonneg_right (abs_le.1 habs).2 hw0.le
    · rw [Set.mem_preimage, Set.mem_Icc]
      constructor
      · rw [← le_div_iff₀ hw0]; exact Int.floor_le _
      · rw [← div_le_iff₀ hw0]; exact le_of_lt (Int.lt_floor_add_one _)
  -- Split the finitely many relevant indices by parity.
  set sE : Finset ℤ := J.filter (fun j => j % 2 = 0) with hsE
  set sO : Finset ℤ := J.filter (fun j => ¬ j % 2 = 0) with hsO
  have hpar : ∀ (s : Finset ℤ), (∀ j ∈ s, ∀ j' ∈ s, j % 2 = j' % 2) →
      ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → Disjoint (Zs j) (Zs j') := by
    intro s hs j hj j' hj' hne
    have hmod := hs j hj j' hj'
    rcases (by omega : j + 2 ≤ j' ∨ j' + 2 ≤ j) with hc | hc
    · exact hdisj2 j j' hc
    · exact (hdisj2 j' j hc).symm
  have hcovE : HasSplitCover (⋃ j ∈ sE, Zs j) h :=
    HasSplitCover.biUnion_of_pairwise_disjoint (fun j _ => hZsc j) (fun j _ => hZss j)
      (hpar sE (by intro j hj j' hj'
                   rw [hsE, Finset.mem_filter] at hj hj'
                   rw [hj.2, hj'.2])) (fun j _ => hZsplit j)
  have hcovO : HasSplitCover (⋃ j ∈ sO, Zs j) h :=
    HasSplitCover.biUnion_of_pairwise_disjoint (fun j _ => hZsc j) (fun j _ => hZss j)
      (hpar sO (by intro j hj j' hj'
                   rw [hsO, Finset.mem_filter] at hj hj'
                   omega)) (fun j _ => hZsplit j)
  have hsub : Z ⊆ (⋃ j ∈ sE, Zs j) ∪ (⋃ j ∈ sO, Zs j) := by
    intro x hx
    obtain ⟨j, hjmem, hxj⟩ := hgrid x hx
    by_cases hp : j % 2 = 0
    · refine Or.inl (mem_biUnion ?_ hxj)
      simp only [hsE, Finset.mem_coe, Finset.mem_filter]
      exact ⟨hjmem, hp⟩
    · refine Or.inr (mem_biUnion ?_ hxj)
      simp only [hsO, Finset.mem_coe, Finset.mem_filter]
      exact ⟨hjmem, hp⟩
  rw [two_mul]
  exact (hcovE.union hcovO).mono hsub

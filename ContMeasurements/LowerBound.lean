/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import ContMeasurements.Scheme
import BasicResults.Halving
import BasicResults.BorsukUlam

/-!
# The lower bound

`n` adaptively chosen continuous measurements cannot recover a vector of an
`m`-dimensional normed space to within an error smaller than the radius of the ball
it is taken from, unless `2ⁿ ≥ m + 1`.

## The argument

The heart of the matter is the covering proposition
`AdaptiveScheme.DistinguishesAntipodes.hasSplitCover`: if `n` adaptive continuous
measurements separate every antipodal pair of a compact symmetric set `K`, then `K`
is covered by `2ⁿ - 1` split sets.  The induction on `n` splits the first
measurement `λ₁` into its odd and its even part:

* Where its **odd part** `δ(x) = λ₁(x) - λ₁(-x)` is nonzero, one real value already
  decides between `x` and `-x`; that region is a single split set
  (`hasSplitCover_one_of_odd_ne_zero`).
* On the coincidence set `Z = δ⁻¹{0}` the measurement is **even**, so it says nothing
  about the antipodal question; all it does is sort the points into level sets.  On
  each level set the remaining `n-1` measurements still separate antipodes, and the
  induction hypothesis applies: every point of one level set faces the *same* next
  functional, so adaptivity is disarmed.  The halving lemma
  (`hasSplitCover_two_mul_of_forall_fiber`) then pays a factor of `2` to pass from
  the level sets to `Z` itself.

The count is therefore `c(n) = 2 c(n-1) + 1` with `c(0) = 0`, that is `c(n) = 2ⁿ - 1`.
Distance functions turn the covering into a continuous odd map into `ℝ^{2ⁿ-1}`
without zeros (`HasSplitCover.exists_odd_continuous_ne_zero`), which Borsuk–Ulam
forbids on the sphere of an `m`-dimensional space unless `2ⁿ - 1 ≥ m`.

## Main results

* `AdaptiveScheme.DistinguishesAntipodes.hasSplitCover` — the covering proposition.
  **Proved unconditionally**, no Borsuk–Ulam involved.
* `exists_norm_eq_and_info_eq_info_neg` — if `2ⁿ ≤ m`, some antipodal pair on the
  sphere of radius `R` produces identical information.  This is the Borsuk–Ulam theorem for
  adaptive measurements: adaptivity moves the antipodal threshold from `m - 1` to
  `log₂ m`, and no further.
* `AdaptiveScheme.DistinguishesAntipodes.finrank_add_one_le_two_pow` — the same as
  the counting statement `2ⁿ ≥ dim E + 1`.
* `exists_norm_eq_and_le_norm_sub` — every algorithm using `n` measurements with
  `2ⁿ ≤ m` has error at least `R` somewhere on the sphere of radius `R`; the
  measurements are useless.
-/

namespace ContMeasurements

open Metric Set AdaptiveScheme

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- **The covering proposition.**  If `n` adaptive continuous measurements distinguish
all antipodal pairs of a compact symmetric set `K`, then `K` is covered by `2ⁿ - 1`
split sets.

The proof is the induction described in the module docstring; it uses no topology
beyond compactness, and in particular **no** Borsuk–Ulam. -/
theorem AdaptiveScheme.DistinguishesAntipodes.hasSplitCover (n : ℕ)
    (S : AdaptiveScheme E) (K : Set E) (hK : IsCompact K) (hsymm : ∀ x ∈ K, -x ∈ K)
    (hN : S.DistinguishesAntipodes n K) : HasSplitCover K (2 ^ n - 1) := by
  induction n generalizing S K with
  | zero =>
    -- With no measurement at all, `N x = N (-x)` always: the empty tuple is unique.
    have hKe : K = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨x, hx⟩
      exact hN x hx (Subsingleton.elim _ _)
    rw [hKe]
    simpa using hasSplitCover_empty (E := E) 0
  | succ n ih =>
    -- The odd part of the first measurement.
    set δ : E → ℝ := fun x => S.first x - S.first (-x) with hδ
    have hδc : Continuous δ :=
      S.continuous_first.sub (S.continuous_first.comp continuous_neg)
    have hδodd : Function.Odd δ := by
      intro x
      simp only [hδ, neg_neg]
      ring
    -- The coincidence set, on which the first measurement is even.
    set Z : Set E := K ∩ δ ⁻¹' {0} with hZdef
    have hZc : IsCompact Z := hK.inter_right (isClosed_singleton.preimage hδc)
    have hZs : ∀ x ∈ Z, -x ∈ Z := by
      rintro x ⟨hxK, hx0⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx0
      exact ⟨hsymm x hxK, by
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hδodd x, hx0, neg_zero]⟩
    have hZneg : -Z = Z := by
      ext x
      simp only [Set.mem_neg]
      exact ⟨fun h => by simpa using hZs _ h, fun h => hZs x h⟩
    have hμeven : ∀ x ∈ Z, S.first (-x) = S.first x := by
      rintro x ⟨-, hx0⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hδ] at hx0
      linarith
    -- Each level set of the first measurement is handled by the induction hypothesis:
    -- its points share the first value, hence face the same continuation `S.tail y`.
    have hlevel : ∀ y : ℝ, HasSplitCover (Z ∩ S.first ⁻¹' {y}) (2 ^ n - 1) := by
      intro y
      refine ih (S.tail y) (Z ∩ S.first ⁻¹' {y})
        (hZc.inter_right (isClosed_singleton.preimage S.continuous_first)) ?_ ?_
      · rintro x ⟨hxZ, hxy⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hxy
        exact ⟨hZs x hxZ, by
          simp only [Set.mem_preimage, Set.mem_singleton_iff, hμeven x hxZ, hxy]⟩
      · rintro x ⟨hxZ, hxy⟩ heq
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hxy
        refine hN x hxZ.1 ?_
        have h2 : S.first (-x) = y := by rw [hμeven x hxZ]; exact hxy
        rw [info_succ, info_succ, hxy, h2, heq]
    -- One measurement costs a factor of two.
    have hZsplit : HasSplitCover Z (2 * (2 ^ n - 1)) :=
      hasSplitCover_two_mul_of_forall_fiber hZc hZs S.continuous_first hμeven hlevel
    obtain ⟨r, hr0, hr⟩ := hZsplit.exists_cthickening hZc hZs
    -- Away from `Z` the odd part has no zero, and contributes one further split set.
    have hthick : ∀ x : E, -x ∈ Metric.thickening r Z ↔ x ∈ Metric.thickening r Z := by
      intro x
      rw [← Set.mem_neg, neg_thickening, hZneg]
    have hWclosed : IsClosed (K ∩ (Metric.thickening r Z)ᶜ) :=
      hK.isClosed.inter Metric.isOpen_thickening.isClosed_compl
    have hWsymm : ∀ x ∈ K ∩ (Metric.thickening r Z)ᶜ,
        -x ∈ K ∩ (Metric.thickening r Z)ᶜ := by
      rintro x ⟨hxK, hxn⟩
      exact ⟨hsymm x hxK, fun hmem => hxn ((hthick x).1 hmem)⟩
    have hWδ : ∀ x ∈ K ∩ (Metric.thickening r Z)ᶜ, δ x ≠ 0 := by
      rintro x ⟨hxK, hxn⟩ h0
      exact hxn (Metric.self_subset_thickening hr0 Z ⟨hxK, h0⟩)
    have hWsplit : HasSplitCover (K ∩ (Metric.thickening r Z)ᶜ) 1 :=
      hasSplitCover_one_of_odd_ne_zero hWclosed hWsymm hδc hδodd hWδ
    -- Assemble: `2 (2ⁿ - 1) + 1 = 2ⁿ⁺¹ - 1`.
    have harith : 2 * (2 ^ n - 1) + 1 = 2 ^ (n + 1) - 1 := by
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      rw [pow_succ]
      omega
    rw [← harith]
    refine (hr.union hWsplit).mono ?_
    intro x hx
    by_cases hxt : x ∈ Metric.thickening r Z
    · exact Or.inl (Metric.thickening_subset_cthickening _ _ hxt)
    · exact Or.inr ⟨hx, hxt⟩

variable [FiniteDimensional ℝ E]

/-- **Borsuk–Ulam for adaptive measurements.**  If `2ⁿ ≤ m = dim E`, then no matter how
the `n` continuous measurements are chosen, adaptively and with no regularity in the
observed values, some antipodal pair on the sphere of radius `R` produces exactly the
same information.

Classical Borsuk–Ulam is the nonadaptive case and gives the threshold `m - 1`;
adaptivity moves it to `log₂ m`, and by the recovery algorithm of `UpperBound.lean`
no further. -/
theorem exists_norm_eq_and_info_eq_info_neg {m n : ℕ} (hm : Module.finrank ℝ E = m)
    (S : AdaptiveScheme E) (hn : 2 ^ n ≤ m) {R : ℝ} (hR : 0 < R) :
    ∃ x : E, ‖x‖ = R ∧ S.info n x = S.info n (-x) := by
  by_contra hcon
  have hdist : S.DistinguishesAntipodes n (Metric.sphere (0 : E) R) := by
    intro x hx heq
    exact hcon ⟨x, mem_sphere_zero_iff_norm.1 hx, heq⟩
  have hsymm : ∀ x ∈ Metric.sphere (0 : E) R, -x ∈ Metric.sphere (0 : E) R := by
    intro x hx
    rw [mem_sphere_zero_iff_norm] at hx ⊢
    rwa [norm_neg]
  obtain ⟨Ψ, hΨc, hΨo, hΨ⟩ :=
    (hdist.hasSplitCover n S (Metric.sphere (0 : E) R)
      (isCompact_sphere 0 R) hsymm).exists_odd_continuous_ne_zero
  have hlt : 2 ^ n - 1 < m := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  obtain ⟨x, hxn, hx0⟩ :=
    hΨo.exists_norm_eq_and_eq_zero_of_lt_finrank hm hlt hR Ψ hΨc
  exact hΨ x (mem_sphere_zero_iff_norm.2 hxn) hx0

/-- The counting form of the lower bound: `n` adaptive continuous measurements that
separate every antipodal pair of a sphere in a `d`-dimensional normed space satisfy
`2ⁿ ≥ d + 1`, that is `n ≥ ⌈log₂(d+1)⌉`.

Holds for **any** norm and any radius `R > 0`. -/
theorem AdaptiveScheme.DistinguishesAntipodes.finrank_add_one_le_two_pow {n : ℕ}
    (S : AdaptiveScheme E) {R : ℝ} (hR : 0 < R)
    (hdist : S.DistinguishesAntipodes n (Metric.sphere (0 : E) R)) :
    Module.finrank ℝ E + 1 ≤ 2 ^ n := by
  by_contra hcon
  have hn : 2 ^ n ≤ Module.finrank ℝ E := by omega
  obtain ⟨x, hxn, hxeq⟩ := exists_norm_eq_and_info_eq_info_neg rfl S hn hR
  exact hdist x (mem_sphere_zero_iff_norm.2 hxn) hxeq

/-- **The lower bound in the form used for complexity.**  If `2ⁿ ≤ dim E`, then every
algorithm built from `n` adaptive continuous measurements and an arbitrary
reconstruction map `Φ` errs by at least `R` at some point of the sphere of radius `R`.

In words: below `log₂(dim E)` measurements nothing at all can be achieved, since the
error is no better than that of the trivial algorithm returning the centre. -/
theorem exists_norm_eq_and_le_norm_sub {m n : ℕ} (hm : Module.finrank ℝ E = m)
    (S : AdaptiveScheme E) (hn : 2 ^ n ≤ m) {R : ℝ} (hR : 0 < R) (Φ : (Fin n → ℝ) → E) :
    ∃ x : E, ‖x‖ = R ∧ R ≤ ‖x - Φ (S.info n x)‖ := by
  obtain ⟨x, hxn, hxeq⟩ := exists_norm_eq_and_info_eq_info_neg hm S hn hR
  by_contra hcon
  have h1 : ‖x - Φ (S.info n x)‖ < R := by
    by_contra hge
    exact hcon ⟨x, hxn, not_lt.1 hge⟩
  have h2 : ‖-x - Φ (S.info n x)‖ < R := by
    have hneg : ‖-x - Φ (S.info n (-x))‖ < R := by
      by_contra hge
      exact hcon ⟨-x, by rwa [norm_neg], not_lt.1 hge⟩
    rwa [← hxeq] at hneg
  -- The two antipodes are `2R` apart, so they cannot both be within `R` of one point.
  have hsum : ‖x + x‖ ≤ ‖x - Φ (S.info n x)‖ + ‖-x - Φ (S.info n x)‖ := by
    have hle := norm_sub_le (x - Φ (S.info n x)) (-x - Φ (S.info n x))
    have heq : x - Φ (S.info n x) - (-x - Φ (S.info n x)) = x + x := by abel
    rwa [heq] at hle
  have hxx : ‖x + x‖ = 2 * R := by
    rw [← two_smul ℝ x, norm_smul, hxn]
    norm_num
  rw [hxx] at hsum
  linarith

end ContMeasurements

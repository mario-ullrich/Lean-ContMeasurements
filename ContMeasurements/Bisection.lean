/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import ContMeasurements.Scheme
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Bisection over finitely many sets

The general engine of the recovery algorithm.  Suppose the input space is covered by
the closures of finitely many sets `A r`, `r` ranging over a finite set `C` of
"colors", and suppose that for each color there is already an algorithm — a scheme
of `ℓ` measurements and a reconstruction map — that is accurate on `closure (A r)`.
Then `⌈log₂ |C|⌉` further measurements suffice to find a correct color, so
`ℓ + ⌈log₂ |C|⌉` measurements are accurate on the whole union.

The color is found by bisection.  Split `C` into two halves `C₁, C₂`, and measure the
continuous functional
`x ↦ dist(x, ⋃_{r ∈ C₁} A r)`.
Its value is `0` exactly on the closure of that union, so one real number decides
which half to continue with.  This is a *continuous membership oracle*: the
functional is continuous (indeed `1`-Lipschitz), yet the decision it feeds is
discrete, and the choice of the next functional depends on it.  That is precisely
the adaptivity the model allows and the lower bound has to fight.

The recursion halves `|C|`, so it terminates after `⌈log₂ |C|⌉` steps — this is the
`2ᴸ` in the statement below, and the source of the logarithm in the upper bound.

## Main result

* `ContMeasurements.exists_bisection_scheme`.

## Implementation notes

The length of the resulting scheme is written `ℓ + L` rather than `L + ℓ`, so that
`ℓ + 0` reduces to `ℓ` and `ℓ + (L + 1)` reduces to `(ℓ + L) + 1` definitionally, and
the induction needs no transport of `Fin` indices.

The bisection functional uses `Metric.infDist`, which is `0` on the **empty** set as
well as on the closure of a nonempty set.  The branch condition therefore also tests
`(⋃ r ∈ C₁, A r).Nonempty`; this is a fact about the cover, known to the algorithm
designer, not information about the point being measured.
-/

namespace ContMeasurements

open Metric Set AdaptiveScheme

/-- **Bisection over colors.**

Given, for each color `r`, a scheme of `ℓ` measurements together with a
reconstruction map that is `η`-accurate on `closure (A r)`, and a finite set `C` of at
most `2ᴸ` colors, there is a scheme of `ℓ + L` measurements together with a
reconstruction map that is `η`-accurate on `closure (⋃ r ∈ C, A r)`.

The `L` extra measurements are the bisection steps that identify a color. -/
theorem exists_bisection_scheme {X : Type*} [PseudoMetricSpace X] [Nonempty X] {Kc : ℕ}
    {A : Fin Kc → Set X} {η : ℝ} {ℓ : ℕ} {leaf : Fin Kc → AdaptiveScheme X}
    {out : Fin Kc → (Fin ℓ → ℝ) → X}
    (hleaf : ∀ r, ∀ x ∈ closure (A r), dist x (out r ((leaf r).info ℓ x)) ≤ η) :
    ∀ (L : ℕ) (C : Finset (Fin Kc)), C.card ≤ 2 ^ L →
      ∃ (S : AdaptiveScheme X) (Φ : (Fin (ℓ + L) → ℝ) → X),
        ∀ x ∈ closure (⋃ r ∈ C, A r), dist x (Φ (S.info (ℓ + L) x)) ≤ η := by
  classical
  intro L
  induction L with
  | zero =>
    intro C hC
    -- At most one color is left; either none, and there is nothing to prove, or one,
    -- and its own algorithm does the job.
    have h := Finset.card_le_one.1 (by simpa using hC)
    rcases Finset.eq_empty_or_nonempty C with rfl | ⟨r, hr⟩
    · exact ⟨AdaptiveScheme.single (fun _ => (0 : ℝ)) continuous_const,
        fun _ => Classical.arbitrary X, by simp⟩
    · have hCr : C = {r} := Finset.eq_singleton_iff_unique_mem.2 ⟨hr, fun y hy => h y hy r hr⟩
      refine ⟨leaf r, out r, ?_⟩
      intro x hx
      rw [hCr] at hx
      simpa using hleaf r x (by simpa using hx)
  | succ L ih =>
    intro C hC
    -- Split `C` into two halves, each of at most `2ᴸ` colors.
    obtain ⟨C₁, hC₁sub, hC₁card⟩ :=
      Finset.exists_subset_card_eq (min_le_left C.card (2 ^ L))
    have hC₁ : C₁.card ≤ 2 ^ L := by rw [hC₁card]; exact min_le_right _ _
    have hpow : 2 ^ (L + 1) = 2 ^ L + 2 ^ L := by rw [pow_succ]; ring
    have hC₂ : (C \ C₁).card ≤ 2 ^ L := by
      rw [Finset.card_sdiff_of_subset hC₁sub, hC₁card]
      rcases le_total C.card (2 ^ L) with hle | hle
      · rw [min_eq_left hle]; omega
      · rw [min_eq_right hle]; omega
    obtain ⟨S₁, Φ₁, hS₁⟩ := ih C₁ hC₁
    obtain ⟨S₂, Φ₂, hS₂⟩ := ih (C \ C₁) hC₂
    -- The bisection functional: the distance to the union of the first half.
    set U₁ : Set X := ⋃ r ∈ C₁, A r with hU₁
    set f : X → ℝ := fun x => Metric.infDist x U₁ with hf
    have hfc : Continuous f := Metric.continuous_infDist_pt U₁
    set choice : ℝ → AdaptiveScheme X := fun y => if U₁.Nonempty ∧ y = 0 then S₁ else S₂
      with hchoice
    refine ⟨AdaptiveScheme.branch f hfc choice,
      fun y => if U₁.Nonempty ∧ y 0 = 0 then Φ₁ (Fin.tail y) else Φ₂ (Fin.tail y), ?_⟩
    intro x hx
    -- Unfold one step of the scheme.
    have hinfo : (AdaptiveScheme.branch f hfc choice).info (ℓ + (L + 1)) x
        = Fin.cons (f x) ((choice (f x)).info (ℓ + L) x) :=
      AdaptiveScheme.info_branch_succ f hfc choice (ℓ + L) x
    rw [hinfo]
    have hzero : (Fin.cons (f x) ((choice (f x)).info (ℓ + L) x) : Fin (ℓ + L + 1) → ℝ) 0
        = f x := Fin.cons_zero _ _
    have htail :
        Fin.tail (Fin.cons (f x) ((choice (f x)).info (ℓ + L) x) : Fin (ℓ + L + 1) → ℝ)
          = (choice (f x)).info (ℓ + L) x := Fin.tail_cons _ _
    simp only [hzero, htail]
    -- Membership in `closure U₁` is exactly the branch condition.
    have hmem : (U₁.Nonempty ∧ f x = 0) ↔ x ∈ closure U₁ := by
      constructor
      · rintro ⟨hne, h0⟩
        exact (Metric.mem_closure_iff_infDist_zero hne).2 h0
      · intro hxc
        rcases Set.eq_empty_or_nonempty U₁ with he | hne
        · rw [he, closure_empty] at hxc; exact absurd hxc (Set.notMem_empty x)
        · exact ⟨hne, (Metric.mem_closure_iff_infDist_zero hne).1 hxc⟩
    by_cases hb : U₁.Nonempty ∧ f x = 0
    · -- The point lies in the closure of the first half: continue with `S₁`.
      have hce : choice (f x) = S₁ := by rw [hchoice]; exact if_pos hb
      rw [if_pos hb, hce]
      exact hS₁ x (hmem.1 hb)
    · -- Otherwise the point is not in the closure of the first half, hence in the
      -- closure of the second: continue with `S₂`.
      have hxc₂ : x ∈ closure (⋃ r ∈ C \ C₁, A r) := by
        have hsplit : (⋃ r ∈ C, A r) = U₁ ∪ ⋃ r ∈ C \ C₁, A r := by
          rw [hU₁, ← Finset.set_biUnion_union, Finset.union_sdiff_of_subset hC₁sub]
        rw [hsplit, closure_union] at hx
        rcases hx with hx | hx
        · exact absurd (hmem.2 hx) hb
        · exact hx
      have hce : choice (f x) = S₂ := by rw [hchoice]; exact if_neg hb
      rw [if_neg hb, hce]
      exact hS₂ x hxc₂

end ContMeasurements

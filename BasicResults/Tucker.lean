/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import BasicResults.GridSimplex
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Nat

/-!
# Tucker's lemma

Tucker's lemma is the combinatorial form of the Borsuk–Ulam theorem.  Label every point of
the integer cube `[-N, N]ⁿ` by a coordinate together with a sign, so that antipodal
boundary points receive opposite labels.  Then some simplex of the Kuhn triangulation
carries two opposite labels.

The proof is a parity argument.  Call a simplex **happy** when every sign it carries also
occurs as a label on it, and call a happy simplex a **door** of a larger one when it is
that one with a vertex deleted and already carries all of its signs.  Counting the doors
from their two ends makes the total number of doors at a happy simplex even, so an even
number of happy simplices have an odd number of them.

Assuming no simplex carries two opposite labels, a happy simplex comes in one of three
shapes, according to whether it has as many vertices as directions or one more, and
whether its labels are distinct.  Each shape has exactly two doors, with two exceptions:
the origin alone, and the simplices with one coordinate at the boundary of the cube.
Reflection in the origin pairs the latter up, so an odd number of happy simplices have an
odd number of doors.  That is the contradiction.

## Main results

* `GridSimplex.IsHappy`: a simplex all of whose signs occur as labels on it.
* `GridSimplex.odd_deg_iff`: the happy simplices with an odd number of doors are the
  origin alone and those with a coordinate at the boundary of the cube.
* `GridSimplex.tucker`: Tucker's lemma.
-/

@[expose] public section

namespace Finset

/-- **A finite set carrying a fixed-point-free involution has even cardinality.**  Its
elements fall into pairs. -/
theorem even_card_of_involutive {α : Type*} [DecidableEq α] {B : Finset α} {f : α → α}
    (hmaps : ∀ x ∈ B, f x ∈ B) (hinv : ∀ x ∈ B, f (f x) = x) (hne : ∀ x ∈ B, f x ≠ x) :
    Even B.card := by
  suffices h : ∀ m : ℕ, ∀ C : Finset α, C.card ≤ m → (∀ x ∈ C, f x ∈ C) →
      (∀ x ∈ C, f (f x) = x) → (∀ x ∈ C, f x ≠ x) → Even C.card from
    h B.card B le_rfl hmaps hinv hne
  intro m
  induction m with
  | zero =>
    intro C hC _ _ _
    rw [Nat.le_zero.1 hC]
    exact ⟨0, rfl⟩
  | succ m ih =>
    intro C hC hmapsC hinvC hneC
    rcases C.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hfx : f x ∈ C := hmapsC x hx
      have hxfx : x ≠ f x := fun h => hneC x hx h.symm
      have hfxe : f x ∈ C.erase x := Finset.mem_erase.2 ⟨fun h => hxfx h.symm, hfx⟩
      have hpair : ({x, f x} : Finset α) ⊆ C := by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy'
        · exact hx
        · rw [Finset.mem_singleton] at hy'
          subst hy'
          exact hfx
      have h2 : 2 ≤ C.card := by
        have h := Finset.card_le_card hpair
        rwa [Finset.card_insert_of_notMem (by simpa using hxfx), Finset.card_singleton] at h
      have hcard : C.card = ((C.erase x).erase (f x)).card + 2 := by
        rw [Finset.card_erase_of_mem hfxe, Finset.card_erase_of_mem hx]
        omega
      have hmapsD : ∀ y ∈ (C.erase x).erase (f x), f y ∈ (C.erase x).erase (f x) := by
        intro y hy
        rw [Finset.mem_erase, Finset.mem_erase] at hy ⊢
        obtain ⟨hy1, hy2, hy3⟩ := hy
        refine ⟨fun h => hy2 ?_, fun h => hy1 ?_, hmapsC y hy3⟩
        · rw [← hinvC y hy3, h, hinvC x hx]
        · rw [← hinvC y hy3, h]
      have hsubD : (C.erase x).erase (f x) ⊆ C :=
        (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have := ih ((C.erase x).erase (f x)) (by omega) hmapsD
        (fun y hy => hinvC y (hsubD hy)) (fun y hy => hneC y (hsubD hy))
      rw [hcard]
      exact this.add even_two

end Finset


open Finset
open scoped Pointwise

namespace GridSimplex

variable {n N : ℕ} {lam : (Fin n → ℤ) → Label n} {s : Finset (Fin n → ℤ)}

/-! ### Labels on a simplex -/

/-- The labels occurring on a set of grid points. -/
def labels (lam : (Fin n → ℤ) → Label n) (s : Finset (Fin n → ℤ)) : Finset (Label n) :=
  s.image lam

/-- A label occurs on a set exactly when some point carries it. -/
@[simp]
theorem mem_labels {p : Label n} : p ∈ labels lam s ↔ ∃ x ∈ s, lam x = p :=
  Finset.mem_image

/-- A set carries at most as many labels as it has points. -/
theorem card_labels_le : (labels lam s).card ≤ s.card := Finset.card_image_le

/-- Labels of a subset are labels. -/
theorem labels_subset {t : Finset (Fin n → ℤ)} (hts : t ⊆ s) :
    labels lam t ⊆ labels lam s :=
  Finset.image_subset_image hts

/-- Reflecting a set of points reverses its labels, provided the labelling is antipodal
there. -/
theorem labels_neg_of_antipodal
    (h : ∀ x ∈ s, lam (-x) = negLabel (lam x)) :
    labels lam (-s) = (labels lam s).image negLabel := by
  ext p
  simp only [mem_labels, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.1 hx
    exact ⟨lam y, ⟨y, hy, rfl⟩, (h y hy).symm ▸ rfl⟩
  · rintro ⟨q, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨-y, Finset.mem_neg.2 ⟨y, hy, rfl⟩, h y hy⟩

/-! ### Happy simplices -/

/-- A simplex is **happy** for a labelling when every sign it carries occurs as a label on
it.  The parity argument runs over the happy simplices. -/
structure IsHappy (N : ℕ) (lam : (Fin n → ℤ) → Label n) (s : Finset (Fin n → ℤ)) :
    Prop where
  /-- A happy simplex is a simplex. -/
  isSimplex : IsSimplex N s
  /-- Every sign it carries occurs as a label. -/
  signs_subset : signs s ⊆ labels lam s

/-- A happy simplex has at least as many labels as directions. -/
theorem IsHappy.card_directions_le (h : IsHappy N lam s) :
    (directions s).card ≤ (labels lam s).card := by
  rw [← h.isSimplex.card_signs]
  exact Finset.card_le_card h.signs_subset

/-- **The three shapes of a happy simplex.**

Writing `k` for the number of directions, a happy simplex has either `k + 1` vertices and
`k + 1` labels, or `k + 1` vertices and `k` labels, or `k` vertices and `k` labels. -/
theorem IsHappy.shape (h : IsHappy N lam s) :
    (s.card = (directions s).card + 1 ∧ (labels lam s).card = (directions s).card + 1) ∨
      (s.card = (directions s).card + 1 ∧ (labels lam s).card = (directions s).card) ∨
      (s.card = (directions s).card ∧ (labels lam s).card = (directions s).card) := by
  have h1 : (directions s).card ≤ (labels lam s).card := h.card_directions_le
  have h2 : (labels lam s).card ≤ s.card := card_labels_le
  have h3 : s.card ≤ (directions s).card + 1 := h.isSimplex.card_le_card_directions_succ
  omega

/-! ### Doors

Two happy simplices are joined when one is obtained from the other by deleting a vertex
and already carries all of its signs.  The parity argument counts these incidences twice,
once from each end. -/

/-- `σ` is a **door** of `τ`: it is `τ` with one vertex deleted, still nonempty, and it
already carries every sign of `τ`. -/
structure IsDoor (N : ℕ) (lam : (Fin n → ℤ) → Label n) (σ τ : Finset (Fin n → ℤ)) :
    Prop where
  /-- The larger set is a simplex. -/
  isSimplex : IsSimplex N τ
  /-- The smaller one is contained in it. -/
  subset : σ ⊆ τ
  /-- with one vertex fewer. -/
  card_succ : σ.card + 1 = τ.card
  /-- The smaller one is not empty. -/
  nonempty : σ.Nonempty
  /-- Every sign of the larger one already occurs as a label on the smaller one. -/
  signs_subset : signs τ ⊆ labels lam σ

/-- The smaller end of a door is happy. -/
theorem IsDoor.happy_left {σ τ : Finset (Fin n → ℤ)} (h : IsDoor N lam σ τ) :
    IsHappy N lam σ where
  isSimplex := h.isSimplex.subset h.subset h.nonempty
  signs_subset := (_root_.GridSimplex.signs_subset h.subset).trans h.signs_subset

/-- The larger end of a door is happy. -/
theorem IsDoor.happy_right {σ τ : Finset (Fin n → ℤ)} (h : IsDoor N lam σ τ) :
    IsHappy N lam τ where
  isSimplex := h.isSimplex
  signs_subset := h.signs_subset.trans (_root_.GridSimplex.labels_subset h.subset)

/-! ### Counting incidences -/

open scoped Classical in
/-- The happy simplices of the grid, as a finite set. -/
noncomputable def happySet (N : ℕ) (lam : (Fin n → ℤ) → Label n) :
    Finset (Finset (Fin n → ℤ)) :=
  (grid n N).powerset.filter (IsHappy N lam)

/-- A happy simplex belongs to `happySet`. -/
theorem mem_happySet {N : ℕ} : s ∈ happySet N lam ↔ IsHappy N lam s := by
  classical
  rw [happySet, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.isSimplex.subset_grid, h⟩⟩

open scoped Classical in
/-- The number of doors above a happy simplex. -/
noncomputable def upDeg (N : ℕ) (lam : (Fin n → ℤ) → Label n)
    (σ : Finset (Fin n → ℤ)) : ℕ :=
  ((happySet N lam).filter (IsDoor N lam σ)).card

open scoped Classical in
/-- The number of doors below a happy simplex. -/
noncomputable def downDeg (N : ℕ) (lam : (Fin n → ℤ) → Label n)
    (τ : Finset (Fin n → ℤ)) : ℕ :=
  ((happySet N lam).filter fun σ => IsDoor N lam σ τ).card

/-- The degree of a happy simplex in the incidence graph. -/
noncomputable def deg (N : ℕ) (lam : (Fin n → ℤ) → Label n)
    (σ : Finset (Fin n → ℤ)) : ℕ :=
  upDeg N lam σ + downDeg N lam σ

/-- **Every door is counted once from each end**, so the two degree sums agree.  Both are
the number of doors, summed in the two possible orders. -/
theorem sum_upDeg_eq_sum_downDeg (N : ℕ) (lam : (Fin n → ℤ) → Label n) :
    ∑ σ ∈ happySet N lam, upDeg N lam σ = ∑ τ ∈ happySet N lam, downDeg N lam τ := by
  classical
  simp only [upDeg, downDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- The total degree is even, because it counts every door twice. -/
theorem even_sum_deg (N : ℕ) (lam : (Fin n → ℤ) → Label n) :
    Even (∑ σ ∈ happySet N lam, deg N lam σ) := by
  have hsplit : ∑ σ ∈ happySet N lam, deg N lam σ =
      (∑ σ ∈ happySet N lam, upDeg N lam σ) +
        ∑ σ ∈ happySet N lam, downDeg N lam σ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => rfl
  rw [hsplit, ← sum_upDeg_eq_sum_downDeg]
  exact ⟨_, rfl⟩

/-- **The number of happy simplices of odd degree is even.** -/
theorem even_card_odd_deg (N : ℕ) (lam : (Fin n → ℤ) → Label n) :
    Even ((happySet N lam).filter fun σ => Odd (deg N lam σ)).card := by
  classical
  exact (Finset.even_sum_iff_even_card_odd _).1 (even_sum_deg N lam)

/-- In the two shapes with as many labels as vertices, the labelling is injective on the
simplex. -/
theorem injOn_lam_of_card (hcard : (labels lam s).card = s.card) : Set.InjOn lam s := by
  refine Finset.injOn_of_card_image_eq ?_
  rw [← labels]
  exact hcard

/-- Deleting a vertex from a simplex on which the labelling is injective removes exactly
its label. -/
theorem labels_erase_of_injOn (hinj : Set.InjOn lam s) {w : Fin n → ℤ} (hw : w ∈ s) :
    labels lam (s.erase w) = (labels lam s).erase (lam w) := by
  ext p
  constructor
  · intro hp
    obtain ⟨x, hx, rfl⟩ := mem_labels.1 hp
    obtain ⟨hxw, hxs⟩ := Finset.mem_erase.1 hx
    exact Finset.mem_erase.2
      ⟨fun hcon => hxw (hinj hxs hw hcon), mem_labels.2 ⟨x, hxs, rfl⟩⟩
  · intro hp
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hp
    obtain ⟨x, hx, rfl⟩ := mem_labels.1 hmem
    exact mem_labels.2 ⟨x, Finset.mem_erase.2 ⟨fun hcon => hne (by rw [hcon]), hx⟩, rfl⟩

/-! ### Doors as insertions and deletions

The doors above a happy simplex are its extensions by one vertex, and the doors below it
are its deletions of one vertex.  This turns both degrees into counts of vertices. -/

open scoped Classical in
/-- The doors above a happy simplex are the vertices extending it without adding a label
it does not already carry. -/
theorem upDeg_eq_card_extensions (h : IsHappy N lam s) :
    upDeg N lam s = (extensions N s (labels lam s)).card := by
  classical
  have hdoor : ∀ w ∈ extensions N s (labels lam s), IsDoor N lam s (insert w s) := by
    intro w hw
    obtain ⟨hws, ht, hsub⟩ := mem_extensions.1 hw
    exact { isSimplex := ht
            subset := Finset.subset_insert _ _
            card_succ := (Finset.card_insert_of_notMem hws).symm
            nonempty := h.isSimplex.nonempty
            signs_subset := hsub }
  refine (Finset.card_nbij (fun w => insert w s) (fun w hw => ?_) (fun w₁ h₁ w₂ h₂ heq => ?_)
    (fun τ hτ => ?_)).symm
  · rw [Finset.mem_coe] at hw
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨mem_happySet.2 (hdoor w hw).happy_right, hdoor w hw⟩
  · rw [Finset.mem_coe, mem_extensions] at h₁
    have heq' : insert w₁ s = insert w₂ s := heq
    have hmem : w₁ ∈ insert w₂ s := by
      rw [← heq']
      exact Finset.mem_insert_self w₁ s
    rcases Finset.mem_insert.1 hmem with hcase | hcase
    · exact hcase
    · exact absurd hcase h₁.1
  · rw [Finset.mem_coe, Finset.mem_filter] at hτ
    obtain ⟨w, hws, hins⟩ := Finset.exists_eq_insert_iff.2 ⟨hτ.2.subset, hτ.2.card_succ⟩
    refine ⟨w, ?_, hins⟩
    rw [Finset.mem_coe, mem_extensions]
    refine ⟨hws, by rw [hins]; exact hτ.2.isSimplex, by rw [hins]; exact hτ.2.signs_subset⟩

open scoped Classical in
/-- The doors below a happy simplex are the vertices whose deletion leaves a nonempty set
still carrying all of its signs. -/
theorem downDeg_eq_card_filter (hs : IsSimplex N s) :
    downDeg N lam s =
      (s.filter fun w => (s.erase w).Nonempty ∧ signs s ⊆ labels lam (s.erase w)).card := by
  classical
  refine (Finset.card_nbij (fun w => s.erase w) (fun w hw => ?_) (fun w₁ h₁ w₂ h₂ heq => ?_)
    (fun σ hσ => ?_)).symm
  · rw [Finset.mem_coe, Finset.mem_filter] at hw
    obtain ⟨hws, hne, hsub⟩ := hw
    have hpos : 0 < s.card := Finset.card_pos.2 ⟨w, hws⟩
    have hd : IsDoor N lam (s.erase w) s :=
      { isSimplex := hs
        subset := Finset.erase_subset _ _
        card_succ := by rw [Finset.card_erase_of_mem hws]; omega
        nonempty := hne
        signs_subset := hsub }
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨mem_happySet.2 hd.happy_left, hd⟩
  · rw [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
    exact Finset.erase_injOn s h₁.1 h₂.1 heq
  · rw [Finset.mem_coe, Finset.mem_filter] at hσ
    obtain ⟨w, hws, hins⟩ := Finset.exists_eq_insert_iff.2 ⟨hσ.2.subset, hσ.2.card_succ⟩
    have hwmem : w ∈ s := by
      rw [← hins]
      exact Finset.mem_insert_self w σ
    have herase : s.erase w = σ := by rw [← hins, Finset.erase_insert hws]
    refine ⟨w, ?_, herase⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨hwmem, by rw [herase]; exact hσ.2.nonempty, by rw [herase]; exact hσ.2.signs_subset⟩

/-! ### Labellings without a complementary edge

Tucker's lemma is proved by contradiction, so the whole degree computation runs under the
assumption that no simplex carries a pair of opposite labels. -/

/-- A labelling **separates** when no simplex of the grid carries a pair of opposite
labels.  Tucker's lemma says that a labelling antipodal on the boundary never does. -/
def Separates (N : ℕ) (lam : (Fin n → ℤ) → Label n) : Prop :=
  ∀ t : Finset (Fin n → ℤ), IsSimplex N t → ∀ x ∈ t, ∀ y ∈ t, lam x ≠ negLabel (lam y)

/-- Under a separating labelling a simplex carries no pair of opposite labels. -/
theorem Separates.negLabel_not_mem_labels (hsep : Separates N lam) (hs : IsSimplex N s)
    {l : Label n} (hl : l ∈ labels lam s) : negLabel l ∉ labels lam s := by
  intro hcon
  obtain ⟨x, hx, rfl⟩ := mem_labels.1 hl
  obtain ⟨y, hy, hy'⟩ := mem_labels.1 hcon
  exact hsep s hs y hy x hx hy'

/-! ### The shape of a happy simplex, in detail -/

/-- A happy simplex with as many labels as directions carries exactly its signs. -/
theorem IsHappy.labels_eq_signs (h : IsHappy N lam s)
    (hl : (labels lam s).card = (directions s).card) : labels lam s = signs s :=
  (Finset.eq_of_subset_of_card_le h.signs_subset
    (by rw [hl, h.isSimplex.card_signs])).symm

/-- A happy simplex with one more label than directions carries exactly one label beyond
its signs. -/
theorem IsHappy.exists_extra_label (h : IsHappy N lam s)
    (hl : (labels lam s).card = (directions s).card + 1) :
    ∃ l, l ∉ signs s ∧ labels lam s = insert l (signs s) := by
  classical
  have hsigns : (signs s).card = (directions s).card := h.isSimplex.card_signs
  have hcs : (labels lam s \ signs s).card = 1 := by
    rw [Finset.card_sdiff_of_subset h.signs_subset]
    omega
  obtain ⟨l, hlset⟩ := Finset.card_eq_one.1 hcs
  obtain ⟨hlmem, hlnot⟩ : l ∈ labels lam s ∧ l ∉ signs s :=
    Finset.mem_sdiff.1 (by rw [hlset]; exact Finset.mem_singleton_self l)
  refine ⟨l, hlnot, (Finset.eq_of_subset_of_card_le
    (Finset.insert_subset hlmem h.signs_subset) ?_).symm⟩
  rw [Finset.card_insert_of_notMem hlnot]
  omega

/-- Deleting a vertex keeps all the signs exactly when its label is not a sign. -/
theorem subset_labels_erase_iff (hinj : Set.InjOn lam s) (hsub : signs s ⊆ labels lam s)
    {w : Fin n → ℤ} (hw : w ∈ s) :
    signs s ⊆ labels lam (s.erase w) ↔ lam w ∉ signs s := by
  classical
  rw [labels_erase_of_injOn hinj hw]
  constructor
  · intro h hcon
    exact (Finset.mem_erase.1 (h hcon)).1 rfl
  · intro h q hq
    exact Finset.mem_erase.2 ⟨fun hcon => h (hcon ▸ hq), hsub hq⟩

/-- Exactly one vertex carries a given label when the labelling is injective. -/
theorem card_filter_lam_eq {l : Label n} [DecidablePred fun w : Fin n → ℤ => lam w = l]
    (hinj : Set.InjOn lam s) (hl : l ∈ labels lam s) :
    (s.filter fun w => lam w = l).card = 1 := by
  obtain ⟨x, hx, hxl⟩ := mem_labels.1 hl
  refine Finset.card_eq_one.2 ⟨x, ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_singleton]
  exact ⟨fun hy => hinj hy.1 hx (by rw [hy.2, hxl]), fun hy => ⟨hy ▸ hx, hy ▸ hxl⟩⟩

/-! ### The degree of a happy simplex

A happy simplex has degree two, except for the origin alone and for those with one
coordinate at the boundary of the cube, which have degree one. -/

/-- A happy simplex with one more vertex and one more label than it has directions has
exactly one door above it. -/
theorem upDeg_eq_one_of_card_eq_succ (hsep : Separates N lam) (hN : 0 < N)
    (h : IsHappy N lam s) (hv : s.card = (directions s).card + 1)
    (hl : (labels lam s).card = (directions s).card + 1) : upDeg N lam s = 1 := by
  obtain ⟨l, hlnot, hlabels⟩ := h.exists_extra_label hl
  rw [upDeg_eq_card_extensions h, hlabels]
  refine card_extensions_eq_one h.isSimplex hN hv hlnot fun hcon => ?_
  have h1 : l ∈ labels lam s := by
    rw [hlabels]
    exact Finset.mem_insert_self _ _
  exact hsep.negLabel_not_mem_labels h.isSimplex h1 (h.signs_subset hcon)

open scoped Classical in
/-- A happy simplex with one more vertex and one more label than it has directions, and
with more than one vertex, has exactly one door below it. -/
theorem downDeg_eq_one_of_card_eq_succ (h : IsHappy N lam s)
    (hv : s.card = (directions s).card + 1)
    (hl : (labels lam s).card = (directions s).card + 1) (h2 : 2 ≤ s.card) :
    downDeg N lam s = 1 := by
  classical
  obtain ⟨l, hlnot, hlabels⟩ := h.exists_extra_label hl
  have hinj : Set.InjOn lam s := injOn_lam_of_card (by omega)
  rw [downDeg_eq_card_filter h.isSimplex]
  have hfilter : (s.filter fun w => (s.erase w).Nonempty ∧ signs s ⊆ labels lam (s.erase w))
      = s.filter fun w => lam w = l := by
    refine Finset.filter_congr fun w hw => ?_
    have hne : (s.erase w).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hw]
      omega
    rw [subset_labels_erase_iff hinj h.signs_subset hw]
    constructor
    · rintro ⟨-, hns⟩
      have hmem : lam w ∈ labels lam s := mem_labels.2 ⟨w, hw, rfl⟩
      rw [hlabels, Finset.mem_insert] at hmem
      rcases hmem with hcase | hcase
      · exact hcase
      · exact absurd hcase hns
    · intro heq
      exact ⟨hne, by rw [heq]; exact hlnot⟩
  rw [hfilter]
  exact card_filter_lam_eq hinj (by rw [hlabels]; exact Finset.mem_insert_self _ _)

open scoped Classical in
/-- A single vertex has no door below it. -/
theorem downDeg_eq_zero_of_card_eq_one (hs : IsSimplex N s) (h1 : s.card = 1) :
    downDeg N lam s = 0 := by
  classical
  rw [downDeg_eq_card_filter hs, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w hw hcon
  have hpos := Finset.card_pos.2 hcon.1
  rw [Finset.card_erase_of_mem hw, h1] at hpos
  omega

/-- A happy simplex with one more vertex than labels has no door above it. -/
theorem upDeg_eq_zero_of_card_labels_eq (h : IsHappy N lam s)
    (hv : s.card = (directions s).card + 1)
    (hl : (labels lam s).card = (directions s).card) : upDeg N lam s = 0 := by
  rw [upDeg_eq_card_extensions h, h.labels_eq_signs hl, extensions_eq_empty h.isSimplex hv,
    Finset.card_empty]

open scoped Classical in
/-- A happy simplex with one more vertex than labels has exactly two doors below it: the
two vertices sharing a label. -/
theorem downDeg_eq_two_of_card_labels_eq (h : IsHappy N lam s)
    (hv : s.card = (directions s).card + 1)
    (hl : (labels lam s).card = (directions s).card) : downDeg N lam s = 2 := by
  classical
  have hls : labels lam s = signs s := h.labels_eq_signs hl
  have hlt : (labels lam s).card < s.card := by omega
  obtain ⟨u, hu, v, hv', huv, huvl⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
      (fun x hx => mem_labels.2 ⟨x, hx, rfl⟩)
  have hvu : v ∈ s.erase u := Finset.mem_erase.2 ⟨fun hc => huv hc.symm, hv'⟩
  have huv' : u ∈ s.erase v := Finset.mem_erase.2 ⟨huv, hu⟩
  -- deleting either of the two leaves all the labels
  have hlabels : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → lam x = lam y →
      labels lam (s.erase x) = labels lam s := by
    intro x hx y hy hxy hxyl
    refine Finset.Subset.antisymm (labels_subset (Finset.erase_subset _ _)) fun q hq => ?_
    obtain ⟨z, hz, rfl⟩ := mem_labels.1 hq
    rcases eq_or_ne z x with rfl | hzx
    · exact mem_labels.2 ⟨y, Finset.mem_erase.2 ⟨fun hc => hxy hc.symm, hy⟩, hxyl.symm⟩
    · exact mem_labels.2 ⟨z, Finset.mem_erase.2 ⟨hzx, hz⟩, rfl⟩
  have hlu : labels lam (s.erase u) = labels lam s := hlabels u hu v hv' huv huvl
  have hlv : labels lam (s.erase v) = labels lam s :=
    hlabels v hv' u hu (fun hc => huv hc.symm) huvl.symm
  -- outside the two, the labelling is injective
  have hinj : Set.InjOn lam (s.erase u) := by
    refine injOn_lam_of_card ?_
    rw [hlu, Finset.card_erase_of_mem hu]
    omega
  rw [downDeg_eq_card_filter h.isSimplex]
  have hfilter : (s.filter fun w => (s.erase w).Nonempty ∧ signs s ⊆ labels lam (s.erase w))
      = {u, v} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hw, -, hsub⟩
      -- the label of `w` survives the deletion, so some other vertex carries it
      have hmem : lam w ∈ labels lam (s.erase w) := by
        rw [← hls] at hsub
        exact hsub (mem_labels.2 ⟨w, hw, rfl⟩)
      obtain ⟨z, hz, hzl⟩ := mem_labels.1 hmem
      obtain ⟨hzw, hzs⟩ := Finset.mem_erase.1 hz
      by_contra hcon
      have hwu : w ≠ u := fun hc => hcon (Or.inl hc)
      have hwv : w ≠ v := fun hc => hcon (Or.inr hc)
      rcases eq_or_ne z u with rfl | hzu
      · exact hwv (hinj (Finset.mem_erase.2 ⟨hwu, hw⟩) hvu (by rw [← hzl, huvl]))
      · exact hzw (hinj (Finset.mem_erase.2 ⟨hzu, hzs⟩) (Finset.mem_erase.2 ⟨hwu, hw⟩) hzl)
    · rintro (rfl | rfl)
      · exact ⟨hu, ⟨v, hvu⟩, by rw [hlu, hls]⟩
      · exact ⟨hv', ⟨u, huv'⟩, by rw [hlv, hls]⟩
  rw [hfilter, Finset.card_insert_of_notMem (by simpa using huv), Finset.card_singleton]

open scoped Classical in
/-- A happy simplex with as many vertices as directions has no door below it. -/
theorem downDeg_eq_zero_of_card_eq (h : IsHappy N lam s)
    (hv : s.card = (directions s).card)
    (hl : (labels lam s).card = (directions s).card) : downDeg N lam s = 0 := by
  classical
  have hls : labels lam s = signs s := h.labels_eq_signs hl
  have hinj : Set.InjOn lam s := injOn_lam_of_card (by omega)
  rw [downDeg_eq_card_filter h.isSimplex, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w hw hcon
  refine (subset_labels_erase_iff hinj h.signs_subset hw).1 hcon.2 ?_
  rw [← hls]
  exact mem_labels.2 ⟨w, hw, rfl⟩

/-- A happy simplex with as many vertices as directions and no extremal coordinate has
exactly two doors above it. -/
theorem upDeg_eq_two_of_card_eq (h : IsHappy N lam s) (hv : s.card = (directions s).card)
    (hl : (labels lam s).card = (directions s).card) (hext : ¬ IsExtremal N s) :
    upDeg N lam s = 2 := by
  rw [upDeg_eq_card_extensions h, h.labels_eq_signs hl]
  exact card_extensions_eq_two h.isSimplex hv hext

/-- A happy simplex with as many vertices as directions and one extremal coordinate has
exactly one door above it: the cube blocks the other. -/
theorem upDeg_eq_one_of_card_eq (hN : 0 < N) (h : IsHappy N lam s)
    (hv : s.card = (directions s).card)
    (hl : (labels lam s).card = (directions s).card) (hext : IsExtremal N s) :
    upDeg N lam s = 1 := by
  rw [upDeg_eq_card_extensions h, h.labels_eq_signs hl]
  exact card_extensions_eq_one_of_isExtremal h.isSimplex hN hv hext

/-- **A happy simplex has odd degree exactly when it is the origin alone or has one
coordinate at the boundary of the cube.**

Every other happy simplex has degree two: it is joined to exactly two others. -/
theorem odd_deg_iff (hsep : Separates N lam) (hN : 0 < N) (h : IsHappy N lam s) :
    Odd (deg N lam s) ↔
      s = {0} ∨ (s.card = (directions s).card ∧ IsExtremal N s) := by
  by_cases hb : s.card = (directions s).card
  · -- as many vertices as directions
    have hl : (labels lam s).card = (directions s).card := by
      rcases h.shape with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
      · omega
      · omega
      · exact h2
    have hzero : s ≠ {0} := by
      intro hc
      rw [hc, Finset.card_singleton, directions_singleton_zero, Finset.card_empty] at hb
      omega
    by_cases hext : IsExtremal N s
    · simp only [deg, upDeg_eq_one_of_card_eq hN h hb hl hext,
        downDeg_eq_zero_of_card_eq h hb hl]
      exact ⟨fun _ => Or.inr ⟨hb, hext⟩, fun _ => by decide⟩
    · simp only [deg, upDeg_eq_two_of_card_eq h hb hl hext, downDeg_eq_zero_of_card_eq h hb hl]
      constructor
      · intro hodd
        exact absurd hodd (by decide)
      · rintro (hc | ⟨-, hc⟩)
        · exact absurd hc hzero
        · exact absurd hc hext
  · -- one more vertex than directions
    have hv : s.card = (directions s).card + 1 := by
      rcases h.shape with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    have hnotb : ¬(s.card = (directions s).card ∧ IsExtremal N s) := fun hc => hb hc.1
    rcases h.shape with ⟨-, hl⟩ | ⟨-, hl⟩ | ⟨h1, -⟩
    · -- distinct labels
      by_cases h2 : 2 ≤ s.card
      · have hzero : s ≠ {0} := by
          intro hc
          rw [hc, Finset.card_singleton] at h2
          omega
        simp only [deg, upDeg_eq_one_of_card_eq_succ hsep hN h hv hl,
          downDeg_eq_one_of_card_eq_succ h hv hl h2]
        constructor
        · intro hodd
          exact absurd hodd (by decide)
        · rintro (hc | hc)
          · exact absurd hc hzero
          · exact absurd hc hnotb
      · have h1 : s.card = 1 := by omega
        have hzero : s = {0} := eq_singleton_zero h.isSimplex h1 (by omega)
        simp only [deg, upDeg_eq_one_of_card_eq_succ hsep hN h hv hl,
          downDeg_eq_zero_of_card_eq_one h.isSimplex h1]
        exact ⟨fun _ => Or.inl hzero, fun _ => by decide⟩
    · -- one repeated label
      have hzero : s ≠ {0} := by
        intro hc
        have hpos : 0 < (labels lam s).card :=
          Finset.card_pos.2 (Finset.Nonempty.image h.isSimplex.nonempty lam)
        have hd : (directions s).card = 0 := by
          rw [hc, directions_singleton_zero, Finset.card_empty]
        omega
      simp only [deg, upDeg_eq_zero_of_card_labels_eq h hv hl,
        downDeg_eq_two_of_card_labels_eq h hv hl]
      constructor
      · intro hodd
        exact absurd hodd (by decide)
      · rintro (hc | hc)
        · exact absurd hc hzero
        · exact absurd hc hnotb
    · omega

/-! ### Tucker's lemma -/

/-- **Tucker's lemma.**

Label every point of the integer cube `[-N, N]ⁿ` by a coordinate together with a sign, so
that antipodal boundary points get opposite labels.  Then two points of one simplex of the
Kuhn triangulation carry opposite labels.

The proof counts the doors between happy simplices in two ways.  All but two kinds of
happy simplex have exactly two doors; the exceptions are the origin alone and the
simplices with one coordinate at the boundary of the cube, and reflection in the origin
pairs the latter up.  So the number of happy simplices of odd degree is odd, while
counting the doors from both ends makes it even. -/
theorem tucker (hN : 0 < N) (lam : (Fin n → ℤ) → Label n)
    (hlam : ∀ v ∈ grid n N, IsBoundary N v → lam (-v) = negLabel (lam v)) :
    ∃ u ∈ grid n N, ∃ w ∈ grid n N, u ≤ w ∧ (∀ i, w i - u i ≤ 1) ∧
      lam u = negLabel (lam w) := by
  classical
  by_contra hcon
  -- without such a pair, no simplex carries opposite labels
  have hsep : Separates N lam := by
    intro t ht x hx y hy heq
    refine hcon ?_
    rcases eq_or_ne x y with rfl | hne
    · exact ⟨x, ht.subset_grid hx, x, ht.subset_grid hx, le_rfl, fun i => by omega, heq⟩
    rcases ht.chain hx hy hne with hxy | hxy
    · exact ⟨x, ht.subset_grid hx, y, ht.subset_grid hy, hxy,
        fun i => ht.sub_le_one x hx y hy i, heq⟩
    · refine ⟨y, ht.subset_grid hy, x, ht.subset_grid hx, hxy,
        fun i => ht.sub_le_one y hy x hx i, ?_⟩
      rw [heq, negLabel_negLabel]
  -- the origin alone is happy
  have hzerohappy : IsHappy N lam ({0} : Finset (Fin n → ℤ)) :=
    { isSimplex := isSimplex_singleton zero_mem_grid
      signs_subset := by
        rw [signs_singleton_zero]
        exact Finset.empty_subset _ }
  have hzeromem : ({0} : Finset (Fin n → ℤ)) ∈ happySet N lam := mem_happySet.2 hzerohappy
  -- the happy simplices of odd degree are the origin and the extremal faces
  have hoddset : ((happySet N lam).filter fun t => Odd (deg N lam t)) =
      insert ({0} : Finset (Fin n → ℤ))
        ((happySet N lam).filter fun t => t.card = (directions t).card ∧ IsExtremal N t) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨ht, hodd⟩
      rcases (odd_deg_iff hsep hN (mem_happySet.1 ht)).1 hodd with hc | hc
      · exact Or.inl hc
      · exact Or.inr ⟨ht, hc⟩
    · rintro (rfl | ⟨ht, hc⟩)
      · exact ⟨hzeromem, (odd_deg_iff hsep hN hzerohappy).2 (Or.inl rfl)⟩
      · exact ⟨ht, (odd_deg_iff hsep hN (mem_happySet.1 ht)).2 (Or.inr hc)⟩
  have hzeronot : ({0} : Finset (Fin n → ℤ)) ∉
      (happySet N lam).filter fun t => t.card = (directions t).card ∧ IsExtremal N t := by
    intro hmem
    have h := (Finset.mem_filter.1 hmem).2.1
    rw [Finset.card_singleton, directions_singleton_zero, Finset.card_empty] at h
    omega
  -- reflection pairs the extremal faces up
  have hBeven : Even ((happySet N lam).filter
      fun t => t.card = (directions t).card ∧ IsExtremal N t).card := by
    refine Finset.even_card_of_involutive (f := fun t => -t) (fun t ht => ?_)
      (fun t _ => neg_neg t) (fun t ht => ?_)
    · rw [Finset.mem_filter] at ht ⊢
      obtain ⟨ht1, ht2, ht3⟩ := ht
      have hh : IsHappy N lam t := mem_happySet.1 ht1
      have hbd : ∀ z ∈ t, lam (-z) = negLabel (lam z) := by
        intro z hz
        obtain ⟨c, hc⟩ := ht3
        refine hlam z (hh.isSimplex.subset_grid hz) ⟨c, ?_⟩
        rcases hc with hc | hc
        · exact Or.inl (hc z hz)
        · exact Or.inr (hc z hz)
      refine ⟨mem_happySet.2 ⟨hh.isSimplex.neg, ?_⟩, ?_, ht3.neg⟩
      · rw [labels_neg_of_antipodal hbd, signs_neg]
        exact Finset.image_subset_image hh.signs_subset
      · rw [Finset.card_neg, directions_neg]
        exact ht2
    · rw [Finset.mem_filter] at ht
      exact ht.2.2.neg_ne (mem_happySet.1 ht.1).isSimplex.nonempty hN
  have heven := even_card_odd_deg N lam
  rw [hoddset, Finset.card_insert_of_notMem hzeronot] at heven
  obtain ⟨m, hm⟩ := heven
  obtain ⟨m', hm'⟩ := hBeven
  omega


end GridSimplex

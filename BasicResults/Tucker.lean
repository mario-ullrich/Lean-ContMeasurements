/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import BasicResults.GridSimplex

/-!
# Tucker's lemma

Tucker's lemma is the combinatorial form of the Borsuk–Ulam theorem.  Label every point of
the integer cube `[-N, N]ⁿ` by a coordinate together with a sign, so that antipodal
boundary points receive opposite labels.  Then some simplex of the Kuhn triangulation
carries two opposite labels.

The proof is a parity argument.  Call a simplex **happy** when every sign it carries also
occurs as a label on it.  Assuming no simplex carries two opposite labels, a happy simplex
comes in one of three shapes, according to whether it has as many vertices as directions or
one more, and whether its labels are distinct.  Joining a happy simplex to the happy
simplices obtained by adding or deleting one vertex gives a graph in which all but two
kinds of vertex have degree two.  The odd-degree vertices are the single point `{0}` and
certain simplices on the boundary, and reflection in the origin pairs the latter up.  So
their number is even, while the handshake lemma makes the total number of odd-degree
vertices even.  That is a contradiction.

## Main definitions

* `GridSimplex.labels` — the labels occurring on a simplex.
* `GridSimplex.IsHappy` — a simplex all of whose signs occur as labels on it.
-/

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

end GridSimplex

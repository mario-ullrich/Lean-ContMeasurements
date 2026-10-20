/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Algebra.Group.EvenFunction
import BasicResults.Tucker

/-!
# The Borsuk–Ulam theorem

The odd-map form of the Borsuk–Ulam theorem states that a continuous odd map from the
sphere `S^{m-1}` into `ℝᵏ` with `k < m` must vanish somewhere.  Equivalently, a
continuous map `S^{m-1} → ℝᵏ` with `k < m` takes the same value at some antipodal
pair.

Mathlib has neither this theorem nor Brouwer's fixed point theorem nor Sperner's lemma,
so it is proved here, combinatorially.  Tucker's lemma (`GridSimplex.tucker`) gives the
cube form `borsukUlam_cube`: a map of the cube into `ℝⁿ`, continuous on the cube and odd
on its boundary, vanishes somewhere.  Lifting the cube onto the unit sphere of the sup
norm and projecting that radially onto the Euclidean sphere gives the statement above.

## Main statements

* `borsukUlam_cube` — Borsuk's antipodal theorem for the cube, from Tucker's lemma by
  uniform continuity.
* `borsukUlam_pi` — the odd-map form on the unit sphere of `Fin m → ℝ` with the sup
  norm, which is the boundary of a cube one dimension lower.
* `borsukUlam` — the theorem itself, on the unit sphere of `EuclideanSpace ℝ (Fin m)`.
* `Function.Odd.exists_norm_eq_and_eq_zero_of_lt_finrank` — the form actually used: on
  *any* finite-dimensional real normed space `E` of dimension `m`, and on the sphere
  of *any* radius `R > 0`, a continuous odd map `E → ℝᵏ` with `k < m` has a zero.
  This is proved from the Euclidean case by transporting along a linear
  homeomorphism and rescaling radially, and it is what makes the lower bound valid
  for an arbitrary norm.
-/

open Metric

/-! ### Labelling a point by its largest coordinate

Tucker's lemma is applied to the labelling that sends a point of the cube to the
coordinate in which its image is largest, together with the sign there.  Taking the
**least** such coordinate is what makes the labelling antipodal: reflecting a point
reverses every coordinate of its image without moving the set of largest ones. -/

namespace CubeLabel

variable {n : ℕ}

open scoped Classical in
/-- The coordinates in which `y` attains its sup norm. -/
noncomputable def maxCoords (y : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => ‖y‖ ≤ |y i|

/-- Membership in `maxCoords`, unfolded. -/
theorem mem_maxCoords {y : Fin n → ℝ} {i : Fin n} : i ∈ maxCoords y ↔ ‖y‖ ≤ |y i| := by
  classical
  simp [maxCoords]

/-- At a largest coordinate the absolute value is the sup norm. -/
theorem abs_eq_norm_of_mem {y : Fin n → ℝ} {i : Fin n} (hi : i ∈ maxCoords y) :
    |y i| = ‖y‖ :=
  le_antisymm (by simpa [Real.norm_eq_abs] using norm_le_pi_norm y i) (mem_maxCoords.1 hi)

/-- Some coordinate attains the sup norm. -/
theorem maxCoords_nonempty (hn : 0 < n) (y : Fin n → ℝ) : (maxCoords y).Nonempty := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun i => |y i|)
      Finset.univ_nonempty
  refine ⟨j, mem_maxCoords.2 ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => ?_)⟩
  simpa [Real.norm_eq_abs] using hj i (Finset.mem_univ i)

/-- Reflection does not move the largest coordinates. -/
theorem maxCoords_neg (y : Fin n → ℝ) : maxCoords (-y) = maxCoords y := by
  classical
  ext i
  simp [mem_maxCoords]

open scoped Classical in
/-- The least coordinate in which `y` attains its sup norm. -/
noncomputable def maxIdx (hn : 0 < n) (y : Fin n → ℝ) : Fin n :=
  (maxCoords y).min' (maxCoords_nonempty hn y)

/-- The chosen coordinate is a largest one. -/
theorem maxIdx_mem (hn : 0 < n) (y : Fin n → ℝ) : maxIdx hn y ∈ maxCoords y :=
  Finset.min'_mem _ _

/-- At the chosen coordinate the absolute value is the sup norm. -/
theorem abs_maxIdx (hn : 0 < n) (y : Fin n → ℝ) : |y (maxIdx hn y)| = ‖y‖ :=
  abs_eq_norm_of_mem (maxIdx_mem hn y)

/-- Reflection does not move the chosen coordinate. -/
theorem maxIdx_neg (hn : 0 < n) (y : Fin n → ℝ) : maxIdx hn (-y) = maxIdx hn y :=
  le_antisymm
    (Finset.min'_le _ _ (by rw [maxCoords_neg]; exact maxIdx_mem hn y))
    (Finset.min'_le _ _ (by rw [← maxCoords_neg]; exact maxIdx_mem hn (-y)))

/-- The label of a point: the least coordinate of largest absolute value, together with
its sign. -/
noncomputable def label (hn : 0 < n) (y : Fin n → ℝ) : GridSimplex.Label n :=
  (maxIdx hn y, if 0 < y (maxIdx hn y) then true else false)

/-- A positively labelled point attains its sup norm there with a positive sign. -/
theorem norm_le_of_label_true (hn : 0 < n) {y : Fin n → ℝ} {i : Fin n}
    (h : label hn y = (i, true)) : ‖y‖ ≤ y i := by
  have hi : maxIdx hn y = i := congrArg Prod.fst h
  have hs : (if 0 < y (maxIdx hn y) then true else false) = true := congrArg Prod.snd h
  have hpos : 0 < y (maxIdx hn y) := by
    by_contra hcon
    rw [ite_eq_right hcon] at hs
    exact Bool.noConfusion hs
  rw [← hi, ← abs_maxIdx hn y, abs_of_pos hpos]

/-- A negatively labelled point attains its sup norm there with a negative sign. -/
theorem le_neg_norm_of_label_false (hn : 0 < n) {y : Fin n → ℝ} {i : Fin n}
    (h : label hn y = (i, false)) : y i ≤ -‖y‖ := by
  have hi : maxIdx hn y = i := congrArg Prod.fst h
  have hs : (if 0 < y (maxIdx hn y) then true else false) = false := congrArg Prod.snd h
  have hnpos : ¬ 0 < y (maxIdx hn y) := by
    intro hcon
    rw [ite_eq_left hcon] at hs
    exact Bool.noConfusion hs
  have habs := abs_maxIdx hn y
  rw [abs_of_nonpos (not_lt.1 hnpos)] at habs
  rw [← hi]
  linarith

/-- **Reflection reverses the label**, away from the origin. -/
theorem label_neg (hn : 0 < n) {y : Fin n → ℝ} (hy : y ≠ 0) :
    label hn (-y) = GridSimplex.negLabel (label hn y) := by
  have hi := maxIdx_neg hn y
  have habs := abs_maxIdx hn y
  have hnorm : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hne : y (maxIdx hn y) ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at habs
    linarith
  simp only [label, GridSimplex.negLabel, hi]
  congr 1
  simp only [Pi.neg_apply]
  by_cases hpos : 0 < y (maxIdx hn y)
  · rw [ite_eq_left hpos, ite_eq_right (by linarith), Bool.not_true]
  · have hneg : y (maxIdx hn y) < 0 := lt_of_le_of_ne (not_lt.1 hpos) hne
    rw [ite_eq_right hpos, ite_eq_left (by linarith), Bool.not_false]

end CubeLabel

/-! ### Borsuk's antipodal theorem for the cube -/

open GridSimplex in
/-- **Borsuk's antipodal theorem, cube form.**

A map of the cube `[-1, 1]ⁿ` into `ℝⁿ` that is continuous on the cube and odd on its
boundary vanishes somewhere in the cube.  Here `Fin n → ℝ` carries the sup norm, so the
closed unit ball is the cube and the unit sphere is its boundary.

The proof is Tucker's lemma plus uniform continuity.  If the map never vanished, its norm
would have a positive minimum `ε` on the compact cube.  Choose a mesh `1 / N` below the
modulus of continuity for `2 * ε` and label each grid point of `[-N, N]ⁿ` by the
coordinate in which its image is largest, together with the sign there.  Oddness on the
boundary makes this labelling antipodal, so Tucker's lemma gives two neighbouring grid
points whose labels are opposite.  Their images then differ by at least `2 * ε` in one
coordinate, although the points are closer than the mesh. -/
theorem borsukUlam_cube {n : ℕ} (hn : 0 < n) (g : (Fin n → ℝ) → (Fin n → ℝ))
    (hg : ContinuousOn g (closedBall 0 1))
    (hodd : ∀ x : Fin n → ℝ, ‖x‖ = 1 → g (-x) = -g x) :
    ∃ x ∈ closedBall (0 : Fin n → ℝ) 1, g x = 0 := by
  by_contra hcon
  have hzero : ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, g x ≠ 0 :=
    fun x hx h0 => hcon ⟨x, hx, h0⟩
  -- the image is bounded away from the origin on the cube
  have hK : IsCompact (closedBall (0 : Fin n → ℝ) 1) := isCompact_closedBall 0 1
  have hKne : (closedBall (0 : Fin n → ℝ) 1).Nonempty :=
    ⟨0, mem_closedBall_self zero_le_one⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKne (continuous_norm.comp_continuousOn hg)
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = ‖g x₀‖ := ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    rw [hε]
    exact norm_pos_iff.2 (hzero x₀ hx₀)
  have hlow : ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ε ≤ ‖g x‖ := by
    intro x hx
    rw [hε]
    exact isMinOn_iff.1 hmin x hx
  -- a mesh finer than the modulus of continuity for `2 * ε`
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hg) (2 * ε)
      (by linarith)
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = max M 1 := ⟨_, rfl⟩
  have hNpos : 0 < N := by
    rw [hNdef]
    exact lt_of_lt_of_le Nat.one_pos (le_max_right M 1)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hmesh : 1 / (N : ℝ) < δ := by
    have hMN : M ≤ N := by
      rw [hNdef]
      exact le_max_left M 1
    have h1 : (1 : ℝ) / δ < N := lt_of_lt_of_le hM (by exact_mod_cast hMN)
    rw [div_lt_iff₀ hδpos] at h1
    rw [div_lt_iff₀ hNreal, mul_comm]
    exact h1
  -- the grid points, rescaled into the cube
  obtain ⟨pt, hpt⟩ : ∃ pt : (Fin n → ℤ) → (Fin n → ℝ), ∀ v i, pt v i = (v i : ℝ) / N :=
    ⟨_, fun _ _ => rfl⟩
  have hptmem : ∀ v ∈ grid n N, pt v ∈ closedBall (0 : Fin n → ℝ) 1 := by
    intro v hv
    rw [mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    rw [Real.norm_eq_abs, hpt, abs_div, abs_of_pos hNreal, div_le_one hNreal, abs_le]
    have h := (mem_grid.1 hv) i
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  -- the boundary of the grid lands on the unit sphere of the sup norm
  have hnorm_one : ∀ v ∈ grid n N, IsBoundary N v → ‖pt v‖ = 1 := by
    intro v hv hb
    obtain ⟨c, hc⟩ := hb
    refine le_antisymm ?_ ?_
    · have h := hptmem v hv
      rwa [mem_closedBall, dist_zero_right] at h
    · have hvc : |((v c : ℤ) : ℝ)| = (N : ℝ) := by
        rcases hc with h | h <;> rw [h] <;> push_cast
        · exact abs_of_pos hNreal
        · rw [abs_neg]
          exact abs_of_pos hNreal
      have h1 : |pt v c| = 1 := by
        rw [hpt, abs_div, hvc, abs_of_pos hNreal, div_self (ne_of_gt hNreal)]
      calc (1 : ℝ) = |pt v c| := h1.symm
        _ ≤ ‖pt v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm (pt v) c
  -- the labelling, antipodal on the boundary
  obtain ⟨lam, hlamdef⟩ :
      ∃ lam : (Fin n → ℤ) → Label n, ∀ v, lam v = CubeLabel.label hn (g (pt v)) :=
    ⟨_, fun _ => rfl⟩
  have hantip : ∀ v ∈ grid n N, IsBoundary N v → lam (-v) = negLabel (lam v) := by
    intro v hv hb
    have hptneg : pt (-v) = -(pt v) := by
      funext i
      simp only [hpt, Pi.neg_apply]
      push_cast
      ring
    have hgneg : g (pt (-v)) = -(g (pt v)) := by
      rw [hptneg]
      exact hodd _ (hnorm_one v hv hb)
    rw [hlamdef, hlamdef, hgneg]
    exact CubeLabel.label_neg hn (hzero _ (hptmem v hv))
  -- Tucker's lemma produces two neighbouring points with opposite labels
  obtain ⟨u, hu, w, hw, huw, hspan, hlab⟩ := tucker hNpos lam hantip
  obtain ⟨i, hidef⟩ : ∃ i, i = (lam w).1 := ⟨_, rfl⟩
  have hlw : lam w = (i, (lam w).2) := by rw [hidef]
  have hlu : lam u = (i, !(lam w).2) := by rw [hlab, negLabel, hidef]
  have hεu : ε ≤ ‖g (pt u)‖ := hlow _ (hptmem u hu)
  have hεw : ε ≤ ‖g (pt w)‖ := hlow _ (hptmem w hw)
  -- at that coordinate the two images differ by at least `2 * ε`
  have hkey : 2 * ε ≤ |g (pt u) i - g (pt w) i| := by
    cases hb : (lam w).2
    · have hw' : CubeLabel.label hn (g (pt w)) = (i, false) := by
        rw [← hlamdef w, hlw, hb]
      have hu' : CubeLabel.label hn (g (pt u)) = (i, true) := by
        rw [← hlamdef u, hlu, hb, Bool.not_false]
      have h1 : g (pt w) i ≤ -‖g (pt w)‖ := CubeLabel.le_neg_norm_of_label_false hn hw'
      have h2 : ‖g (pt u)‖ ≤ g (pt u) i := CubeLabel.norm_le_of_label_true hn hu'
      linarith [le_abs_self (g (pt u) i - g (pt w) i)]
    · have hw' : CubeLabel.label hn (g (pt w)) = (i, true) := by
        rw [← hlamdef w, hlw, hb]
      have hu' : CubeLabel.label hn (g (pt u)) = (i, false) := by
        rw [← hlamdef u, hlu, hb, Bool.not_true]
      have h1 : ‖g (pt w)‖ ≤ g (pt w) i := CubeLabel.norm_le_of_label_true hn hw'
      have h2 : g (pt u) i ≤ -‖g (pt u)‖ := CubeLabel.le_neg_norm_of_label_false hn hu'
      linarith [neg_abs_le (g (pt u) i - g (pt w) i)]
  -- but the two points are closer than the modulus of continuity allows
  have hdistpt : dist (pt u) (pt w) < δ := by
    have hle : dist (pt u) (pt w) ≤ 1 / (N : ℝ) := by
      refine (dist_pi_le_iff (by positivity)).2 fun j => ?_
      have h1 : u j ≤ w j := Pi.le_def.1 huw j
      have h2 : w j - u j ≤ 1 := hspan j
      have hr : |(u j : ℝ) - (w j : ℝ)| ≤ 1 := by
        rw [abs_le]
        constructor
        · have h3 : (w j : ℝ) - (u j : ℝ) ≤ 1 := by exact_mod_cast h2
          linarith
        · have h3 : (u j : ℝ) ≤ (w j : ℝ) := by exact_mod_cast h1
          linarith
      rw [Real.dist_eq, hpt, hpt, div_sub_div_same, abs_div, abs_of_pos hNreal]
      gcongr
    linarith
  have hdistlt : dist (g (pt u)) (g (pt w)) < 2 * ε :=
    hδ (pt u) (hptmem u hu) (pt w) (hptmem w hw) hdistpt
  have hdistge : 2 * ε ≤ dist (g (pt u)) (g (pt w)) := by
    refine le_trans hkey ?_
    rw [← Real.dist_eq]
    exact dist_le_pi_dist _ _ i
  linarith


/-! ### From the cube to the sphere

The cube `[-1, 1]ⁿ` maps onto the unit sphere of `ℝ^{n+1}` by lifting a point to the
height left over by its sup norm and then projecting radially.  On the boundary of the
cube the slack vanishes, so there the map is odd. -/

namespace CubeSphere

variable {n : ℕ}

/-- The lift of a point of `ℝⁿ` to `ℝ^{n+1}`: its own coordinates, with the slack of its
sup norm as the last one. -/
noncomputable def lift (x : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.snoc x (1 - ‖x‖)

/-- The lift keeps the original coordinates. -/
@[simp]
theorem lift_castSucc (x : Fin n → ℝ) (j : Fin n) : lift x j.castSucc = x j := by
  simp [lift]

/-- The last coordinate of the lift is the slack of the sup norm. -/
@[simp]
theorem lift_last (x : Fin n → ℝ) : lift x (Fin.last n) = 1 - ‖x‖ := by
  simp [lift]

/-- Lifting does not decrease the sup norm. -/
theorem norm_le_norm_lift (x : Fin n → ℝ) : ‖x‖ ≤ ‖lift x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have h := norm_le_pi_norm (lift x) j.castSucc
  rwa [lift_castSucc] at h

/-- The slack is bounded by the norm of the lift. -/
theorem abs_one_sub_norm_le (x : Fin n → ℝ) : |1 - ‖x‖| ≤ ‖lift x‖ := by
  have h := norm_le_pi_norm (lift x) (Fin.last n)
  rwa [lift_last, Real.norm_eq_abs] at h

/-- **The lift never comes near the origin.**  Either the point itself is large, or its
slack is. -/
theorem half_le_norm_lift (x : Fin n → ℝ) : (1 : ℝ) / 2 ≤ ‖lift x‖ := by
  rcases le_total (1 / 2 : ℝ) ‖x‖ with h | h
  · exact le_trans h (norm_le_norm_lift x)
  · refine le_trans ?_ (abs_one_sub_norm_le x)
    rw [abs_of_nonneg (by linarith [norm_nonneg x])]
    linarith

/-- The lift is never the origin. -/
theorem norm_lift_pos (x : Fin n → ℝ) : 0 < ‖lift x‖ :=
  lt_of_lt_of_le (by norm_num) (half_le_norm_lift x)

/-- On the boundary of the cube the slack vanishes, so the lift is odd there. -/
theorem lift_neg_of_norm_eq_one {x : Fin n → ℝ} (hx : ‖x‖ = 1) : lift (-x) = -(lift x) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [hx]
  | cast j => simp

/-- The lift is continuous. -/
theorem continuous_lift : Continuous (lift : (Fin n → ℝ) → Fin (n + 1) → ℝ) := by
  refine continuous_pi fun i => ?_
  induction i using Fin.lastCases with
  | last =>
    simp only [lift_last]
    exact continuous_const.sub continuous_norm
  | cast j =>
    simp only [lift_castSucc]
    exact continuous_apply j

/-- The radial projection of the lift onto the unit sphere of `ℝ^{n+1}`. -/
noncomputable def proj (x : Fin n → ℝ) : Fin (n + 1) → ℝ := ‖lift x‖⁻¹ • lift x

/-- The projection lands on the unit sphere. -/
theorem norm_proj (x : Fin n → ℝ) : ‖proj x‖ = 1 := by
  rw [proj, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt (norm_lift_pos x))]

/-- On the boundary of the cube the projection is odd. -/
theorem proj_neg_of_norm_eq_one {x : Fin n → ℝ} (hx : ‖x‖ = 1) : proj (-x) = -(proj x) := by
  rw [proj, proj, lift_neg_of_norm_eq_one hx, norm_neg, smul_neg]

/-- The projection is continuous, because the lift stays away from the origin. -/
theorem continuous_proj : Continuous (proj : (Fin n → ℝ) → Fin (n + 1) → ℝ) := by
  have h1 : Continuous fun x : Fin n → ℝ => ‖lift x‖ := continuous_norm.comp continuous_lift
  have h2 : Continuous fun x : Fin n → ℝ => (‖lift x‖)⁻¹ :=
    h1.inv₀ fun x => ne_of_gt (norm_lift_pos x)
  exact h2.smul continuous_lift

end CubeSphere

/-- **Borsuk–Ulam theorem for the sup norm.**

A map into `ℝᵏ` with `k < m` that is odd and continuous on the unit sphere of
`Fin m → ℝ`, taken with the sup norm, vanishes at some point of that sphere.

The unit sphere of the sup norm is the boundary of the cube one dimension lower, reached
by `CubeSphere.proj`; padding the values with zeros to `m - 1` coordinates turns the
statement into `borsukUlam_cube`. -/
theorem borsukUlam_pi {m k : ℕ} (hk : k < m) (f : (Fin m → ℝ) → (Fin k → ℝ))
    (hf : ContinuousOn f (sphere 0 1)) (hodd : Function.Odd f) :
    ∃ x ∈ sphere (0 : Fin m → ℝ) 1, f x = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · -- with no functional, any point of the sphere will do
    have hmpos : 0 < m := hk
    refine ⟨fun _ => 1, ?_, funext fun i => absurd i.2 (by omega)⟩
    rw [mem_sphere_zero_iff_norm]
    refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp) ?_
    simpa using norm_le_pi_norm (fun _ : Fin m => (1 : ℝ)) ⟨0, hmpos⟩
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hn : 0 < n := by omega
    have hkn : k ≤ n := by omega
    -- pad the values with zeros to `n` coordinates
    obtain ⟨pad, hpad⟩ : ∃ pad : (Fin k → ℝ) → (Fin n → ℝ),
        ∀ z j, pad z j = if h : (j : ℕ) < k then z ⟨j, h⟩ else 0 := ⟨_, fun _ _ => rfl⟩
    have hpadcont : Continuous pad := by
      refine continuous_pi fun j => ?_
      by_cases h : (j : ℕ) < k
      · simp only [hpad, dite_eq_left h]
        exact continuous_apply _
      · simp only [hpad, dite_eq_right h]
        exact continuous_const
    have hpadodd : ∀ z : Fin k → ℝ, pad (-z) = -(pad z) := by
      intro z
      funext j
      rw [Pi.neg_apply, hpad, hpad]
      by_cases h : (j : ℕ) < k
      · rw [dite_eq_left h, dite_eq_left h, Pi.neg_apply]
      · rw [dite_eq_right h, dite_eq_right h, neg_zero]
    have hpadzero : ∀ z : Fin k → ℝ, pad z = 0 → z = 0 := by
      intro z hz
      funext i
      have hi : (i : ℕ) < n := lt_of_lt_of_le i.2 hkn
      have h := congrFun hz ⟨i, hi⟩
      rw [hpad, dite_eq_left i.2] at h
      simpa using h
    -- the map on the cube
    obtain ⟨g, hgdef⟩ : ∃ g : (Fin n → ℝ) → (Fin n → ℝ),
        ∀ x, g x = pad (f (CubeSphere.proj x)) := ⟨_, fun _ => rfl⟩
    have hprojmem : ∀ x : Fin n → ℝ, CubeSphere.proj x ∈ sphere (0 : Fin (n + 1) → ℝ) 1 := by
      intro x
      rw [mem_sphere_zero_iff_norm]
      exact CubeSphere.norm_proj x
    have hgcont : Continuous g := by
      have h1 : Continuous fun x : Fin n → ℝ => f (CubeSphere.proj x) :=
        hf.comp_continuous CubeSphere.continuous_proj hprojmem
      have h2 : g = fun x => pad (f (CubeSphere.proj x)) := funext hgdef
      rw [h2]
      exact hpadcont.comp h1
    have hgodd : ∀ x : Fin n → ℝ, ‖x‖ = 1 → g (-x) = -g x := by
      intro x hx
      rw [hgdef, hgdef, CubeSphere.proj_neg_of_norm_eq_one hx, hodd, hpadodd]
    obtain ⟨x, -, hgx⟩ := borsukUlam_cube hn g hgcont.continuousOn hgodd
    refine ⟨CubeSphere.proj x, hprojmem x, hpadzero _ ?_⟩
    rwa [hgdef] at hgx


/-- **Borsuk–Ulam theorem** (odd-map form).  A map into `ℝᵏ` with `k < m` that is odd
and continuous on the unit sphere of `ℝᵐ` vanishes at some point of that sphere.

Equivalently: `k < m` continuous functionals cannot separate all antipodal pairs of
`S^{m-1}`.

The Euclidean sphere is reached from the sphere of the sup norm by projecting radially
along a linear homeomorphism, which is odd and continuous away from the origin. -/
theorem borsukUlam {m k : ℕ} (hk : k < m)
    (f : EuclideanSpace ℝ (Fin m) → (Fin k → ℝ))
    (hf : ContinuousOn f (Metric.sphere 0 1)) (hodd : Function.Odd f) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1, f x = 0 := by
  -- the identity onto the Euclidean model, as a linear homeomorphism
  let e : (Fin m → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin m) := (EuclideanSpace.equiv (Fin m) ℝ).symm
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m),
      ∀ u, Φ u = ‖e u‖⁻¹ • e u := ⟨_, fun _ => rfl⟩
  have hene : ∀ u : Fin m → ℝ, ‖u‖ = 1 → ‖e u‖ ≠ 0 := by
    intro u hu
    rw [norm_ne_zero_iff]
    intro h0
    have hu0 : u = 0 := by simpa using congrArg e.symm h0
    rw [hu0, norm_zero] at hu
    exact zero_ne_one hu
  have hΦnorm : ∀ u : Fin m → ℝ, ‖u‖ = 1 → ‖Φ u‖ = 1 := by
    intro u hu
    rw [hΦ, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hene u hu)]
  have hΦodd : Function.Odd Φ := by
    intro u
    rw [hΦ, hΦ, map_neg, norm_neg, smul_neg]
  have hΦcont : ContinuousOn Φ (Metric.sphere (0 : Fin m → ℝ) 1) := by
    have hfun : Φ = fun u => ‖e u‖⁻¹ • e u := funext hΦ
    rw [hfun]
    exact ((e.continuous.norm.continuousOn).inv₀
      fun u hu => hene u (mem_sphere_zero_iff_norm.1 hu)).smul e.continuous.continuousOn
  have hmaps : ∀ u ∈ Metric.sphere (0 : Fin m → ℝ) 1,
      Φ u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 := by
    intro u hu
    rw [mem_sphere_zero_iff_norm]
    exact hΦnorm u (mem_sphere_zero_iff_norm.1 hu)
  have hcont : ContinuousOn (fun u => f (Φ u)) (Metric.sphere (0 : Fin m → ℝ) 1) :=
    hf.comp hΦcont hmaps
  have hoddc : Function.Odd fun u => f (Φ u) := by
    intro u
    show f (Φ (-u)) = -f (Φ u)
    rw [hΦodd u, hodd]
  obtain ⟨u, hu, hfu⟩ := borsukUlam_pi hk (fun u => f (Φ u)) hcont hoddc
  exact ⟨Φ u, hmaps u hu, hfu⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Borsuk–Ulam for an arbitrary norm and an arbitrary radius.**

On a real normed space of finite dimension `m`, every continuous odd map
`Ψ : E → ℝᵏ` with `k < m` vanishes at some point of norm `R`, for every `R > 0`.

The reduction to the Euclidean unit sphere is purely formal: a linear homeomorphism
`EuclideanSpace ℝ (Fin m) ≃L[ℝ] E` carries the Euclidean unit sphere onto a compact
symmetric set, and the radial map `u ↦ (R / ‖e u‖) • e u` sends it onto the sphere of
radius `R` of `E` oddly and continuously.  No property of the norm of `E` is used
beyond homogeneity, which is why the lower bound holds for *any* norm. -/
theorem Function.Odd.exists_norm_eq_and_eq_zero_of_lt_finrank {m k : ℕ}
    (hm : Module.finrank ℝ E = m) (hk : k < m) {R : ℝ} (hR : 0 < R)
    (Ψ : E → (Fin k → ℝ)) (hΨc : Continuous Ψ) (hΨo : Function.Odd Ψ) :
    ∃ x : E, ‖x‖ = R ∧ Ψ x = 0 := by
  -- A linear homeomorphism from the Euclidean model space.
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin.trans hm.symm)
  -- The radial map onto the sphere of radius `R`, introduced with a pointwise defining
  -- equation so that rewriting under it stays straightforward.
  obtain ⟨g, hg⟩ :
      ∃ g : EuclideanSpace ℝ (Fin m) → E, ∀ u, g u = (R / ‖e u‖) • e u :=
    ⟨_, fun _ => rfl⟩
  have hne : ∀ u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1, ‖e u‖ ≠ 0 := by
    intro u hu
    rw [norm_ne_zero_iff]
    intro h0
    have hu0 : u = 0 := by simpa using congrArg e.symm h0
    rw [mem_sphere_zero_iff_norm, hu0, norm_zero] at hu
    exact zero_ne_one hu
  -- `g` is odd, since `e` is linear and the norm is even.
  have hgodd : Function.Odd g := by
    intro u
    rw [hg, hg, map_neg, norm_neg, smul_neg]
  -- `g` is continuous away from the origin, in particular on the unit sphere.
  have hgcont : ContinuousOn g (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) := by
    have hgfun : g = fun u => (R / ‖e u‖) • e u := funext hg
    rw [hgfun]
    exact (continuousOn_const.div e.continuous.norm.continuousOn hne).smul
      e.continuous.continuousOn
  have hcont : ContinuousOn (Ψ ∘ g) (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    hΨc.comp_continuousOn hgcont
  have hodd : Function.Odd (Ψ ∘ g) := by
    intro u
    show Ψ (g (-u)) = -Ψ (g u)
    rw [hgodd u, hΨo]
  -- Borsuk–Ulam produces a zero on the unit sphere; rescaling gives the point wanted.
  obtain ⟨u₀, hu₀, hzero⟩ := borsukUlam hk (Ψ ∘ g) hcont hodd
  refine ⟨g u₀, ?_, hzero⟩
  have h1 : ‖e u₀‖ ≠ 0 := hne u₀ hu₀
  have h2 : (0 : ℝ) < ‖e u₀‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h1)
  rw [hg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_cancel₀ _ h1]

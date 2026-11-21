/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Adaptive continuous measurements: the model

An *algorithm using `n` adaptive continuous measurements* on a space `X` observes a
point `x ∈ X` through `n` real numbers, and each measurement may be chosen on the
basis of the values already observed:

* the first measurement is a fixed continuous functional `λ₁ : X → ℝ`, giving
  `y₁ = λ₁ x`;
* for `2 ≤ k ≤ n` there is an **arbitrary** rule `(y₁, …, y_{k-1}) ↦ λ_k^{(y)}`
  assigning to each vector of already observed values a continuous functional, and
  `y_k = λ_k^{(y₁,…,y_{k-1})} x`.

The resulting *information map* is `N : X → ℝⁿ`, `N x = (y₁, …, y_n)`, and an
algorithm is `A = Φ ∘ N` with an arbitrary reconstruction map `Φ : ℝⁿ → X`.

The point of the model is the contrast between the two kinds of dependence.  In `x`
every single measurement is continuous; in the observed values `y` the rule may be
completely irregular.  Consequently `N` itself is in general **discontinuous**, which
is exactly why the Borsuk–Ulam theorem does not apply to it directly, and why `n` can
be exponentially smaller than `dim X`.

## Main definitions

* `ContMeasurements.AdaptiveScheme X`: the rule `λ` in bundled form: a family
  `fct k y : X → ℝ` of continuous functionals, indexed by the number `k` of values
  already observed and by those values `y : Fin k → ℝ`.
* `ContMeasurements.AdaptiveScheme.first`: the first functional `λ₁`.
* `ContMeasurements.AdaptiveScheme.tail`: the scheme that governs the remaining
  measurements once the first value `y` has been observed.  This is the formal
  counterpart of "the algorithm continues with one measurement less".
* `ContMeasurements.AdaptiveScheme.info`: the information map `N` of the first `n`
  measurements.
* `ContMeasurements.AdaptiveScheme.DistinguishesAntipodes`: `N x ≠ N (-x)` for all
  `x` in a set; the property that lower bounds have to rule out.

## Combinators

* `comap`: transport a scheme along a continuous map `π : Y → X`
  (used to move between a normed space and its coordinates);
* `const`: the scheme that keeps asking one fixed functional;
* `branch`: ask `f` first and then continue with a scheme chosen arbitrarily from
  the value of `f`.  This is the one place where adaptivity is *created*, and it is
  what the bisection algorithm of the upper bound is built from.

## Conventions

* **Indexing is 0-based**: `S.info n x : Fin n → ℝ`, and `S.info n x 0` is the value
  of the first measurement.
* Functionals are required to be continuous on all of `X`, whereas the papers only
  ask for continuity on the set `F ⊆ X` of admissible inputs.  For closed `F` this is
  no loss: by the Tietze extension theorem every functional continuous on `F` extends
  to a continuous functional on `X`.  Working with globally continuous functionals
  keeps the model free of a set parameter.
* Errors are stated **pointwise** rather than through a supremum: an upper bound reads
  `∀ x ∈ F, dist x (Φ (S.info n x)) ≤ ε` and a lower bound
  `∃ x ∈ F, R ≤ dist x (Φ (S.info n x))`.  This avoids `sSup` side conditions and is
  equivalent to the formulation with the worst-case error.
-/

@[expose] public section

namespace ContMeasurements

universe u v

/-- An **adaptive scheme of continuous measurements** on `X`.

After `k` values `y : Fin k → ℝ` have been observed, the next functional to be
evaluated is `fct k y : X → ℝ`.  Each such functional is continuous in the point
being measured; the dependence of `fct k y` on `y` is arbitrary, and that dependence
is precisely what "adaptive" means.

The scheme carries no length: a scheme of any length is obtained by reading off only
the first `n` measurements, see `AdaptiveScheme.info`. -/
@[ext]
structure AdaptiveScheme (X : Type u) [TopologicalSpace X] where
  /-- The functional asked after the values `y : Fin k → ℝ` have been observed. -/
  fct : (k : ℕ) → (Fin k → ℝ) → X → ℝ
  /-- Every functional of the scheme is continuous. -/
  continuous_fct : ∀ k y, Continuous (fct k y)

namespace AdaptiveScheme

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The first functional `λ₁` of a scheme, asked before anything has been observed. -/
def first (S : AdaptiveScheme X) : X → ℝ :=
  S.fct 0 Fin.elim0

/-- The first functional of a scheme is continuous. -/
theorem continuous_first (S : AdaptiveScheme X) : Continuous S.first :=
  S.continuous_fct 0 _

/-- The scheme governing the remaining measurements once the value `y` has been
observed: its `k`-th functional is the `(k+1)`-st functional of `S`, asked after the
values `y, ys`.

This is the formal content of the informal step "on a set where the first answer is
constant, the algorithm continues with one measurement less"; the crucial point for
the lower bound is that `S.tail y` depends only on the *value* `y`, so two points
producing the same first answer face literally the same continuation. -/
def tail (S : AdaptiveScheme X) (y : ℝ) : AdaptiveScheme X where
  fct k ys := S.fct (k + 1) (Fin.cons y ys)
  continuous_fct _ _ := S.continuous_fct _ _

/-- The **information map** `N : X → ℝⁿ` of the first `n` measurements of a scheme:
`N x = (λ₁ x, λ₂^{(y₁)} x, …)`, each functional being selected by the values already
produced.

The recursion peels off the first measurement, so what changes in the recursive call
is the scheme, not the point. -/
def info : (n : ℕ) → AdaptiveScheme X → X → (Fin n → ℝ)
  | 0, _, _ => Fin.elim0
  | n + 1, S, x => Fin.cons (S.first x) (info n (S.tail (S.first x)) x)

/-- No measurements produce the empty tuple. -/
@[simp]
theorem info_zero (S : AdaptiveScheme X) (x : X) : S.info 0 x = Fin.elim0 := rfl

/-- Unfolding one measurement: the first value, then the information of the tail scheme. -/
theorem info_succ (S : AdaptiveScheme X) (n : ℕ) (x : X) :
    S.info (n + 1) x = Fin.cons (S.first x) ((S.tail (S.first x)).info n x) := rfl

/-- The first entry of the information is the first measurement. -/
@[simp]
theorem info_succ_zero (S : AdaptiveScheme X) (n : ℕ) (x : X) :
    S.info (n + 1) x 0 = S.first x := by
  rw [info_succ, Fin.cons_zero]

/-- The later entries of the information are those of the tail scheme. -/
@[simp]
theorem info_succ_succ (S : AdaptiveScheme X) (n : ℕ) (x : X) (i : Fin n) :
    S.info (n + 1) x i.succ = (S.tail (S.first x)).info n x i := by
  rw [info_succ, Fin.cons_succ]

/-! ### Combinators -/

/-- Transport a scheme along a continuous map `π : Y → X`: measure `π y` instead of
`y`.  Used to carry a scheme from a space to another one it is homeomorphic to. -/
def comap (π : Y → X) (hπ : Continuous π) (S : AdaptiveScheme X) : AdaptiveScheme Y where
  fct k y := S.fct k y ∘ π
  continuous_fct k y := (S.continuous_fct k y).comp hπ

/-- The first functional of a transported scheme. -/
@[simp]
theorem first_comap (π : Y → X) (hπ : Continuous π) (S : AdaptiveScheme X) (z : Y) :
    (S.comap π hπ).first z = S.first (π z) := rfl

/-- Transport commutes with taking the tail. -/
theorem tail_comap (π : Y → X) (hπ : Continuous π) (S : AdaptiveScheme X) (y : ℝ) :
    (S.comap π hπ).tail y = (S.tail y).comap π hπ := rfl

/-- The information of a transported scheme is the original information at the image point. -/
@[simp]
theorem info_comap (π : Y → X) (hπ : Continuous π) (n : ℕ) (S : AdaptiveScheme X) (z : Y) :
    (S.comap π hπ).info n z = S.info n (π z) := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih => rw [info_succ, info_succ, first_comap, tail_comap, ih]

/-- The scheme that asks the same functional `f` over and over. Only its first
measurement is ever used, through `info_const_one`. -/
def const (f : X → ℝ) (hf : Continuous f) : AdaptiveScheme X where
  fct _ _ := f
  continuous_fct _ _ := hf

/-- The first functional of `const f hf` is `f`. -/
@[simp]
theorem first_const (f : X → ℝ) (hf : Continuous f) : (const f hf).first = f := rfl

/-- One measurement of `const f hf` returns the value of `f`. -/
theorem info_const_one (f : X → ℝ) (hf : Continuous f) (x : X) :
    (const f hf).info 1 x = Fin.cons (f x) Fin.elim0 := rfl

/-- Ask `f` first, then continue with the scheme `choice y` selected from the observed
value `y = f x`.  The selection rule `choice` is an arbitrary function `ℝ → _`; no
regularity is assumed, and none is available.

This combinator builds every adaptive algorithm in this development: the bisection of
the upper bound branches on `choice`, and `tail_branch` is what lets the lower bound
analyse one measurement at a time. -/
def branch (f : X → ℝ) (hf : Continuous f) (choice : ℝ → AdaptiveScheme X) :
    AdaptiveScheme X where
  fct
    | 0, _ => f
    | k + 1, y => (choice (y 0)).fct k (Fin.tail y)
  continuous_fct k y := by
    cases k with
    | zero => exact hf
    | succ k => exact (choice _).continuous_fct _ _

/-- The first functional of a branching scheme is the branching functional. -/
@[simp]
theorem first_branch (f : X → ℝ) (hf : Continuous f) (choice : ℝ → AdaptiveScheme X) :
    (branch f hf choice).first = f := rfl

/-- After the first value `y` is observed, a branching scheme continues with `choice y`. -/
theorem tail_branch (f : X → ℝ) (hf : Continuous f) (choice : ℝ → AdaptiveScheme X)
    (y : ℝ) : (branch f hf choice).tail y = choice y := by
  ext k ys x
  rfl

/-- Information of a branching scheme: `f x`, then the information of the chosen continuation. -/
theorem info_branch_succ (f : X → ℝ) (hf : Continuous f) (choice : ℝ → AdaptiveScheme X)
    (n : ℕ) (x : X) :
    (branch f hf choice).info (n + 1) x = Fin.cons (f x) ((choice (f x)).info n x) := by
  rw [info_succ, first_branch, tail_branch]

/-! ### Distinguishing antipodes -/

section Neg

variable [Neg X]

/-- A scheme **distinguishes antipodes** on `K` with `n` measurements if the
information map separates every antipodal pair of `K`.

This is the property that an algorithm with small error forces: if
`dist x (Φ (N x)) < R` for all `x` on the sphere of radius `R`, then `N x = N (-x)`
would put the two antipodes, which are `2R` apart, at distance `< R` from a common
point.  The lower bound therefore consists in showing that `n` measurements cannot
distinguish antipodes unless `2ⁿ ≥ dim X + 1`. -/
def DistinguishesAntipodes (S : AdaptiveScheme X) (n : ℕ) (K : Set X) : Prop :=
  ∀ x ∈ K, S.info n x ≠ S.info n (-x)

/-- Distinguishing antipodes passes to subsets. -/
theorem DistinguishesAntipodes.mono {S : AdaptiveScheme X} {n : ℕ} {K K' : Set X}
    (h : S.DistinguishesAntipodes n K) (hK : K' ⊆ K) : S.DistinguishesAntipodes n K' :=
  fun x hx => h x (hK hx)

end Neg

end AdaptiveScheme

end ContMeasurements

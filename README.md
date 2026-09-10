# Adaptive continuous measurements — Lean 4 / Mathlib formalisation

A Lean 4 / Mathlib formalisation of the upper and lower bounds for **recovery from
adaptively chosen continuous measurements**, in the noise-free setting.

## The question

You want to know a vector `x` of a `d`-dimensional real normed space, up to an error
`ε` in the norm. You cannot see `x`; you may only compute real numbers
`λ₁(x), …, λₙ(x)`. How large must `n` be?

* If the `λᵢ` are **linear**, fewer than `d` measurements are useless — even if each
  is chosen after seeing the previous values. Whatever you learn, a whole affine
  subspace is consistent with it.
* If the `λᵢ` are **continuous but fixed in advance**, fewer than `d` are useless
  again, this time by the Borsuk–Ulam theorem: some antipodal pair, at distance `2R`,
  produces identical values.
* If the `λᵢ` are **continuous and chosen adaptively**, the answer changes completely:
  `⌈log₂ d⌉ + 1` measurements suffice for arbitrary accuracy, and `⌈log₂(d+1)⌉` are
  necessary.

Neither ingredient alone helps; their combination buys an exponential saving. The
reason the classical obstruction disappears is that the information map
`x ↦ (λ₁(x), …, λₙ(x))` of an adaptive scheme is in general **discontinuous**, so
Borsuk–Ulam does not apply to it.

The formalisation follows two papers, whose sources are in [`refs/`](refs/):

* the upper bound: D. Krieg, E. Novak, M. Ullrich, *How many questions do you need to
  find a vector?* (`refs/2026-06-18-main.tex`);
* the lower bound: M. Ullrich, *Optimal learning based on adaptive continuous
  measurements* (`refs/Continuous-lower.tex`).

`refs/paper-current.tex` is the companion paper on **noisy** measurements; it is not
formalised here.

## The model

An *adaptive scheme* (`ContMeasurements.AdaptiveScheme`) on a topological space `X`
is a family of functionals `fct k y : X → ℝ`, one for each number `k` of values
already observed and each vector `y : Fin k → ℝ` of those values. Every single
functional is continuous **in the point being measured**; the dependence on `y` is
completely arbitrary, and that is exactly what "adaptive" means.

The information map `S.info n x : Fin n → ℝ` evaluates the first `n` measurements in
sequence. An algorithm is `Φ ∘ S.info n` with an arbitrary reconstruction map `Φ`.

Three conventions:

* **Indexing is 0-based**: `S.info n x 0` is the value of the first measurement.
* Functionals are continuous on the whole space, whereas the papers only require
  continuity on the set `F` of admissible inputs. For closed `F` this is no loss, by
  the Tietze extension theorem, and it keeps the model free of a set parameter.
* Errors are stated **pointwise**, not through a supremum: an upper bound reads
  `∀ x, ‖x - Φ (S.info n x)‖ ≤ ε` and a lower bound
  `∃ x, R ≤ ‖x - Φ (S.info n x)‖`. This avoids `sSup` side conditions and says the
  same thing as the worst-case error.

## What is formalised

Legend: ✅ proved unconditionally; ⚠️ proved, but the proof uses the Borsuk–Ulam
theorem and therefore its `sorry`; ❌ stated with a `sorry`.

The three columns are not a matter of taste: `#print axioms` separates them. Every ⚠️
entry reports `sorryAx`, every ✅ entry does not.

### The model

| Result | Status |
|---|---|
| `AdaptiveScheme`, `first`, `tail`, `info` | ✅ defined |
| Combinators `comap`, `const`, `branch` and their `info` lemmas | ✅ proved |
| `DistinguishesAntipodes` | ✅ defined |

### The lower bound

| Result | Status |
|---|---|
| Split sets and `HasSplitCover`; monotonicity, padding, unions | ✅ proved |
| A closed symmetric set with a nonvanishing odd function is one split set (`hasSplitCover_one_of_odd_ne_zero`) | ✅ proved |
| Disjoint compact symmetric pieces **share** their split sets (`HasSplitCover.biUnion_of_pairwise_disjoint`) | ✅ proved |
| Fattening a split cover to a neighbourhood (`HasSplitCover.exists_cthickening`) | ✅ proved |
| A split cover gives a continuous odd map into `ℝᵏ` without zeros (`HasSplitCover.exists_odd_continuous_ne_zero`) | ✅ proved |
| Level set to slab (`HasSplitCover.exists_pos_inter_preimage_ball`) | ✅ proved |
| **Halving lemma**: level sets covered by `h` split sets ⟹ the set by `2h` (`hasSplitCover_two_mul_of_forall_fiber`) | ✅ proved |
| **Covering proposition**: `n` measurements separating antipodes ⟹ a cover by `2ⁿ - 1` split sets (`AdaptiveScheme.DistinguishesAntipodes.hasSplitCover`) | ✅ proved |
| Borsuk–Ulam, odd-map form (`borsukUlam`) | ❌ `sorry` |
| The cases `k ≤ 1` of that same statement (`borsukUlam_of_le_one`) | ✅ proved |
| Borsuk–Ulam for any norm and radius (`Function.Odd.exists_norm_eq_and_eq_zero_of_lt_finrank`) | ⚠️ proved |
| Antipodal coincidence: `2ⁿ ≤ d` ⟹ some antipodal pair is indistinguishable (`exists_norm_eq_and_info_eq_info_neg`) | ⚠️ proved |
| Counting form `2ⁿ ≥ d + 1` (`AdaptiveScheme.DistinguishesAntipodes.finrank_add_one_le_two_pow`) | ⚠️ proved |
| Error `≥ R` on the sphere of radius `R` when `2ⁿ ≤ d` (`exists_norm_eq_and_le_norm_sub`) | ⚠️ proved |

### The upper bound

| Result | Status |
|---|---|
| `ColoredCover`, color classes, rescaling (`ColoredCover.scale`) | ✅ defined and proved |
| **Bisection**: `⌈log₂ N⌉` measurements find the color among `N` (`exists_bisection_scheme`) | ✅ proved |
| Collar function, locally finite terms, the identification functional (`identify`) | ✅ proved |
| **Identification**: one measurement names the piece, with an integer value (`exists_identification`) | ✅ proved |
| A continuous injection `ℝ → (0,1)` and its inverse (`Real.logistic`, `Real.logit`) | ✅ proved |
| Skeleta, faces, and the geometric separation lemma (`LebesgueCover.exists_int_abs_sub_le_of_ne`) | ✅ proved |
| **Lebesgue cover**: `ℝᵐ` covered with `m + 1` colors, pieces of diameter `≤ 3/2`, separation `1/(4(m+2))` (`ColoredCover.lebesgue`) | ✅ proved |
| **Upper bound in `ℝᵈ`**, maximum norm (`exists_recovery_scheme_pi`) | ✅ proved |
| **Upper bound for any finite-dimensional real normed space** (`exists_recovery_scheme`) | ✅ proved |

### Both bounds together

| Result | Status |
|---|---|
| `minMeasurements` — the minimal number `n*` | ✅ defined |
| `n* ≤ ⌈log₂ d⌉ + 1` (`minMeasurements_le`) | ✅ proved |
| `⌈log₂(d+1)⌉ ≤ n*` (`clog_le_minMeasurements`) | ⚠️ proved |
| The sandwich `⌈log₂(d+1)⌉ ≤ n* ≤ ⌈log₂ d⌉ + 1` | ⚠️ proved |
| `n* = k + 1` in dimension `2ᵏ` (`minMeasurements_eq_of_finrank_eq_two_pow`) | ⚠️ proved |

The two bounds meet when `d` is a power of two and differ by one otherwise. For
`d = 2` and `d = 4`, for instance, they pin `n*` down exactly at `2` and `3`.

## The one gap

Mathlib does not contain the Borsuk–Ulam theorem, nor Brouwer's fixed point theorem,
nor Sperner's or Tucker's lemma from which it is usually derived. It is therefore
stated in `BasicResults/BorsukUlam.lean` with a `sorry`, and that is the **only**
`sorry` in the project:

```
grep -rn "^ *sorry$" BasicResults ContMeasurements
```

returns exactly one line, and `lake build` emits exactly one `declaration uses 'sorry'`
warning. Everything specific to this development — the covering proposition, the
halving lemma, the whole upper bound — is proved unconditionally.

The cases `k ≤ 1` of the very same statement are proved, in `borsukUlam_of_le_one`.
They are there to check the statement rather than to be used: a `sorry` that says
something subtly different from Borsuk–Ulam would invalidate every ⚠️ row above, and
neither the build nor `#print axioms` would notice, whereas two proved instances of
the statement do.

If Borsuk–Ulam enters Mathlib, one `exact` replaces the `sorry` and nothing else
changes.

## What is left to do

* Prove Borsuk–Ulam in general, or import it once Mathlib has it. The cases `k ≤ 1`
  are proved; the theorem is applied only with `k = 2ⁿ - 1`, so the next case the
  development needs is `k = 3`.

* The Banach-space extension of the lower bound: `eₙᶜᵒⁿᵗ(F, Y) ≥ b_{2ⁿ-1}(F, Y)` in
  terms of Bernstein widths (Section 5 of the lower-bound paper). The proof is local —
  it uses only one sphere inside `F` — so the machinery here already covers it.
* The **noisy** setting of `refs/paper-current.tex`, where the answer is governed by
  entropy numbers instead.
* The Lipschitz variant: all functionals used here are `1`-Lipschitz except the
  identification measurement; the paper's Lipschitz version costs one more
  measurement.
* A leanblueprint and continuous integration, as in the `Lean-SNumbers` project.

## Candidates for Mathlib

* **The Borsuk–Ulam theorem** itself, in any of its forms.
* `Metric.infDist` under negation: there is `EMetric.infEdist_neg` but no real-valued
  `infDist_neg`; here it is derived from `Metric.infDist_image isometry_neg`.
* The passage from level sets to slabs by a Lebesgue-number argument
  (`HasSplitCover.exists_pos_inter_preimage_ball`), which is generic.
* The bisection lemma (`exists_bisection_scheme`): a finite family of "membership
  oracles" realised by distance functionals.
* The Lebesgue cover (`ColoredCover.lebesgue`): a colored covering of `ℝᵐ` with
  `m + 1` colors and separated pieces of the same color.
* The logistic function and the logit (`Real.logistic`, `Real.logit`), which Mathlib
  does not have.

## Layout

Two libraries. `BasicResults` holds the general mathematics the theory consumes:
nothing there mentions measurements, every statement is a candidate for Mathlib, and
the single `sorry` sits there rather than among the results of the papers.
`ContMeasurements` holds the theory itself.

Names follow the Mathlib conventions: `UpperCamelCase` for types and Prop-valued
definitions, `lowerCamelCase` for data, `snake_case` for theorems, spelled out of the
statement with the conclusion first and the hypotheses after `of_`. The results of
`BasicResults` live in root namespaces, as a Mathlib contribution would; the theory
lives in `ContMeasurements`.

```
.
├── lakefile.toml               ← Lake configuration; depends on Mathlib
├── lean-toolchain              ← Lean 4 version (v4.33.1)
├── lake-manifest.json          ← the pinned Mathlib revision
├── BasicResults.lean           ← entry point of the general library
├── BasicResults/
│   ├── BorsukUlam.lean         ← Borsuk–Ulam (the only `sorry`) + transfer
│   ├── SplitCover.lean         ← split sets, split covers, odd maps
│   ├── Halving.lean            ← level sets → slabs → the halving lemma
│   ├── ColoredCover.lean       ← colored covers and rescaling
│   ├── LebesgueCover.lean      ← the m+1 color cover of ℝᵐ
│   └── Logistic.lean           ← the logistic function and the logit
├── ContMeasurements.lean       ← entry point of the theory
├── ContMeasurements/
│   ├── Scheme.lean             ← the model: AdaptiveScheme, info, combinators
│   ├── LowerBound.lean         ← 2ⁿ ≥ d+1; antipodal coincidence; error ≥ R
│   ├── Bisection.lean          ← finding a color by bisection
│   ├── Identification.lean     ← naming a piece with one measurement
│   ├── UpperBound.lean         ← ⌈log₂ d⌉ + 1 measurements suffice
│   └── Complexity.lean         ← the minimal number n* and the sandwich
└── refs/                       ← the two papers, plus the noisy companion
```

## Building

```
lake exe cache get
lake build
```

The Mathlib revision is pinned in `lake-manifest.json`; `lake exe cache get` fetches
the matching precompiled oleans. Do **not** run `lake update`: it re-resolves the
dependencies and makes the build non-reproducible.

Both libraries pass the Mathlib style linter, which checks among other things that
every declaration is documented and that no hypothesis goes unused:

```
lake exe runLinter BasicResults
lake exe runLinter ContMeasurements
```

## AI assistance

The Lean proofs in this project were produced with AI assistance. What is checked by
hand is the structure of the development and the statements of all definitions and
results; the proofs themselves are guaranteed by the Lean kernel, with the single
exception recorded above.

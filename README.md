# Adaptive continuous measurements — Lean 4 / Mathlib formalisation

A Lean 4 / Mathlib formalisation of the upper and lower bounds for **recovery from
adaptively chosen continuous measurements**, in the noise-free setting.

**Blueprint**: a human-readable account of the same mathematics, with every statement
linked to the Lean declaration proving it, in `blueprint/`. Built locally with
`leanblueprint`; see *Building the blueprint* below.

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

The formalisation follows two papers:

* the upper bound: D. Krieg, E. Novak, M. Ullrich, *How many questions do you need to
  find a vector?*;
* the lower bound: M. Ullrich, *Optimal learning based on adaptive continuous
  measurements*.

A companion paper treats **noisy** measurements, where entropy numbers govern the
answer; that setting is left for later.

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

Everything below is proved unconditionally: the project has no `sorry` and no axiom
beyond `propext`, `Classical.choice` and `Quot.sound`.

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
| Kuhn triangulation of the integer cube: signs, directions, extensions (`GridSimplex`) | ✅ proved |
| **Tucker's lemma**: a labelling antipodal on the boundary gives one simplex two opposite labels (`GridSimplex.tucker`) | ✅ proved |
| **Borsuk's antipodal theorem for the cube** (`borsukUlam_cube`) | ✅ proved |
| **Borsuk–Ulam**, odd-map form (`borsukUlam`) | ✅ proved |
| Borsuk–Ulam for any norm and radius (`Function.Odd.exists_norm_eq_and_eq_zero_of_lt_finrank`) | ✅ proved |
| Antipodal coincidence: `2ⁿ ≤ d` ⟹ some antipodal pair is indistinguishable (`exists_norm_eq_and_info_eq_info_neg`) | ✅ proved |
| Counting form `2ⁿ ≥ d + 1` (`AdaptiveScheme.DistinguishesAntipodes.finrank_add_one_le_two_pow`) | ✅ proved |
| Error `≥ R` on the sphere of radius `R` when `2ⁿ ≤ d` (`exists_norm_eq_and_le_norm_sub`) | ✅ proved |

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
| `d + 1 ≤ 2^n*` in counting form (`finrank_add_one_le_two_pow_minMeasurements`) | ✅ proved |
| `⌈log₂(d+1)⌉ ≤ n*` (`clog_le_minMeasurements`) | ✅ proved |
| The sandwich `⌈log₂(d+1)⌉ ≤ n* ≤ ⌈log₂ d⌉ + 1` | ✅ proved |
| `n* = k + 1` in dimension `2ᵏ` (`minMeasurements_eq_of_finrank_eq_two_pow`) | ✅ proved |

The two bounds meet when `d` is a power of two and differ by one otherwise. For
`d = 2` and `d = 4`, for instance, they pin `n*` down exactly at `2` and `3`.

## One note on provenance

The Borsuk–Ulam development — `GridSimplex.lean`, `Tucker.lean`, `BorsukUlam.lean` — was
produced with substantial AI assistance, and I have checked the statements rather than
the proof scripts line by line; what guarantees them is the kernel check. The argument
is the classical one: Tucker's lemma by a parity count over the Kuhn triangulation of
the integer cube, then Borsuk's antipodal theorem for the cube by uniform continuity,
then the sphere.

## What is left to do

* The Banach-space extension of the lower bound: `eₙᶜᵒⁿᵗ(F, Y) ≥ b_{2ⁿ-1}(F, Y)` in
  terms of Bernstein widths (Section 5 of the lower-bound paper). The proof is local —
  it uses only one sphere inside `F` — so the machinery here already covers it.
* The **noisy** setting of the companion paper, where the answer is governed by
  entropy numbers instead.
* The Lipschitz variant: all functionals used here are `1`-Lipschitz except the
  identification measurement; the paper's Lipschitz version costs one more
  measurement.
* A leanblueprint and continuous integration, as in the `Lean-SNumbers` project.

## Candidates for Mathlib

* **The Borsuk–Ulam theorem** itself, in any of its forms, together with **Tucker's
  lemma** and the Kuhn triangulation of the integer cube it runs on.
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
nothing there mentions measurements and every statement is a candidate for Mathlib.
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
│   ├── BorsukUlam.lean         ← Borsuk–Ulam, from Tucker's lemma, + transfer
│   ├── SplitCover.lean         ← split sets, split covers, odd maps
│   ├── Halving.lean            ← level sets → slabs → the halving lemma
│   ├── ColoredCover.lean       ← colored covers and rescaling
│   ├── GridSimplex.lean        ← the Kuhn triangulation of an integer cube
│   ├── LebesgueCover.lean      ← the m+1 color cover of ℝᵐ
│   ├── Logistic.lean           ← the logistic function and the logit
│   └── Tucker.lean             ← Tucker's lemma
├── blueprint/
│   ├── src/                    ← plastex config, LaTeX masters, content.tex
│   └── scripts/                ← rewrites the Lean links into source permalinks
├── ContMeasurements.lean       ← entry point of the theory
└── ContMeasurements/
    ├── Scheme.lean             ← the model: AdaptiveScheme, info, combinators
    ├── LowerBound.lean         ← 2ⁿ ≥ d+1; antipodal coincidence; error ≥ R
    ├── Bisection.lean          ← finding a color by bisection
    ├── Identification.lean     ← naming a piece with one measurement
    ├── UpperBound.lean         ← ⌈log₂ d⌉ + 1 measurements suffice
    └── Complexity.lean         ← the minimal number n* and the sandwich
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

## Building the blueprint

The blueprint follows the [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
convention. It needs `leanblueprint` with its plasTeX plugins, Graphviz, and a LaTeX
installation:

```
leanblueprint pdf      # produces blueprint/print/print.pdf
leanblueprint web      # produces blueprint/web/index.html and the dependency graph
```

Every `\lean{...}` tag names a declaration of this project; `leanblueprint checkdecls`
verifies that they all resolve, once the `checkdecls` package is among the Lake
dependencies.

## AI assistance

The Lean proofs in this project were produced with AI assistance. What is checked by
hand is the structure of the development and the statements of all definitions and
results; the proofs themselves are guaranteed by the Lean kernel, with the single
exception recorded above.

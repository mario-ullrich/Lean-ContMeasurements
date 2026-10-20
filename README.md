# A Borsuk–Ulam theorem for adaptive continuous measurements in Lean 4 / Mathlib

A Lean 4 / Mathlib formalisation of matching upper and lower bounds for **recovery from
adaptively chosen continuous measurements**, in the noise-free setting. Together they
determine the minimal number of measurements up to one, and exactly when the dimension is a
power of two. The project builds without `sorry`, and every theorem uses only the three
axioms Mathlib relies on throughout (`propext`, `Classical.choice`, `Quot.sound`).

* **Blueprint** (the mathematics, with the Lean name at every statement):
  <https://mario-ullrich.github.io/Lean-ContMeasurements/>
* **Blueprint as PDF**:
  <https://mario-ullrich.github.io/Lean-ContMeasurements/blueprint.pdf>
* **Dependency graph**:
  <https://mario-ullrich.github.io/Lean-ContMeasurements/dep_graph_document.html>

## The question

You want to know a vector `x` of a `d`-dimensional real normed space, up to an error
`ε` in the norm. You cannot see `x`; you may only compute real numbers
`λ₁(x), …, λₙ(x)`. How large must `n` be?

* If the `λᵢ` are **linear**, fewer than `d` measurements are useless, even if each
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

## The model

An *adaptive scheme* (`ContMeasurements.AdaptiveScheme`) on a topological space `X` is a
family of functionals `fct k y : X → ℝ`, one for each number `k` of values already observed
and each vector `y : Fin k → ℝ` of those values. Every single functional is continuous **in
the point being measured**; the dependence on `y` is completely arbitrary, and that is
exactly what "adaptive" means. The information map `S.info n x : Fin n → ℝ` evaluates the
first `n` measurements in sequence, and an algorithm is `Φ ∘ S.info n` with an arbitrary
reconstruction map `Φ`. The module docstring of `ContMeasurements/Scheme.lean` explains the
three conventions the development fixes.

## Main results

Throughout, `E` is a finite-dimensional real normed space of dimension `d`, and `S` is an
adaptive scheme on it. `Nat.clog 2 d` is Mathlib's `⌈log₂ d⌉`.

* **Lower bound.** If `2ⁿ ≤ d`, then for every scheme and every radius `R > 0` some `x` with
  `‖x‖ = R` satisfies `S.info n x = S.info n (-x)`: `n` measurements cannot tell an
  antipodal pair apart (`exists_norm_eq_and_info_eq_info_neg`). Hence every reconstruction
  `Φ` errs by at least `R` somewhere on that sphere (`exists_norm_eq_and_le_norm_sub`), and
  a scheme that does distinguish antipodes needs `d + 1 ≤ 2ⁿ`
  (`AdaptiveScheme.DistinguishesAntipodes.finrank_add_one_le_two_pow`).
* **The covering proposition** carrying that bound: if `n` measurements separate antipodes
  on a compact symmetric set, that set is covered by `2ⁿ - 1` split sets
  (`AdaptiveScheme.DistinguishesAntipodes.hasSplitCover`), by way of the halving lemma
  (`hasSplitCover_two_mul_of_forall_fiber`). The least such number is the covering form of
  the Krasnosel'skiĭ genus. This step uses no topology beyond compactness, and in particular
  no Borsuk–Ulam.
* **Borsuk–Ulam**, proved here rather than assumed, since Mathlib has neither it nor
  Brouwer's fixed point theorem nor Sperner's lemma. Tucker's lemma on the triangulation of
  the integer cube (`GridSimplex.tucker`) gives the antipodal theorem for the cube
  (`borsukUlam_cube`), then the odd-map form on the Euclidean sphere (`borsukUlam`), and
  finally the form the lower bound uses: for a continuous odd `Ψ : E → ℝᵏ` with `k < d` and
  any `R > 0` there is an `x` with `‖x‖ = R` and `Ψ x = 0`
  (`Function.Odd.exists_norm_eq_and_eq_zero_of_lt_finrank`).
* **Upper bound.** If `0 < d ≤ 2ᵏ`, then for every `ε > 0` there are a scheme and a
  reconstruction with `‖x - Φ (S.info (k + 1) x)‖ ≤ ε` for **every** `x`, with no bound on
  `‖x‖` assumed (`exists_recovery_scheme`). In particular `⌈log₂ d⌉ + 1` measurements
  suffice (`exists_recovery_scheme_clog`); the maximum norm on `ℝᵈ` is the case
  `exists_recovery_scheme_pi`.
* **The three ingredients of the upper bound.** A Lebesgue cover of `ℝᵐ` by `m + 1` colors,
  with pieces of diameter at most `3/2` and pieces of one color at distance at least
  `1/(4(m+2))` from each other (`ColoredCover.lebesgue`), used for the first `m = d - 1`
  coordinates, so that it has `d` colors; one measurement that names a piece of a given
  color by an integer value (`exists_identification`) and carries the last coordinate in
  its fractional part, through the logistic function; and bisection, which joins the
  schemes for at most `2^L` color classes into one for their union at the cost of `L`
  further measurements (`exists_bisection_scheme`).
* **Both bounds together.** `minMeasurements E R ε` is the least `n` admitting a scheme with
  error at most `ε` on the ball of radius `R`. For `d > 0` and `0 < ε < R`,

  ```
  ⌈log₂(d+1)⌉ ≤ minMeasurements E R ε ≤ ⌈log₂ d⌉ + 1
  ```

  (`clog_le_minMeasurements_and_le`, whose halves are `clog_le_minMeasurements` and
  `minMeasurements_le`; the counting form of the lower half is
  `finrank_add_one_le_two_pow_minMeasurements`). The upper half needs only `ε > 0`. The two
  bounds meet when `d` is a power of two, where `minMeasurements E R ε = k + 1` for
  `d = 2ᵏ` (`minMeasurements_eq_of_finrank_eq_two_pow`), and differ by one otherwise. For
  `d = 2` and `d = 4`, for instance, they pin the answer down at `2` and `3`.

The upper bound and the covering proposition are independent of Borsuk–Ulam; the lower
bound rests on it. Everything else is in the blueprint, with its Lean name at every
statement.

## What is left to do

* The Banach-space extension of the lower bound: `eₙᶜᵒⁿᵗ(F, Y) ≥ b_{2ⁿ-1}(F, Y)` in
  terms of Bernstein widths (Section 5 of the lower-bound paper). The proof is local:
  it uses only one sphere inside `F`, so the machinery here already covers it.
* The **noisy** setting of a companion paper, where the answer is governed by entropy
  numbers instead.
* The Lipschitz variant: all functionals used here are `1`-Lipschitz except the
  identification measurement; the paper's Lipschitz version costs one more measurement.

## Organisation

Two libraries. `BasicResults` holds the general mathematics the theory consumes: nothing
there mentions measurements, every statement is a candidate for Mathlib, and the results
live in root namespaces as a Mathlib contribution would. It contains split covers and the
halving lemma, the triangulation of the integer cube, Tucker's lemma, Borsuk–Ulam, colored
covers with the Lebesgue cover, and the logistic function with its inverse;
[MathlibCandidates.md](MathlibCandidates.md) lists what could be upstreamed.
`ContMeasurements` holds the theory itself: the model, the lower bound with its covering
proposition, bisection and identification, the upper bound, and the minimal number of
measurements. The blueprint states the results of the two papers in seven chapters and
proves the Borsuk–Ulam theorem in an appendix, which the dependency graph shows as a
block.

Names follow the Mathlib conventions: `UpperCamelCase` for types and Prop-valued
definitions, `lowerCamelCase` for data, `snake_case` for theorems, spelled out of the
statement with the conclusion first and the hypotheses after `of_`.

## Building

Requires [`elan`](https://github.com/leanprover/elan). The Lean version is pinned in
`lean-toolchain` and Mathlib in `lake-manifest.json`, so a clone builds against Lean /
Mathlib `v4.35.0-rc2`:

```bash
lake exe cache get   # downloads the prebuilt Mathlib oleans
lake build           # builds the project
```

Run `lake` from inside this folder, since `elan` reads `lean-toolchain` from the working
directory, and do not run `lake update`: it re-resolves the dependencies and makes the
build non-reproducible. Both libraries pass the Mathlib style linter, which checks among
other things that every declaration is documented and that no hypothesis goes unused:

```bash
lake exe runLinter BasicResults
lake exe runLinter ContMeasurements
```

The blueprint follows the
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) convention and needs a TeX
installation, `graphviz` for the dependency graph, and the `leanblueprint` package:

```bash
leanblueprint pdf          # blueprint/print/print.pdf
leanblueprint web          # blueprint/web/index.html and the dependency graph

python blueprint/scripts/check_lean_decls.py --output check_decls.lean
lake env lean check_decls.lean   # every \lean{Decl} must compile
```

On Windows, set `PYTHONUTF8=1` before `leanblueprint web` (in PowerShell
`$env:PYTHONUTF8 = 1`): without it plasTeX writes some characters of the pages, the
proof arrows among them, through the system code page, and the browser shows them
garbled. The GitHub Actions build runs on Linux, where UTF-8 is the default.

GitHub Actions builds the project and the blueprint on every push to `main`, checks every
`\lean` tag against the compiled project, uploads the site and the PDF as a run artifact,
and deploys the blueprint to GitHub Pages. Neither output is committed.

## AI assistance

The Lean proofs in this project were produced with AI assistance. What is checked by
hand is the structure of the development and the statements of all individual
definitions and results; the proofs themselves are guaranteed by the Lean kernel.
An exception is the Borsuk–Ulam development (`GridSimplex.lean`, `Tucker.lean`,
`BorsukUlam.lean`) which was autonomously produced by AI, and was not (yet) checked by
myself apart from the main theorem statement.

## License

Apache 2.0, the same as Mathlib. See [LICENSE](LICENSE).

## References

* D. Krieg, E. Novak, M. Ullrich, *How many continuous measurements are needed to learn a
  vector?*, to appear in Proc. Amer. Math. Soc.,
  [arxiv](https://arxiv.org/abs/2412.06468). The upper bound.
* M. Ullrich, *Optimal learning based on adaptive continuous measurements*, preprint, 2026.
  The lower bound.
* K. Borsuk, *Drei Sätze über die n-dimensionale euklidische Sphäre*, Fund. Math. **20**
  (1933), 177–190, [doi](https://doi.org/10.4064/fm-20-1-177-190). The odd-map form of the
  antipodal theorem.
* A. W. Tucker, *Some topological properties of disk and sphere*, in: Proc. First Canadian
  Math. Congress (Montreal, 1945), University of Toronto Press, 1946, 285–309,
  [link](https://zbmath.org/3102257). Its combinatorial form, which the proof here runs on.
* J. Matoušek, *Using the Borsuk-Ulam Theorem*, Springer, Berlin, 2003,
  [doi](https://doi.org/10.1007/978-3-540-76649-0). The modern account of that lemma and of
  the method.
* H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*, Ann. of Math. (2)
  **43** (1942), no. 3, 580–582, [doi](https://doi.org/10.2307/1968813). The triangulation
  of the cube that Tucker's lemma is stated on.
* H. W. Kuhn, *Some combinatorial lemmas in topology*, IBM J. Res. Develop. **4** (1960),
  no. 5, 518–524, [doi](https://doi.org/10.1147/rd.45.0518). The same triangulation.
* M. A. Krasnosel'skiĭ, *On the estimation of the number of critical points of functionals*,
  Uspekhi Mat. Nauk **7** (1952), no. 2, 157–164,
  [link](https://www.mathnet.ru/eng/rm8306). The genus whose covering form the number of
  split sets is.

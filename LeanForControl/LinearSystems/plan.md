# Plan: Linear Systems Theory

Roadmap for the `LinearSystems` track and its supporting `MatrixAlgebra` infrastructure.

The organizing spine is João P. Hespanha, *Linear Systems Theory* (2nd ed.) — the book
already cited by most of the work in this area. Following the citation convention in
`CONTRIBUTING.md`, parts and results are named descriptively rather than by
edition-specific chapter or section number.

## Directory structure

```
LeanForControl/
  MatrixAlgebra/                matrix facts with no system semantics
    Rank.lean                   rank / kernel / surjectivity bridges
    Spectrum.lean               eigenpairs, spectral radius
    Exponential.lean            the matrix exponential as an algebraic object
    QuadraticForm.lean          matrix quadratic forms, derivatives, PD/PSD bounds
    Jordan.lean                 Jordan normal form (planned)

  LinearSystems/
    Basic.lean                  shared conventions and index-type choices
    Defs.lean                   the system object (A, B, C, D) — time-agnostic data (planned)

    Controllability/             identical in discrete and continuous time — no split
      Controllability.lean      controllability matrix and rank test
      Defs.lean                 reachable subspace
      Reachability.lean         reachable-subspace characterizations, A-invariance
      Hautus.lean               controllability PBH test, via duality with Observability
      Decomposition.lean        standalone controllable decomposition (planned)

    Observability/
      Defs.lean                 observability matrix and predicate
      Observability.lean        observability matrix, rank/kernel forms
      Hautus.lean               unobservable subspace, observability PBH test
      Decomposition.lean        standalone observable decomposition (planned)

    KalmanDecomposition/         needs both Controllability/ and Observability/
      Defs.lean                 the four coordinate sectors and their lattice relations
      Decomposition.lean        existence, adapted coordinates, forced block-zero pattern
      DecompositionExamples.lean

    Solutions/
      DefsCtsLTV.lean           Peano-Baker series, state transition matrix
      CtsLTV.lean               Phi solves the matrix ODE; variation of constants
      CtsLTI.lean               the LTI case: e^{At}
      DefsDiscLTV.lean          discrete state transition matrix (ordered product)
      DiscLTV.lean              discrete variation of constants

    Stability/
      Continuous/
        DefsHurwitz.lean        IsHurwitz, IsHurwitzWithRate
        Hurwitz.lean            rate monotonicity, spectral shift, decay bounds
        LyapunovEquation.lean   AᵀP + PA = -Q
        ExponentialStability.lean
      Discrete/
        DefsSchur.lean          IsSchur (spectral radius < 1) (planned)
        Schur.lean              (planned)
        LyapunovEquation.lean   AᵀPA - P = -Q (planned)

    Gramians/                   (planned)
      Continuous.lean           ∫ e^{At} B Bᵀ e^{Aᵀt} dt
      Discrete.lean             Σ Aᵏ B Bᵀ (Aᵀ)ᵏ

  Stability/                    nonlinear ẋ = f(x) — existing track, unchanged
    LyapunovIndirect/           the only bridge from LinearSystems to nonlinear stability
```

Note that `LinearSystems/Stability/` and the top-level `Stability/` are different subjects,
not a split of one: the former is the stability theory *of linear systems* (a spectral
condition on `A`), the latter is Lyapunov theory for a general vector field `f`. Rule 2
below is what keeps them apart.

## Placement rules

Four mechanical tests, applied in order. They exist so that placement is settled before a
PR is opened rather than during review.

1. **Does the statement mention a system at all?** If it quantifies only over matrices and
   says nothing about `A` being a state matrix, it belongs in `MatrixAlgebra/`. Jordan
   form, spectral radius bounds, and the rank/kernel bridges are matrix facts that happen
   to be used by control theory, not control results.
2. **Does the statement mention `f : E → E`, or only `A`, `B`, `C`?** A statement in terms
   of a general vector field belongs in the top-level `Stability/`; a statement purely in
   terms of the system matrices belongs in `LinearSystems/`. A theorem whose hypothesis is
   about `A` and whose conclusion is about `f` is a bridge, and bridges live in
   `Stability/` — there should be very few of them.
3. **Which topic is it?** Pick the topic directory first: `Controllability/`,
   `Observability/`, `KalmanDecomposition/`, `Solutions/`, `Stability/`, `Gramians/`. Within
   the structural theory, controllability-only results go in `Controllability/`,
   observability-only results go in `Observability/`, and a result needing both (the Kalman
   decomposition; eventually minimal realizations) goes in its own directory rather than
   into either single-subject one.
4. **Does time enter the statement?** If the result is the same sentence in discrete and
   continuous time, it goes directly in the topic directory. Otherwise it goes in that
   directory's `Continuous` or `Discrete` half — as a subdirectory where that half has
   several files, as a single `Continuous.lean` / `Discrete.lean` where it does not.

**Tie-breaker, for the Lyapunov-equation cluster.** Rule 1 read literally would send
`SolvesContinuousLyapunovEquation` to `MatrixAlgebra/` — it quantifies only over matrices. It does
not go there: a statement mentioning `IsHurwitz` or `SolvesContinuousLyapunovEquation` goes to
`LinearSystems/Stability/Continuous/`; one mentioning neither, and no `f`, goes to
`MatrixAlgebra/`. The topic table below places the Lyapunov equation explicitly, and explicit
wins over the mechanical rule.

### Why the time split is per-topic, and controllability/observability are split apart

The structural theory is genuinely time-agnostic: the controllability matrix
`[B  A B  ⋯  Aⁿ⁻¹B]`, its rank test, the reachable subspace, the unobservable subspace,
the PBH test, duality, and the Kalman decomposition are the same statements with the same
proofs in both settings, so none of `Controllability/`, `Observability/`, or
`KalmanDecomposition/` splits by time. Splitting at the top of the track would have forced
an arbitrary home for the bulk of the existing work.

`Controllability/` and `Observability/` are separate directories, not one `Structure/`
holding both — controllability and observability are dual but distinct properties, each
with its own definition, matrix, and PBH test, and Hespanha gives them separate parts of
the book (Part III and Part IV) for the same reason. `Hautus.lean` exists once in each
directory: the observability-side file builds the PBH test from an eigenvector argument
on the unobservable subspace, and the controllability-side file is a short duality
corollary that imports it (`IsControllable A B ↔ IsObservable Aᵀ Bᵀ`) rather than
repeating the argument. A result needing both subspaces at once — the Kalman decomposition
today, minimal realizations eventually — gets its own directory instead of being folded
into either side, so that "controllable decomposition" (in `Controllability/`) and "the
Kalman decomposition" (in `KalmanDecomposition/`) stay visibly different results.

What actually differs is a short list: the solution formula (`e^{At}` vs `Aᵏ`), the
stability region (`Re λ < 0` vs `|λ| < 1`), the Gramians (integral vs sum), and the
Lyapunov equation (`AᵀP + PA` vs `AᵀPA - P`). Splitting inside each of those topics keeps
the two versions of a result adjacent, so the discrete-time gaps are visible per topic
instead of hiding in one empty directory. This is also how Hespanha organizes it: the
discrete-time case is a section within each chapter, not a separate part.

`Solutions/` now has both halves: the discrete state transition matrix is an ordered product
rather than a series, so every proof there is an induction with no convergence, no
differentiation and no Grönwall estimate. The remaining `Discrete` halves —
`Stability/Discrete/` and `Gramians/` — are still empty, and are listed so the asymmetry is a
visible gap rather than an unstated assumption that this library is continuous-time only.

## Status: matrix algebra infrastructure

| Result | Lean name | File | Status |
|---|---|---|---|
| Trivial kernel ⟺ full column rank | `mulVec_kernel_trivial_iff_rank_eq_card_cols` | `Rank.lean` | ✅ done |
| Surjectivity ⟺ full row rank | `mulVec_range_top_iff_rank_eq_card_rows` | `Rank.lean` | ✅ done |
| Eigenpair real/imaginary transport, generalized-eigenspace resonance, reverse spectral mapping for `exp` | `mulVec_re`/`mulVec_im`, `matrixMulVec_re_smul_eigenpair`/`_im_smul_eigenpair`, `eigenpair_real_imag`, `bilinear_eq_zero_of_no_resonance`, `toBilin_*`, `exists_eigenpair_of_mem_spectrum_exp` | `MatrixAlgebra/Spectrum.lean` | ✅ moved (interfaces not yet reviewed) |
| Complexification of a real matrix as a named def | — | — | retired — `A.map (algebraMap ℝ ℂ)` is inlined at each use instead. The complexification *bridges* that remain live in `MatrixAlgebra/Exponential.lean` (row below), not in `Spectrum.lean` |
| Spectral radius of `exp A` | `spectralRadius_exp_complexification_lt_one` | `LinearSystems/Stability/Continuous/ExponentialStability.lean` | ✅ done |
| Quadratic forms represented by a matrix | `quadraticForm` and friends | `MatrixAlgebra/QuadraticForm.lean` | ✅ done |
| The matrix exponential's complexification bridges | `complexification_exp`, `norm_complexification` | `MatrixAlgebra/Exponential.lean` | ✅ done |
| A contractive power from a spectral radius bound (general Banach algebra, no matrices) | `exists_pow_norm_lt_one_of_spectralRadius_lt_one` | `Analysis/SpectralRadius.lean` | ✅ done |
| Jordan normal form | — | `Jordan.lean` | planned |

`MatrixAlgebra/` deliberately has no `plan.md` of its own: like `Comparison/` and
`Analysis/`, it is generic infrastructure serving other tracks, and its roadmap is the
"needed by" column of the tables below.

## Status: structural theory (time-agnostic)

| Result | Lean name | File | Status |
|---|---|---|---|
| Controllability matrix | `controllabilityMatrix` | `Controllability/Controllability.lean` | ✅ done |
| Controllability ⟺ full row rank | `isControllable_iff_controllabilityMatrix_rank_eq` | `Controllability/Controllability.lean` | ✅ done |
| Reachable subspace | `reachableSubspace` | `Controllability/Defs.lean` | ✅ done |
| Reachable subspace ⟺ controllability | `reachableSubspace_eq_top_iff_isControllable` | `Controllability/Reachability.lean` | ✅ done |
| PBH test for controllability | `isControllable_iff_hautus` | `Controllability/Hautus.lean` | ✅ done |
| Controllability/observability duality | `isControllable_iff_isObservable_transpose` | `Controllability/Hautus.lean` | ✅ done |
| Controllable decomposition (standalone) | — | `Controllability/Decomposition.lean` | planned |
| Stabilizability | — | `Controllability/Hautus.lean` | planned |
| Observability matrix | `observabilityMatrix` | `Observability/Observability.lean` | ✅ done |
| Observability ⟺ trivial kernel | `isObservable_iff_observabilityMatrix_ker_trivial` | `Observability/Observability.lean` | ✅ done |
| Observability ⟺ full column rank | `isObservable_iff_observabilityMatrix_rank_eq` | `Observability/Observability.lean` | ✅ done |
| Unobservable subspace, `A`-invariance | `unobservableSubspace` | `Observability/Hautus.lean` | ✅ done |
| PBH test for observability | `isObservable_iff_hautus` | `Observability/Hautus.lean` | ✅ done |
| Observable decomposition (standalone) | — | `Observability/Decomposition.lean` | planned |
| Detectability | — | `Observability/Hautus.lean` | planned |
| Four coordinate sectors | — | `KalmanDecomposition/Defs.lean` | ✅ done |
| Kalman decomposition | `exists_kalmanDecomposition` | `KalmanDecomposition/Decomposition.lean` | ✅ done |
| Block zero pattern of the decomposition | `kalman_block_matrix_zero_pattern` | `KalmanDecomposition/Decomposition.lean` | ✅ done |
| Minimal realizations | — | — | planned, no directory settled (needs both — see open questions) |

## Status: solutions

| Result | Lean name | File | Status |
|---|---|---|---|
| Peano–Baker series, state transition matrix | `peanoBakerTerm`, `stateTransitionMatrix` | `Solutions/DefsCtsLTV.lean` | ✅ done |
| `Φ` solves `Φ̇ = A(t)Φ`, `Φ(t₀,t₀) = I`, and is unique | `hasDerivAt_stateTransitionMatrix`, `stateTransitionMatrix_mul_unique` | `Solutions/CtsLTV.lean` | ✅ done |
| Semigroup, invertibility, composition | `stateTransitionMatrix_semigroup`, `_inv`, `_comp` | `Solutions/CtsLTV.lean` | ✅ done |
| Variation of constants (continuous) | `hasDerivAt_variationOfConstants`, `variationOfConstants_unique` | `Solutions/CtsLTV.lean` | ✅ done |
| The LTI case: `e^{At}` | — | `Solutions/CtsLTI.lean` | ✅ done |
| Discrete state transition matrix (ordered product) | `discStateTransitionMatrix` | `Solutions/DefsDiscLTV.lean` | ✅ done |
| Discrete variation of constants | `discVariationOfConstants_unique` | `Solutions/DiscLTV.lean` | ✅ done |
| State-space system object, `ẋ = A x + B u` | — | `Defs.lean` | planned — see open questions |
| Impulse response / transfer function | — | `Solutions/` | planned |
| BIBO stability | — | `Solutions/` | planned |

## Status: stability of linear systems

| Result | Lean name | File | Status |
|---|---|---|---|
| Hurwitz predicates | `IsHurwitz`, `IsHurwitzWithRate` | `Continuous/DefsHurwitz.lean` | ✅ done |
| Rate monotonicity, spectral shift | `IsHurwitzWithRate.mono`, `isHurwitzWithRate_iff_add_smul_one` | `Continuous/Hurwitz.lean` | ✅ done |
| Hurwitz ⟹ `‖exp(kA)‖ < 1` for some `k` | `IsHurwitz.exists_norm_exp_nat_smul_lt_one` | `Continuous/ExponentialStability.lean` | ✅ done |
| Lyapunov equation solvable with `P` positive definite | `IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov` | `Continuous/LyapunovEquation.lean` | ✅ done |
| Quadratic instability certificate from an unstable eigenpair | `exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos` | `Continuous/InstabilityCertificate.lean` | ✅ done |
| Eigenvalue assignment by state feedback | — | — | planned |
| Schur predicate and discrete Lyapunov equation | — | `Discrete/` | planned |

## Status: bridge to nonlinear stability

| Result | Lean name | File | Status |
|---|---|---|---|
| Hurwitz Jacobian ⟹ local exponential stability | `hurwitz_linearization_locally_exponentially_stable` | `Stability/LyapunovIndirect/Linearization.lean` | ✅ done |
| Unstable eigenvalue ⟹ instability (affine-linear) | `unstable_affineLinear_of_eigenvalue_re_pos` | `Stability/LyapunovIndirect/LinearizationInstability.lean` | ✅ done |
| Unstable eigenvalue ⟹ instability (`C¹` field) | `unstable_of_exists_complex_eigenvalue_re_pos` | `Stability/LyapunovIndirect/NonlinearInstability.lean` | ✅ done |
| Chetaev's instability theorem (exponential form) | `unstable_of_exponential_chetaev` | `Stability/LyapunovIndirect/Chetaev.lean` | ✅ done (closes issue #8) |
| Chetaev's instability theorem (boundary form) | — | — | planned — see `Stability/plan.md` |

Rule 2 keeps this list short by construction: a theorem whose hypothesis is about `A` and whose
conclusion is about `f` is a bridge, and these five are all of them.

## Status: blueprint coverage

Every public declaration in the rest of the library carries a `@[blueprint]` node, every label
resolves, and nothing is declared-but-unrendered — `scripts/check_blueprint_labels.py` enforces
the last two on demand. **The 18 files below are the whole gap**, and they are held back
deliberately: each needs a rewrite or a clean-interfaces pass first, and annotating one now would
document a shape that is about to change. Seven also still carry `Original:` docstring
boilerplate, a leftover of the first deletion pass.

| Files | Blocked on |
|---|---|
| `Controllability/{Controllability, Defs, Hautus, Reachability}.lean` | rewrite |
| `Observability/{Defs, Hautus, Observability}.lean` | rewrite |
| `KalmanDecomposition/{Defs, Decomposition, DecompositionExamples}.lean` | rewrite |
| `Stability/Continuous/{DefsHurwitz, ExponentialStability, Hurwitz, InstabilityCertificate, LyapunovEquation}.lean` | clean-interfaces pass |
| `MatrixAlgebra/{QuadraticForm, Rank, Spectrum}.lean` | clean-interfaces pass |

162 declarations between them. `MatrixAlgebra/Spectrum.lean` is the case that motivated the rule:
everything in it went `private` → public because Lean requires that once a declaration crosses a
file boundary, which is not the same as being *designed* as public API. Annotate after deciding
what the interface is, not before — the audit of the rest of the library repeatedly found that a
node written against a provisional shape is worse than no node, because it reads as settled.

## Migration map

**First pass, done.** #13 and #14 merged, then one housekeeping commit moved everything
into a single time-agnostic `Structure/` directory — the five pre-existing files plus both
PRs' new files landed in the same pass, so nothing was moved twice.

| Original location | Landed at (first pass) |
|---|---|
| `LinearSystems/MatrixLemmas.lean` | `MatrixAlgebra/Rank.lean` |
| `LinearSystems/Controllability.lean` | `LinearSystems/Structure/Controllability.lean` |
| `LinearSystems/Observability.lean` | `LinearSystems/Structure/Observability.lean` |
| `LinearSystems/Hautus.lean` | `LinearSystems/Structure/Hautus.lean` |
| `LinearSystems/Basic.lean` | unchanged |
| PR #13: `LinearSystems/Stability/DefsHurwitz.lean`, `Hurwitz.lean` | `LinearSystems/Stability/Continuous/` |
| PR #14: `LinearSystems/Reachability/DefsReachability.lean` | `LinearSystems/Structure/DefsReachability.lean` |
| PR #14: `LinearSystems/Reachability/Reachability.lean` | `LinearSystems/Structure/Reachability.lean` |
| PR #14: `LinearSystems/Reachability/DefsKalmanDecomposition.lean` | `LinearSystems/Structure/DefsDecomposition.lean` |
| PR #14: `LinearSystems/Reachability/KalmanDecomposition.lean` | `LinearSystems/Structure/Decomposition.lean` |
| PR #14: `LinearSystems/Reachability/KalmanDecompositionExamples.lean` | `LinearSystems/Structure/DecompositionExamples.lean` |

One deliberate rename rode along with the first pass: `MatrixLemmas`'s namespace changed
from `LinearSystems.MatrixLemmas` to bare `MatrixAlgebra`, matching the rule that this file
has no system semantics and shouldn't carry the `LinearSystems` prefix. Four call sites
updated accordingly.

`LinearSystems/Reachability/plan.md` and `LinearSystems/Stability/plan.md` (added by
PR #14 and PR #13 respectively) were folded into this file and deleted, rather than kept
as a third and fourth roadmap for the same track.

**Second pass, done.** `Structure/` was itself judged too generic a name — a bare English
word that also shadows Lean's `structure` keyword — and, more substantively, too coarse a
bucket: it merged two dual-but-distinct properties (controllability, observability) with
the one result that genuinely needs both (the Kalman decomposition). Split into three
directories:

| First pass | Landed at (second pass) |
|---|---|
| `Structure/Controllability.lean` | `Controllability/Controllability.lean` |
| `Structure/DefsReachability.lean` | `Controllability/DefsReachability.lean` |
| `Structure/Reachability.lean` | `Controllability/Reachability.lean` |
| `Structure/Observability.lean` | `Observability/Observability.lean` |
| `Structure/DefsDecomposition.lean` | `KalmanDecomposition/DefsDecomposition.lean` |
| `Structure/Decomposition.lean` | `KalmanDecomposition/Decomposition.lean` |
| `Structure/DecompositionExamples.lean` | `KalmanDecomposition/DecompositionExamples.lean` |
| `Structure/Hautus.lean` | split in two — see below |

`Structure/Hautus.lean` did not move as a unit: it already had an internal divider
(`## Hautus controllability via duality`) separating an observability-side eigenvector
argument from a controllability-side duality corollary, so it was split at that existing
boundary rather than arbitrarily:

- Lines before the divider (`unobservableSubspace` through `isObservable_iff_hautus`) →
  `Observability/Hautus.lean`.
- Lines after the divider (`controllabilityMatrix_transpose` through
  `isControllable_iff_hautus`) → `Controllability/Hautus.lean`, which imports
  `Observability/Hautus.lean` for the duality argument.

Both directories deliberately keep the filename `Hautus.lean` — the directory
(`Controllability.` vs `Observability.`) disambiguates the fully qualified module path,
and a shared name for the same underlying technique (the PBH test) in its two dual forms
reads as consistent rather than confusing.

**Third pass, done.** PR #15 (Lyapunov's indirect method) rebased onto `main`, dropped its
stale copy of the Hurwitz foundation, and landed. Two targets changed from what was planned
above: the quadratic-form file became `MatrixAlgebra/QuadraticForm.lean` rather than a
`PositiveDefinite.lean`, because what it actually contains is quadratic forms and their
derivatives rather than a PD/PSD theory; and the affine-linear vector field stayed on the
nonlinear side, since by Rule 2 a definition mentioning a vector field `f` is not a
`LinearSystems/` object.

| PR #15, as submitted | Landed at (third pass) |
|---|---|
| `LinearSystems/DefsHurwitz.lean`, `Hurwitz.lean` | dropped — duplicated #13, already at `LinearSystems/Stability/Continuous/` |
| `LinearSystems/LyapunovEquation.lean`, `ExponentialStability.lean`, `InstabilityCertificate.lean` | `LinearSystems/Stability/Continuous/` |
| `LinearSystems/DefsLyapunov.lean`, `Lyapunov.lean` | split: matrix half → `MatrixAlgebra/QuadraticForm.lean`, remainder-absorption half → `Stability/LyapunovIndirect/Lyapunov.lean` |
| `LinearSystems/DefsDynamics.lean` | `Stability/LyapunovIndirect/DefsDynamics.lean` |
| `Stability/Linearization.lean`, `Chetaev.lean`, `LinearizationInstability.lean`, `NonlinearInstability.lean` | `Stability/LyapunovIndirect/` |
| `Stability/DefsForward.lean`, `Forward.lean` | dropped — the `Forward*` predicates were folded into the ordinary autonomous ones |
| `Analysis/Linearization.lean` | `Analysis/FrechetDerivative.lean` |

`LinearSystems/Defs.lean` — the time-agnostic system object — was *not* created: nothing yet
needs an `(A, B, C, D)` record, and the open question below about `D` is unsettled. It stays
in the directory tree above marked `(planned)`.

## Known tech debt

Not blocking anything; recorded so it is not rediscovered.

### Clean-interfaces pass on `MatrixAlgebra/Spectrum.lean`

Everything in that file went `private` → public purely because Lean requires it once a
declaration crosses a file boundary. Three things to settle: whether the `bilinear_*` /
`toBilin_*` cluster (stated over an arbitrary `[Module ℂ V]`, with no matrix in sight) belongs in
this file at all, versus a linear-algebra-flavoured file or an upstream Mathlib contribution;
whether `exists_eigenpair_of_mem_spectrum_exp`'s two helpers should go back to `private`; and
naming and grouping generally, now that everything sits in one place.

### The discrete-time payoff is already proved, in the wrong place

`conjugationOperator C : X ↦ Cᵀ X C` **is** the discrete Lyapunov operator, and
`tsum_conjugationOperator_pow_apply_posDef` is essentially *"`P = Σₖ (Cᵀ)ᵏ Q Cᵏ` is positive
definite"* — the Schur-case solution. Both are `private` helpers inside
`Stability/Continuous/LyapunovEquation.lean`, serving the continuous-time proof.

Promoting these seven into a shared home (`MatrixAlgebra/Congruence.lean`, or
`Stability/Congruence.lean` to keep them inside the track) —

`conjugationOperator`, `conjugationOperator_norm_lt_one`,
`tendsto_conjugationOperator_pow_apply_zero`, `eq_zero_of_conjugationOperator_fixed`,
`posDef_conjugationOperator`, `summable_conjugationOperator_pow_apply`,
`tsum_conjugationOperator_pow_apply_posDef`

— would make `DefsSchur` and the discrete Lyapunov equation `AᵀPA - P = -Q` mostly assembly
rather than new proof. Deferred deliberately: the decision was to finish the already-established
`Stability/Continuous/` destination before opening new territory.

### Small cleanup

`entryCLM` and `quadraticEvalCLM` (`Stability/Continuous/LyapunovEquation.lean`) — check whether
Mathlib's `Matrix.entryLinearMap` or existing CLM combinators already cover these.

## Open questions

- **The time-split naming rule and `Solutions/` disagree.** Rule 4 says a topic's two halves
  are named `Continuous` / `Discrete`. `Solutions/` instead uses `CtsLTI` / `CtsLTV` /
  `DiscLTV`, which also encodes time-invariant vs time-varying — a second axis the rule does
  not mention. Either the rule should acknowledge that second axis, or `Solutions/` should be
  renamed. Settle it before `Gramians/` is written, since it faces the same choice.

- **Scalar generality.** `Controllability.lean` and `Observability.lean` are stated over a
  `Semiring` with a `Field`-scoped section for the rank forms; both `Hautus.lean` files are
  `ℂ`-only because eigenvalues live in `ℂ`; the Hurwitz work is `ℝ`-with-complexification.
  Settle whether `Controllability/` and `Observability/` should be uniformly `Field`-generic
  with `ℂ` specializations, or whether the current per-file choice is the right trade.
- **Does `Defs.lean` carry a `D` matrix?** Nothing currently needs feedthrough, but adding
  it later is a breaking change to every consumer. Decide before the first system object
  lands. Settle alongside it whether `affineLinearVectorField`
  (`Stability/LyapunovIndirect/DefsDynamics.lean`, the whole file) moves into `Defs.lean`: by
  Rule 2 a definition mentioning a vector field `f : E → E` belongs on the nonlinear side, which
  is why the third migration pass left it where it is.
- **How much does the discrete-time half share?** Some results (the Lyapunov equation
  existence argument, the Gramian positive-definiteness argument) have near-identical
  proofs in both settings. Decide whether to abstract over the two or to accept the
  duplication before writing the first `Discrete` file, not after.
- **Index types.** `Basic.lean` fixes the `Fin n × Fin m` convention for block matrices.
  Confirm this survives contact with the Gramians and the decomposition work before
  treating it as settled.
- **Where do minimal realizations live?** Minimality means controllable *and* observable,
  so — like the Kalman decomposition — it needs both `Controllability/` and
  `Observability/`. Decide when the first file is written whether it joins
  `KalmanDecomposition/`, gets its own directory, or is named accordingly (`Realization/`,
  say) rather than defaulting silently into whichever directory is convenient at the time.

## Lessons learned

- **A subject-area directory without a `plan.md` grows one layout per contributor.** Three
  independent PRs proposed three incompatible directory schemes for this track, in good
  faith, because there was nothing to read. `CONTRIBUTING.md` already requires a living
  `plan.md` in actively-developed directories; this file is that requirement being met
  late rather than a new rule.
- **A textbook's chapter order is a teaching order, not a dependency order.** Hespanha
  reaches exponential stability through the Jordan normal form because that is how the
  subject is taught. In Lean it is cheaper to go through Mathlib's spectral-radius
  machinery and leave Jordan form for later. Take the book's partition of the subject;
  derive the dependency graph from Mathlib.
- **Separate the matrix fact from the control statement.** Every result proved in this
  track so far has factored into a matrix-algebra lemma plus a short control-level
  wrapper. Keeping that factoring explicit — `MatrixAlgebra/` for the first half — is what
  makes the control files short enough to review.

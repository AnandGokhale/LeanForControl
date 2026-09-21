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
    Spectrum.lean               eigenpairs, spectral radius, complexification
    Exponential.lean            the matrix exponential as an algebraic object
    PositiveDefinite.lean       PD / PSD forms and quadratics
    Jordan.lean                 Jordan normal form (planned)

  LinearSystems/
    Basic.lean                  shared conventions and index-type choices
    Defs.lean                   the system object (A, B, C, D) — time-agnostic data

    Controllability/             identical in discrete and continuous time — no split
      Controllability.lean      controllability matrix and rank test
      Defs.lean                 controllability, reachable-subspace definitions
      Reachability.lean         reachable-subspace characterizations, A-invariance
      Hautus.lean               controllability PBH test, via duality with Observability
      DefsDecomposition.lean    canonical reachable restriction and matrices
      Decomposition.lean        standalone controllable decomposition

    Observability/
      Observability.lean        observability matrix, rank/kernel forms
      Hautus.lean               unobservable subspace, observability PBH test
      DefsDecomposition.lean    canonical observable quotient and matrices
      Decomposition.lean        standalone observable decomposition

    KalmanDecomposition/         needs both Controllability/ and Observability/
      Defs.lean                 the four coordinate sectors and their lattice relations
      Dimensions.lean           sector dimensions and canonicality
      DefsSemantic.lean         canonical controllable-observable quotient
      Semantic.lean             semantic block properties and structural summary
      Decomposition.lean        existence, adapted coordinates, forced block-zero pattern
      DecompositionExamples.lean

    Realization/                 algebraic external behavior and minimality
      Defs.lean                 bundled (A,B,C,D) realization
      MarkovParameters.lean     Markov parameters, behavior, similarity
      Hankel.lean               arbitrary finite Hankel matrices
      Minimal.lean              quantified minimality and rank lower bound
      Reduction.lean            canonical core realization
      Minimality.lean           minimality characterization and existence
      Examples.lean             public-API regression examples

    Solutions/
      Continuous.lean           e^{At}, variation of constants
      Discrete.lean             Aᵏ, discrete variation of constants (planned)

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
    Linearization.lean          the only bridge from LinearSystems to nonlinear stability
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

Every `Discrete` half is currently empty. They are listed so the asymmetry is a visible
gap rather than an unstated assumption that this library is continuous-time only.

## Status: matrix algebra infrastructure

| Result | Lean name | File | Status |
|---|---|---|---|
| Trivial kernel ⟺ full column rank | `mulVec_kernel_trivial_iff_rank_eq_card_cols` | `Rank.lean` | ✅ done |
| Surjectivity ⟺ full row rank | `mulVec_range_top_iff_rank_eq_card_rows` | `Rank.lean` | ✅ done |
| Complexification of a real matrix | — | `Spectrum.lean` | 🔶 in review (PR #13, PR #15) |
| Spectral radius of `exp A` | — | `Spectrum.lean` | 🔶 in review (PR #15) |
| Positive-definite quadratic forms | `matrixQuadratic` and friends | `PositiveDefinite.lean` | 🔶 in review (PR #15) |
| Jordan normal form | — | `Jordan.lean` | planned |

`MatrixAlgebra/` deliberately has no `plan.md` of its own: like `Comparison/` and
`Analysis/`, it is generic infrastructure serving other tracks, and its roadmap is the
"needed by" column of the tables below.

## Status: structural theory (time-agnostic)

| Result | Lean name | File | Status |
|---|---|---|---|
| Controllability matrix | `controllabilityMatrix` | `Controllability/Controllability.lean` | ✅ done |
| Controllability ⟺ full row rank | `isControllable_iff_controllabilityMatrix_rank_eq` | `Controllability/Controllability.lean` | ✅ done |
| Reachable subspace | `reachableSubspace` | `Controllability/DefsReachability.lean` | ✅ done |
| Reachable subspace ⟺ controllability | `reachableSubspace_eq_top_iff_isControllable` | `Controllability/Reachability.lean` | ✅ done |
| PBH test for controllability | `isControllable_iff_hautus` | `Controllability/Hautus.lean` | ✅ done |
| Controllability/observability duality | `isControllable_iff_isObservable_transpose` | `Controllability/Hautus.lean` | ✅ done |
| Controllable decomposition (standalone) | `reachableMatrices_isControllable` | `Controllability/Decomposition.lean` | ✅ done |
| Stabilizability | — | `Controllability/Hautus.lean` | planned |
| Observability matrix | `observabilityMatrix` | `Observability/Observability.lean` | ✅ done |
| Observability ⟺ trivial kernel | `isObservable_iff_observabilityMatrix_ker_trivial` | `Observability/Observability.lean` | ✅ done |
| Observability ⟺ full column rank | `isObservable_iff_observabilityMatrix_rank_eq` | `Observability/Observability.lean` | ✅ done |
| Unobservable subspace, `A`-invariance | `unobservableSubspace` | `Observability/Hautus.lean` | ✅ done |
| PBH test for observability | `isObservable_iff_hautus` | `Observability/Hautus.lean` | ✅ done |
| Observable decomposition (standalone) | `observableMatrices_isObservable` | `Observability/Decomposition.lean` | ✅ done |
| Detectability | — | `Observability/Hautus.lean` | planned |
| Kalman decomposition | `exists_kalmanDecomposition` | `KalmanDecomposition/Decomposition.lean` | ✅ done |
| Block zero pattern of the decomposition | `kalman_block_matrix_zero_pattern` | `KalmanDecomposition/Decomposition.lean` | ✅ done |
| Kalman sector dimension identities | `finrank_cuo_add_co_add_uuo_add_uo` | `KalmanDecomposition/Dimensions.lean` | ✅ done |
| Controllable-observable core | `controllableObservableMatrices_isControllable_and_isObservable` | `KalmanDecomposition/Semantic.lean` | ✅ done |
| Structural Kalman theorem | `exists_kalmanDecomposition_with_semantics` | `KalmanDecomposition/Semantic.lean` | ✅ done |
| Realization object and behavioral equivalence | Realization, BehaviorallyEquivalent | Realization/Defs.lean, Realization/MarkovParameters.lean | ✅ done |
| Finite Hankel factorization and rank bound | hankelMatrix_eq_observability_mul_controllability, hankelMatrix_rank_le_stateDim | Realization/Hankel.lean, Realization/Minimal.lean | ✅ done |
| Canonical behavior-preserving core | behaviorallyEquivalent_core | Realization/Reduction.lean | ✅ done |
| Minimal iff controllable and observable | isMinimal_iff_isControllable_and_isObservable | Realization/Minimality.lean | ✅ done over ℂ |
| Existence of minimal realizations | exists_behaviorallyEquivalent_isMinimal | Realization/Minimality.lean | ✅ done over ℂ |
| Uniqueness of minimal realizations up to similarity | — | Realization/ | planned |

## Status: solutions

| Result | Lean name | File | Status |
|---|---|---|---|
| State-space system object, `ẋ = A x + B u` | — | `../Defs.lean` | 🔶 in review (PR #15, as `DefsDynamics.lean`) |
| Matrix exponential solution, variation of constants | — | `Continuous.lean` | planned |
| Impulse response / transfer function | — | `Continuous.lean` | planned |
| BIBO stability | — | `Continuous.lean` | planned |
| Discrete-time solution `Aᵏ` | — | `Discrete.lean` | planned |

## Status: stability of linear systems

| Result | Lean name | File | Status |
|---|---|---|---|
| Hurwitz predicates | `IsHurwitz`, `IsHurwitzWithRate` | `Continuous/DefsHurwitz.lean` | ✅ done |
| Rate monotonicity, spectral shift | `IsHurwitzWithRate.mono`, `isHurwitzWithRate_iff_add_smul_one` | `Continuous/Hurwitz.lean` | ✅ done |
| Hurwitz ⟹ `‖exp(kA)‖ < 1` for some `k` | `IsHurwitz.exists_norm_exp_nat_smul_lt_one` | `Continuous/ExponentialStability.lean` | 🔶 in review (PR #15) |
| Lyapunov equation solvable with `P` positive definite | `IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov` | `Continuous/LyapunovEquation.lean` | 🔶 in review (PR #15) |
| Quadratic instability certificate from an unstable eigenpair | `exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos` | `Continuous/LyapunovEquation.lean` | 🔶 in review (PR #15) |
| Eigenvalue assignment by state feedback | — | — | planned |
| Schur predicate and discrete Lyapunov equation | — | `Discrete/` | planned |

## Status: bridge to nonlinear stability

| Result | Lean name | File | Status |
|---|---|---|---|
| Hurwitz Jacobian ⟹ local exponential stability | `hurwitz_linearization_forward_locally_exponentially_stable` | `Stability/Linearization.lean` | 🔶 in review (PR #15) |
| Hurwitz Jacobian ⟹ local asymptotic stability | `hurwitz_linearization_local_asymptotic_stable` | `Stability/Linearization.lean` | 🔶 in review (PR #15) |
| Unstable eigenvalue ⟹ instability | — | `Stability/LinearizationInstability.lean` | 🔶 in review (PR #15) |
| Chetaev's instability theorem | — | `Stability/Chetaev.lean` | 🔶 in review (PR #15, also closes issue #8) |

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

**Still pending:** PR #15 branched before #13's review landed, so it carries a stale copy
of the Hurwitz foundation — see the ordering note below. Its own migration happens when it
rebases, not as part of this pass.

| PR #15, as submitted | Target |
|---|---|
| `LinearSystems/DefsHurwitz.lean`, `Hurwitz.lean` | drop — duplicates #13, now at `Stability/Continuous/` |
| `LinearSystems/LyapunovEquation.lean`, `ExponentialStability.lean`, `InstabilityCertificate.lean` | `LinearSystems/Stability/Continuous/` |
| `LinearSystems/DefsLyapunov.lean` | `MatrixAlgebra/PositiveDefinite.lean` |
| `LinearSystems/DefsDynamics.lean` | `LinearSystems/Defs.lean` |
| `Stability/Linearization.lean`, `Chetaev.lean`, `Forward.lean`, … | `Stability/` — unchanged |
| `Analysis/Linearization.lean` | `Analysis/` — unchanged |

Ordering note: PR #15 currently contains PR #13's first two commits verbatim, from before
review, including the `complexification` wrapper that was dropped and the unattributed
reference line that was replaced. Now that #13 is merged at its target path, #15 needs to
rebase onto `main` and delete its own copy of the Hurwitz foundation rather than
reconciling two versions in review.

## Open questions

- **Scalar generality.** `Controllability.lean` and `Observability.lean` are stated over a
  `Semiring` with a `Field`-scoped section for the rank forms; both `Hautus.lean` files are
  `ℂ`-only because eigenvalues live in `ℂ`; the Hurwitz work is `ℝ`-with-complexification.
  Settle whether `Controllability/` and `Observability/` should be uniformly `Field`-generic
  with `ℂ` specializations, or whether the current per-file choice is the right trade.
- **Does `Defs.lean` carry a `D` matrix?** Nothing currently needs feedthrough, but adding
  it later is a breaking change to every consumer. Decide before the first system object
  lands.
- **How much does the discrete-time half share?** Some results (the Lyapunov equation
  existence argument, the Gramian positive-definiteness argument) have near-identical
  proofs in both settings. Decide whether to abstract over the two or to accept the
  duplication before writing the first `Discrete` file, not after.
- **Index types.** `Basic.lean` fixes the `Fin n × Fin m` convention for block matrices.
  Confirm this survives contact with the Gramians and the decomposition work before
  treating it as settled.
- **Minimal realizations now live in `Realization/`.** The directory owns the bundled
  `(A,B,C,D)` object, Markov behavior, Hankel matrices, reductions, and semantic
  minimality. `KalmanDecomposition/` remains structural and supplies its canonical core
  to the realization reduction layer.

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

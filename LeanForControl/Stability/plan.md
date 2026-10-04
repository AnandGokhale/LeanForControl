# Plan: Lyapunov Stability Theory

## Status: Autonomous systems (`ẋ = f(x)`)

| Result | Lean name | File | Status |
|---|---|---|---|
| Lyapunov stability | `lyapunov_stable` | `Autonomous.lean` | ✅ done |
| Global asymptotic stability via strict Lyapunov function | `lyapunov_asymptotic_stable` | `Autonomous.lean` | ✅ done |
| Global asymptotic stability via radially unbounded V | `lyapunov_global_asymptotic_stable` | `Autonomous.lean` | ✅ done |
| Local asymptotic stability via strict local Lyapunov function | `lyapunov_local_asymptotic_stable` | `Autonomous.lean` | ✅ done |
| Quantitative exponential Chetaev criterion | `unstable_of_exponential_chetaev` | `LyapunovIndirect/Chetaev.lean` | ✅ done |
| Boundary-form/geometric Chetaev theorem | — | — | planned |
| ω-limit set of a trajectory | `omegaLimitTraj`, `mem_omegaLimitTraj_iff` | `LaSalle.lean` | ✅ done |
| ω-limit set is positively invariant (Khalil Lemma 4.1) | `isPositivelyInvariant_omegaLimitTraj` | `LaSalle.lean` | ✅ done |
| `V̇ = 0` on the ω-limit set | `lieDeriv_eq_zero_on_omegaLimitTraj` | `LaSalle.lean` | ✅ done |
| LaSalle's invariance principle | `lasalle_invariance_principle` | `LaSalle.lean` | ✅ done |
| Barbashin's theorem (local asymptotic stability via LaSalle) | `lasalle_local_asymptotic_stable` | `LaSalle.lean` | ✅ done |
| Krasovskii's theorem (global asymptotic stability via LaSalle) | `lasalle_global_asymptotic_stable` | `LaSalle.lean` | ✅ done |
| Stable branch of Lyapunov's indirect method | `hurwitz_linearization_locally_exponentially_stable` | `LyapunovIndirect/Linearization.lean` | ✅ done |
| Unstable branch of Lyapunov's indirect method | `unstable_of_exists_complex_eigenvalue_re_pos` | `LyapunovIndirect/NonlinearInstability.lean` | ✅ done |

Files:

- `DefsAutonomous.lean` — autonomous trajectory, stability, and Lyapunov-function definitions
- `Autonomous.lean` — Lyapunov stability / GAS / LAS
- `LaSalle.lean` — invariance principle and Barbashin/Krasovskii corollaries
- `LyapunovIndirect/Chetaev.lean` — smooth-cutoff continuation, first-exit machinery, and the
  exponential Chetaev criterion
- `LyapunovIndirect/Linearization.lean` — stable branch of Lyapunov's indirect method
- `LyapunovIndirect/LinearizationInstability.lean` — exact affine-linear positive-mode instability
- `LyapunovIndirect/NonlinearInstability.lean` — quadratic-certificate application and nonlinear unstable branch
- `LyapunovIndirect/DefsDynamics.lean` — affine-linear vector fields on the Euclidean state convention
- `LyapunovIndirect/Lyapunov.lean` — the remainder-absorption step shared by both branches

## Status: Non-autonomous systems (`ẋ = f(t, x)`)

| Result | Lean name | File | Status |
|---|---|---|---|
| Trajectories, equilibria, stability predicates | — | `DefsNonAutonomous.lean` | ✅ done |
| Picard–Lindelöf existence on `[t₀, ∞)` | `exists_isIntegralCurveOn_Ici` | `ODEs/PicardLindelof.lean` | ✅ done, axiom-free |
| Class-K sandwich bounds for positive-definite functions | `LyapunovClassKBounds` | `LyapunovBounds.lean` | ✅ done |
| Class-KL solution of the scalar decay ODE `ẏ = −α(y)` | `ClassK.exists_classKL_decaySolution` | `ClassKDecay.lean` | ✅ done |
| Comparison bound `D⁺v ≤ −α(v)` ⟹ class-KL decay | `classK_dini_bound` | `ClassKDecay.lean` | ✅ done |
| Class-K characterization of uniform stability | `uniformlyStableNA_iff_classK` | `KLCharacterization.lean` | ✅ done |
| Class-KL characterization of uniform asymptotic stability | `uniformlyAsymptoticStableNA_iff_classKL` | `KLCharacterization.lean` | ✅ done |
| Class-KL characterization of global uniform asymptotic stability | `globallyUniformlyAsymptoticStableNA_iff_classKL` | `KLCharacterization.lean` | ✅ done |
| Lyapunov's uniform stability theorem | `lyapunov_uniformly_stable_NA` | `NonAutonomous.lean` | ✅ done |
| Lyapunov's uniform asymptotic stability theorem | `lyapunov_uniformly_asymptotic_stable_NA` | `NonAutonomous.lean` | ✅ done |
| Exponential stability from a power-law Lyapunov sandwich | — | — | planned — Khalil Theorem 4.10; `ExponentiallyStableNA` is defined but nothing concludes it |
| Hespanha's Definition 8.1 for `ẋ = A(t)x` ⟺ the predicates below | `stableNA_linearVectorField_iff` and friends | `LinearSystems/Stability/Continuous/LyapunovLTV.lean` | ✅ done — see `L` |

Files:

- `DefsNonAutonomous.lean` — trajectories, equilibria, and the stability predicates
  (stable, uniformly stable, unstable, asymptotically stable, uniformly asymptotically
  stable, globally uniformly asymptotically stable, exponentially stable, globally
  exponentially stable)
- `LyapunovBounds.lean` — class-K sandwich bounds for continuous positive-definite
  functions (annulus-infimum / ball-supremum construction plus smoothing); only
  `LyapunovClassKBounds` is public
- `ClassKDecay.lean` — class-KL bound from the scalar decay ODE `ẏ = -α(y)`, plus the
  comparison-based decay bound `classK_dini_bound`
- `KLCharacterizationTools.lean` — uniform decay envelopes (`exists_classLSingular_decayBound`,
  `exists_decayBound_family`); everything else in the file is private construction
- `KLCharacterization.lean` — class-K / class-KL characterizations of the stability
  predicates in `DefsNonAutonomous.lean`
- `NonAutonomous.lean` — the two main Lyapunov theorems for non-autonomous systems

The predicates of `DefsNonAutonomous.lean` are also the ones the linear track uses: Hespanha's
Definition 8.1, stated on the state transition matrix of `ẋ = A(t)x`, is proved equivalent to
them in `LinearSystems/Stability/Continuous/LyapunovLTV.lean` rather than re-defined there. That
file lives on the linear side because its subject is the linear system; see
`LeanForControl/LinearSystems/plan.md`.

Comparison-function library (`LeanForControl/Comparison/`):

- `ClassK.lean`, `ClassKInfty.lean`, `ClassKL.lean`, `ClassL.lean` — the class K, K∞, KL,
  and L function structures and their algebra (composition, inverse, restriction)
- `Axioms.lean` — assumed comparison-function results (three axioms)
- `../axioms.lean` — the monotone-to-strictly-monotone lower smoothing axiom, plus proved
  global and bounded upper majorants (with the necessary right-continuity-at-zero hypothesis)
- `ComparisonFunctions.lean` — shared comparison-function infrastructure

---

## Finite-segment quantification and Lyapunov's indirect method

Every autonomous stability predicate quantifies over *finite forward solution segments*
(`IsTrajectoryOn φ f t₀ t₁`, an abbreviation for `IsIntegralCurveOn φ (fun _ x => f x)
(Icc t₀ t₁)`) rather than over solutions defined on all of `ℝ`. This prevents a system whose
solution escapes in finite time from satisfying a stability predicate merely because no global
trajectory exists.

There is no longer a separate "forward" API: the `Forward*` predicates and their compatibility
theorems were folded into the ordinary ones, so `LyapunovStable`, `LocallyExponentiallyStable`
and `Unstable` in `DefsAutonomous.lean` *are* the finite-segment notions.

| Infrastructure or result | Lean name | File | Status |
|---|---|---|---|
| Finite forward solution segment | `IsTrajectoryOn` (abbrev for Mathlib's `IsIntegralCurveOn`) | `DefsAutonomous.lean` | ✅ done |
| Lyapunov stability, local exponential stability, instability | `LyapunovStable`, `LocallyExponentiallyStable`, `Unstable` | `DefsAutonomous.lean` | ✅ done |
| Local finite segment for a `C¹` field | `ContDiffAt.exists_isIntegralCurveOn_Icc` | `ODEs/ODE_properties.lean` | ✅ done |
| Lyapunov first-exit theorem | `lyapunov_stable` | `Autonomous.lean` | ✅ done |
| Exponential stability implies Lyapunov stability | `LocallyExponentiallyStable.lyapunovStable` | `Autonomous.lean` | ✅ done |
| Escape witness gives instability | `unstable_of_fixed_escape` | `Autonomous.lean` | ✅ done |
| Hurwitz exponential contractivity block | `IsHurwitz.exists_norm_exp_nat_smul_lt_one` | `LinearSystems/Stability/Continuous/ExponentialStability.lean` | ✅ done |
| Arbitrary-`Q` continuous Lyapunov equation | `IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov` | `LinearSystems/Stability/Continuous/LyapunovEquation.lean` | ✅ done, axiom-free |
| Linearization-error bound, `ε`–`δ` form | `HasFDerivAt.exists_linearization_error_bound` | `Analysis/FrechetDerivative.lean` | ✅ done |
| Remainder absorption shared by both branches | `exists_abs_fderiv_centeredQuadraticForm_remainder_le` | `LyapunovIndirect/Lyapunov.lean` | ✅ done |
| Hurwitz Jacobian gives local exponential stability | `hurwitz_linearization_locally_exponentially_stable` | `LyapunovIndirect/Linearization.lean` | ✅ done |
| Positive-real eigenpair gives a quadratic Chetaev certificate | `exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos` | `LinearSystems/Stability/Continuous/InstabilityCertificate.lean` | ✅ done, axiom-free |
| Positive-real mode destabilizes the exact affine-linear system | `unstable_affineLinear_of_eigenvalue_re_pos` | `LyapunovIndirect/LinearizationInstability.lean` | ✅ done |
| Exponential Chetaev criterion on finite segments | `unstable_of_exponential_chetaev` | `LyapunovIndirect/Chetaev.lean` | ✅ done |
| Positive-real Jacobian eigenpair destabilizes a `C¹` equilibrium | `unstable_of_exists_complex_eigenvalue_re_pos` | `LyapunovIndirect/NonlinearInstability.lean` | ✅ done |

Supporting files outside `Stability/`:

- `Analysis/FrechetDerivative.lean` — generic little-o and quantitative bounds for the
  centered Fréchet-derivative remainder
- `MatrixAlgebra/QuadraticForm.lean` — matrix quadratic forms, their derivatives and bounds
- `MatrixAlgebra/Spectrum.lean` — eigenpairs, real/imaginary transport, spectral radius
- `LinearSystems/Stability/Continuous/ExponentialStability.lean` — the contractive
  integer-time exponential block, from spectral mapping and Gelfand's formula
- `LinearSystems/Stability/Continuous/LyapunovEquation.lean` — an axiom-free construction of
  the continuous-time Lyapunov solution for every `Q.PosDef`, positive definiteness of the
  solution, and uniqueness among all matrix solutions
- `LinearSystems/Stability/Continuous/InstabilityCertificate.lean` — an axiom-free shifted
  Lyapunov–Sylvester construction of a quadratic instability certificate

### Stable branch

Let `A` represent `fderiv ℝ f x_eq`, with `f` of class `C¹` and `f x_eq = 0`.
For a Hurwitz `A`, the completed path is:

1. Spectral mapping and Gelfand's formula give a positive integer time at which the
   matrix exponential is contractive.
2. For every `Q.PosDef`, a convergent finite-block construction gives a unique matrix
   `P` satisfying `P A + Aᵀ P = -Q`; the proof also establishes `P.PosDef`. This result
   is infrastructure, not an axiom.
3. With `Q = I`, the quadratic function centered at `x_eq` has a negative quadratic
   Lie-derivative bound after the first-order remainder is absorbed locally.
4. A weighted-energy argument proves `LocallyExponentiallyStable f x_eq`, from which
   `LocallyExponentiallyStable.lyapunovStable` gives Lyapunov stability.

Because the predicate quantifies over finite forward segments, the formal statement covers
solutions with a finite maximal interval, which the classical statement silently omits.

### Unstable branch

For a nonzero complex eigenvector of `A` with eigenvalue `μ` and `0 < μ.re`, the
completed path is:

1. Choose a positive nonresonant shift `α < μ.re` and solve a shifted
   Lyapunov–Sylvester equation. Uniqueness makes its real solution symmetric.
2. The real or imaginary part of the eigenvector supplies a direction where the resulting
   quadratic form is positive, while
   `H A + Aᵀ H - 2 α H` is positive definite.
3. The `C¹` remainder estimate absorbs the nonlinear error on a small ball, yielding
   `2 α V(x) ≤ DV(x) f(x)` and positive seeds arbitrarily close to the equilibrium.
4. `unstable_of_exponential_chetaev` globalizes the field with a smooth cutoff, constructs
   arbitrarily long finite solution segments, and proves a first-radius escape.

The conclusion is `Unstable f x_eq`. This is the appropriate instability notion for a general
nonlinear field because it tests every finite forward segment and does not assume that
solutions extend globally in time. The existential wrapper
`unstable_of_exists_complex_eigenvalue_re_pos` is the direct formal counterpart of the
statement that the Jacobian has an eigenvalue in the open right half-plane.

References for the two branches: Khalil, *Nonlinear Systems*; Hahn,
*Stability of Motion*.

---

## Still planned: boundary-form/geometric Chetaev theorem

The completed `unstable_of_exponential_chetaev` is a quantitative criterion tailored to the indirect-method proof. It assumes, on a closed
ball, a quadratic upper bound
`|V(x)| ≤ C ‖x - x_eq‖²`, an exponential growth inequality
`2 α V(x) ≤ DV(x) f(x)`, and positive values of `V` arbitrarily close to `x_eq`.
Those hypotheses are enough for the quadratic certificate above.

This is distinct from the more general boundary-form version of Chetaev's theorem, which
remains planned. Its geometric hypotheses should package an open set `D₁` with `x_eq` on
its frontier, positivity of `V` and its Lie derivative in `D₁`, and vanishing of `V` on
the relevant boundary. The target conclusion should use `Unstable`, which already quantifies
over finite forward segments, so finite-time escape is handled without a global-trajectory
assumption.

The remaining work for that general theorem is geometric rather than spectral:

- define a boundary-form Chetaev certificate in a dedicated definitions file;
- derive positive seed points from the frontier hypothesis;
- control retention in the positive component and exit through its boundary;
- replace the quantitative exponential growth estimate by the compact-set argument for a
  merely positive Lie derivative.

The smooth-cutoff continuation, finite-segment chain rule, and first-exit machinery already
proved for the exponential criterion should be reusable.

---

## Infrastructure already in place (autonomous side)

Public, in `Autonomous.lean` unless noted:

- `hasDerivAt_V_comp_traj`, `hasDerivAt_V_comp_integralCurveOn` (chain rule along solutions)
- `antitoneOn_V_comp_traj`, `V_nonincreasing_on`
- `isCompact_sublevel_set`, `sublevel_set_invariant` (the latter in `DefsAutonomous.lean`)
- `strict_implies_semidefinite`, `asymptotic_implies_strict`, `strict_local_implies_semidefinite`
- `omegaLimitTraj`, `mem_omegaLimitTraj_iff` (`LaSalle.lean`) — Mathlib's `omegaLimit`
  specialized to a single trajectory, and its membership criterion
- `isPositivelyInvariant_omegaLimitTraj`, `lieDeriv_eq_zero_on_omegaLimitTraj`,
  `LieDerivZeroSet` (`LaSalle.lean`)

The four classical LaSalle steps — `V ∘ φ` antitone, `V(φ t) → L`, `V ≡ L` on `ω(φ)`, and
`ω(φ) ⊆ Ω` — are `private` in `LaSalle.lean`: they are steps of one proof, not results.

## Known tech debt

Not blocking anything; recorded so it is not rediscovered.

### The class-KL construction is ~7x longer than the class-K one

| half of Khalil 4.5 | method | lines |
|---|---|---|
| uniform stability ⟺ class `K` | build a crude monotone `ω`, majorize with `exists_strictMono_upper_bound` | **57** |
| UAS ⟺ class `KL` | build `T̄`, hand-construct a smoothing, prove strictness, invert | **~400** |

`T̄(η, r)` maps radius → time; the decay factor needs time → radius, so the construction inverts.
Inversion needs injectivity, hence strict antitonicity, hence the half-window average (continuity)
and the `r/η` penalty (strictness and blow-up at `0⁺`). Every `W_fn_*` lemma serves that.

**The axiom route was considered and rejected — do not re-propose it.** Building time → radius
directly and majorizing with a two-parameter analogue of `exists_strictMono_upper_bound` would
delete ~500 lines, but that axiom *is* the Massera/Sontag majorization — the hard direction of
Khalil 4.5 itself, which `CONTRIBUTING.md` §4 forbids axiomatizing. Keep the constructive proof.

What is open is readability, in descending value:

1. **`W_fn` is still written in control-theory terms.** `Analysis/MonotoneFunctions` (inversion)
   and `Analysis/Integrals` (half-window average) are stated on bare functions; the sliding
   average itself is not. Lifting it is the last step of the separation. The interfaces are
   narrow — `T̄ → W` needs nonneg + antitone + eventually-zero (integrability is *derived* from
   antitonicity); `W → inversion` needs continuous + strictly antitone + two limits; `U →` the KL
   proof needs `ClassLSingular` + `T̄(U s) < s`.
2. **Names.** `W_fn`, `Tbar_fn` and `validTSet` are `private`, so they no longer break the
   no-construction-names rule from outside — but they still name nothing, and step 1 would force
   naming them anyway. Proposed: `strictMajorant` / `strictMajorantInv`, `Tbar_fn` →
   `uniformConvergenceTime`, `validTSet` → `uniformConvergenceTimes`.
3. **`T̄(U s) < s` deserves a name.** It is the entire point of the construction — the step
   converting "the elapsed time exceeds the optimal convergence time to the `U`-ball" into the
   decay bound — and is an anonymous three-step `calc` inside `U_decay_bound`.
4. **Argument order.** `Tbar_fn` takes `η r`, `W_fn` takes `r η` — opposite orders on adjacent
   functions, invisible because neither name says which slot is which. Fixing it lets partial
   application feed the abstraction with no lambda.

### `ClassKLGlobal.continuous_r` concludes on the wrong set

`ClassKLGlobal.continuous_r` (`Comparison/ClassKL.lean`) takes a phantom `{a : ℝ}` and concludes
`ContinuousOn (fun r => β.toFun r s) (Set.Ico 0 a)`, but `ClassKLGlobal` is defined on `Ici 0` —
there is no `a` in the structure. The conclusion should be `ContinuousOn … (Set.Ici 0)`; as
written it is strictly weaker than the `continuous` field supports, and the `a` exists only to
make the global version look like the bounded one. Its one caller in `KLCharacterization.lean`
passes an `Ico` membership, so tightening the type means touching that site too.
(`ClassKL.continuous_r` is fine — there the `a` is the structure's own.)

### Files that should move

| Declaration / file | Destination | Why |
|---|---|---|
| `LyapunovIndirect/Chetaev.lean` | `Stability/Chetaev.lean` | general instability tool; mentions `f`, never `A`; imports only `Autonomous` |
| `exists_abs_fderiv_centeredQuadraticForm_remainder_le` (`LyapunovIndirect/Lyapunov.lean`) | `Stability/QuadraticRemainder.lean` *(new, small)* | both branches call it, so leaving it in `Linearization.lean` would make the unstable branch import the stable branch and invert the dependency |
| `realMulVec` (`LyapunovIndirect/LinearizationInstability.lean`) | inline it | one-line private wrapper for `Matrix.toEuclideanCLM`, 2 call sites in its own file |

`Lyapunov.lean` holds that one declaration and nothing else, so it is deleted by the same move.
What remains in `LyapunovIndirect/` is then `Linearization.lean`, `LinearizationInstability.lean`,
`NonlinearInstability.lean` and `DefsDynamics.lean` — all genuinely linearization, so the
directory name stays accurate.

`Chetaev.lean`'s three `private` `*_forward_segment*` lemmas are **deliberately** left alone by
the `forward` rename sweep: there `forward` means *forward in time from 0* — a solution on
`Icc 0 T` — which is accurate and unrelated to the retired `Forward*` stability predicates.

## Open questions

- **Flat vs subdirectory for the bridges.** `LinearSystems/plan.md` Rule 2 says bridges from the
  linear track to nonlinear stability should be few. `LyapunovIndirect/` now holds six files, so
  a growing bridge directory is a signal worth keeping visible rather than tidying away.

- **Do the two trajectory abbreviations earn their keep?** `IsTrajectoryOn` (autonomous,
  `Icc t₀ t₁`) and `IsTrajectoryNA` (non-autonomous, `Ici t₀`) sit on a genuinely separate
  generalization axis, and **no file in the library mentions both**. `LaSalle.lean` needs both
  shapes at once — `isPositivelyInvariant_omegaLimitTraj` takes an `Ici 0`-shaped curve and
  concludes `IsPositivelyInvariant`, which quantifies over `Icc t₀ t₁`-shaped ones — and handles
  it by writing `IsIntegralCurveOn` directly and calling `.mono`. So a bridge, if wanted, is a
  one-line restriction lemma rather than a design problem; the real question is whether either
  abbreviation is pulling its weight.

## Lessons from the Lyapunov stability proofs

- **Finite-forward quantification avoids vacuity.** Global trajectories remain useful for
  asymptotic limits, but local stability and instability statements should not silently
  omit solutions that have only a finite maximal interval.

- **Pointwise Lie derivatives** (`∀ x, fderiv ℝ V x (f x) ≤ 0`) are cleaner than
  trajectory-based hypotheses. A chain-rule bridge should connect that form to either
  global trajectories or finite forward solution segments.

- **The Lyapunov equation is reusable infrastructure.** The Hurwitz-to-`P` result is proved
  for arbitrary positive-definite `Q` and uniqueness among all solutions; the indirect
  method specializes it to `Q = I` rather than hiding that result behind an axiom.

- **The Fréchet remainder belongs in generic analysis.** The little-o statement and its
  quantitative local bound are independent of control theory and support both branches of
  the indirect method.

- **A shifted quadratic form avoids spectral splitting.** A nonresonant shift
  turns the positive-real eigenmode into a real Chetaev certificate without assuming a
  stable/unstable invariant-subspace decomposition.

- **`hequil : f x_eq = 0`** belongs in Lyapunov-function structures when several proof
  branches use it; re-deriving equilibrium facts ad hoc makes later composition harder.

- **Mathlib lemma names that landed** include:
  - `HasFDerivAt.comp_hasDerivAt` — chain rule
  - `antitone_of_deriv_nonpos` — monotone calculus
  - `tendsto_atTop_ciInf` — antitone plus bounded below implies convergence
  - `Antitone.le_of_tendsto` — an antitone limit lower-bounds values
  - `IsCompact.exists_isMaxOn` / `exists_isMinOn` — EVT
  - `isPreconnected_Icc.intermediate_value₂` — IVT
  - `comap_norm_atTop` plus `Metric.cobounded_eq_cocompact` — compact sublevel sets

- **`hf_cont : Continuous f`** is needed as a theorem hypothesis rather than a field of the
  Lyapunov structure, because continuity of `x ↦ fderiv ℝ V x (f x)` needs it — see
  `lie_deriv_continuous`.

- **The one step of LaSalle that needs uniqueness is invariance of `ω(φ)`.** Everything else
  in the principle is compactness and monotone convergence. Mathlib's
  `Flow.isInvariant_omegaLimit` is unusable here because it presumes a globally defined flow;
  comparing two solutions directly with `dist_le_of_trajectories_ODE` needs only a Lipschitz
  hypothesis, and yields the invariance with no boundedness assumption at all.

- **Non-autonomous work reuses the comparison-function library** (`Comparison/ClassK.lean`
  and related files) rather than the autonomous Lyapunov-function structures directly.
  Stability notions are characterized via class-K / class-KL bounds, and the main theorems
  in `NonAutonomous.lean` combine those bounds with the Dini-derivative comparison lemma.

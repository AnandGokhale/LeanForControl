# Plan: Lyapunov Stability Theory

## Status: Autonomous systems (`ẋ = f(x)`)

| Result | Lean name | File | Status |
|---|---|---|---|
| Lyapunov stability | `lyapunov_stable` | `Autonomous.lean` | ✅ done |
| Global asymptotic stability via strict Lyapunov function | `lyapunov_asymptotic_stable` | `Autonomous.lean` | ✅ done |
| Global asymptotic stability via radially unbounded V | `lyapunov_global_asymptotic_stable` | `Autonomous.lean` | ✅ done |
| Local asymptotic stability via strict local Lyapunov function | `lyapunov_local_asymptotic_stable` | `Autonomous.lean` | ✅ done |
| Quantitative exponential Chetaev criterion | `NonlinearInstability.forwardUnstable_of_exponential_chetaev` | `Chetaev.lean` | ✅ done |
| Boundary-form/geometric Chetaev theorem | — | — | planned |
| LaSalle's invariance principle | `lasalle_invariance_principle` | `LaSalle.lean` | ✅ done |
| Barbashin's theorem (local asymptotic stability via LaSalle) | `lasalle_local_asymptotic_stable` | `LaSalle.lean` | ✅ done |
| Krasovskii's theorem (global asymptotic stability via LaSalle) | `lasalle_global_asymptotic_stable` | `LaSalle.lean` | ✅ done |
| Stable branch of Lyapunov's indirect method | `hurwitz_linearization_forward_locally_exponentially_stable` | `Linearization.lean` | ✅ done |
| Unstable branch of Lyapunov's indirect method | `forwardUnstable_of_exists_complex_eigenvalue_re_pos` | `NonlinearInstability.lean` | ✅ done |

Files:

- `DefsAutonomous.lean` — autonomous trajectory, stability, and Lyapunov-function definitions
- `Autonomous.lean` — Lyapunov stability / GAS / LAS
- `LaSalle.lean` — invariance principle and Barbashin/Krasovskii corollaries
- `LyapunovIndirect/DefsForward.lean` — finite-forward trajectory and stability predicates
- `LyapunovIndirect/Forward.lean` — finite-forward compatibility, local existence, and Lyapunov first-exit theory
- `LyapunovIndirect/Chetaev.lean` — generic finite-forward cutoff, continuation, and exponential Chetaev theory
- `LyapunovIndirect/Linearization.lean` — stable branch of Lyapunov's indirect method
- `LyapunovIndirect/LinearizationInstability.lean` — exact affine-linear positive-mode instability
- `LyapunovIndirect/NonlinearInstability.lean` — quadratic-certificate application and nonlinear unstable branch
- `LyapunovIndirect/DefsDynamics.lean`, `DefsLyapunov.lean`, `Lyapunov.lean`, `LyapunovEquation.lean`,
  `ExponentialStability.lean`, `InstabilityCertificate.lean`, `FrechetRemainder.lean` — supporting
  linear-system Lyapunov-equation and Fréchet-remainder infrastructure used by the indirect method

## Status: Non-autonomous systems (`ẋ = f(t, x)`)

| Result | Lean name | File | Status |
|---|---|---|---|
| Trajectories, equilibria, stability predicates | — | `DefsNonAutonomous.lean` | ✅ done |
| Picard–Lindelöf existence/uniqueness | `exists_unique_trajectory` (axiom) | `DefsNonAutonomous.lean` | ✅ axiomatized |
| Class-K sandwich bounds for positive-definite functions | `LyapunovClassKBounds` | `LyapunovBounds.lean` | ✅ done |
| Class-KL bound from the scalar decay ODE (Osgood construction) | `ClassK.sigma_isClassKL` | `ClassKDecay.lean` | ✅ done |
| Class-K characterization of uniform stability | `uniformlyStableNA_iff_classK` | `KLCharacterization.lean` | ✅ done |
| Class-KL characterization of uniform asymptotic stability | `uniformlyAsymptoticStableNA_iff_classKL` | `KLCharacterization.lean` | ✅ done |
| Class-KL characterization of global uniform asymptotic stability | `globallyUniformlyAsymptoticStableNA_iff_classKL` | `KLCharacterization.lean` | ✅ done |
| Lyapunov's uniform stability theorem | `lyapunov_uniformly_stable_NA` | `NonAutonomous.lean` | ✅ done |
| Lyapunov's uniform asymptotic stability theorem | `lyapunov_uniformly_asymptotic_stable_NA` | `NonAutonomous.lean` | ✅ done |

Files:

- `DefsNonAutonomous.lean` — trajectories, equilibria, and the stability predicates
  (stable, uniformly stable, unstable, asymptotically stable, uniformly asymptotically
  stable, globally uniformly asymptotically stable, exponentially stable, globally
  exponentially stable), and the Picard–Lindelöf existence axiom
- `LyapunovBounds.lean` — class-K sandwich bounds for continuous positive-definite
  functions (`ψ`/`φ` construction plus smoothing)
- `ClassKDecay.lean` — class-KL bound from the scalar decay ODE `ẏ = -α(y)`, plus the
  comparison-based decay bound `classK_dini_bound`
- `KLCharacterizationTools.lean` — supporting machinery for the KL characterizations
- `KLCharacterization.lean` — class-K / class-KL characterizations of the stability
  predicates in `DefsNonAutonomous.lean`
- `NonAutonomous.lean` — the two main Lyapunov theorems for non-autonomous systems

Comparison-function library (`LeanForControl/Comparison/`):

- `ClassK.lean`, `ClassKInfty.lean`, `ClassKL.lean`, `ClassL.lean` — the class K, K∞, KL,
  and L function structures and their algebra (composition, inverse, restriction)
- `Axioms.lean` — smoothing axioms used to turn monotone bounds into class K functions
- `ComparisonFunctions.lean` — shared comparison-function infrastructure

---

## Finite-forward stability and Lyapunov's indirect method

The indirect-method results use finite forward solution segments. This prevents a system
whose solution escapes in finite time from satisfying a stability predicate merely because
there is no trajectory defined on all of `ℝ`. The legacy autonomous API remains available,
with one-way compatibility theorems where the quantifiers make that sound.

| Infrastructure or result | Lean name | File | Status |
|---|---|---|---|
| Finite forward solution segment | Mathlib's `IsIntegralCurveOn ... (Icc 0 T)`, used directly | — | ✅ done (bespoke wrapper retired) |
| Forward Lyapunov stability | `ForwardLyapunovStable` | `DefsForward.lean` | ✅ done |
| Forward local exponential stability | `ForwardLocallyExponentiallyStable` | `DefsForward.lean` | ✅ done |
| Forward instability | `ForwardUnstable` | `DefsForward.lean` | ✅ done |
| Local finite segment for a `C¹` field | `ContDiffAt.exists_isIntegralCurveOn_Icc` | `Forward.lean` | ✅ done |
| Forward Lyapunov first-exit theorem | `forwardLyapunovStable_of_isLocalLyapunovFunction` | `Forward.lean` | ✅ done |
| Forward exponential stability implies legacy LAS | `ForwardLocallyExponentiallyStable.localAsymptoticStable` | `Forward.lean` | ✅ done |
| Hurwitz exponential contractivity block | `IsHurwitz.exists_norm_exp_nat_smul_lt_one` | `ExponentialStability.lean` | ✅ done |
| Arbitrary-`Q` continuous Lyapunov equation | `IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov` | `LyapunovEquation.lean` | ✅ done, axiom-free |
| Fréchet linearization remainder | `HasFDerivAt.centered_remainder_isLittleO` | `Analysis/Linearization.lean` | ✅ done |
| Quantitative remainder bound | `HasFDerivAt.exists_centered_remainder_bound` | `Analysis/Linearization.lean` | ✅ done |
| Hurwitz Jacobian gives forward local exponential stability | `hurwitz_linearization_forward_locally_exponentially_stable` | `Linearization.lean` | ✅ done |
| Hurwitz Jacobian gives legacy local asymptotic stability | `hurwitz_linearization_local_asymptotic_stable` | `Linearization.lean` | ✅ done |
| Positive-real eigenpair gives a quadratic Chetaev certificate | `exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos` | `InstabilityCertificate.lean` | ✅ done, axiom-free |
| Positive-real mode destabilizes the exact affine-linear system | `forwardUnstable_affineLinear_of_eigenvalue_re_pos` | `LinearizationInstability.lean` | ✅ done |
| Exponential Chetaev criterion on finite segments | `NonlinearInstability.forwardUnstable_of_exponential_chetaev` | `Chetaev.lean` | ✅ done |
| Positive-real Jacobian eigenpair destabilizes a `C¹` equilibrium | `forwardUnstable_of_complex_eigenvalue_re_pos` | `NonlinearInstability.lean` | ✅ done |
| Existential positive-real Jacobian eigenpair destabilizes a `C¹` equilibrium | `forwardUnstable_of_exists_complex_eigenvalue_re_pos` | `NonlinearInstability.lean` | ✅ done |

Supporting files outside `Stability/`:

- `Analysis/Linearization.lean` — generic little-o and quantitative bounds for the
  centered Fréchet-derivative remainder
- `LinearSystems/DefsDynamics.lean` — affine-linear vector fields on the repository's
  Euclidean state convention
- `LinearSystems/DefsLyapunov.lean` — the continuous-time Lyapunov equation and matrix
  quadratic-form definitions
- `LinearSystems/ExponentialStability.lean` — the contractive integer-time exponential
  block obtained from spectral mapping and Gelfand's formula
- `LinearSystems/Lyapunov.lean` — smoothness, derivative, coercivity, and norm bounds for
  matrix quadratic forms
- `LinearSystems/LyapunovEquation.lean` — an axiom-free construction of the
  continuous-time Lyapunov solution for every `Q.PosDef`, positive definiteness of the
  solution, and uniqueness among all matrix solutions
- `LinearSystems/InstabilityCertificate.lean` — an axiom-free shifted
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
4. A weighted-energy argument proves `ForwardLocallyExponentiallyStable f x_eq`.
   Compatibility with globally defined trajectories then gives `LocalAsymptoticStable`.

Thus the formal stable statement is stronger than the classical local-asymptotic
conclusion on finite forward segments, while still supplying that legacy conclusion.

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
4. `NonlinearInstability.forwardUnstable_of_exponential_chetaev` globalizes the field
   with a smooth cutoff, constructs arbitrarily long finite solution segments, and proves
   a first-radius escape.

The conclusion is `ForwardUnstable f x_eq`. This is the appropriate instability notion
for a general nonlinear field because it tests every finite forward segment and does not
assume that solutions extend globally in time. The existential wrapper
`forwardUnstable_of_exists_complex_eigenvalue_re_pos` is the direct formal counterpart of
the statement that the Jacobian has an eigenvalue in the open right half-plane.

References for the two branches: Khalil, *Nonlinear Systems*; Hahn,
*Stability of Motion*.

---

## Still planned: boundary-form/geometric Chetaev theorem

The completed `NonlinearInstability.forwardUnstable_of_exponential_chetaev` is a
quantitative criterion tailored to the indirect-method proof. It assumes, on a closed
ball, a quadratic upper bound
`|V(x)| ≤ C ‖x - x_eq‖²`, an exponential growth inequality
`2 α V(x) ≤ DV(x) f(x)`, and positive values of `V` arbitrarily close to `x_eq`.
Those hypotheses are enough for the quadratic certificate above.

This is distinct from the more general boundary-form version of Chetaev's theorem, which
remains planned. Its geometric hypotheses should package an open set `D₁` with `x_eq` on
its frontier, positivity of `V` and its Lie derivative in `D₁`, and vanishing of `V` on
the relevant boundary. The target conclusion should use `ForwardUnstable`, so finite-time
escape is handled without a global-trajectory assumption.

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

- `hasDerivAt_V_comp_traj` (chain rule)
- `V_nonincreasing`, `V_le_initial`, `V_nonneg`
- `V_tendsto_limit` (via `tendsto_atTop_ciInf`)
- `V_limit_zero` (EVT on compact sublevel set plus antitone bound)
- `isCompact_sublevel_set` (via `comap_norm_atTop`)
- `sphere_nonempty`, `trajectory_continuous`
- `omegaLimitTraj` (Mathlib `omegaLimit` wrapper for a single trajectory)
- `V_antitoneOn_lasalle` (`V̇ ≤ 0` on `Ω` makes `V ∘ φ` antitone on `[0,∞)`)
- `lasalle_V_tendsto` (`V(φ t)` tends to its infimum)
- `V_const_on_omegaLimit` (`V = L` on `ω(φ)` via `MapClusterPt`)
- `omegaLimit_subset_of_invariant` (`ω(φ) ⊆ Ω` when `Ω` is compact and positively invariant)

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

- **`hf_cont : Continuous f`** is needed as a theorem hypothesis (not in the Lyapunov
  structure) for `V_limit_zero`, because continuity of `x ↦ fderiv ℝ V x (f x)` needs it.

- **Non-autonomous work reuses the comparison-function library** (`Comparison/ClassK.lean`
  and related files) rather than the autonomous Lyapunov-function structures directly.
  Stability notions are characterized via class-K / class-KL bounds, and the main theorems
  in `NonAutonomous.lean` combine those bounds with the Dini-derivative comparison lemma.

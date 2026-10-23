# Plan: Lyapunov Stability Theory

## Status: Autonomous systems (`ẋ = f(x)`)

| Result | Lean name | File | Status |
|---|---|---|---|
| Lyapunov stability | `IsUniformLyapunovFunction.uniformlyStable` | `Continuous/LyapunovTheorems.lean` | ✅ done |
| Global asymptotic stability via strict Lyapunov function with compact sublevel sets | `globallyUniformlyAsymptoticallyStable_of_lyapunov` | `Continuous/LyapunovTheorems.lean` | ✅ done |
| Radially unbounded V has compact sublevel sets | `isCompact_sublevel_set` | `Analysis/SublevelSet.lean` | ✅ done |
| Local asymptotic stability via strict local Lyapunov function | `IsStrictUniformLyapunovFunction.uniformlyAsymptoticallyStable` | `Continuous/LyapunovTheorems.lean` | ✅ done |
| Exponential stability via exponential Lyapunov function | `IsExponentialLyapunovFunction.locallyExponentiallyStable`, `.globallyExponentiallyStable` | `Continuous/LyapunovTheorems.lean` | ✅ done |
| Quantitative exponential Chetaev criterion | `unstable_of_exponential_chetaev` | `Continuous/Chetaev.lean` | ✅ done |
| Boundary-form/geometric Chetaev theorem | `ContinuousSystem.unstable_of_geometric_chetaev` | `Continuous/Chetaev.lean` | ✅ done |
| ω-limit set of a trajectory | `omegaLimitSet`, `mem_omegaLimitSet_iff` | `Analysis/OmegaLimit.lean` | ✅ done |
| ω-limit set is forward invariant (Khalil Lemma 4.1) | `isForwardInvariant_omegaLimitSet` | `Continuous/LaSalle.lean` | ✅ done |
| `V̇ = 0` on the ω-limit set | `fderiv_apply_eq_zero_of_mem_omegaLimitSet` | `Continuous/LaSalle.lean` | ✅ done |
| LaSalle's invariance principle | `lasalle_invariance_principle` | `Continuous/LaSalle.lean` | ✅ done |
| Barbashin's theorem (local asymptotic stability via LaSalle) | `locallyAsymptoticallyStable_of_lasalle` | `Continuous/LaSalle.lean` | ✅ done |
| Krasovskii's theorem (global asymptotic stability via LaSalle) | `globallyAsymptoticallyStable_of_lasalle` | `Continuous/LaSalle.lean` | ✅ done |
| Stable branch of Lyapunov's indirect method | `hurwitz_linearization_locally_exponentially_stable` | `Continuous/Linearization.lean` | ✅ done |
| Unstable branch of Lyapunov's indirect method | `unstable_of_exists_complex_eigenvalue_re_pos` | `Continuous/Linearization.lean` | ✅ done |

Files:

- `DefsAutonomous.lean`, `DefsNonAutonomous.lean`, `Autonomous.lean`, `NonAutonomous.lean`,
  `LaSalle.lean`, `Continuous/Bridges.lean` — retired: the predicates are those of
  `Continuous/Defs.lean`, stated once on `ContinuousSystem` for time-varying and time-invariant
  systems alike, and the theorems are in the `Continuous/` files below
- `Continuous/LaSalle.lean` — invariance principle and Barbashin/Krasovskii corollaries
- `Continuous/Chetaev.lean` — smooth-cutoff continuation, first-exit machinery, and the
  exponential and geometric Chetaev criteria
- `Continuous/LyapunovFunctions.lean` — Lyapunov and state-only Chetaev certificates
- `Continuous/Linearization.lean` — Lyapunov's indirect method, both branches

## Status: Non-autonomous systems (`ẋ = f(t, x)`)

| Result | Lean name | File | Status |
|---|---|---|---|
| Trajectories, stability predicates | `ContinuousSystem.IsTrajectoryOn`, `Stable`, `UniformlyStable`, … | `Systems/Continuous.lean`, `Continuous/Defs.lean` | ✅ done |
| Picard–Lindelöf existence on `[t₀, ∞)` | `exists_isIntegralCurveOn_Ici` | `ODEs/PicardLindelof.lean` | ✅ done, axiom-free |
| Class-K sandwich bounds for positive-definite functions | `IsPositiveDefiniteOn.exists_classK_bounds` | `Comparison/PositiveDefiniteBounds.lean` | ✅ done |
| Class-KL solutions of the decay system `ẏ = −α(y)` | `ClassK.exists_classKL_trajectory_decaySystem` | `Comparison/DecaySystem.lean` | ✅ done |
| Subsolutions `D⁺v ≤ −α(v)` of the decay system ⟹ class-KL decay | `ClassK.exists_classKL_bound_of_subsolution` | `Comparison/DecaySystem.lean` | ✅ done |
| Class-K characterization of (uniform) stability | `stable_iff_classK`, `uniformlyStable_iff_classK` | `Continuous/KLCharacterization.lean` | ✅ done |
| Class-KL characterization of uniform asymptotic stability | `uniformlyAsymptoticallyStable_iff_classKL` | `Continuous/KLCharacterization.lean` | ✅ done |
| Class-KL characterization of global uniform asymptotic stability | `globallyUniformlyAsymptoticallyStable_iff_classKL` | `Continuous/KLCharacterization.lean` | ✅ done |
| Lyapunov's uniform stability theorem | `IsUniformLyapunovFunction.uniformlyStable` | `Continuous/LyapunovTheorems.lean` | ✅ done |
| Lyapunov's uniform asymptotic stability theorem | `IsStrictUniformLyapunovFunction.uniformlyAsymptoticallyStable` | `Continuous/LyapunovTheorems.lean` | ✅ done |
| Exponential stability from a power-law Lyapunov sandwich (Khalil Theorem 4.10) | `IsExponentialLyapunovFunction.locallyExponentiallyStable`, `.globallyExponentiallyStable` | `Continuous/LyapunovTheorems.lean` | ✅ done |
| Hespanha's Definition 8.1 for `ẋ = A(t)x` ⟺ the predicates of the unforced system | `stable_iff_boundedHomogeneousResponse` and friends | `LinearSystems/Stability/Continuous/LyapunovLTV.lean` | ✅ done |

Files:

- `Continuous/Defs.lean` — the stability predicates (stable, uniformly stable, unstable,
  locally/globally asymptotically stable, uniformly asymptotically stable, globally uniformly
  asymptotically stable, locally/globally exponentially stable), on trajectory segments
- `Comparison/PositiveDefiniteBounds.lean` (moved out of `Stability/`) — class-K sandwich
  bounds for continuous positive-definite functions (annulus-infimum / ball-supremum
  construction plus smoothing); only `IsPositiveDefiniteOn.exists_classK_bounds` is public
- `Comparison/DecaySystem.lean` (formerly `ClassKDecay.lean`) — the decay system `ẏ = -α(y)` as
  a `ContinuousSystem`, its class-KL solutions, and the class-KL bound on its subsolutions
- `Continuous/KLCharacterization.lean` — class-K / class-KL characterizations of the stability
  notions on `ContinuousSystem`, with the uniform decay envelopes they are built from; the old
  `KLCharacterization.lean` and `KLCharacterizationTools.lean`, stated on the ray-based
  predicates, are retired
- `Continuous/LyapunovTheorems.lean` — the two main Lyapunov theorems, stated on
  `ContinuousSystem` with the certificates of `Continuous/LyapunovFunctions.lean`

The predicates of `Continuous/Defs.lean` are also the ones the linear track uses, applied to the
unforced system `s.toContinuousSystem.zeroInput`: Hespanha's Definition 8.1, stated on the state
transition matrix of `ẋ = A(t)x`, is proved equivalent to them in `LinearSystems/Stability/Continuous/LyapunovLTV.lean` rather than re-defined there. That
file lives on the linear side because its subject is the linear system; see
`LeanForControl/LinearSystems/plan.md`.

Comparison-function library (`LeanForControl/Comparison/`):

- `ClassK.lean`, `ClassKInfty.lean`, `ClassKL.lean`, `ClassL.lean` — the class K, K∞, KL,
  and L function structures and their algebra (composition, inverse, restriction)
- `../Analysis/MonotoneFunctions.lean` — the monotone-to-strictly-monotone smoothing lemmas
  (minorant, global majorant, and the bounded-interval majorant derived from it)
- `ComparisonFunctions.lean` — shared comparison-function infrastructure

---

## Status: Discrete-time systems (`x⁺ = f(k, x)`)

The notions of `Continuous/Defs.lean` under the same names in namespace `DiscreteSystem`, ported
from the retired `DiscreteStability` branch (kept as a reference until the port is done).
Trajectories always exist and are unique, so every notion quantifies over rays `[k₀, ∞)` and no
forward completeness appears.

| Phase | Content | File | Status |
|---|---|---|---|
| 1 | Existence/uniqueness of trajectories, iterates, `zeroInput`; stability definitions, ultimate boundedness, implications | `Systems/Discrete.lean`, `Discrete/Defs.lean` | ✅ done |
| 2 | Lyapunov theorems for `x⁺ = f(x)`: uniformly stable, LAS, GAS, LES, GES | `Discrete/LyapunovTheorems.lean` | ✅ done |
| 3 | Linear: responses as trajectories, `Φ = A^(t-t₀)`; Hespanha Def. 8.2 on the unforced system | `LinearSystems/Solutions/DiscLTV.lean`, `LinearSystems/Stability/Discrete/LyapunovLTV.lean` | ✅ done |
| 4 | `IsSchur` ⇔ `Aᵏ → 0` ⇔ geometric envelope; Hespanha Thm. 8.3(2) | `LinearSystems/Stability/Discrete/Schur.lean`, `.../Discrete/LyapunovLTI.lean` | ✅ done |
| 5 | Discrete Lyapunov equation `AᵀPA - P = -Q`; Hespanha Thm. 8.4 (TFAE) | `LinearSystems/Stability/Discrete/LyapunovEquation.lean`, `.../Discrete/LyapunovLTI.lean` | ✅ done |
| — | Thm. 8.3(1), (3): marginal stability, instability | — | blocked: Jordan normal form |
| — | Difference along the system; time-varying certificates `V(k, x)` and uniform Lyapunov theorems | — | later |

Backlog:

- **References for the definitions.** `Discrete/Defs.lean` cites Khalil (read in discrete time)
  and Jungers and van de Wouw on some definitions only; the plan is to cite a discrete-time source
  throughout.  Jungers and van de Wouw, *Discrete-time nonlinear control systems* (Encyclopedia
  of Systems and Control Engineering, 2026), Definitions 2–3 and Remark 2, covers the
  time-invariant notions. For
  the time-varying and uniform ones, candidates are Elaydi, *An Introduction to Difference
  Equations* (3rd ed., 2005), Chapter 4; Bof, Carli and Schenato, *Lyapunov Theory for Discrete
  Time Systems* (arXiv:1809.05289); Agarwal, *Difference Equations and Inequalities* (2nd ed.,
  2000).  Check the exact definition numbers before citing.

## Finite-segment quantification and Lyapunov's indirect method

Every stability predicate of `Continuous/Defs.lean` quantifies over *finite forward solution
segments* (`s.IsTrajectoryOn u x (Icc t₀ t₁)`, an integral curve of the system's vector field on
the segment) rather than over solutions defined on all of `ℝ`. This prevents a system whose
solution escapes in finite time from satisfying a stability predicate merely because no global
trajectory exists.

There is no separate "forward" API: `Stable`, `LocallyExponentiallyStable` and `Unstable` in
`Continuous/Defs.lean` *are* the finite-segment notions.

| Infrastructure or result | Lean name | File | Status |
|---|---|---|---|
| Finite forward solution segment | `ContinuousSystem.IsTrajectoryOn` (Mathlib's `IsIntegralCurveOn`) | `Systems/Continuous.lean` | ✅ done |
| Stability, local exponential stability, instability | `Stable`, `LocallyExponentiallyStable`, `Unstable` | `Continuous/Defs.lean` | ✅ done |
| Local finite segment for a `C¹` field | `ContDiffAt.exists_isIntegralCurveOn_Icc` | `ODEs/ODE_properties.lean` | ✅ done |
| Lyapunov first-exit theorem | `IsUniformLyapunovFunction.uniformlyStable` | `Continuous/LyapunovTheorems.lean` | ✅ done |
| Exponential stability implies stability | `LocallyExponentiallyStable.uniformlyStable` | `Continuous/Defs.lean` | ✅ done |
| Escape witness gives instability | `unstable_of_escape` | `Continuous/Defs.lean` | ✅ done |
| Hurwitz exponential contractivity block | `IsHurwitz.exists_norm_exp_nat_smul_lt_one` | `LinearSystems/Stability/Continuous/ExponentialStability.lean` | ✅ done |
| Arbitrary-`Q` continuous Lyapunov equation | `IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov` | `LinearSystems/Stability/Continuous/LyapunovEquation.lean` | ✅ done, axiom-free |
| Linearization-error bound, `ε`–`δ` form | `HasFDerivAt.exists_linearization_error_bound` | `Analysis/FrechetDerivative.lean` | ✅ done |
| Remainder absorption shared by both branches | `exists_abs_fderiv_centeredQuadraticForm_remainder_le` | `MatrixAlgebra/QuadraticForm.lean` | ✅ done |
| Hurwitz Jacobian gives local exponential stability | `hurwitz_linearization_locally_exponentially_stable` | `Continuous/Linearization.lean` | ✅ done |
| Positive-real eigenpair gives a quadratic Chetaev certificate | `exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos` | `LinearSystems/Stability/Continuous/InstabilityCertificate.lean` | ✅ done, axiom-free |
| Positive-real mode destabilizes `ẋ = A x` at the origin | `unstable_linear_of_eigenvalue_re_pos` | `Continuous/Linearization.lean` (corollary of the nonlinear theorem) | ✅ done |
| Exponential Chetaev criterion on finite segments | `unstable_of_exponential_chetaev` | `Continuous/Chetaev.lean` | ✅ done |
| Positive-real Jacobian eigenpair destabilizes a `C¹` equilibrium | `unstable_of_exists_complex_eigenvalue_re_pos` | `Continuous/Linearization.lean` | ✅ done |

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

## Completed: boundary-form/geometric Chetaev theorem

The completed `unstable_of_exponential_chetaev` is a quantitative criterion tailored to the indirect-method proof. It assumes, on a closed
ball, a quadratic upper bound
`|V(x)| ≤ C ‖x - x_eq‖²`, an exponential growth inequality
`2 α V(x) ≤ DV(x) f(x)`, and positive values of `V` arbitrarily close to `x_eq`.
Those hypotheses are enough for the quadratic certificate above.

`ContinuousSystem.IsChetaevFunction` in `Continuous/LyapunovFunctions.lean` packages an open
region `D` with `x_eq` on its topological boundary, a positive radius, globally `C¹` state-only
certificate `V`, positivity in `D` inside the closed ball, boundary vanishing there, and
strictly positive system Lie derivative at every nonnegative time. Boundary means `∂D`,
represented by Mathlib's `frontier D`; the corresponding field is `hmem_boundary`.

`ContinuousSystem.unstable_of_geometric_chetaev` assumes a globally `C¹` field `f` and
`s.F t x () = f x`, and concludes `s.Unstable x_eq`. This negates `Stable`, whose radius
may depend on initial time, rather than merely negating `UniformlyStable`. Escape on finite
segments at time zero contradicts either reading. The time-independent state equation was
implicit in the original field-based formulation; there is no output restriction, equilibrium
premise, or forward-completeness assumption. All sign and boundary conditions remain local
to the fixed closed ball, and neither `D` nor `V` is assumed globally bounded.

The proof separates a positive derivative minimum on the seed's compact superlevel,
solution retention/nondecrease, and the growth-versus-ceiling escape contradiction. It reuses
the shared Lie-derivative chain rule and monotonicity lemmas. General boundary crossings
are public in `Analysis/Continuity.lean`; sphere crossing is their open-ball specialization.
The exponential criterion is now a corollary on the full positive set `{V > 0}`: the
quadratic bound gives `V(x_eq) = 0`, and positive seeds supply closure membership, together
placing the base point on the boundary. Its public statement and positional use in
`Linearization.lean` are preserved; the three exponential-only helpers are removed.
`tests/Chetaev.lean` exercises the migrated certificate on constant
rightward flow: zero is not an equilibrium, the criterion negates `Stable`, and the
regression also rules out `UniformlyStable`.

Reference: Khalil, *Nonlinear Systems*, 3rd ed. (Prentice Hall, 2002), Theorem 4.3,
p. 125. This is a boundary formulation of its positive-superlevel escape argument, with
an independent open region, stronger global regularity, and finite-segment system predicates.

---

## Infrastructure already in place (autonomous side)

- Differentiating along solutions: `Analysis/LieDerivative.lean` (`lieDerivative`,
  `IsIntegralCurveOn.antitoneOn_of_lieDerivative_nonpos`,
  `IsIntegralCurveOn.le_exp_mul_of_lieDerivative_le`)
- `isCompact_sublevel_set` (`Analysis/SublevelSet.lean`)
- `omegaLimitSet`, `mem_omegaLimitSet_iff` (`Analysis/OmegaLimit.lean`) — Mathlib's `omegaLimit`
  specialized to a single trajectory, and its membership criterion
- `isForwardInvariant_omegaLimitSet`, `fderiv_apply_eq_zero_of_mem_omegaLimitSet`
  (`Continuous/LaSalle.lean`)

The four classical LaSalle steps — `V ∘ φ` antitone, `V(φ t) → L`, `V ≡ L` on `ω(φ)`, and
`ω(φ) ⊆ Ω` — are `private` in `Continuous/LaSalle.lean`: they are steps of one proof, not results.

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

### Files that should move — done

`Chetaev.lean` now lives in `Stability/Continuous/`.  The remainder-absorption lemma
`exists_abs_fderiv_centeredQuadraticForm_remainder_le` moved to `MatrixAlgebra/QuadraticForm.lean`
(namespace `MatrixAlgebra`), and `Lyapunov.lean` was deleted.  `LinearizationInstability.lean`
was deleted: the linear instability theorem is a corollary of the nonlinear one, so `realMulVec`
went with it.  The two branches were then merged into `Stability/Continuous/Linearization.lean`,
and the `LyapunovIndirect/` directory removed.

`Chetaev.lean`'s remaining private `exists_cutoff_forward_segment` lemma keeps `forward`
in its name: it means *forward in time from 0* — a solution on `Icc 0 T` — which is
accurate and unrelated to the retired `Forward*` stability predicates.

## Open questions

- **Flat vs subdirectory for the bridges.** `LinearSystems/plan.md` Rule 2 says bridges from the
  linear track to nonlinear stability should be few. They are now one file,
  `Continuous/Linearization.lean`.

- **Do the two trajectory abbreviations earn their keep?** Resolved for the autonomous one: the
  old `IsTrajectoryOn` went with `DefsAutonomous.lean`, replaced by
  `ContinuousSystem.IsTrajectoryOn`, which takes the interval as an argument; `IsTrajectoryNA`
  went with `DefsNonAutonomous.lean`.

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
  in `Continuous/LyapunovTheorems.lean` combine those bounds with the Dini-derivative
  comparison lemma.

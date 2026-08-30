# Plan: Lyapunov Stability Theory

## Status: Autonomous systems (`ẋ = f(x)`)

| Result | Lean name | File | Status |
|---|---|---|---|
| Lyapunov stability | `lyapunov_stable` | `Autonomous.lean` | ✅ done |
| Global asymptotic stability via strict Lyapunov function | `lyapunov_asymptotic_stable` | `Autonomous.lean` | ✅ done |
| Global asymptotic stability via radially unbounded V | `lyapunov_global_asymptotic_stable` | `Autonomous.lean` | ✅ done |
| Local asymptotic stability via strict local Lyapunov function | `lyapunov_local_asymptotic_stable` | `Autonomous.lean` | ✅ done |
| Chetaev's instability theorem | — | — | planned |
| LaSalle's invariance principle | `lasalle_invariance_principle` | `LaSalle.lean` | ✅ done |
| Barbashin's theorem (local asymptotic stability via LaSalle) | `lasalle_local_asymptotic_stable` | `LaSalle.lean` | ✅ done |
| Krasovskii's theorem (global asymptotic stability via LaSalle) | `lasalle_global_asymptotic_stable` | `LaSalle.lean` | ✅ done |
| Linearization (indirect Lyapunov method) | — | — | planned |

Files:
- `DefsAutonomous.lean` — definitions, fully populated
- `Autonomous.lean` — Lyapunov stability / GAS / LAS, fully proved
- `LaSalle.lean` — invariance principle + Barbashin/Krasovskii corollaries, fully proved

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
| Lyapunov's uniform stability theorem (non-autonomous) | `lyapunov_uniformly_stable_NA` | `NonAutonomous.lean` | ✅ done |
| Lyapunov's uniform asymptotic stability theorem (non-autonomous, via comparison lemma) | `lyapunov_uniformly_asymptotic_stable_NA` | `NonAutonomous.lean` | ✅ done |

Files:
- `DefsNonAutonomous.lean` — trajectories, equilibria, the six stability predicates
  (stable, uniformly stable, unstable, asymptotically stable, uniformly asymptotically
  stable, globally uniformly asymptotically stable, exponentially stable), and the
  Picard–Lindelöf existence axiom
- `LyapunovBounds.lean` — class-K sandwich bounds for continuous positive-definite
  functions (`ψ`/`φ` construction + smoothing)
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

Infrastructure already in place (autonomous side):
- `hasDerivAt_V_comp_traj` (chain rule)
- `V_nonincreasing`, `V_le_initial`, `V_nonneg`
- `V_tendsto_limit` (via `tendsto_atTop_ciInf`)
- `V_limit_zero` (EVT on compact sublevel set + antitone bound)
- `isCompact_sublevel_set` (via `comap_norm_atTop`)
- `sphere_nonempty`, `trajectory_continuous`
- `omegaLimitTraj` (Mathlib `omegaLimit` wrapper for single trajectory)
- `V_antitoneOn_lasalle` (V̇ ≤ 0 on Ω → V ∘ φ antitone on [0,∞))
- `lasalle_V_tendsto` (V(φ t) → infimum via max-trick + `tendsto_atTop_ciInf`)
- `V_const_on_omegaLimit` (V = L on ω(φ) via `MapClusterPt`)
- `omegaLimit_subset_of_invariant` (ω(φ) ⊆ Ω when Ω compact positively invariant)

---

## Next: Chetaev's Instability Theorem

### Statement

Let x_eq be an equilibrium. Suppose there exists a C¹ function V : D → ℝ and an open
set D₁ ⊂ D with x_eq ∈ ∂D₁ ∩ D such that:
- V(x) > 0 and V̇(x) > 0 for all x ∈ D₁
- V(x) = 0 for all x ∈ ∂D₁ ∩ D

Then x_eq is **unstable** (i.e., ¬ LyapunovStable f x_eq).

### Required definitions (new in `DefsAutonomous.lean`)

```lean
-- IsChetaevFunction: all the hypotheses of Chetaev's theorem packaged together
structure IsChetaevFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) (D₁ : Set ℝⁿ) : Prop where
  hV_c1        : ContDiff ℝ 1 V
  hD₁_open     : IsOpen D₁
  hx_eq_bdry   : x_eq ∈ frontier D₁   -- x_eq ∈ ∂D₁ = closure D₁ \ interior D₁
  hV_pos       : ∀ x ∈ D₁, 0 < V x
  hLie_pos     : ∀ x ∈ D₁, 0 < fderiv ℝ V x (f x)
  hV_zero_bdry : ∀ x ∈ frontier D₁, V x = 0
```

### Target theorem

```lean
theorem chetaev_unstable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} {D₁ : Set ℝⁿ}
    (hV : IsChetaevFunction f V x_eq D₁) :
    ¬ LyapunovStable f x_eq
```

### Proof strategy

Unfold instability: find ε > 0 such that for every δ > 0 there exists a trajectory
starting in Bδ(x_eq) that eventually leaves Bε(x_eq).

Key argument:
1. Fix ε > 0 small enough that Bε(x_eq) ⊂ D (the domain).
2. Since x_eq ∈ ∂D₁, every ball Bδ(x_eq) intersects D₁. Pick x₀ ∈ Bδ(x_eq) ∩ D₁.
3. Let φ be the trajectory through x₀. Since V̇ > 0 in D₁, V(φ(t)) is strictly increasing
   while φ(t) ∈ D₁.
4. V(φ(t)) > V(φ(0)) > 0 for all t > 0 with φ(t) ∈ D₁, so φ cannot re-enter {V ≤ 0}
   which forces φ to stay in D₁ ∩ Bε(x_eq) or exit through ∂Bε(x_eq).
5. If φ stays in D₁ ∩ Bε(x_eq) forever, V(φ(t)) is strictly increasing and bounded above
   (by compactness), so V(φ(t)) → L > 0. But then φ is eventually in the compact set
   {x ∈ D₁ | V(x) ≥ V(x₀)/2} ∩ Bε(x_eq), so V̇ ≥ γ > 0 there (EVT), giving
   V(φ(t)) → ∞, contradiction.
6. So φ must exit Bε(x_eq). This shows instability.

Key Lean lemmas needed:
- `frontier_mem_nhds` or similar to find points of D₁ near x_eq
- `V_strictly_increasing` (mirror of `V_nonincreasing`): V̇ > 0 on D₁ → V ∘ φ strictly increasing
  while φ ∈ D₁. Lean path: `strictMono_of_deriv_pos` on D₁ time interval.
- EVT on compact subset of D₁: same `IsCompact.exists_isMaxOn` pattern as in `V_limit_zero`

---

## Next: Linearization (Indirect Lyapunov Method)

### Statement

Let f : ℝⁿ → ℝⁿ be C¹ with f(x_eq) = 0. Let A = fderiv ℝ f x_eq (the Jacobian at x_eq).

1. If A is Hurwitz (all eigenvalues have Re < 0), then x_eq is locally asymptotically stable.
2. If A has an eigenvalue with Re > 0, then x_eq is unstable.

### Required infrastructure

This theorem needs substantial external infrastructure:

- **Hurwitz matrices**: `IsHurwitz A ↔ ∀ λ ∈ A.eigenvalues ℂ, λ.re < 0`
  (partially developed in `Lyapunov_old/LinearSystems.lean`)

- **Lyapunov equation for Hurwitz matrices**: If A is Hurwitz, then for any Q ≻ 0 there exists
  a unique P ≻ 0 satisfying PA + AᵀP = -Q. Use Q = I for simplicity.
  (sketched in `Lyapunov_old/LinearSystems.lean`, all sorry)

- **Linearization error bound**: f(x) = Ax + g(x) where ‖g(x)‖/‖x‖ → 0 as x → x_eq.
  Lean path: Taylor's theorem / `HasFDerivAt` remainder bound.

### Proof strategy

Given P satisfying PA + AᵀP = -I:
1. Define V(x) = ‖x - x_eq‖²_P = (x - x_eq)ᵀ P (x - x_eq) (quadratic Lyapunov function).
2. V is positive definite (P ≻ 0).
3. V̇ along ẋ = f(x):
   - V̇ = (x - x_eq)ᵀ(PA + AᵀP)(x - x_eq) + 2(x - x_eq)ᵀPg(x)
   - = -(x - x_eq)ᵀ(x - x_eq) + 2(x - x_eq)ᵀPg(x)   (using PA + AᵀP = -I)
   - = -‖x - x_eq‖² + 2(x - x_eq)ᵀPg(x)
4. Since ‖g(x)‖/‖x - x_eq‖ → 0, for small enough ‖x - x_eq‖, the second term is dominated,
   giving V̇ < 0 in a neighborhood of x_eq.
5. Apply `lyapunov_asymptotic_stable` with this V restricted to a sublevel set.

### Priority assessment

Linearization is low priority for immediate Lean work because:
- It requires substantial eigenvalue/Hurwitz infrastructure not yet in the library.
- The LinearSystems files have this sketched but all sorry.
- Proving the Lyapunov equation existence (Sylvester-type) is a significant standalone project.

Suggested order: prove Chetaev's theorem first, then revisit linearization.

---

## Recommended execution order

1. **Chetaev's instability theorem** — new file `Stability/Instability.lean`.
   Self-contained, mirrors the stability proof structure.
   Difficulty: medium. Estimated effort: 1–2 sessions.

2. ~~**LaSalle's invariance principle**~~ — ✅ done in `LaSalle.lean`.

3. ~~**Barbashin/Krasovskii corollaries**~~ — ✅ done in `LaSalle.lean`.

4. **Linearization (indirect method)** — new file `Stability/Linearization.lean`.
   Blocked on eigenvalue / Lyapunov equation infrastructure.
   Estimated effort: 4+ sessions after unblocking.

---

## Lessons from the Lyapunov stability proofs

- **Pointwise Lie derivative** (`∀ x, fderiv ℝ V x (f x) ≤ 0`) cleaner than trajectory-based
  (`∀ φ t, HasDerivAt (V ∘ φ) ... t`). The chain rule bridge lemma `hasDerivAt_V_comp_traj`
  handles the connection.

- **`hequil : f x_eq = 0`** must be in the Lyapunov function struct to handle the `x_eq`
  case in `strict_implies_semidefinite`. Remember this for future structures.

- **Mathlib lemma names that landed**:
  - `HasFDerivAt.comp_hasDerivAt` — chain rule
  - `antitone_of_deriv_nonpos` — monotone calculus
  - `tendsto_atTop_ciInf` — antitone + bddBelow → convergence
  - `Antitone.le_of_tendsto` — antitone limit lower-bounds values
  - `IsCompact.exists_isMaxOn` / `exists_isMinOn` — EVT
  - `isPreconnected_Icc.intermediate_value₂` — IVT
  - `comap_norm_atTop` + `Metric.cobounded_eq_cocompact` — compact sublevel sets

- **`hf_cont : Continuous f`** is needed as a theorem hypothesis (not in the Lyapunov struct)
  for `V_limit_zero`, because continuity of `x ↦ fderiv ℝ V x (f x)` requires it.
  Carry this pattern forward.

- **Non-autonomous work reuses the comparison-function library** (`Comparison/ClassK.lean`
  etc.) rather than the autonomous Lyapunov-function structs directly: stability notions are
  characterized via class-K / class-KL bounds (`KLCharacterization.lean`), and the main
  theorems in `NonAutonomous.lean` are built from those bounds plus the Dini-derivative
  comparison lemma (`ClassKDecay.lean`), not from the `IsLocalLyapunovFunction`-style
  structs used for autonomous systems.

## Goal

Build a Lean library for core finite-dimensional linear systems theory in the spirit of Hespanha.

Long-term targets include:

- controllability
- observability
- Hautus tests
- stability and Lyapunov theory
- LQR
- estimator theory

## Current campaign

Use `dp-infhor.tex` as the current proving ground.

This is not the final goal. It is a focused subproject chosen because it forces the right reusable infrastructure:

- semidefinite covariance geometry
- block-matrix algebra
- finite-horizon quadratic optimization
- Riccati / LQR wrappers
- detectability and coercivity arguments

## Rule for what to prove now

A result belongs in the current queue if it is either:

1. needed directly for `dp-infhor.tex`, or
2. clearly part of the long-term linear-systems backbone

Avoid one-off technical work that serves neither.

## Recap

Already landed:

- observability matrix
- controllability matrix
- rank characterizations
- observability Hautus over `ℂ`
- reporting / blueprint infrastructure

So the linear-systems base is real. The next work should broaden it in the direction needed by `dp-infhor.tex`.

## Immediate todo

Work in this order:

1. Wrap up the current work and finish up the controllability Hautus sprint
1. Switch focus to dp-infhor.tex
    1. pass the execution gates
    2. formalize semidefinite-prior geometry
    3. formalize the reduced finite-horizon quadratic problem
    4. import or wrap the standard infinite-horizon LQR convergence fact
    5. prove coercivity of the nonstabilizable block
    6. prove cross-term decay
    7. prove convergence of the reduced minimizer and optimal value

## Roadmap for dp-infhor.tex

### Phase 0 — execution gates

Before Phase 1, check or build the required infrastructure: matrix order, block-matrix identities, quadratic minimization lemmas, semidefinite-prior primitives, discrete-time recursion conventions, imported-fact wrappers, and a fixed file split.

### Phase 1 — semidefinite prior geometry

Need:

- support/range constraint
- block covariance decomposition
- C2 implies the lower-right prior block is positive definite
- range parameterization of the semidefinite block

Deliverables:

- `Σ₂ ≻ 0`
- reduced coordinates `e₁ - a₁ = Z₁ η`
- prior quadratic term rewritten in `η`

### Phase 2 — finite-horizon reduced problem

Need:

- forecasted-disturbance Bellman recursion
- matrices `P_T`, `Y_T`, `S_T`
- reduced quadratic form
- positive definite reduced Hessian
- uniqueness of the finite-horizon minimizer

Deliverables:

- forecasted-disturbance LQR lemma
- reduced quadratic-form lemma
- finite-horizon minimizer theorem

### Phase 3 — asymptotic controllable block

Need:

- standard infinite-horizon LQR convergence wrapper
- limiting Riccati solution
- limiting gain and closed loop

Deliverables:

- `P_T → P`
- `K_T → K`
- `A_c,T → A_c`
- `A_c` Schur

### Phase 4 — coercivity of the nonstabilizable block

Need:

- finite zero-output test
- finite-window coercivity
- sampled Gramian divergence
- growth of the tail block

Deliverables:

- zero-output test
- coercivity corollary
- `λ_min(S_T) → ∞`
- `λ_min(Σ₂⁻¹ + S_T) → ∞`

### Phase 5 — cross-term decay

Need:

- Schur-complement positivity bound
- control of `P_T - Y_T M_T⁻¹ Y_T'`
- use coercive growth of `M_T = Σ₂⁻¹ + S_T`

Deliverables:

- `M_T⁻¹ Y_T' → 0`
- `Y_T M_T⁻¹ → 0`
- `M_T⁻¹ Σ₂⁻¹ a₂ → 0`

### Phase 6 — infinite-horizon limit

Split the final result into small pieces.

Deliverables:

1. closed-form minimizer in the nonstabilizable variable for fixed `η`
2. coefficientwise convergence of the reduced objective
3. `η_T* → η_∞`
4. `e₂(0|T)* → 0`
5. optimal value convergence
6. packaged infinite-horizon estimator theorem

## Theorem queue

### Preliminary lemmas

- semidefinite initial variance optimization lemma
- `Σ₂ ≻ 0`
- prior diagonalization / range parameterization
- forecasted-disturbance LQR lemma
- reduced quadratic-form lemma
- reduced Hessian positive definite
- standard LQR convergence wrapper
- finite zero-output test
- finite-window coercivity
- Gramian divergence / tail coercivity
- Schur-complement cross-term decay lemmas

### Main results

- convergence of the reduced minimizer
- convergence of the nonstabilizable initial block to zero
- convergence of the optimal value
- packaged infinite-horizon estimator theorem

## Working rules

- stay in `ℝ` unless a lemma truly needs `ℂ`
- prove reusable lemmas when possible
- keep matrix plumbing out of main theorem files
- do not wander into unrelated control topics
- do not jump to the final proposition too early

## Done condition

This campaign is successful when:

- the `dp-infhor.tex` chain is formalized
- the reusable pieces clearly strengthen the linear-systems library
- `lake build` stays green
- no `sorry`, `admit`, or `axiom`
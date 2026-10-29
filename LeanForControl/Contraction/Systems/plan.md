# Plan: Contraction theory — contracting systems

Roadmap for `Contraction/Systems/`: solutions of systems whose vector field or map is one-sided
Lipschitz or Lipschitz in some norm, the grades of contractivity, and worked certificates.
Statements about solutions are made on `ContinuousSystem` / `DiscreteSystem` and their
trajectories, not on a raw vector field with a chosen solution.  Builds on the one-sided Lipschitz
maps of `Contraction/Norms/`.

Remaining work only; done results are removed. Status: ◐ partial · ✗ missing (easy / med / hard).

## Solutions of one-sided Lipschitz systems `ẋ = F(t, x)`

| Result | Status | Where / what is needed |
|---|---|---|
| **Contraction bound**: if `F t` is one-sided Lipschitz with `b(t)`, then `‖x(t) - y(t)‖ ≤ e^{∫ₛᵗ b} ‖x(s) - y(s)‖`, any norm | ✗ med | curve norm derivative + Dini comparison, as for the Coppel bounds |
| Forward uniqueness | ✗ easy | contraction bound |
| Displacement: `‖x(t) - x₀‖ ≤ ∫_{t₀}^t e^{∫ₛᵗ b} ‖F(s, x₀)‖ ds` | ✗ med | same method |
| Forward completeness | ✗ hard | extension of solutions; existence from continuity alone (Peano) |
| Equivalence: one-sided Lipschitz with `b` ⟺ `D⁺‖x - y‖ ≤ b ‖x - y‖` along every pair of solutions | ✗ med | ⇒ contraction bound; ⇐ assumes a solution through every point |
| Discrete twin: Lipschitz with `b` ⟺ `‖x(k+1) - y(k+1)‖ ≤ b ‖x(k) - y(k)‖` | ✗ easy | |
| Speed bound `‖F(x(t))‖ ≤ e^{c(t-s)} ‖F(x(s))‖`, any norm | ✗ med | contraction bound applied to `x` and its time shift |

## Grades of contractivity

| Result | Status | Where / what is needed |
|---|---|---|
| Continuous time: infinitesimally nonexpansive, strictly and strongly (rate `c`) infinitesimally contracting | ✗ easy | in any norm, through `osL` |
| Discrete time: nonexpansive, strictly contracting, strongly contracting (factor `ρ`) | ✗ easy | |
| Strong ⇒ strict ⇒ nonexpansive | ✗ easy | |
| Jacobian forms `μ(DF) ≤ -c`, `‖DF‖ ≤ ρ` on convex sets | ✗ easy | `oneSidedLipschitz_le_iff_logNorm_le`; on `ℝⁿ`, `HasJacobianAt` |

## Certificates

| System | Norm | Status |
|---|---|---|
| `ẋ = -a x - b x³`; `x ↦ q x / (1 + b \|x\|)` | ℝ | ✗ easy |
| Affine `ẋ = A x + d`; Hurwitz ⇒ some `P ≻ 0` works | any, then ℓ² | ✗ easy |
| Descent–ascent saddle flow with a `log cosh` penalty | ℓ² | ✗ med (`sech²` bound) |
| Two-node Hopfield network, optimal weight `η = (√a, √b)` | weighted ℓ∞ | ✗ med (`tanh' ∈ (0, 1]`, `HasJacobianAt`) |
| Biochemical reaction network | weighted ℓ¹, Metzler | ✗ med |

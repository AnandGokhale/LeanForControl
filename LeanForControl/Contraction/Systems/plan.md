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
| Displacement: `‖x(t) - x₀‖ ≤ ∫_{t₀}^t e^{∫ₛᵗ b} ‖F(s, x₀)‖ ds` | ✗ med | same method |
| Forward completeness | ✗ hard | extension of solutions; existence from continuity alone (Peano) |
| Converse of the contraction bound: `IsInfinitesimallyContractingOn s u C c` ⇒ `osL(F(t, ·, u(t))) ≤ -c` on open `C` | ✗ med | difference quotients of pairs of trajectories through every point of `C` (an existence assumption) |
| Discrete twin: Lipschitz with `b` ⟺ `‖x(k+1) - y(k+1)‖ ≤ b ‖x(k) - y(k)‖` | ✗ easy | |
| Speed bound `‖F(x(t))‖ ≤ e^{c(t-s)} ‖F(x(s))‖`, any norm | ✗ med | contraction bound applied to `x` and its time shift |

## Grades of contractivity

| Result | Status | Where / what is needed |
|---|---|---|
| Continuous time: strictly contracting (`‖x(t) - y(t)‖` decreasing, no rate) | ✗ easy | `IsContractingOn` covers rate `c` (strong for `c > 0`, nonexpansive for `c = 0`) |
| Discrete time: nonexpansive, strictly contracting, strongly contracting (factor `ρ`) | ✗ easy | |
| Strong ⇒ strict ⇒ nonexpansive | ✗ easy | |
| Jacobian form: `μ(DF(t, ·)) ≤ -c` on an open convex `C` ⇒ `IsInfinitesimallyContractingOn`; discrete `‖DF‖ ≤ ρ` | ✗ easy | `oneSidedLipschitz_le_iff_logNorm_le` + `isInfinitesimallyContractingOn_of_oneSidedLipschitz`; on `ℝⁿ`, `HasJacobianAt` |

## Certificates

| System | Norm | Status |
|---|---|---|
| `ẋ = -a x - b x³`; `x ↦ q x / (1 + b \|x\|)` | ℝ | ✗ easy |
| Affine `ẋ = A x + d`; Hurwitz ⇒ some `P ≻ 0` works | any, then ℓ² | ✗ easy |
| Descent–ascent saddle flow with a `log cosh` penalty | ℓ² | ✗ med (`sech²` bound) |
| Two-node Hopfield network, optimal weight `η = (√a, √b)` | weighted ℓ∞ | ✗ med (`tanh' ∈ (0, 1]`, `HasJacobianAt`) |
| Biochemical reaction network | weighted ℓ¹, Metzler | ✗ med |

# Plan: Contraction theory — contracting systems

Roadmap for `Contraction/Systems/`: solutions of systems whose vector field or map is one-sided
Lipschitz or Lipschitz in some norm, the grades of contractivity, and worked certificates.
Statements about solutions are made on `ContinuousSystem` / `DiscreteSystem` and their
trajectories, not on a raw vector field with a chosen solution.  Builds on the one-sided Lipschitz
maps of `Contraction/Norms/`.

Remaining work only; done results are removed. Status: ◐ partial or stated with `sorry` · ✗ missing
(easy / med / hard).

## Well-posedness of one-sided Lipschitz systems `ẋ = F(t, x)`

| Result | Status | Where / what is needed |
|---|---|---|
| Uniqueness: `osL(F(t, ·)) ≤ b(t)`, `b` continuous ⇒ `HasUniqueSolutions` | ✗ easy | `norm_sub_le_exp_integral_of_oneSidedLipschitz`; today only the constant rate (`IsInfinitesimallyContractingOn.hasUniqueSolutions`) |
| Displacement: `‖x(t) - x₀‖ ≤ ∫_{t₀}^t e^{∫ₛᵗ b} ‖F(s, x₀)‖ ds` | ✗ med | the forced curve lemma `norm_le_exp_integral_add_of_pairing_le` (`Norms/CurveNormDerivative.lean`) with `x - x₀` |
| Comparison with an approximate trajectory `z`: forcing `‖F(s, z(s)) - ż(s)‖` | ✗ med | the same forced lemma with `x - z`; the displacement is `z ≡ x₀` |
| Local existence | ✗ med | Picard–Lindelöf for locally Lipschitz `F` (Mathlib); from continuity alone needs Peano (not in Mathlib, finite-dimensional) |
| Forward completeness: `osL(F(t, ·)) ≤ b(t)` on the whole space, `F` continuous ⇒ `IsForwardComplete` | ✗ hard | displacement bound keeps solutions in a ball on `[t₀, T]`; uniform Picard–Lindelöf step there; gluing of trajectories |
| Forward completeness on a closed forward-invariant convex set | ✗ hard | the above, with local existence in the set assumed |
| Forward uniqueness without backward uniqueness: `ẋ = -sign(x) √\|x\|` | ✗ easy | optional example |

## Contraction and the vector field

| Result | Status | Where / what is needed |
|---|---|---|
| Converse of the contraction bound: `IsInfinitesimallyContractingOn s u C c` ⇒ `osL(F(t, ·, u(t))) ≤ -c` on open `C` | ✗ med | difference quotients of pairs of trajectories through every point of `C` (an existence assumption) |
| Discrete twin: Lipschitz with `b` ⟺ `‖x(k+1) - y(k+1)‖ ≤ b ‖x(k) - y(k)‖` | ✗ easy | |
| Speed bound `‖F(x(t))‖ ≤ e^{-c(t-s)} ‖F(x(s))‖`, any norm | ✗ med | contraction bound applied to `x` and its time shift |
| Averaged estimate: `D⁺‖x - y‖ ≤ (∫₀¹ μ(DF(t, y + α(x - y))) dα) ‖x - y‖` | ✗ med | optional; integral form of the mean value theorem |

## Grades of contractivity

| Result | Status | Where / what is needed |
|---|---|---|
| Continuous time: strictly contracting (`‖x(t) - y(t)‖` decreasing, no rate) | ✗ easy | `IsContractingOn` covers rate `c` (strong for `c > 0`, nonexpansive for `c = 0`) |
| Discrete time: nonexpansive, strictly contracting, strongly contracting (factor `ρ`) | ✗ easy | |
| Strong ⇒ strict ⇒ nonexpansive | ✗ easy | |
| Discrete Jacobian form `‖DF‖ ≤ ρ` | ✗ easy | discrete-time definitions (above) |
| Jacobian forms for locally Lipschitz `F`, with `ess sup` | ✗ hard | the `ess sup` Jacobian tests (`Norms/plan.md`) |

## Certificates

| System | Norm | Status |
|---|---|---|
| `ẋ = -a x - b x³`; `x ↦ q x / (1 + b \|x\|)`: the three grades | ℝ | ✗ easy |
| Affine maps `x ↦ T x + d`: `‖T‖ ≤ ρ` ⇒ strongly contracting | any | ✗ easy (discrete definitions) |
| Descent–ascent saddle flow with a `log cosh` penalty | ℓ² | ✗ med (`sech²` bound) |
| Two-node Hopfield network, `tanh`, optimal weight `η = (√a, √b)` | weighted ℓ∞ | ✗ med (`tanh' ∈ (0, 1]`, `HasJacobianAt`) |
| Two-node Hopfield network, ReLU | weighted ℓ∞ | ✗ med: secant matrix `D ∈ [0, I]` diagonal, no `ess sup` needed |
| Biochemical reaction network | weighted ℓ¹, Metzler | ✗ med |
| Molecule sequestered by `n` substrates | weighted ℓ¹, Metzler | ✗ med |

# Plan: Contraction theory — norms, log norms and pairings

Roadmap for `Contraction/Norms/`: norms, induced norms, logarithmic norms and regular pairings on
`ℝⁿ` and on general normed spaces, the foundation for contracting systems.

Spine: F. Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), and A. V. Proskurnikov
and F. Bullo, *Regular Pairings for Nonquadratic Lyapunov Functions and Contraction Analysis*,
SIAM J. Control Optim. 64(1):496–521 (2026). Following `CONTRIBUTING.md`, results are named
descriptively rather than by number.

Remaining work only; done results are removed. Status: ◐ partial · ✗ missing (easy / med / hard).

## Norms, induced norms, log norms

| Result | Status | Where / what is needed |
|---|---|---|
| Log norm as the growth rate of `‖e^{Ah}x‖` at `h = 0` | ✗ med | derivative of the matrix exponential + Lumer |
| ℓ² induced norm `‖A‖₂ = √λ_max(AᵀA)` | ✗ med | |
| Weighted ℓ² induced norm as an LMI `AᵀPA ⪯ b²P` | ✗ med | needs the induced norm in `√(xᵀPx)` |
| ℓ¹/ℓ∞ log norms as sups of the sign/max pairings | ✗ med | sign and max pairings (below) + Lumer |

## Spectrum and monotonicity

| Result | Status | Where / what is needed |
|---|---|---|
| `\|λ\| ≤ ρ(A) ≤ ‖A‖`, `1/‖A⁻¹‖ ≤ \|λ\|` | ✗ med–hard | real `λ` easy; complex `λ` needs the norm on `ℂⁿ` |
| `-μ(-A) ≤ Re λ ≤ α(A) ≤ μ(A)` | ✗ med–hard | same |
| Monotonic norm, diagonal `A`: `‖A‖ = ρ(A)`, `μ(A) = α(A)` | ✗ med | monotonic norms |
| Monotonicity of `ρ`, `‖·‖`, `α`, `μ` under `\|A\|`, `\|A\|_M` | ✗ hard | monotonic norms, Perron–Frobenius-type facts |

## Optimal norms

| Result | Status | Where / what is needed |
|---|---|---|
| ε-optimal weighted norms via triangularization | ✗ hard | Schur form over `ℂ`, complex weights |
| Existence of optimal norms ⇔ semisimple critical eigenvalues | ✗ hard | Jordan form |
| Feasibility at `b = α(A)` ⇔ semisimple | ✗ hard | Jordan form |
| Optimal diagonal weights for nonnegative / Metzler matrices | ✗ hard | Perron–Frobenius |
| Majorant Hurwitz ⇒ diagonally stable ⇒ totally Hurwitz ⇒ Hurwitz | ✗ hard | |
| `α(A)` as the infimum of weighted log norms | ✗ hard | the three results above |

## Regular pairings

| Result | Status | Where / what is needed |
|---|---|---|
| Curve norm derivative a.e., locally Lipschitz curves | ◐ med | Mathlib's Rademacher + `hasDerivAt_norm_sq` |
| Sign and max pairings for weighted ℓ¹/ℓ∞; they are regular | ✗ med | the 7 axioms; max pairing is fiddly |
| Compatible pairings are squeezed by the upper pairing; agree a.e. | ✗ med | squeeze easy; a.e. needs Rademacher |

## Matrix sets

| Result | Status | Where / what is needed |
|---|---|---|
| Transpose-closed polytope of Hurwitz matrices ⇒ `μ₂ < 0` on it | ✗ med | `μ₂ = λ_max`; symmetric Hurwitz ⇒ `λ_max < 0` |
| Worst-case `μ₁`, `μ∞`, `‖·‖₁`, `‖·‖∞` of `[d]A` over `d ∈ [0,1]ⁿ` | ✗ med | explicit formulas; affine maximization over the cube |

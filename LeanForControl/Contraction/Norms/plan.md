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

## Spectrum and monotonicity

| Result | Status | Where / what is needed |
|---|---|---|
| `\|λ\| ≤ ρ(A) ≤ ‖A‖`, `1/‖A⁻¹‖ ≤ \|λ\|` | ✗ med–hard | real `λ` easy; complex `λ` needs the norm on `ℂⁿ` |
| `-μ(-A) ≤ Re λ ≤ α(A) ≤ μ(A)` | ◐ med–hard | ℓ² weights: `α(A) ≤ μ_{2,P^½}(A)` follows from `isHurwitzWithRate_iff_exists_logNormL2PosDef_lt` once `α(A)` is defined; general norms need the norm on `ℂⁿ` |
| Monotonic norm, diagonal `A`: `‖A‖ = ρ(A)`, `μ(A) = α(A)` | ✗ med | monotonic norms |
| Monotonicity of `ρ`, `‖·‖`, `α`, `μ` under `\|A\|`, `\|A\|_M` | ✗ hard | monotonic norms, Perron–Frobenius-type facts |

## Optimal norms

| Result | Status | Where / what is needed |
|---|---|---|
| ε-optimal weighted norms via triangularization | ✗ hard | Schur form over `ℂ`, complex weights |
| Existence of optimal norms ⇔ semisimple critical eigenvalues | ✗ hard | Jordan form (parked: `MatrixAlgebra/plan.md`) |
| Feasibility at `b = α(A)` ⇔ semisimple | ✗ hard | Jordan form (parked: `MatrixAlgebra/plan.md`) |
| Optimal diagonal weights for nonnegative / Metzler matrices | ✗ hard | Perron–Frobenius |
| Majorant Hurwitz ⇒ diagonally stable ⇒ totally Hurwitz ⇒ Hurwitz | ✗ hard | |
| `α(A)` as the infimum of weighted log norms | ◐ hard | ℓ² weights: the strict form is `isHurwitzWithRate_iff_exists_logNormL2PosDef_lt` (`LinearSystems/Stability/Continuous/HurwitzLogNorm.lean`); stating `α(A) = inf_P μ_{2,P^½}(A)` needs a definition of `α(A)`; diagonal ℓ¹/ℓ∞ weights need the three results above |

## Regular pairings

| Result | Status | Where / what is needed |
|---|---|---|
| Curve norm derivative a.e., locally Lipschitz curves | ◐ med | Mathlib's Rademacher + `hasDerivAt_norm_sq` |
| Compatible pairings are squeezed by the upper pairing; agree a.e. | ✗ med | squeeze easy; a.e. needs Rademacher |

## Matrix sets

| Result | Status | Where / what is needed |
|---|---|---|
| Transpose-closed polytope of Hurwitz matrices ⇒ `μ₂ < 0` on it | ✗ med | `μ₂ = λ_max`; symmetric Hurwitz ⇒ `λ_max < 0` |
| Worst-case `μ₁`, `μ∞`, `‖·‖₁`, `‖·‖∞` of `[d]A` over `d ∈ [0,1]ⁿ` | ✗ med | explicit formulas; affine maximization over the cube |

## One-sided Lipschitz maps

The nonlinear counterpart of the log norm, `osL F on C = sup_{x ≠ y ∈ C} ⟦F x - F y; x - y⟧ / ‖x - y‖²`
in `EReal` (`Defs.lean`); results in `OneSidedLipschitz.lean`.  Maps of `ℝⁿ` state their Jacobian
matrix with `HasJacobianAt F (J x) x` (`Analysis/Jacobian.lean`).

| Result | Status | Where / what is needed |
|---|---|---|
| Metzler Jacobian: `osL_{1,[η]} F ≤ b` ⟺ ordered increments, and the ℓ∞ form along `η` | ✗ easy | `oneSidedLipschitzLpWeight_eq_iSup` + diagonal log-norm formulas + `row_le_iff_ordered_increments` / `col_le_iff_increments_along` + `metzlerMajorant_eq_self` |
| Affine maps: `x ↦ A x + d` is Lipschitz with `ℓ` iff `‖A‖ ≤ ℓ` | ✗ easy | Mathlib's operator-norm API; the `osL` half is `oneSidedLipschitz_affine` |
| Lipschitz constant from the Jacobian: `Lip(F) = sup_C ‖DF‖` on open convex `C` | ✗ easy | Mathlib: `Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le`, `HasFDerivAt.le_of_lipschitzOn`; only a statement in our form |
| Lipschitz inverse: `osL F on C < 0` ⇒ `F⁻¹` on `F '' C` is Lipschitz with `-1 / osL F` | ✗ easy | `neg_mul_norm_sub_le_of_oneSidedLipschitz_le`; injectivity is `injOn_of_oneSidedLipschitz_neg` |
| Pairing-free formula: `osL F = sup_{x ≠ y} lim_{h→0⁺} (‖x - y + h(F x - F y)‖ - ‖x - y‖) / (h ‖x - y‖)` | ✗ med | the upper pairing as a right derivative of the norm (`Norms/CurveNormDerivative.lean`) |
| One-sided Lipschitz but not Lipschitz: `-x - x³` (`osL = -1`), `1/√x` on `(0, 1)` | ✗ easy | optional examples |
| `HasJacobianAt` on `EuclideanSpace`: `HasFDerivAt f (toEuclideanCLM A) x` ⟺ `HasJacobianAt (ofLp ∘ f ∘ toLp) A (ofLp x)` | ✗ easy | for the linearization theorems (`Stability/Continuous/Linearization.lean`) |
| Discrete ℓ² test: `‖DF‖_{2,P^½} ≤ ℓ` ⟺ `DFᵀ P DF ⪯ ℓ² P` ⟺ Lipschitz in `‖·‖_P` | ✗ med | weighted ℓ² induced norm as an LMI (above) |
| Monotonic norms: `osL` as a sup over ordered pairs only | ✗ hard | monotonic norms, sign-flip invariance of the pairing |
| Mean value inequality along translated segments: for a.e. small shift `w`, the segment from `y + w` to `x + w` meets the non-differentiability set in a null set | ✗ hard | Rademacher (Mathlib: `LipschitzWith.ae_differentiableAt`), Fubini |
| Jacobian tests with `ess sup` for locally Lipschitz `F`: `Lip(F) = ess sup ‖DF‖`, `osL(F) = ess sup μ(DF)` | ✗ hard | the translated segments, then continuity of `F` |
| Ordered incremental inequalities (Metzler forms above) from a.e. Jacobian bounds | ✗ med | the `ess sup` tests |

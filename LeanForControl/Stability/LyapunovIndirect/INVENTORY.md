# `Stability/LyapunovIndirect/` — declaration inventory

Every `def`, `lemma`, and `theorem` in this directory, grouped by file in import order
(roughly: shared infrastructure first, then the stable branch, then the unstable branch).
`private` declarations are visible only within their own file. Descriptions are taken from
each declaration's docstring where one exists; a `—` means the source has no docstring.

## `DefsDynamics.lean`
| Name | Kind | Description |
|---|---|---|
| `affineLinearVectorField` | def | The affine-linear vector field with equilibrium `x_eq` and state matrix `A`. |

## `DefsForward.lean`
| Name | Kind | Description |
|---|---|---|
| `IsForwardTrajectoryOn` | def | `φ` solves `x' = f x` on the finite forward interval `[0, T]`. |
| `ForwardLyapunovStable` | def | Forward Lyapunov stability, quantified over all finite forward solution segments. |
| `ForwardLocallyExponentiallyStable` | def | Local exponential stability on every finite forward solution segment. |
| `ForwardUnstable` | def | Forward instability is the negation of forward Lyapunov stability. |

## `DefsLyapunov.lean`
| Name | Kind | Description |
|---|---|---|
| `SolvesContinuousLyapunovEquation` | def | `P` solves the continuous-time Lyapunov equation `P A + Aᵀ P = -Q`. |
| `matrixQuadratic` | def | The real quadratic form `x ↦ xᵀ P x` represented on Euclidean space. |
| `centeredMatrixQuadratic` | def | The quadratic form associated to `P`, centered at an equilibrium `x_eq`. |

## `FrechetRemainder.lean`
| Name | Kind | Description |
|---|---|---|
| `HasFDerivAt.centered_remainder_isLittleO` | theorem | The centered error after subtracting a Fréchet derivative is little-o of the distance from the base point. |
| `HasFDerivAt.exists_centered_remainder_bound` | theorem | A Fréchet derivative gives an arbitrarily small linear bound on the centered first-order remainder near the base point. |

## `ComplexEigenpair.lean`
*(new — factored out during the duplication cleanup; shared by `InstabilityCertificate.lean` and `LinearizationInstability.lean`)*
| Name | Kind | Description |
|---|---|---|
| `matrixMulVec_re_smul_eigenpair` | lemma | For a complex eigenpair `(μ, v)` of the complexification of `A`, the real matrix `A` maps the real part of `c • v` to the real part of `c * μ • v`, for any complex scalar `c`. |
| `matrixMulVec_im_smul_eigenpair` | lemma | Same statement as above for the imaginary part. |

## `Lyapunov.lean`
| Name | Kind | Description |
|---|---|---|
| `posDef_one` | lemma | The identity matrix is positive definite, including in dimension zero. |
| `matrixQuadratic_contDiff` | lemma | A matrix quadratic form is smooth. |
| `matrixQuadratic_pos` | lemma | A positive-definite matrix has a positive quadratic form away from zero. |
| `matrixQuadratic_smul` | lemma | A matrix quadratic form is homogeneous of degree two. |
| `abs_matrixQuadratic_le` | lemma | The absolute value of a real matrix quadratic form is bounded by the operator norm times the squared vector norm; no definiteness required. |
| `matrixQuadratic_matrix_add` | lemma | A matrix quadratic form is additive in its representing matrix. |
| `matrixQuadratic_matrix_smul` | lemma | A matrix quadratic form is homogeneous in its representing matrix. |
| `exists_pos_mul_norm_sq_le_matrixQuadratic` | lemma | In positive dimension, a positive-definite matrix quadratic form uniformly dominates the square of the Euclidean norm. |
| `centeredMatrixQuadratic_contDiff` | lemma | A centered matrix quadratic form is smooth. |
| `fderiv_centeredMatrixQuadratic_apply` | theorem | The Fréchet derivative of a centered matrix quadratic form, evaluated at a direction. |
| `fderiv_centeredMatrixQuadratic_apply_matrix` | theorem | The derivative of a centered, possibly indefinite matrix quadratic form along `y' = A y` is represented by `P A + Aᵀ P`. |
| `abs_fderiv_centeredMatrixQuadratic_le` | theorem | The absolute derivative of a centered matrix quadratic form is controlled by twice the operator norm of its representing matrix. |
| `exists_abs_fderiv_centeredMatrixQuadratic_remainder_le` | theorem | *(new, factored out)* Near an equilibrium, the derivative of a centered matrix quadratic form applied to the first-order remainder of `f` is dominated by any prescribed positive multiple of the squared distance to the equilibrium — the shared remainder-absorption step of both branches of the indirect method. |
| `fderiv_centeredMatrixQuadratic_linear_general` | theorem | A solution of the Lyapunov equation makes the derivative of the `P`-quadratic form along the linear vector field equal to minus the `Q`-quadratic form. |
| `fderiv_centeredMatrixQuadratic_linear` | theorem | For identity forcing, the quadratic derivative along the linear vector field is `-‖x - x_eq‖²`. |
| `matrixQuadratic_le_opNorm_mul_norm_sq` | lemma | A matrix quadratic form is bounded above by the operator norm of its representing continuous linear map times the squared Euclidean norm. *(now a one-line corollary of `abs_matrixQuadratic_le`)* |
| `fderiv_centeredMatrixQuadratic_le` | theorem | The derivative of a centered matrix quadratic form is bounded by the product of the state norm, direction norm, and twice the matrix operator norm. *(now a one-line corollary of `abs_fderiv_centeredMatrixQuadratic_le`)* |
| `isCompact_centeredMatrixQuadratic_sublevel` | lemma | In positive dimension, every sublevel set of a centered positive-definite matrix quadratic form is compact. |

## `LyapunovEquation.lean`
| Name | Kind | Description |
|---|---|---|
| `entryCLM` | private def | *(new, factored out)* The continuous linear map extracting entry `(i, j)` of a matrix — shared row/column projection helper. |
| `quadraticEvalCLM` | private def | *(new, factored out)* The continuous linear map evaluating `xᵀ P x` in its matrix argument `P`, for a fixed vector `x`. |
| `lyapunovKernel` | private def | — the integrand `exp(tAᵀ) Q exp(tA)` of the finite Lyapunov integral. |
| `finiteLyapunovIntegral` | private def | — `∫₀ᵐ lyapunovKernel A Q t dt`. |
| `lyapunovOperator` | private def | — the linear map `P ↦ P A + Aᵀ P`. |
| `conjugationOperator` | private def | — the linear map `X ↦ Cᵀ X C`. |
| `hasDerivAt_lyapunovKernel_operator` | private lemma | — derivative of the kernel expressed via `lyapunovOperator`. |
| `hasDerivAt_lyapunovKernel` | private lemma | — derivative of the kernel in `t`. |
| `continuous_lyapunovKernel` | private lemma | — continuity of the kernel in `t`. |
| `finiteLyapunovIntegral_operator` | private lemma | — the finite integral telescopes via the fundamental theorem of calculus into an endpoint difference. |
| `finiteLyapunovIntegral_lyapunovOperator` | private lemma | — `lyapunovOperator` commutes with the finite integral. |
| `finiteLyapunovIntegral_neg` | private lemma | — the finite integral is additive/negation-compatible in `Q`. |
| `conjugationOperator_norm_lt_one` | private lemma | — operator-norm bound for `conjugationOperator C` when `‖C‖ < 1`. |
| `tendsto_conjugationOperator_pow_apply_zero` | private lemma | — `(conjugationOperator C)^k X → 0` when `‖C‖ < 1`. |
| `eq_zero_of_conjugationOperator_fixed` | private lemma | — a fixed point of a strictly contractive `conjugationOperator` is zero. |
| `lyapunovOperator_injective_of_exp_norm_lt_one` | private lemma | — `lyapunovOperator A` is injective when some exponential time-block is a strict contraction. |
| `finiteLyapunovIntegral_posDef` | private lemma | — the finite Lyapunov integral of a positive-definite `Q` is positive definite. |
| `posDef_conjugationOperator` | private lemma | — `conjugationOperator C X` is positive definite when `X` is and `C` is a unit. |
| `summable_conjugationOperator_pow_apply` | private lemma | — summability of `(conjugationOperator C)^k R` when `‖C‖ < 1`. |
| `lyapunovOperator_conjugationOperator` | private lemma | — a commutation identity between `lyapunovOperator` and `conjugationOperator` under `Commute A C`. |
| `lyapunovOperator_conjugationOperator_pow` | private lemma | — the same commutation identity, iterated to the `k`-th power. |
| `tsum_conjugationOperator_pow_apply_posDef` | private lemma | — the convergent series `∑' k, (conjugationOperator C)^k R` is positive definite. |
| `exists_posDef_unique_solution_continuous_lyapunov_of_exp_nat_norm_lt_one` | theorem | If one positive integer time step of the matrix exponential is a strict contraction, then every positive-definite forcing matrix `Q` has a positive-definite solution of `P A + Aᵀ P = -Q`, unique among all matrix solutions. |
| `IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov` | theorem | — the Hurwitz-hypothesis specialization of the theorem above (via `IsHurwitz.exists_norm_exp_nat_smul_lt_one`). |

## `ExponentialStability.lean`
| Name | Kind | Description |
|---|---|---|
| `continuousLinearMap_exp_apply_of_apply_eq_smul` | private lemma | — |
| `exp_mulVec_of_mulVec_eq_smul` | private lemma | The matrix exponential acts on an eigenvector by exponentiating its eigenvalue. |
| `exists_eigenpair_of_mem_spectrum_exp` | private lemma | Every spectral value of a complex matrix exponential is the exponential of an eigenvalue of the original matrix. |
| `exists_pow_norm_lt_one_of_spectralRadius_lt_one` | private lemma | An element with spectral radius strictly below one has a positive power whose norm is strictly below one. |
| `complexification_exp` | lemma | Entrywise complexification commutes with the matrix exponential. |
| `norm_complexification` | lemma | Entrywise complexification preserves the Frobenius norm. |
| `norm_lt_one_of_mem_spectrum_exp_complexification` | private lemma | Every spectral value of the exponential of a complexified Hurwitz matrix lies strictly inside the unit disk. |
| `spectralRadius_exp_complexification_lt_one` | lemma | The exponential of a complexified Hurwitz matrix has spectral radius strictly below one. |
| `IsHurwitz.exists_norm_exp_nat_smul_lt_one` | theorem | A real Hurwitz matrix has a positive integer-time exponential block with Frobenius norm strictly below one. |

## `Linearization.lean` *(stable branch)*
| Name | Kind | Description |
|---|---|---|
| `exists_centeredMatrixQuadratic_decay` | theorem | Near an equilibrium, a quadratic Lyapunov function solving the identity-forced Lyapunov equation has a uniform negative quadratic Lie-derivative bound. |
| `forwardLocallyExponentiallyStable_of_continuousLyapunovEquation` | theorem | A positive-definite solution of the identity-forced Lyapunov equation for the linearization gives local exponential stability of the nonlinear equilibrium on every finite forward solution segment. |
| `localAsymptoticStable_of_continuousLyapunovEquation` | theorem | A positive-definite solution of the identity-forced Lyapunov equation for the linearization implies local asymptotic stability in the legacy global-trajectory sense. |
| `hurwitz_linearization_forward_locally_exponentially_stable` | theorem | — the Hurwitz-hypothesis specialization (via the Lyapunov-equation existence theorem). |
| `hurwitz_linearization_local_asymptotic_stable` | theorem | — the legacy-trajectory compatibility corollary of the theorem above. |

## `Chetaev.lean` *(unstable-branch infrastructure, exponential criterion)*
| Name | Kind | Description |
|---|---|---|
| `exists_forward_segment_of_lipschitz_bounded` | private theorem | A globally Lipschitz, globally bounded autonomous vector field has a solution on every prescribed finite forward interval. |
| `exists_cutoff_forward_segment` | private theorem | A `C¹` vector field can be globalized by a smooth bump without changing it on a prescribed closed ball. |
| `exists_first_sphere_hit` | private theorem | A continuous curve that starts strictly inside a ball and later reaches its complement has a first hitting time of the sphere. |
| `exponential_lower_bound_on_forward_segment` | private theorem | A differential Chetaev inequality on one forward segment integrates to an exponential lower bound at the terminal time. |
| `exists_radius_escape_on_segment` | private theorem | If the exponential lower bound at the terminal time exceeds the quadratic upper bound on a ball, the segment must leave that ball. |
| `exists_cutoff_segment_reaching_radius` | private theorem | The smooth-cutoff segment from a positive Chetaev seed reaches the boundary of the certificate ball on some finite horizon. |
| `forwardUnstable_of_cutoff_segment_escape` | private theorem | Cutoff solution segments which start arbitrarily close to the equilibrium and reach a fixed radius witness forward instability. |
| `forwardUnstable_of_exponential_chetaev` | theorem | An exponentially increasing Chetaev function forces forward instability. |

## `InstabilityCertificate.lean` *(unstable branch: real quadratic certificate from a complex eigenvalue)*
| Name | Kind | Description |
|---|---|---|
| `bilinear_eq_zero_on_genEigenspaces` | private lemma | A resonance-avoiding bilinear form vanishes on a pair of generalized eigenspaces. |
| `hasEigenvalue_of_mem_maxGenEigenspace_ne_zero` | private lemma | A nonzero vector in a maximal generalized eigenspace witnesses that eigenvalue. |
| `bilinear_eq_zero_of_no_resonance` | private lemma | The bilinear form vanishes identically when no pairwise spectral resonance occurs. |
| `shiftedLyapunovOperator` | private def | The shifted Lyapunov map `P ↦ P A + Aᵀ P - (2a) • P`. |
| `toBilin_right_mul` | private lemma | Compatibility of `Matrix.toBilin'` with right multiplication. |
| `toBilin_left_transpose_mul` | private lemma | Compatibility of `Matrix.toBilin'` with left multiplication by a transpose. |
| `shiftedLyapunovOperator_injective_of_no_resonance` | private lemma | `shiftedLyapunovOperator` is injective when no resonance occurs among the shifted spectrum. |
| `exists_symmetric_shifted_lyapunov_solution` | private lemma | Existence of a symmetric solution to the shifted Lyapunov equation `H A + Aᵀ H - (2a) • H = 1`. |
| `toBilin_symm_real` | private lemma | — |
| `eigenpair_real_imag` | private lemma | Real/imaginary decomposition of `A *ᵥ Re(v)` and `A *ᵥ Im(v)` from a complexified eigenpair. *(now a corollary of `ComplexEigenpair.lean`)* |
| `exists_positive_matrixQuadratic_direction` | private lemma | — |
| `exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos` | theorem | A complex eigenvalue with positive real part supplies a real, positive-definite-direction quadratic Chetaev certificate for the shifted linearization. |

## `LinearizationInstability.lean` *(unstable branch: affine-linear systems)*
| Name | Kind | Description |
|---|---|---|
| `realEigenmode` | private def | The real growing mode `t ↦ Re(q e^{μt} v)` built from a complex eigenpair. |
| `realMulVec` | private def | `A` acting on `ℝⁿ` via `Matrix.toEuclideanCLM`. |
| `hasDerivAt_realEigenmode` | private lemma | The real eigenmode has the expected pointwise derivative in `t`. |
| `realEigenmode_deriv_eq_mulVec` | private lemma | The eigenmode's derivative equals `A` applied to the eigenmode. *(now a corollary of `ComplexEigenpair.lean`)* |
| `hasDerivAt_realEigenmode_of_eigenvector` | private lemma | The real eigenmode solves `x' = A x`. |
| `norm_realPart_toLp_le` | private lemma | The real part of a complex vector has norm at most the original vector's norm. |
| `abs_apply_le_euclideanNorm` | private lemma | A coordinate's absolute value is bounded by the Euclidean norm. |
| `norm_realEigenmode_le` | private lemma | Norm bound on the real eigenmode in terms of `‖q‖`, the exponential growth rate, and `‖v‖`. |
| `forwardUnstable_affineLinear_of_eigenvalue_re_pos` | theorem | An affine-linear system is forward unstable when its state matrix has a complex eigenvalue with positive real part. |

## `NonlinearInstability.lean` *(unstable branch: nonlinear equilibria via linearization)*
| Name | Kind | Description |
|---|---|---|
| `exists_centered_quadratic_seed` | private theorem | A positive value of a quadratic form gives positive points arbitrarily close to its center by scaling the witnessing direction. |
| `forwardUnstable_of_quadratic_certificate` | theorem | A quadratic Chetaev certificate for the shifted linearization implies forward instability of the nonlinear equilibrium. |
| `forwardUnstable_of_complex_eigenvalue_re_pos` | theorem | A `C¹` equilibrium is forward unstable when its Jacobian has a nonzero complex eigenvector whose eigenvalue has positive real part. |
| `forwardUnstable_of_exists_complex_eigenvalue_re_pos` | theorem | Same as above, stated with existential quantification over the eigenpair instead of explicit witnesses. |

## `Forward.lean` *(finite-forward trajectory infrastructure, used by both branches)*
| Name | Kind | Description |
|---|---|---|
| `ForwardLocallyExponentiallyStable.forwardLyapunovStable` | theorem | Local exponential stability on finite forward segments implies forward Lyapunov stability. |
| `IsTrajectory.isForwardTrajectoryOn` | theorem | A globally defined trajectory restricts to a finite forward solution segment. |
| `ForwardLyapunovStable.lyapunovStable` | theorem | Forward Lyapunov stability implies the legacy stability predicate for global trajectories. |
| `ForwardLocallyExponentiallyStable.localAsymptoticStable` | theorem | Local exponential stability on finite forward segments implies the legacy local asymptotic-stability predicate for globally defined trajectories. |
| `unstable_implies_forwardUnstable` | theorem | Instability in the legacy global-trajectory sense implies instability for finite forward segments. |
| `forwardUnstable_of_fixed_escape` | theorem | A fixed escape radius witnessed from arbitrarily small initial perturbations on finite forward segments implies forward instability. |
| `hasDerivWithinAt_V_comp_forwardTrajectoryOn` | lemma | Chain rule for a Lyapunov function along a finite forward solution segment. |
| `IsForwardTrajectoryOn.continuousOn` | lemma | A finite forward solution segment is continuous on its interval of definition. |
| `V_nonincreasing_on_forwardTrajectoryOn` | lemma | A Lyapunov function is nonincreasing between two times of a finite forward solution segment, provided the segment remains in the certificate region. |
| `forwardLyapunovStable_of_isLocalLyapunovFunction` | theorem | **Forward Lyapunov stability theorem.** A local Lyapunov function makes the equilibrium stable with respect to every finite forward solution segment. |
| `ContDiffAt.exists_isForwardTrajectoryOn` | theorem | A `C¹` vector field admits a nontrivial finite forward solution segment from every point at which it is `C¹`. |

# Audit: declarations added on the `ISS` branch

Declarations in the working tree whose names do not exist on `main` and are still to be audited.
Approved ones are deleted from this list.  *Lines* counts statement and proof, not the docstring.
Public unless marked *private*.

## Generalized or moved in the specific-function sweep (re-audit)

| ✓ | Declaration | Lines | Says | Notes |
|---|---|---|---|---|
| [ ] | [`Continuous.hasDerivAt_integral_comp`](LeanForControl/Analysis/Integrals.lean#L139) | | d/dτ ∫_a^{h(τ)} w = h′(t) w(h(t)): FTC + chain rule | replaces `hasDerivAt_integral_sub_add` (upper limit τ − t + c only) |
| [ ] | [`setIntegral_Ioi_comp_add_right`](LeanForControl/Analysis/Integrals.lean#L342) | | ∫_a^∞ w(σ + c) = ∫_{a+c}^∞ w | was private in Converse with a = 0; now any a, vector-valued w, proof from Mathlib translation invariance |
| [ ] | [`IsIntegralCurveOn.norm_sub_le`](LeanForControl/Analysis/IntegralCurves.lean#L329) | | integral curve of a field bounded by B on a convex set moves ≤ B\|τ₂ − τ₁\| | was private `norm_sub_le_of_isIntegralCurveOn` (ℝⁿ, Ici t) |
| [ ] | [`lipschitzWith_smul_of_lipschitzOnWith`](LeanForControl/Analysis/Continuity.lean#L186) | | g L-Lipschitz, ‖g‖ ≤ B on S, χ M-Lipschitz, \|χ\| ≤ 1, χ = 0 off S ⇒ χg is (L + MB)-Lipschitz | was private in Converse on ℝⁿ; now any pseudometric space |
| [ ] | [`IsIntegralCurveOn.norm_sub_mul_exp_le`](LeanForControl/ODEs/ODE_properties.lean#L386) | | **Khalil Ex 3.17:** ‖γ(t) − x_eq‖e^{−L(τ−t)} ≤ ‖γ(τ) − x_eq‖ | was private `norm_sq_mul_exp_le` (squared, ℝⁿ, Ici t); now norm form, inner product space, hypotheses only on (t, τ) |
| [ ] | [`abs_dotProduct_le`](LeanForControl/MatrixAlgebra/NormComparison.lean#L63) | | \|x · y\| ≤ \|X\|‖x‖‖y‖ (sup norm) | was private in DifferentialLyapunov |
| [ ] | [`dotProduct_mulVec_le`](LeanForControl/MatrixAlgebra/NormComparison.lean#L74) | | xᵀMx ≤ \|X\|‖M‖‖x‖² | was private in DifferentialLyapunov |
| [ ] | [`dotProduct_transpose_mul_mulVec`](LeanForControl/MatrixAlgebra/NormComparison.lean#L82) | | xᵀ(MᵀNM)x = (Mx)ᵀN(Mx) | was private in DifferentialLyapunov |

Inlined, no longer a lemma: `abs_sub_le_of_hasDerivAt` (Mathlib's mean value inequality at its one use).

## Analysis

| ✓ | Declaration | Lines | Says | Notes |
|---|---|---|---|---|
| [ ] | [`fderiv_eq_fderiv_uncurry_comp_inr`](LeanForControl/Analysis/FrechetDerivative.lean#L124) | 5 | ∂V/∂x is the joint derivative restricted to (0, v) | |
| [ ] | [`HasDerivWithinAt.hasDerivWithinAt_lieDerivative`](LeanForControl/Analysis/LieDerivative.lean#L93) | 6 | chain rule at a point, within any set (e.g. one-sided) | |
| [ ] | [`IsIntegralCurveOn.lieDerivative_eq_of_hasDerivWithinAt`](LeanForControl/Analysis/LieDerivative.lean#L128) | 7 | V̇ at (t, γ(t)) is the right derivative of V along the solution | |
| [ ] | [`lieDerivative_eq_add_fderiv_sub`](LeanForControl/Analysis/LieDerivative.lean#L150) | 7 | L_w V = L_v V + ∂V/∂x · (w − v) | |
| [ ] | [`lieDerivative_le_add_norm_fderiv_mul`](LeanForControl/Analysis/LieDerivative.lean#L159) | 6 | L_w V ≤ L_v V + ‖∂V/∂x‖ ‖w − v‖ | |
| [ ] | [`ContinuousOn.comp_uncurry_of_differentiableAt`](LeanForControl/Analysis/LieDerivative.lean#L167) | 5 | V is continuous along a curve wherever it is differentiable | |

## Comparison functions

| ✓ | Declaration | Lines | Says | Notes |
|---|---|---|---|---|
| [ ] | [`ClassKInfty.isPositiveDefiniteOn_comp`](LeanForControl/Comparison/ClassKInfty.lean#L100) | 5 | K∞ ∘ (positive definite) is positive definite | |
| [ ] | [`ClassKInfty.toClassK_invFun`](LeanForControl/Comparison/ClassKInfty.lean#L310) | 6 | restricting to class K keeps the inverse | |
| [ ] | [`ClassKLGlobal.unboundedMajorant`](LeanForControl/Comparison/ClassKL.lean#L568) (def) | 11 | β(r, s) + re^{−s}: global KL, ≥ β, radially unbounded | |
| [ ] | [`ClassKLGlobal.le_unboundedMajorant`](LeanForControl/Comparison/ClassKL.lean#L581) | 3 | the majorant is ≥ β | |
| [ ] | [`ClassKLGlobal.tendsto_unboundedMajorant_atTop`](LeanForControl/Comparison/ClassKL.lean#L586) | 4 | β(r, 0) + r → ∞ | |
| [ ] | [`ClassKLGlobal.mono_r`](LeanForControl/Comparison/ClassKL.lean#L593) | 3 | global KL is nondecreasing in r | |
| [ ] | [`ClassKLGlobal.anti_s_mono`](LeanForControl/Comparison/ClassKL.lean#L599) | 3 | global KL is nonincreasing in s | |
| [ ] | [`ClassK.exists_classKL_bound_above_level`](LeanForControl/Comparison/DecaySystem.lean#L829) | 26 | v̇ ≤ −α(v) only above η gives v(t) ≤ max (σ(v(t₀), t − t₀)) η | |
| [ ] | [`massera_rate`](LeanForControl/Comparison/Massera.lean#L31) *private* | 24 | the inverse rate θ of η(t) = g(t) + 1/t | |
| [ ] | [`ClassKInfty.massera`](LeanForControl/Comparison/Massera.lean#L94) | 183 | **Massera's lemma:** G, G′ ∈ K∞ with ∫G(u) ≤ k₁, ∫G′(u)h ≤ k₂ for 0 ≤ u ≤ g | |

## Matrix algebra

| ✓ | Declaration | Lines | Says | Notes |
|---|---|---|---|---|
| [ ] | [`norm_ofLp_le`](LeanForControl/MatrixAlgebra/NormComparison.lean#L29) | 2 | sup norm ≤ Euclidean norm | |
| [ ] | [`norm_le_sqrt_card_mul_norm_ofLp`](LeanForControl/MatrixAlgebra/NormComparison.lean#L33) | 10 | Euclidean norm ≤ √\|X\| · sup norm | |
| [ ] | [`sq_norm_le_dotProduct_self`](LeanForControl/MatrixAlgebra/NormComparison.lean#L45) | 8 | (sup norm)² ≤ sum of squares | |
| [ ] | [`norm_le_of_mulVec_le`](LeanForControl/MatrixAlgebra/NormComparison.lean#L55) | 4 | ‖Mx‖ ≤ C‖x‖ ∀x bounds the L∞ operator norm | |
| [ ] | [`norm_toEuclideanCLM_le`](LeanForControl/MatrixAlgebra/NormComparison.lean#L89) | 10 | Euclidean operator norm ≤ √\|X\| · L∞ operator norm | |
| [ ] | [`norm_toEuclideanCLM_symm_le`](LeanForControl/MatrixAlgebra/NormComparison.lean#L102) | 13 | and conversely | |
| [ ] | [`IsIntegralCurveOn.lieDerivative_eq_of_eq_add_integral`](LeanForControl/Analysis/LieDerivative.lean#L150) | | V(τ, γ(τ)) = C + ∫_t^τ ψ along a solution ⇒ V̇(t) = ψ(t) | new; shared by 4.12 and 4.16 |
| [ ] | [`quadraticForm_eq_dotProduct`](LeanForControl/MatrixAlgebra/QuadraticForm.lean#L80) | 5 | the quadratic form is yᵀ(Py) on `Fin n → ℝ` | |

## ODEs — `LeanForControl/ODEs/Sensitivity.lean` (new file)

| ✓ | Declaration | Lines | Says | Notes |
|---|---|---|---|---|
| [ ] | [`gronwallBound_zero_eq_mul`](LeanForControl/ODEs/Sensitivity.lean#L48) *private* | 4 | the Gronwall bound from 0 is linear in the forcing | |
| [ ] | [`ContDiff.exists_norm_sub_sub_fderiv_le`](LeanForControl/ODEs/Sensitivity.lean#L69) | 25 | uniform first-order Taylor estimate on a compact set | |
| [ ] | [`IsIntegralCurveOn.exists_dist_le_of_contDiff`](LeanForControl/ODEs/Sensitivity.lean#L111) | 70 | near a solution of a C¹ system, solutions separate at most like e^{Ks} | |
| [ ] | [`IsIntegralCurveOn.exists_variational`](LeanForControl/ODEs/Sensitivity.lean#L196) | 30 | Φ̇ = Dg(γ)Φ, Φ(0) = I has a solution | |
| [ ] | [`IsIntegralCurveOn.exists_norm_sub_sub_variational_le`](LeanForControl/ODEs/Sensitivity.lean#L252) | 86 | the linearization predicts the displacement to o(‖β(0) − γ(0)‖) | |
| [ ] | [`hasFDerivAt_of_isIntegralCurveOn`](LeanForControl/ODEs/Sensitivity.lean#L353) | 13 | solutions are differentiable in the initial state, with derivative Φ | |

## Linear time-varying systems

| ✓ | Declaration | Lines | Says | Notes |
|---|---|---|---|---|
| [ ] | [`hasDerivAt_stateTransitionMatrix_snd`](LeanForControl/LinearSystems/Solutions/CtsLTV.lean#L915) | 27 | ∂Φ(τ, t)/∂t = −Φ(τ, t)A(t) | |
| [ ] | [`norm_stateTransitionMatrix_le`](LeanForControl/LinearSystems/Solutions/CtsLTV.lean#L956) | 17 | ‖Φ(t, t₀)‖ ≤ ‖I‖e^{M\|t − t₀\|} | |
| [ ] | [`mem_uIcc_or_mem_uIcc_or_mem_uIcc`](LeanForControl/LinearSystems/Solutions/CtsLTV.lean#L984) *private* | 14 | of three times, one lies between the other two | |
| [ ] | [`stateTransitionMatrix_mul_swap`](LeanForControl/LinearSystems/Solutions/CtsLTV.lean#L1000) *private* | 5 | Φ(τ, s)Φ(s, τ) = I | |
| [ ] | [`stateTransitionMatrix_mul`](LeanForControl/LinearSystems/Solutions/CtsLTV.lean#L1015) | 8 | Φ(t, s)Φ(s, τ) = Φ(t, τ), no ordering, for bounded A | |
| [ ] | [`hasDerivAt_stateTransitionMatrix_of_bound`](LeanForControl/LinearSystems/Solutions/CtsLTV.lean#L1033) | 9 | ∂Φ(t, τ)/∂t = A(t)Φ(t, τ) everywhere, for bounded A | |
| [ ] | [`hasDerivAt_stateTransitionMatrix_snd_of_bound`](LeanForControl/LinearSystems/Solutions/CtsLTV.lean#L1052) | 9 | ∂Φ(τ, t)/∂t = −Φ(τ, t)A(t) everywhere, for bounded A | |
| [ ] | [`DifferentialLyapunovEquation`](LeanForControl/LinearSystems/Stability/DefsStability.lean#L124) (def) | 2 | −Ṗ = PA + AᵀP + Q for t ≥ 0 | |
| [ ] | [`differentialLyapunovEquation_const_iff`](LeanForControl/LinearSystems/Stability/Continuous/DifferentialLyapunov.lean#L58) | 13 | for constant matrices it is the algebraic Lyapunov equation | |
| [ ] | [`differentiableAt_dotProduct_mulVec`](LeanForControl/LinearSystems/Stability/Continuous/DifferentialLyapunov.lean#L74) *private* | 13 | xᵀP(t)x is differentiable in (t, x) | |
| [ ] | [`exists_differentialLyapunovEquation`](LeanForControl/LinearSystems/Stability/Continuous/DifferentialLyapunov.lean#L125) | 226 | **Khalil 4.12:** exponential stability ⇒ bounded symmetric P solving the differential Lyapunov equation | |
| [ ] | [`uniformlyAsymptoticallyStable_iff_decayingStateTransition`](LeanForControl/LinearSystems/Stability/Continuous/LyapunovLTV.lean#L541) | 82 | **Khalil 4.11:** LTV UAS ⇔ ‖Φ(t, t₀)x‖ ≤ ke^{−γ(t−t₀)}‖x‖ | |
| [ ] | [`globallyUniformlyAsymptoticallyStable_iff_decayingStateTransition`](LeanForControl/LinearSystems/Stability/Continuous/LyapunovLTV.lean#L642) | 9 | **4.11, global form** | |

## Stability definitions

| ✓ | Declaration | Lines | Says | Notes |
|---|---|---|---|---|
| [ ] | [`UniformlyBounded`](LeanForControl/Stability/Continuous/Defs.lean#L290) (def) | 4 | Khalil Def 4.6: uniformly bounded around x_c | |
| [ ] | [`GloballyUniformlyBounded`](LeanForControl/Stability/Continuous/Defs.lean#L306) (def) | 4 | uniformly bounded for every initial radius | |
| [ ] | [`UniformlyUltimatelyBounded`](LeanForControl/Stability/Continuous/Defs.lean#L336) (def) | 5 | forward complete from a ball, reaching the b-ball in time T(a, b) | |
| [ ] | [`GloballyUniformlyUltimatelyBounded`](LeanForControl/Stability/Continuous/Defs.lean#L357) (def) | 6 | the global version | |
| [ ] | [`LocallyExponentiallyStable.of_semiconj`](LeanForControl/Stability/Continuous/Defs.lean#L624) | 31 | exponential stability pulls back along a linear semiconjugacy | |
| [ ] | [`UniformlyBounded`](LeanForControl/Stability/Discrete/Defs.lean#L223) (def, discrete) | 4 | discrete-time counterpart | |
| [ ] | [`GloballyUniformlyBounded`](LeanForControl/Stability/Discrete/Defs.lean#L234) (def, discrete) | 4 | discrete-time counterpart | |

## Lyapunov theorems

| ✓ | Declaration | Lines | Says | Notes |
|---|---|---|---|---|
| [ ] | [`norm_lt_of_level_lt`](LeanForControl/Stability/Continuous/LyapunovTheorems.lean#L212) | 26 | trapping by a level set: V̇ ≤ 0 above η keeps a right trajectory inside the sphere | |

## Boundedness — `LeanForControl/Stability/Continuous/Boundedness.lean` (new file)

| ✓ | Declaration | Lines | Says | Notes |
|---|---|---|---|---|
| [ ] | [`exists_classKL_ultimateBound_of_lyapunov`](LeanForControl/Stability/Continuous/Boundedness.lean#L111) | 137 | **Khalil 4.18:** ‖x(t) − x_c‖ ≤ max (β(‖x(t₀) − x_c‖, t − t₀)) (α₁⁻¹(α₂(μ))) | |
| [ ] | [`uniformlyBounded_of_lyapunov`](LeanForControl/Stability/Continuous/Boundedness.lean#L262) | 28 | 4.18 ⇒ uniformly bounded | |
| [ ] | [`uniformlyUltimatelyBounded_of_lyapunov`](LeanForControl/Stability/Continuous/Boundedness.lean#L310) | 37 | 4.18 ⇒ uniformly ultimately bounded, bound α₁⁻¹(α₂(μ)) | |
| [ ] | [`exists_classKLGlobal_ultimateBound_of_lyapunov`](LeanForControl/Stability/Continuous/Boundedness.lean#L399) | 123 | **4.18, global case** | |
| [ ] | [`globallyUniformlyBounded_of_lyapunov`](LeanForControl/Stability/Continuous/Boundedness.lean#L537) | 22 | global 4.18 ⇒ globally uniformly bounded | |
| [ ] | [`globallyUniformlyUltimatelyBounded_of_lyapunov`](LeanForControl/Stability/Continuous/Boundedness.lean#L576) | 27 | global 4.18 ⇒ globally uniformly ultimately bounded | |

## ISS — `LeanForControl/Stability/Continuous/ISS.lean` (new file)

| ✓ | Declaration | Lines | Says | Notes |
|---|---|---|---|---|
| [ ] | [`InputToStateStable`](LeanForControl/Stability/Continuous/ISS.lean#L96) (def) | 5 | **Khalil Def 4.7** about (x_eq, u_eq): ‖x(t) − x_eq‖ ≤ β(‖x(t₀) − x_eq‖, t − t₀) + γ(M) along right trajectories, M bounding ‖u − u_eq‖ | |
| [ ] | [`InputToStateStable.globallyUniformlyAsymptoticallyStable`](LeanForControl/Stability/Continuous/ISS.lean#L120) | 10 | ISS ⇒ GUAS of `s.constInput u_eq` | |
| [ ] | [`norm_le_of_isISSLyapunov`](LeanForControl/Stability/Continuous/ISS.lean#L177) | 40 | ISS-Lyapunov function (V̇ ≤ −W₃ when ‖x − x_c‖ ≥ ρ(‖u − u_eq‖)) ⇒ ISS estimate, gain α₁⁻¹ ∘ α₂ ∘ ρ | |
| [ ] | [`inputToStateStable_of_isISSLyapunov`](LeanForControl/Stability/Continuous/ISS.lean#L236) | 12 | **Khalil 4.19** | |
| [ ] | [`inputToStateStable_of_globallyExponentiallyStable`](LeanForControl/Stability/Continuous/ISS.lean#L292) | 45 | **Khalil Lemma 4.6:** GES of ẋ = f(t, x, u_eq) + ‖f(t, x, u) − f(t, x, u_eq)‖ ≤ L‖u − u_eq‖ ⇒ ISS about (x_c, u_eq) | |

## Cascades — `LeanForControl/Stability/Continuous/Cascade.lean` (new file)

| ✓ | Declaration | Lines | Says | Notes |
|---|---|---|---|---|
| [ ] | [`cascadeKL`](LeanForControl/Stability/Continuous/Cascade.lean#L43) *private* (def) | 81 | the cascade's KL bound from β₁, γ₁, β₂ | |
| [ ] | [`norm_fst_sub_le_of_cascade`](LeanForControl/Stability/Continuous/Cascade.lean#L130) *private* | 33 | the driven state, by ISS twice (from t₀ and from the midpoint) | |
| [ ] | [`cascade_globallyUniformlyAsymptoticallyStable`](LeanForControl/Stability/Continuous/Cascade.lean#L201) | 30 | **Khalil Lemma 4.7:** s₁ ISS about (x_c, x_e) + s₂ GUAS at x_e ⇒ cascade GUAS | |
| [ ] | [`cascade_inputToStateStable`](LeanForControl/Stability/Continuous/Cascade.lean#L258) | 98 | s₁ ISS about (x_c, x_e) + s₂ ISS about (x_e, w_eq) ⇒ cascade ISS about ((x_c, x_e), w_eq) | |

## Linearization — `LeanForControl/Stability/Continuous/Linearization.lean`

| ✓ | Declaration | Lines | Says | Notes |
|---|---|---|---|---|
| [ ] | [`norm_linearization_remainder_le`](LeanForControl/Stability/Continuous/Linearization.lean#L369) *private* | 12 | ‖A(t)(x − x_eq) − f(t, x)‖ ≤ L₁‖x − x_eq‖² | |
| [ ] | [`ContinuousSystem.locallyExponentiallyStable_linearization`](LeanForControl/Stability/Continuous/Linearization.lean#L422) | 60 | **4.15 "only if":** exponential stability passes to the linearization (name ambiguous) | |
| [ ] | [`ContinuousSystem.locallyExponentiallyStable_of_linearization`](LeanForControl/Stability/Continuous/Linearization.lean#L518) | 158 | **Khalil 4.13:** Lyapunov's indirect method, time-varying | |
| [ ] | [`ContinuousSystem.locallyExponentiallyStable_iff_linearization`](LeanForControl/Stability/Continuous/Linearization.lean#L690) | 12 | **Khalil 4.15** | |

## Converse theorems — `LeanForControl/Stability/Continuous/Converse.lean` (new file)

| ✓ | Declaration | Lines | Says | Notes |
|---|---|---|---|---|
| [ ] | [`isIntegralCurveOn_timeAugmented`](LeanForControl/Stability/Continuous/Converse.lean#L66) *private* | 9 | appending time to the state | |
| [ ] | [`exists_hasFDerivAt_flow`](LeanForControl/Stability/Continuous/Converse.lean#L79) *private* | 12 | solutions are differentiable in initial time and state | |
| [ ] | [`differentiableAt_integral_norm_sq`](LeanForControl/Stability/Continuous/Converse.lean#L100) *private* | 82 | 4.14's V is differentiable | |
| [ ] | [`lieDerivative_integral_norm_sq`](LeanForControl/Stability/Continuous/Converse.lean#L187) *private* | 50 | 4.14's V̇ = ‖φ(t+δ) − x_eq‖² − ‖x − x_eq‖² | |
| [ ] | [`dist_flow_le`](LeanForControl/Stability/Continuous/Converse.lean#L242) *private* | 9 | solutions separate at most like e^{Lσ} in the initial state | |
| [ ] | [`norm_fderiv_integral_norm_sq_le`](LeanForControl/Stability/Continuous/Converse.lean#L255) *private* | 75 | 4.14's ‖∂V/∂x‖ = O(‖x − x_eq‖) | |
| [ ] | [`exists_quadraticLyapunov_of_estimateOn`](LeanForControl/Stability/Continuous/Converse.lean#L340) *private* | 80 | the 4.14 construction for a global field | |
| [ ] | [`exists_cutoff`](LeanForControl/Stability/Continuous/Converse.lean#L432) *private* | 47 | the cut-off field fχ | |
| [ ] | [`estimate_of_cutoff`](LeanForControl/Stability/Continuous/Converse.lean#L485) *private* | 34 | solutions of fχ from D₀ obey the estimate | |
| [ ] | [`exists_quadraticLyapunov_of_exponentialEstimate`](LeanForControl/Stability/Continuous/Converse.lean#L566) | 47 | **Khalil 4.14** (local) | |
| [ ] | [`exists_quadraticLyapunov_of_globallyExponentiallyStable`](LeanForControl/Stability/Continuous/Converse.lean#L660) | 20 | **4.14, global** | |
| [ ] | [`klRate`](LeanForControl/Stability/Continuous/Converse.lean#L689) *private* (def) | 2 | ĝ(σ) = β(r₀, max(σ−1, 0)) + r₀e^{1−σ} | |
| [ ] | [`klRate_spec`](LeanForControl/Stability/Continuous/Converse.lean#L692) *private* | 39 | ĝ positive, continuous, strictly decreasing to 0, dominates β | |
| [ ] | [`norm_flow_sub_flow_le`](LeanForControl/Stability/Continuous/Converse.lean#L736) *private* | 53 | nearby (t, x) ⇒ nearby solutions, (2B+1)e^{Lσ} | |
| [ ] | [`norm_flow_le_klRate`](LeanForControl/Stability/Continuous/Converse.lean#L794) *private* | 65 | solutions from near (t₀, x₀) obey ĝ | |
| [ ] | [`integrableOn_comp_classKL`](LeanForControl/Stability/Continuous/Converse.lean#L861) *private* | 17 | G(β(ρ,·)²) is integrable | |
| [ ] | [`integrableOn_comp_flow`](LeanForControl/Stability/Continuous/Converse.lean#L881) *private* | 22 | G(‖φ(t+σ) − x_eq‖²) is integrable | |
| [ ] | [`gradRate`](LeanForControl/Stability/Continuous/Converse.lean#L906) *private* (def) | 3 | A(ρ,σ) = 2G′(β²)βe^{Lσ} | |
| [ ] | [`gradRate_spec`](LeanForControl/Stability/Continuous/Converse.lean#L912) *private* | 36 | A nonnegative, dominated, continuous, integrable | |
| [ ] | [`exists_classK_ge_integral_gradRate`](LeanForControl/Stability/Continuous/Converse.lean#L951) *private* | 43 | ∫A(ρ,·) + ρ is class K | |
| [ ] | [`hasFDerivAt_integral_comp_flow`](LeanForControl/Stability/Continuous/Converse.lean#L1001) *private* | 149 | differentiation under the integral sign, plus the state-gradient bound | |
| [ ] | [`le_integral_comp_flow`](LeanForControl/Stability/Continuous/Converse.lean#L1161) *private* | 28 | G(e^{−2L}‖x − x_eq‖²) ≤ V | |
| [ ] | [`lieDerivative_integral_comp_flow`](LeanForControl/Stability/Continuous/Converse.lean#L1196) *private* | 50 | V̇ = −G(‖x − x_eq‖²) | |
| [ ] | [`exists_lyapunov_of_KLBoundedOn`](LeanForControl/Stability/Continuous/Converse.lean#L1253) *private* | 107 | the 4.16 construction for a global field | |
| [ ] | [`exists_lyapunov_of_KLBounded`](LeanForControl/Stability/Continuous/Converse.lean#L1430) | 47 | **Khalil 4.16** | |

## Changed on `main` declarations (breaking)

| ✓ | Declaration | Change | Notes |
|---|---|---|---|
| [ ] | `IsLyapunovFunction` and descendants | field `differentiable` → `differentiableAt` (t ≥ 0, x ∈ D) | |
| [ ] | `IsExponentialLyapunovFunction` | exponent `a` a parameter, field `exponent_pos`; `differentiableAt` | |
| [ ] | `IsExponentialLyapunovFunction.locallyExponentiallyStable`, `.globallyExponentiallyStable` | take `{a}` | |
| [ ] | `Is(Strict)UniformLyapunovFunction.of_timeInvariant` | `hV_diff : ∀ x ∈ D, DifferentiableAt ℝ V x` | |
| [ ] | `IsIntegralCurveOn.hasDerivWithinAt_lieDerivative`, `.antitoneOn_of_lieDerivative_nonpos`, `.le_exp_mul_of_lieDerivative_le` | differentiability only along the curve | |
| [ ] | `globallyUniformlyAsymptoticallyStable_iff_classKL` and two variants | `∃ β : ClassKLGlobal` instead of six spelled-out properties | |
| [ ] | `zeroInput` | defined as `s.constInput 0` (lemmas still `rfl`) | |

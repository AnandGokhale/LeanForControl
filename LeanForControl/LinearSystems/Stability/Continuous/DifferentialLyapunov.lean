import LeanForControl.LinearSystems.Stability.DefsStability
import LeanForControl.LinearSystems.Stability.Continuous.LyapunovLTV
import LeanForControl.Stability.Continuous.LyapunovFunctions
import LeanForControl.Analysis.LieDerivative
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Architect

/-!
# `LinearSystems.Stability.Continuous.DifferentialLyapunov` — the differential Lyapunov equation

The time-varying Lyapunov equation `-Ṗ = PA + AᵀP + Q` (`DifferentialLyapunovEquation`) of a
linear time-varying system `ẋ = A(t) x`.

Derivatives of matrix-valued functions are taken for the `L∞` operator norm, as in
`DifferentialLyapunovEquation`; the construction of Theorem 4.12 runs in the algebra of operators
on Euclidean space, where the transpose is the adjoint.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Section 4.6.

## Main results

* `differentialLyapunovEquation_const_iff` — for constant matrices the differential equation is
  the continuous (algebraic) Lyapunov equation.
* `exists_differentialLyapunovEquation` — Khalil's Theorem 4.12: an exponentially stable linear
  time-varying system has a solution `P` of the differential Lyapunov equation, and
  `V(t, x) = xᵀ P(t) x` is an exponential Lyapunov function for it.

## The construction

Khalil's `P(t) = ∫_t^∞ Φ(τ, t)ᵀ Q(τ) Φ(τ, t) dτ` is written as
`P(t) = Φ(0, t)ᵀ R(t) Φ(0, t)` with `R(t) = ∫_t^∞ G` and `G(τ) = Φ(τ, 0)ᵀ Q(τ) Φ(τ, 0)`, using
`Φ(τ, t) = Φ(τ, 0) Φ(0, t)`.  All the dependence on `t` inside the integral is then in its lower
limit, so `Ṗ` is the product rule, `∂Φ(0, t)/∂t = -Φ(0, t) A(t)`, and `Ṙ = -G` — no
differentiation under an infinite integral.  The bounds on `xᵀ P(t) x` and its derivative along
the system are read off `xᵀ P(t) x = ∫_t^∞ ψ`, with `ψ(τ) = (Φ(τ, t) x)ᵀ Q(τ) Φ(τ, t) x`.
-/

namespace LinearSystems

open Matrix
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X]

open Set MeasureTheory

local notation "𝔼" => EuclideanSpace ℝ X

/-- **For constant matrices the differential Lyapunov equation is the algebraic one**: a
constant `P` has zero derivative, so `-Ṗ = PA + AᵀP + Q` reads `PA + AᵀP = -Q`. -/
@[blueprint "lem:differentialLyapunovEquation-const-iff"
  (title := "Constant solutions of the differential Lyapunov equation")
  (latexEnv := "lemma")
  (statement := /-- For constant $A$, $P$ and $Q$, the differential Lyapunov equation
    (\cref{def:differentialLyapunovEquation}) holds if and only if the continuous Lyapunov
    equation (\cref{def:continuousLyapunovEquation}) does. -/)
  (proof := /-- The derivative of a constant is $0$, and derivatives are unique, so the
    differential equation says $0 = -(PA + A^{\mathsf T}P + Q)$. -/)]
theorem differentialLyapunovEquation_const_iff {A P Q : Matrix X X ℝ} :
    DifferentialLyapunovEquation (fun _ => A) (fun _ => P) (fun _ => Q) ↔
      ContinuousLyapunovEquation A P Q := by
  constructor
  · intro h
    have h0 : (0 : Matrix X X ℝ) = -(P * A + Aᵀ * P + Q) :=
      (hasDerivAt_const (0 : ℝ) P).unique (h 0 le_rfl)
    exact eq_neg_of_add_eq_zero_left (neg_eq_zero.mp h0.symm)
  · intro h t _
    have h0 : -(P * A + Aᵀ * P + Q) = 0 := by
      rw [show P * A + Aᵀ * P = -Q from h, neg_add_cancel, neg_zero]
    rw [h0]
    exact hasDerivAt_const t P

/-- The transpose of a matrix is the adjoint of the operator it defines on Euclidean space. -/
theorem toEuclideanCLM_transpose [DecidableEq X] (M : Matrix X X ℝ) :
    toEuclideanCLM (n := X) (𝕜 := ℝ) Mᵀ = star (toEuclideanCLM (n := X) (𝕜 := ℝ) M) := by
  rw [← conjTranspose_eq_transpose_of_trivial, ← Matrix.star_eq_conjTranspose]
  exact (toEuclideanCLM (n := X) (𝕜 := ℝ)).map_star' M

/-- `∫_t^∞ e^{-c(σ - t)} dσ = 1 / c` for `c > 0`, with the integrability that makes it
meaningful. -/
theorem integral_exp_neg_mul_sub_Ioi {c : ℝ} (hc : 0 < c) (t : ℝ) :
    IntegrableOn (fun σ => Real.exp (-c * (σ - t))) (Ioi t) ∧
      ∫ σ in Ioi t, Real.exp (-c * (σ - t)) = 1 / c := by
  have h_split : (fun σ => Real.exp (-c * (σ - t))) =
      fun σ => Real.exp (c * t) * Real.exp (-c * σ) := funext fun σ => by
    rw [← Real.exp_add]; congr 1; ring
  have h_one : Real.exp (c * t) * Real.exp (-c * t) = 1 := by
    rw [← Real.exp_add, show c * t + -c * t = 0 by ring, Real.exp_zero]
  rw [h_split]
  refine ⟨(integrableOn_exp_mul_Ioi (by linarith) t).const_mul _, ?_⟩
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith), neg_div_neg_eq, mul_div_assoc',
    h_one]

/-! ## Khalil's Theorem 4.12

`P(t) = ∫_t^∞ Φ(τ, t)ᵀ Q(τ) Φ(τ, t) dτ` (`ContinuousLTV.lyapunovIntegral`).  Since
`Φ(τ, t) = Φ(τ, 0) Φ(0, t)`, `P(t) = Φ(0, t)ᵀ (∫_t^∞ G) Φ(0, t)` with
`G(τ) = Φ(τ, 0)ᵀ Q(τ) Φ(τ, 0)`: all the dependence on `t` inside the integral is in its lower
limit, so `Ṗ` is the product rule, with no differentiation under the integral sign. -/

namespace ContinuousLTV

variable {U Y : Type*} [DecidableEq X] {s : ContinuousLTV X U Y ℝ} {Q : ℝ → Matrix X X ℝ}

/-- `Φ(τ, t)ᵀ Q(τ) Φ(τ, t) = Φ(0, t)ᵀ (Φ(τ, 0)ᵀ Q(τ) Φ(τ, 0)) Φ(0, t)`. -/
lemma lyapunovIntegrand_eq (hA : Continuous s.A) (t τ : ℝ) :
    s.lyapunovIntegrand Q t τ =
      star (s.stateTransition 0 t) * s.lyapunovIntegrand Q 0 τ * s.stateTransition 0 t := by
  simp only [lyapunovIntegrand, ← s.stateTransition_mul hA τ 0 t, StarMul.star_mul, mul_assoc]

lemma continuous_lyapunovIntegrand (hA : Continuous s.A) (hQ : Continuous Q) (t : ℝ) :
    Continuous (s.lyapunovIntegrand Q t) :=
  ((continuous_star.comp (s.continuous_stateTransition hA t)).mul
    (continuous_toEuclideanCLM.comp hQ)).mul (s.continuous_stateTransition hA t)

/-- Under exponential decay of `Φ`, the integrand decays like `e^{-2γ(τ - t)}`. -/
lemma norm_lyapunovIntegrand_le {k γ q : ℝ} (hk : 0 ≤ k)
    (h_decay : ∀ t₀, 0 ≤ t₀ → ∀ t ≥ t₀, ∀ x : EuclideanSpace ℝ X,
      ‖s.stateTransition t t₀ x‖ ≤ k * Real.exp (-γ * (t - t₀)) * ‖x‖)
    (hQ_bdd : ∀ t, ‖toEuclideanCLM (n := X) (𝕜 := ℝ) (Q t)‖ ≤ q) {t τ : ℝ} (ht : 0 ≤ t)
    (hτ : t ≤ τ) :
    ‖s.lyapunovIntegrand Q t τ‖ ≤ q * k ^ 2 * Real.exp (-(2 * γ) * (τ - t)) := by
  have hq : 0 ≤ q := (norm_nonneg _).trans (hQ_bdd 0)
  have hΦ : ‖s.stateTransition τ t‖ ≤ k * Real.exp (-γ * (τ - t)) :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) (h_decay t ht τ hτ)
  unfold lyapunovIntegrand
  calc ‖star (s.stateTransition τ t) * toEuclideanCLM (n := X) (𝕜 := ℝ) (Q τ) *
        s.stateTransition τ t‖
      ≤ ‖star (s.stateTransition τ t)‖ * ‖toEuclideanCLM (n := X) (𝕜 := ℝ) (Q τ)‖ *
          ‖s.stateTransition τ t‖ := (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ (k * Real.exp (-γ * (τ - t))) * q * (k * Real.exp (-γ * (τ - t))) := by
        rw [norm_star]
        exact mul_le_mul (mul_le_mul hΦ (hQ_bdd τ) (norm_nonneg _) (by positivity)) hΦ
          (norm_nonneg _) (by positivity)
    _ = q * k ^ 2 * Real.exp (-(2 * γ) * (τ - t)) := by
        rw [show -(2 * γ) * (τ - t) = -γ * (τ - t) + -γ * (τ - t) by ring, Real.exp_add]
        ring

/-- **`P` is symmetric** when `Q` is. -/
lemma star_lyapunovIntegral (hQ_symm : ∀ t, (Q t)ᵀ = Q t) (t : ℝ) :
    star (s.lyapunovIntegral Q t) = s.lyapunovIntegral Q t := by
  have h := (starL' ℝ : (EuclideanSpace ℝ X →L[ℝ] EuclideanSpace ℝ X) ≃L[ℝ] _).integral_comp_comm
    (μ := volume.restrict (Ioi t)) (s.lyapunovIntegrand Q t)
  simp only [starL'_apply] at h
  unfold lyapunovIntegral
  rw [← h]
  congr 1
  funext τ
  simp only [lyapunovIntegrand, StarMul.star_mul, star_star,
    ← toEuclideanCLM_transpose, hQ_symm, mul_assoc]

variable [Fintype U] [DecidableEq U]

/-- For an exponentially stable system the integrand is integrable on every right ray, for every
initial time. -/
lemma integrableOn_lyapunovIntegrand (hA : Continuous s.A) (hQ : Continuous Q) {q : ℝ}
    (hQ_bdd : ∀ t, ‖toEuclideanCLM (n := X) (𝕜 := ℝ) (Q t)‖ ≤ q)
    (h_exp : s.toContinuousSystem.zeroInput.LocallyExponentiallyStable 0) (t a : ℝ) :
    IntegrableOn (s.lyapunovIntegrand Q t) (Ioi a) := by
  obtain ⟨k, hk, γ, hγ, h_decay⟩ :=
    (locallyExponentiallyStable_iff_decayingStateTransition s hA).mp h_exp
  have h₀ : IntegrableOn (s.lyapunovIntegrand Q 0) (Ioi 0) :=
    Integrable.mono' ((integral_exp_neg_mul_sub_Ioi (by linarith : 0 < 2 * γ) 0).1.const_mul
        (q * k ^ 2)) (continuous_lyapunovIntegrand hA hQ 0).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ =>
        norm_lyapunovIntegrand_le hk.le h_decay hQ_bdd le_rfl hτ.le)
  have h₀a : IntegrableOn (s.lyapunovIntegrand Q 0) (Ioi a) :=
    ((continuous_lyapunovIntegrand hA hQ 0).integrableOn_Ioc.union h₀).mono_set fun τ hτ => by
      rcases le_or_gt τ 0 with h | h
      exacts [Or.inl ⟨hτ, h⟩, Or.inr h]
  exact ((ContinuousLinearMap.mulLeftRight ℝ _ (star (s.stateTransition 0 t))
    (s.stateTransition 0 t)).integrable_comp h₀a).congr (ae_of_all _ fun τ => by
      simp only [ContinuousLinearMap.mulLeftRight_apply]
      exact (lyapunovIntegrand_eq hA t τ).symm)

/-- `P(t) = Φ(0, t)ᵀ (∫_t^∞ G) Φ(0, t)` with `G(τ) = Φ(τ, 0)ᵀ Q(τ) Φ(τ, 0)`. -/
lemma lyapunovIntegral_eq (hA : Continuous s.A) (hQ : Continuous Q) {q : ℝ}
    (hQ_bdd : ∀ t, ‖toEuclideanCLM (n := X) (𝕜 := ℝ) (Q t)‖ ≤ q)
    (h_exp : s.toContinuousSystem.zeroInput.LocallyExponentiallyStable 0) (t : ℝ) :
    s.lyapunovIntegral Q t = star (s.stateTransition 0 t) *
      (∫ τ in Ioi t, s.lyapunovIntegrand Q 0 τ) * s.stateTransition 0 t := by
  let conj := ContinuousLinearMap.mulLeftRight ℝ (EuclideanSpace ℝ X →L[ℝ] EuclideanSpace ℝ X)
    (star (s.stateTransition 0 t)) (s.stateTransition 0 t)
  calc s.lyapunovIntegral Q t
      = ∫ τ in Ioi t, conj (s.lyapunovIntegrand Q 0 τ) := by
        unfold lyapunovIntegral
        congr 1
        funext τ
        exact lyapunovIntegrand_eq hA t τ
    _ = conj (∫ τ in Ioi t, s.lyapunovIntegrand Q 0 τ) :=
        conj.integral_comp_comm (integrableOn_lyapunovIntegrand hA hQ hQ_bdd h_exp 0 t)

/-- **`P` is bounded** on `[0, ∞)`, by `q k² / (2γ)` (Khalil's `c₂`, up to the norm of `x`). -/
lemma exists_norm_lyapunovIntegral_le (hA : Continuous s.A) {q : ℝ}
    (hQ_bdd : ∀ t, ‖toEuclideanCLM (n := X) (𝕜 := ℝ) (Q t)‖ ≤ q)
    (h_exp : s.toContinuousSystem.zeroInput.LocallyExponentiallyStable 0) :
    ∃ p, ∀ t, 0 ≤ t → ‖s.lyapunovIntegral Q t‖ ≤ p := by
  obtain ⟨k, hk, γ, hγ, h_decay⟩ :=
    (locallyExponentiallyStable_iff_decayingStateTransition s hA).mp h_exp
  refine ⟨q * k ^ 2 * (1 / (2 * γ)), fun t ht => ?_⟩
  obtain ⟨h_int, h_eq⟩ := integral_exp_neg_mul_sub_Ioi (by linarith : 0 < 2 * γ) t
  rw [← h_eq, ← integral_const_mul]
  exact norm_integral_le_of_norm_le (h_int.const_mul _)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ =>
      norm_lyapunovIntegrand_le hk.le h_decay hQ_bdd ht hτ.le)

/-- **The quadratic form of `P` integrates `Q` along the solution** (Khalil):
`xᵀ P(t) x = ∫_t^∞ φ(τ; t, x)ᵀ Q(τ) φ(τ; t, x) dτ` with `φ(τ; t, x) = Φ(τ, t) x`. -/
lemma inner_lyapunovIntegral (hA : Continuous s.A) (hQ : Continuous Q) {q : ℝ}
    (hQ_bdd : ∀ t, ‖toEuclideanCLM (n := X) (𝕜 := ℝ) (Q t)‖ ≤ q)
    (h_exp : s.toContinuousSystem.zeroInput.LocallyExponentiallyStable 0) (t : ℝ)
    (x : EuclideanSpace ℝ X) :
    IntegrableOn (fun τ => inner ℝ (s.stateTransition τ t x)
        (toEuclideanCLM (n := X) (𝕜 := ℝ) (Q τ) (s.stateTransition τ t x))) (Ioi t) ∧
      inner ℝ x (s.lyapunovIntegral Q t x) = ∫ τ in Ioi t, inner ℝ (s.stateTransition τ t x)
        (toEuclideanCLM (n := X) (𝕜 := ℝ) (Q τ) (s.stateTransition τ t x)) := by
  let ℓ : (EuclideanSpace ℝ X →L[ℝ] EuclideanSpace ℝ X) →L[ℝ] ℝ :=
    (innerSL ℝ x).comp (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ X) x)
  have hℓ : ∀ τ, ℓ (s.lyapunovIntegrand Q t τ) = inner ℝ (s.stateTransition τ t x)
      (toEuclideanCLM (n := X) (𝕜 := ℝ) (Q τ) (s.stateTransition τ t x)) := fun τ => by
    simp only [ℓ, lyapunovIntegrand, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, innerSL_apply_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have h_int := integrableOn_lyapunovIntegrand hA hQ hQ_bdd h_exp t t
  rw [← funext hℓ]
  refine ⟨ℓ.integrable_comp h_int, ?_⟩
  calc inner ℝ x (s.lyapunovIntegral Q t x)
      = ℓ (s.lyapunovIntegral Q t) := by simp [ℓ]
    _ = ∫ τ in Ioi t, ℓ (s.lyapunovIntegrand Q t τ) := (ℓ.integral_comp_comm h_int).symm

/-- **`P` is uniformly positive definite** (Khalil's `c₁ = c₃ / (2L)`): the solution from `x`
loses norm at most at rate `L` (Exercise 3.17), so the integrand is at least
`q₁ ‖x‖² e^{-2L(τ - t)}`. -/
lemma exists_lower_bound_lyapunovIntegral (hA : Continuous s.A) {L : ℝ}
    (hA_bdd : ∀ t, ‖toEuclideanCLM (n := X) (𝕜 := ℝ) (s.A t)‖ ≤ L) (hQ : Continuous Q) {q : ℝ}
    (hQ_bdd : ∀ t, ‖toEuclideanCLM (n := X) (𝕜 := ℝ) (Q t)‖ ≤ q) {q₁ : ℝ} (hq₁ : 0 < q₁)
    (hQ_pos : ∀ t (x : EuclideanSpace ℝ X),
      q₁ * ‖x‖ ^ 2 ≤ inner ℝ x (toEuclideanCLM (n := X) (𝕜 := ℝ) (Q t) x))
    (h_exp : s.toContinuousSystem.zeroInput.LocallyExponentiallyStable 0) :
    ∃ c₁ > 0, ∀ t (x : EuclideanSpace ℝ X),
      c₁ * ‖x‖ ^ 2 ≤ inner ℝ x (s.lyapunovIntegral Q t x) := by
  set K := |L| + 1
  have hK : 0 < K := by positivity
  refine ⟨q₁ * (1 / (2 * K)), by positivity, fun t x => ?_⟩
  obtain ⟨hψ_int, hψ_eq⟩ := inner_lyapunovIntegral hA hQ hQ_bdd h_exp t x
  obtain ⟨h_exp_int, h_exp_eq⟩ := integral_exp_neg_mul_sub_Ioi (by linarith : 0 < 2 * K) t
  -- Exercise 3.17 along the solution from `(t, x)`.
  have h_ex317 : ∀ τ, t ≤ τ → ‖x‖ * Real.exp (-K * (τ - t)) ≤ ‖s.stateTransition τ t x‖ :=
    fun τ hτ => by
      have h := (ContinuousSystem.IsTrajectoryOn.norm_exp_bounds (L := K)
        (IsIntegralCurveOn.mono (isTrajectoryOn_homogeneousResponse s hA t x)
          (Icc_subset_Ici_self : Icc t τ ⊆ Ici t)) (fun r _ => ?_) ⟨hτ, le_rfl⟩).1
      · rwa [stateTransition_self] at h
      simp only [ContinuousSystem.vectorField_apply, Pi.zero_apply, toContinuousSystem_F,
        map_zero, add_zero]
      calc ‖toEuclideanLin (s.A r) (s.stateTransition r t x)‖
          = ‖toEuclideanCLM (n := X) (𝕜 := ℝ) (s.A r) (s.stateTransition r t x)‖ := rfl
        _ ≤ ‖toEuclideanCLM (n := X) (𝕜 := ℝ) (s.A r)‖ * ‖s.stateTransition r t x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * ‖s.stateTransition r t x‖ := by
            gcongr
            exact (hA_bdd r).trans (by linarith [le_abs_self L])
  rw [hψ_eq, ← h_exp_eq, ← integral_const_mul, ← integral_mul_const]
  refine setIntegral_mono_on ((h_exp_int.const_mul _).mul_const _) hψ_int measurableSet_Ioi
    fun τ hτ => ?_
  calc q₁ * Real.exp (-(2 * K) * (τ - t)) * ‖x‖ ^ 2
      = q₁ * (‖x‖ * Real.exp (-K * (τ - t))) ^ 2 := by
        rw [show -(2 * K) * (τ - t) = -K * (τ - t) + -K * (τ - t) by ring, Real.exp_add]
        ring
    _ ≤ q₁ * ‖s.stateTransition τ t x‖ ^ 2 := by
        gcongr
        exact h_ex317 τ (le_of_lt hτ)
    _ ≤ _ := hQ_pos τ _

/-- **`P` solves the differential Lyapunov equation** `-Ṗ = PA + AᵀP + Q`, at every time, in the
algebra of operators (the transpose is the adjoint). -/
lemma hasDerivAt_lyapunovIntegral (hA : Continuous s.A) (hQ : Continuous Q) {q : ℝ}
    (hQ_bdd : ∀ t, ‖toEuclideanCLM (n := X) (𝕜 := ℝ) (Q t)‖ ≤ q)
    (h_exp : s.toContinuousSystem.zeroInput.LocallyExponentiallyStable 0) (t : ℝ) :
    HasDerivAt (s.lyapunovIntegral Q)
      (-(s.lyapunovIntegral Q t * toEuclideanCLM (n := X) (𝕜 := ℝ) (s.A t) +
        star (toEuclideanCLM (n := X) (𝕜 := ℝ) (s.A t)) * s.lyapunovIntegral Q t +
        toEuclideanCLM (n := X) (𝕜 := ℝ) (Q t))) t := by
  have hG := continuous_lyapunovIntegrand hA hQ (s := s) 0
  -- `R(σ) = ∫_σ^∞ G` has derivative `-G(t)`.
  have hR : HasDerivAt (fun σ => ∫ τ in Ioi σ, s.lyapunovIntegrand Q 0 τ)
      (-s.lyapunovIntegrand Q 0 t) t := by
    refine (((hG.integral_hasStrictDerivAt (t - 1) t).hasDerivAt).const_sub
      (∫ τ in Ioi (t - 1), s.lyapunovIntegrand Q 0 τ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (by linarith : t - 1 < t)] with σ hσ
    rw [← intervalIntegral.integral_Ioi_sub_Ioi
      (integrableOn_lyapunovIntegrand hA hQ hQ_bdd h_exp 0 (t - 1)) (le_of_lt hσ), sub_sub_cancel]
  have hΦ₀ := s.hasDerivAt_stateTransition_snd hA 0 t
  have h_one : s.stateTransition t t = 1 := ContinuousLinearMap.ext (s.stateTransition_self t)
  have h_Q : star (s.stateTransition 0 t) * s.lyapunovIntegrand Q 0 t * s.stateTransition 0 t =
      toEuclideanCLM (n := X) (𝕜 := ℝ) (Q t) := by
    rw [← lyapunovIntegrand_eq hA t t, lyapunovIntegrand, h_one, star_one, one_mul, mul_one]
  rw [show s.lyapunovIntegral Q = fun σ => star (s.stateTransition 0 σ) *
      (∫ τ in Ioi σ, s.lyapunovIntegrand Q 0 τ) * s.stateTransition 0 σ from
    funext (lyapunovIntegral_eq hA hQ hQ_bdd h_exp)]
  convert (hΦ₀.star.mul hR).mul hΦ₀ using 1
  rw [← h_Q]
  simp only [Pi.mul_apply, star_neg, StarMul.star_mul]
  noncomm_ring

end ContinuousLTV

variable {U Y : Type*} [DecidableEq X] [Fintype U] [DecidableEq U]

/-- **Converse Lyapunov theorem for linear time-varying systems**, Khalil's Theorem 4.12: if the
origin of `ẋ = A(t) x` is exponentially stable, with `A` continuous and bounded, then for every
continuous, bounded, uniformly positive definite, symmetric `Q(t)` there is a bounded, uniformly
positive definite, symmetric `P(t)` solving the differential Lyapunov equation
`-Ṗ = PA + AᵀP + Q`.

Norms of matrices are those of the operators they define on Euclidean space.  That
`V(t, x) = xᵀ P(t) x` is then a Lyapunov function is a separate result (Khalil's Example 4.21).

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.12. -/
@[blueprint "thm:continuousLTV-exists-differentialLyapunovEquation"
  (title := "Converse Lyapunov theorem for linear time-varying systems")
  (statement := /-- Consider $\dot x = A(t)x$ with $A$ continuous and $\|A(t)\| \le L$, and let
    the origin be exponentially stable
    (\cref{def:continuousSystem-locallyExponentiallyStable}).  Let $Q(t)$ be continuous,
    symmetric, with $\|Q(t)\| \le q$ and $x^{\mathsf T}Q(t)x \ge q_1\|x\|^2$, $q_1 > 0$.  Then
    there is a symmetric $P(t)$ satisfying the differential Lyapunov equation
    (\cref{def:differentialLyapunovEquation}) with $\|P(t)\| \le p$ for $t \ge 0$ and
    $x^{\mathsf T}P(t)x \ge c_1\|x\|^2$, $c_1 > 0$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.12. -/)
  (proof := /-- Take Khalil's $P(t) = \int_t^\infty \Phi(\tau, t)^{\mathsf T}Q(\tau)\Phi(\tau, t)\,
    d\tau$ (\cref{def:continuousLTV-lyapunovIntegral}).  It is bounded by exponential decay of
    $\Phi$, uniformly positive definite by Exercise 3.17
    (\cref{thm:continuousSystem-isTrajectoryOn-norm-exp-bounds}), symmetric because $Q$ is,
    and solves the differential Lyapunov equation by the product rule after writing
    $\Phi(\tau, t) = \Phi(\tau, 0)\Phi(0, t)$
    (\cref{thm:hasDerivAt-stateTransitionMatrix-snd}). -/)]
theorem exists_differentialLyapunovEquation (s : ContinuousLTV X U Y ℝ) (hA : Continuous s.A)
    {L : ℝ} (hA_bdd : ∀ t, ‖toEuclideanCLM (n := X) (𝕜 := ℝ) (s.A t)‖ ≤ L)
    {Q : ℝ → Matrix X X ℝ} (hQ : Continuous Q) {q : ℝ}
    (hQ_bdd : ∀ t, ‖toEuclideanCLM (n := X) (𝕜 := ℝ) (Q t)‖ ≤ q) (hQ_symm : ∀ t, (Q t)ᵀ = Q t)
    {q₁ : ℝ} (hq₁ : 0 < q₁) (hQ_pos : ∀ t (x : EuclideanSpace ℝ X),
      q₁ * ‖x‖ ^ 2 ≤ inner ℝ x (toEuclideanCLM (n := X) (𝕜 := ℝ) (Q t) x))
    (h_exp : s.toContinuousSystem.zeroInput.LocallyExponentiallyStable 0) :
    ∃ P : ℝ → Matrix X X ℝ, DifferentialLyapunovEquation s.A P Q ∧ (∀ t, (P t)ᵀ = P t) ∧
      (∃ p, ∀ t, 0 ≤ t → ‖toEuclideanCLM (n := X) (𝕜 := ℝ) (P t)‖ ≤ p) ∧
      ∃ c₁ > 0, ∀ t (x : EuclideanSpace ℝ X),
        c₁ * ‖x‖ ^ 2 ≤ inner ℝ x (toEuclideanCLM (n := X) (𝕜 := ℝ) (P t) x) := by
  set e := toEuclideanCLM (n := X) (𝕜 := ℝ)
  -- `e⁻¹`, as a continuous linear map, carries the operator equation back to matrices.
  let T : (EuclideanSpace ℝ X →L[ℝ] EuclideanSpace ℝ X) →L[ℝ] Matrix X X ℝ :=
    LinearMap.toContinuousLinearMap e.symm.toAlgEquiv.toLinearMap
  have he : ∀ t, e (T (s.lyapunovIntegral Q t)) = s.lyapunovIntegral Q t := fun t =>
    e.apply_symm_apply _
  obtain ⟨p, hp⟩ := ContinuousLTV.exists_norm_lyapunovIntegral_le hA hQ_bdd h_exp
  obtain ⟨c₁, hc₁, h_low⟩ :=
    ContinuousLTV.exists_lower_bound_lyapunovIntegral hA hA_bdd hQ hQ_bdd hq₁ hQ_pos h_exp
  refine ⟨fun t => T (s.lyapunovIntegral Q t), fun t _ => ?_, fun t => ?_,
    ⟨p, fun t ht => by rw [he]; exact hp t ht⟩,
    ⟨c₁, hc₁, fun t x => by rw [he]; exact h_low t x⟩⟩
  · convert T.hasFDerivAt.comp_hasDerivAt t
      (ContinuousLTV.hasDerivAt_lyapunovIntegral hA hQ hQ_bdd h_exp t) using 1
    change _ = e.symm (-(s.lyapunovIntegral Q t * e (s.A t) + star (e (s.A t)) *
      s.lyapunovIntegral Q t + e (Q t)))
    rw [← toEuclideanCLM_transpose, map_neg, map_add, map_add, map_mul, map_mul,
      StarAlgEquiv.symm_apply_apply, StarAlgEquiv.symm_apply_apply, StarAlgEquiv.symm_apply_apply]
    rfl
  · change (e.symm (s.lyapunovIntegral Q t))ᵀ = e.symm (s.lyapunovIntegral Q t)
    rw [← e.symm_apply_apply (e.symm (s.lyapunovIntegral Q t))ᵀ, toEuclideanCLM_transpose,
      StarAlgEquiv.apply_symm_apply, ContinuousLTV.star_lyapunovIntegral hQ_symm]

/-- **A solution of the differential Lyapunov equation is a Lyapunov function** (Khalil,
Example 4.21): if `P` solves `-Ṗ = PA + AᵀP + Q` with `c₁‖x‖² ≤ xᵀP(t)x`, `‖P(t)‖ ≤ p` and
`xᵀQ(t)x ≥ q₁‖x‖²`, then `V(t, x) = xᵀ P(t) x` is an exponential Lyapunov function with exponent
`2` for `ẋ = A(t) x`.

Along the system, `V̇ = xᵀṖx + (Ax)ᵀPx + xᵀPAx = -xᵀQx`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Example 4.21. -/
@[blueprint "thm:continuousLTV-isExponentialLyapunovFunction-of-differentialLyapunovEquation"
  (title := "Quadratic Lyapunov functions from the differential Lyapunov equation")
  (statement := /-- Let $P$ satisfy the differential Lyapunov equation
    (\cref{def:differentialLyapunovEquation}) for $A$ with forcing $Q$, with
    $c_1\|x\|^2 \le x^{\mathsf T}P(t)x$, $\|P(t)\| \le p$ and
    $x^{\mathsf T}Q(t)x \ge q_1\|x\|^2$ for $t \ge 0$, $c_1, q_1 > 0$.  Then
    $V(t, x) = x^{\mathsf T}P(t)x$ is an exponential Lyapunov function with exponent $2$
    (\cref{def:continuousSystem-isExponentialLyapunovFunction}) for $\dot x = A(t)x$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Example 4.21. -/)
  (proof := /-- The bounds are the hypotheses and Cauchy--Schwarz.  The derivative along the
    system is $x^{\mathsf T}\dot P x + (Ax)^{\mathsf T}Px + x^{\mathsf T}PAx$, which the
    differential Lyapunov equation turns into $-x^{\mathsf T}Qx \le -q_1\|x\|^2$. -/)]
theorem isExponentialLyapunovFunction_of_differentialLyapunovEquation
    (s : ContinuousLTV X U Y ℝ) {P Q : ℝ → Matrix X X ℝ}
    (hP : DifferentialLyapunovEquation s.A P Q) {p : ℝ}
    (hP_bdd : ∀ t, 0 ≤ t → ‖toEuclideanCLM (n := X) (𝕜 := ℝ) (P t)‖ ≤ p) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hP_low : ∀ t, 0 ≤ t → ∀ x : EuclideanSpace ℝ X,
      c₁ * ‖x‖ ^ 2 ≤ inner ℝ x (toEuclideanCLM (n := X) (𝕜 := ℝ) (P t) x))
    {q₁ : ℝ} (hq₁ : 0 < q₁) (hQ_pos : ∀ t, 0 ≤ t → ∀ x : EuclideanSpace ℝ X,
      q₁ * ‖x‖ ^ 2 ≤ inner ℝ x (toEuclideanCLM (n := X) (𝕜 := ℝ) (Q t) x)) :
    s.toContinuousSystem.zeroInput.IsExponentialLyapunovFunction
      (fun t x => inner ℝ x (toEuclideanCLM (n := X) (𝕜 := ℝ) (P t) x)) 0 univ 2 := by
  set e := toEuclideanCLM (n := X) (𝕜 := ℝ)
  set V : ℝ → EuclideanSpace ℝ X → ℝ := fun t x => inner ℝ x (e (P t) x)
  -- `e`, as a continuous linear map, carries `Ṗ` to the operators.
  let E : Matrix X X ℝ →L[ℝ] (EuclideanSpace ℝ X →L[ℝ] EuclideanSpace ℝ X) :=
    LinearMap.toContinuousLinearMap e.toAlgEquiv.toLinearMap
  have hM : ∀ t, 0 ≤ t → HasDerivAt (fun τ => e (P τ))
      (-(e (P t) * e (s.A t) + star (e (s.A t)) * e (P t) + e (Q t))) t := fun t ht => by
    convert E.hasFDerivAt.comp_hasDerivAt t (hP t ht) using 1
    change _ = e (-(P t * s.A t + (s.A t)ᵀ * P t + Q t))
    rw [map_neg, map_add, map_add, map_mul, map_mul, toEuclideanCLM_transpose]
  have hV_diff : ∀ t, 0 ≤ t → ∀ x, DifferentiableAt ℝ (Function.uncurry V) (t, x) :=
    fun t ht x => differentiableAt_snd.inner ℝ
      ((DifferentiableAt.comp (g := fun τ => e (P τ)) (t, x) (hM t ht).differentiableAt
        differentiableAt_fst).clm_apply differentiableAt_snd)
  have hp : 0 ≤ p := (norm_nonneg _).trans (hP_bdd 0 le_rfl)
  refine ⟨Filter.univ_mem, fun t ht x _ => hV_diff t ht x, two_pos, c₁, hc₁, p + 1,
    by positivity, q₁, hq₁, fun t ht x _ => ?_⟩
  simp only [sub_zero, Real.rpow_two]
  refine ⟨hP_low t ht x, ?_, ?_⟩
  · calc inner ℝ x (e (P t) x)
        ≤ ‖x‖ * ‖e (P t) x‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖e (P t)‖ * ‖x‖) := by gcongr; exact (e (P t)).le_opNorm x
      _ ≤ (p + 1) * ‖x‖ ^ 2 := by nlinarith [hP_bdd t ht, norm_nonneg x, norm_nonneg (e (P t))]
  -- The derivative along the system, read off the straight line through `x` with velocity `Ax`.
  set w := e (s.A t) x
  have hF : ∀ y, s.toContinuousSystem.zeroInput.F t y () = e (s.A t) y := fun y => by
    change toEuclideanLin (s.A t) y + toEuclideanLin (s.B t) 0 = _
    rw [map_zero, add_zero]
    rfl
  set γ : ℝ → EuclideanSpace ℝ X := fun τ => x + (τ - t) • w
  have hγt : γ t = x := by simp [γ]
  have hγ : HasDerivAt γ (s.toContinuousSystem.zeroInput.F t (γ t) ()) t := by
    rw [hγt, hF]
    have h := (((hasDerivAt_id t).sub_const t).smul_const w).const_add x
    rwa [one_smul] at h
  have h_lie := (hasDerivWithinAt_univ.mp (hγ.hasDerivWithinAt.hasDerivWithinAt_lieDerivative
    (V := V) (v := fun t y => s.toContinuousSystem.zeroInput.F t y ())
    (by rw [hγt]; exact hV_diff t ht x))).unique
    (hγ.inner ℝ ((hM t ht).clm_apply hγ))
  rw [hγt] at h_lie
  change s.toContinuousSystem.zeroInput.lieDerivative V t x () ≤ _
  rw [ContinuousSystem.lieDerivative, h_lie, hF]
  have h_adj : inner ℝ x (star (e (s.A t)) (e (P t) x)) = inner ℝ w (e (P t) x) := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mul_apply, inner_add_right, inner_neg_right, h_adj]
  linarith [hQ_pos t ht x]

end LinearSystems

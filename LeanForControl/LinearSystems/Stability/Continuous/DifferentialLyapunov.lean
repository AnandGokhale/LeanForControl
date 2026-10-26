import LeanForControl.LinearSystems.Stability.DefsStability
import LeanForControl.LinearSystems.Stability.Continuous.LyapunovLTV
import LeanForControl.Stability.Continuous.LyapunovFunctions
import LeanForControl.Analysis.LieDerivative
import LeanForControl.MatrixAlgebra.NormComparison
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Architect

/-!
# `LinearSystems.Stability.Continuous.DifferentialLyapunov` — the differential Lyapunov equation

The time-varying Lyapunov equation `-Ṗ = PA + AᵀP + Q` (`DifferentialLyapunovEquation`) of a
linear time-varying system `ẋ = A(t) x`.

Derivatives of matrix-valued functions are taken for the `L∞` operator norm, as for the state
transition matrix in `Solutions/CtsLTV.lean`.

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

/-- A quadratic form `x ↦ xᵀ P(t) x` with `P` differentiable at `t` is differentiable in `(t, x)`:
its value is a polynomial in the entries of `P(t)` and the coordinates of `x`. -/
private lemma differentiableAt_dotProduct_mulVec {P : ℝ → Matrix X X ℝ} {t : ℝ}
    (hP : DifferentiableAt ℝ P t) (x : X → ℝ) :
    DifferentiableAt ℝ (fun p : ℝ × (X → ℝ) => p.2 ⬝ᵥ (P p.1 *ᵥ p.2)) (t, x) := by
  have h_entry : ∀ i j, DifferentiableAt ℝ (fun p : ℝ × (X → ℝ) => P p.1 i j) (t, x) :=
    fun i j => by
      let e : Matrix X X ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (entryLinearMap ℝ ℝ i j)
      exact (e.differentiableAt.comp t hP).comp (t, x)
        (ContinuousLinearMap.fst ℝ ℝ (X → ℝ)).differentiableAt
  have h_coord : ∀ i, DifferentiableAt ℝ (fun p : ℝ × (X → ℝ) => p.2 i) (t, x) := fun i => by
    fun_prop
  simp only [dotProduct, mulVec]
  exact DifferentiableAt.fun_sum fun i _ => (h_coord i).mul
    (DifferentiableAt.fun_sum fun j _ => (h_entry i j).mul (h_coord j))

/-! ## Khalil's Theorem 4.12 -/

variable {U Y : Type*} [DecidableEq X] [Fintype U]

/-- **Converse Lyapunov theorem for linear time-varying systems.**  If the origin of
`ẋ = A(t) x` is exponentially stable, with `A` continuous and bounded, then for every continuous,
bounded, uniformly positive definite, symmetric `Q(t)` there is a bounded symmetric `P(t)`
solving the differential Lyapunov equation `-Ṗ = PA + AᵀP + Q`, and `V(t, x) = xᵀ P(t) x` is
an exponential Lyapunov function with exponent `2`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.12. -/
@[blueprint "thm:continuousLTV-exists-differentialLyapunovEquation"
  (title := "Converse Lyapunov theorem for linear time-varying systems")
  (statement := /-- Consider $\dot x = A(t)x$ with $A$ continuous and $\|A(t)\| \le L$, and let
    the origin be exponentially stable
    (\cref{def:continuousSystem-locallyExponentiallyStable}).  Let $Q(t)$ be continuous,
    symmetric, with $\|Q(t)\| \le q$ and $x^{\mathsf T}Q(t)x \ge q_1\|x\|^2$, $q_1 > 0$.  Then
    there is a bounded symmetric $P(t)$ satisfying the differential Lyapunov equation
    (\cref{def:differentialLyapunovEquation}), and $V(t, x) = x^{\mathsf T}P(t)x$ is an
    exponential Lyapunov function with exponent $2$
    (\cref{def:continuousSystem-isExponentialLyapunovFunction}); in particular
    $c_1\|x\|^2 \le x^{\mathsf T}P(t)x \le c_2\|x\|^2$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.12.  Differences: the
    state space carries the sup norm, as everywhere for linear time-varying systems here. -/)
  (proof := /-- Let $P(t) = \int_t^\infty \Phi(\tau, t)^{\mathsf T}Q(\tau)\Phi(\tau, t)\,d\tau$,
    written as $\Phi(0, t)^{\mathsf T}R(t)\Phi(0, t)$ with
    $R(t) = \int_t^\infty \Phi(\tau, 0)^{\mathsf T}Q(\tau)\Phi(\tau, 0)\,d\tau$, which converges by
    exponential decay of $\Phi$; the same decay bounds $P(t)$.  Then
    $\dot R(t) = -\Phi(t, 0)^{\mathsf T}Q(t)\Phi(t, 0)$ and
    $\partial_t\Phi(0, t) = -\Phi(0, t)A(t)$
    (\cref{thm:hasDerivAt-stateTransitionMatrix-snd-of-bound}), and the product rule gives
    $-\dot P = PA + A^{\mathsf T}P + Q$.  Along a solution,
    $x^{\mathsf T}P(t)x = \int_t^\infty (\Phi(\tau, t)x)^{\mathsf T}Q(\tau)\Phi(\tau, t)x\,d\tau$:
    exponential decay bounds it above, the growth bound
    (\cref{lem:norm-stateTransitionMatrix-le}) bounds it below on $[t, t + 1]$, and its
    derivative along the solution is $-x^{\mathsf T}Q(t)x$. -/)]
theorem exists_differentialLyapunovEquation (s : ContinuousLTV X U Y ℝ) (hA : Continuous s.A)
    {L : ℝ} (hA_bdd : ∀ t, ‖s.A t‖ ≤ L) {Q : ℝ → Matrix X X ℝ} (hQ : Continuous Q)
    {q : ℝ} (hQ_bdd : ∀ t, ‖Q t‖ ≤ q) (hQ_symm : ∀ t, (Q t)ᵀ = Q t) {q₁ : ℝ} (hq₁ : 0 < q₁)
    (hQ_pos : ∀ t (x : X → ℝ), q₁ * ‖x‖ ^ 2 ≤ x ⬝ᵥ (Q t *ᵥ x))
    (h_exp : s.toContinuousSystem.zeroInput.LocallyExponentiallyStable (0 : X → ℝ)) :
    ∃ P : ℝ → Matrix X X ℝ, DifferentialLyapunovEquation s.A P Q ∧ (∀ t, (P t)ᵀ = P t) ∧
      (∃ p, ∀ t, 0 ≤ t → ‖P t‖ ≤ p) ∧
      s.toContinuousSystem.zeroInput.IsExponentialLyapunovFunction
        (fun t x => x ⬝ᵥ (P t *ᵥ x)) 0 univ 2 := by
  set Φ : ℝ → ℝ → Matrix X X ℝ := stateTransitionMatrix s.A with hΦ_def
  have hL : 0 ≤ L := (norm_nonneg _).trans (hA_bdd 0)
  have hq : 0 ≤ q := (norm_nonneg _).trans (hQ_bdd 0)
  have hΦ_mul : ∀ t r τ, Φ t r * Φ r τ = Φ t τ := stateTransitionMatrix_mul hA hA_bdd
  have hΦ_self : ∀ t, Φ t t = 1 := stateTransitionMatrix_self
  have hΦ_cont : ∀ τ, Continuous fun σ => Φ σ τ := fun τ => continuous_iff_continuousAt.mpr
    fun σ => (hasDerivAt_stateTransitionMatrix_of_bound hA hA_bdd τ σ).continuousAt
  -- Transposition, as a continuous linear map.
  let T : Matrix X X ℝ →L[ℝ] Matrix X X ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv X X ℝ ℝ).toLinearMap
  -- Step 1. Exponential decay of `Φ` from `t₀ ≥ 0`, and a growth bound on `[t, t + 1]`.
  obtain ⟨k, hk, γ, hγ, h_decay⟩ :=
    (locallyExponentiallyStable_iff_decayingStateTransition s hA).mp h_exp
  have h_decay_norm : ∀ t₀, 0 ≤ t₀ → ∀ t ≥ t₀, ‖Φ t t₀‖ ≤ k * Real.exp (-γ * (t - t₀)) :=
    fun t₀ ht₀ t ht => MatrixAlgebra.norm_le_of_mulVec_le (by positivity) (h_decay t₀ ht₀ t ht)
  set C := (‖(1 : Matrix X X ℝ)‖ + 1) * Real.exp L with hC_def
  have hC : 0 < C := by positivity
  have h_grow : ∀ t τ, τ ∈ Icc t (t + 1) → ∀ x, ‖x‖ ≤ C * ‖Φ τ t *ᵥ x‖ := by
    intro t τ hτ x
    have h_dist : |t - τ| ≤ 1 := by rw [abs_sub_comm, abs_of_nonneg] <;> linarith [hτ.1, hτ.2]
    calc ‖x‖
        = ‖Φ t τ *ᵥ (Φ τ t *ᵥ x)‖ := by rw [mulVec_mulVec, hΦ_mul, hΦ_self, one_mulVec]
      _ ≤ ‖Φ t τ‖ * ‖Φ τ t *ᵥ x‖ := linfty_opNorm_mulVec _ _
      _ ≤ C * ‖Φ τ t *ᵥ x‖ := by
          gcongr
          calc ‖Φ t τ‖
              ≤ ‖(1 : Matrix X X ℝ)‖ * Real.exp (L * |t - τ|) :=
                norm_stateTransitionMatrix_le fun r _ => hA_bdd r
            _ ≤ C := by
                rw [hC_def]
                gcongr
                · linarith
                · exact mul_le_of_le_one_right hL h_dist
  -- Step 2. `Φ(σ, t)ᵀ Q(σ) Φ(σ, t)` decays like `e^{-2γ(σ - t)}`, whose integral over
  -- `(t, ∞)` is `1 / (2γ)`.
  set K := ‖T‖ * q * k ^ 2
  have hK : 0 ≤ K := by positivity
  have h_conj_bound : ∀ t, 0 ≤ t → ∀ σ, t ≤ σ →
      ‖(Φ σ t)ᵀ * Q σ * Φ σ t‖ ≤ K * Real.exp (-(2 * γ) * (σ - t)) := by
    intro t ht σ hσ
    have hΦσ := h_decay_norm t ht σ hσ
    calc ‖(Φ σ t)ᵀ * Q σ * Φ σ t‖
        ≤ ‖(Φ σ t)ᵀ‖ * ‖Q σ‖ * ‖Φ σ t‖ := (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
      _ ≤ (‖T‖ * ‖Φ σ t‖) * q * ‖Φ σ t‖ := by
          gcongr
          · exact T.le_opNorm (Φ σ t)
          · exact hQ_bdd σ
      _ ≤ (‖T‖ * (k * Real.exp (-γ * (σ - t)))) * q * (k * Real.exp (-γ * (σ - t))) := by gcongr
      _ = K * Real.exp (-(2 * γ) * (σ - t)) := by
          rw [show -(2 * γ) * (σ - t) = -γ * (σ - t) + -γ * (σ - t) by ring, Real.exp_add]
          ring
  have h_exp_int : ∀ t, IntegrableOn (fun σ => K * Real.exp (-(2 * γ) * (σ - t))) (Ioi t) ∧
      ∫ σ in Ioi t, K * Real.exp (-(2 * γ) * (σ - t)) = K / (2 * γ) := by
    intro t
    have h_split : (fun σ => K * Real.exp (-(2 * γ) * (σ - t))) =
        fun σ => K * Real.exp (2 * γ * t) * Real.exp (-(2 * γ) * σ) := funext fun σ => by
      rw [show -(2 * γ) * (σ - t) = 2 * γ * t + -(2 * γ) * σ by ring, Real.exp_add]
      ring
    have h_one : Real.exp (2 * γ * t) * Real.exp (-(2 * γ) * t) = 1 := by
      rw [← Real.exp_add, show 2 * γ * t + -(2 * γ) * t = 0 by ring, Real.exp_zero]
    rw [h_split]
    refine ⟨(integrableOn_exp_mul_Ioi (by linarith) t).const_mul _, ?_⟩
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith), mul_assoc, ← mul_div_assoc,
      mul_neg, h_one, neg_div_neg_eq, mul_one_div]
  -- `G(τ) = Φ(τ, 0)ᵀ Q(τ) Φ(τ, 0)` is integrable, so `R(t) = ∫_t^∞ G` converges; and
  -- `P(t) = Φ(0, t)ᵀ R(t) Φ(0, t)`.
  set G : ℝ → Matrix X X ℝ := fun τ => (Φ τ 0)ᵀ * Q τ * Φ τ 0
  have hG_cont : Continuous G := ((T.continuous.comp (hΦ_cont 0)).mul hQ).mul (hΦ_cont 0)
  have hG_int : IntegrableOn G (Ioi 0) :=
    Integrable.mono' (by simpa using (h_exp_int 0).1) hG_cont.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => by
        simpa using h_conj_bound 0 le_rfl τ (le_of_lt hτ))
  set R₀ := ∫ τ in Ioi 0, G τ
  set R : ℝ → Matrix X X ℝ := fun t => R₀ - ∫ τ in (0 : ℝ)..t, G τ
  have hR_Ioi : ∀ t, 0 ≤ t → R t = ∫ τ in Ioi t, G τ := fun t ht => by
    simp only [R, R₀, ← intervalIntegral.integral_Ioi_sub_Ioi hG_int ht, sub_sub_cancel]
  have hR_deriv : ∀ t, HasDerivAt R (-G t) t := fun t =>
    ((hG_cont.integral_hasStrictDerivAt 0 t).hasDerivAt).const_sub R₀
  set P : ℝ → Matrix X X ℝ := fun t => (Φ 0 t)ᵀ * R t * Φ 0 t
  -- `P(t) = ∫_t^∞ Φ(σ, t)ᵀ Q(σ) Φ(σ, t) dσ` (Khalil's formula), so `‖P(t)‖ ≤ K / (2γ)`.
  have hP_Ioi : ∀ t, 0 ≤ t → P t = ∫ σ in Ioi t, (Φ σ t)ᵀ * Q σ * Φ σ t := by
    intro t ht
    let conj := ContinuousLinearMap.mulLeftRight ℝ (Matrix X X ℝ) (Φ 0 t)ᵀ (Φ 0 t)
    calc P t
        = conj (∫ σ in Ioi t, G σ) := by rw [← hR_Ioi t ht]; rfl
      _ = ∫ σ in Ioi t, conj (G σ) :=
          (conj.integral_comp_comm (hG_int.mono_set (Ioi_subset_Ioi ht))).symm
      _ = ∫ σ in Ioi t, (Φ σ t)ᵀ * Q σ * Φ σ t := by
          congr 1
          funext σ
          simp only [conj, ContinuousLinearMap.mulLeftRight_apply, G, ← hΦ_mul σ 0 t,
            transpose_mul, Matrix.mul_assoc]
  set p := K / (2 * γ)
  have hp : 0 ≤ p := by positivity
  have hP_bdd : ∀ t, 0 ≤ t → ‖P t‖ ≤ p := by
    intro t ht
    rw [hP_Ioi t ht, ← (h_exp_int t).2]
    exact norm_integral_le_of_norm_le (h_exp_int t).1
      (ae_restrict_of_forall_mem measurableSet_Ioi fun σ hσ => h_conj_bound t ht σ (le_of_lt hσ))
  -- Step 3. The differential Lyapunov equation, by the product rule.
  have hP_deriv : ∀ t, HasDerivAt P (-(P t * s.A t + (s.A t)ᵀ * P t + Q t)) t := by
    intro t
    have hΦ₀ := hasDerivAt_stateTransitionMatrix_snd_of_bound hA hA_bdd 0 t
    have hΦ₀T : HasDerivAt (fun σ => (Φ 0 σ)ᵀ) (-(Φ 0 t * s.A t))ᵀ t :=
      T.hasFDerivAt.comp_hasDerivAt t hΦ₀
    have h_cancel : Φ t 0 * Φ 0 t = 1 := by rw [hΦ_mul, hΦ_self]
    have h_cancelT : (Φ 0 t)ᵀ * (Φ t 0)ᵀ = 1 := by
      rw [← transpose_mul, h_cancel, transpose_one]
    have h_Q : (Φ 0 t)ᵀ * G t * Φ 0 t = Q t :=
      calc (Φ 0 t)ᵀ * G t * Φ 0 t
          = ((Φ 0 t)ᵀ * (Φ t 0)ᵀ) * Q t * (Φ t 0 * Φ 0 t) := by
            simp only [G, Matrix.mul_assoc]
        _ = Q t := by rw [h_cancelT, h_cancel, Matrix.one_mul, Matrix.mul_one]
    convert (hΦ₀T.mul (hR_deriv t)).mul hΦ₀ using 1
    rw [← h_Q]
    simp only [P, Pi.mul_apply, transpose_neg, transpose_mul, ← hΦ_def]
    noncomm_ring
  -- Step 4. Along the solution from `(t, x)`, `xᵀ P(t) x = ∫_t^∞ ψ` with
  -- `ψ(σ) = (Φ(σ, t) x)ᵀ Q(σ) Φ(σ, t) x`.
  set ψ : ℝ → (X → ℝ) → ℝ → ℝ := fun t x σ => (Φ σ t *ᵥ x) ⬝ᵥ (Q σ *ᵥ (Φ σ t *ᵥ x))
  have hψ_lin : ∀ t (x : X → ℝ), ∃ ℓ : Matrix X X ℝ →L[ℝ] ℝ,
      (∀ M, ℓ M = (Φ 0 t *ᵥ x) ⬝ᵥ (M *ᵥ (Φ 0 t *ᵥ x))) ∧ ∀ σ, ψ t x σ = ℓ (G σ) := by
    intro t x
    set y := Φ 0 t *ᵥ x
    refine ⟨LinearMap.toContinuousLinearMap
      { toFun := fun M => y ⬝ᵥ (M *ᵥ y)
        map_add' := fun M N => by simp [add_mulVec, dotProduct_add]
        map_smul' := fun c M => by simp [smul_mulVec, dotProduct_smul] },
      fun M => rfl, fun σ => ?_⟩
    change _ = y ⬝ᵥ (G σ *ᵥ y)
    rw [MatrixAlgebra.dotProduct_transpose_mul_mulVec, mulVec_mulVec, hΦ_mul]
  have hψ_cont : ∀ t x, Continuous (ψ t x) := fun t x => by
    obtain ⟨ℓ, -, hℓ⟩ := hψ_lin t x
    rw [funext hℓ]
    exact ℓ.continuous.comp hG_cont
  have hψ_nonneg : ∀ t x σ, q₁ * ‖Φ σ t *ᵥ x‖ ^ 2 ≤ ψ t x σ := fun t x σ => hQ_pos σ _
  have hψ_int : ∀ t, 0 ≤ t → ∀ x,
      IntegrableOn (ψ t x) (Ioi t) ∧ x ⬝ᵥ (P t *ᵥ x) = ∫ σ in Ioi t, ψ t x σ := by
    intro t ht x
    obtain ⟨ℓ, hℓ_apply, hℓ⟩ := hψ_lin t x
    have hG_int_t : IntegrableOn G (Ioi t) := hG_int.mono_set (Ioi_subset_Ioi ht)
    rw [funext hℓ]
    refine ⟨ℓ.integrable_comp hG_int_t, ?_⟩
    calc x ⬝ᵥ (P t *ᵥ x)
        = ℓ (R t) := by rw [hℓ_apply, ← MatrixAlgebra.dotProduct_transpose_mul_mulVec]
      _ = ℓ (∫ σ in Ioi t, G σ) := by rw [hR_Ioi t ht]
      _ = ∫ σ in Ioi t, ℓ (G σ) := (ℓ.integral_comp_comm hG_int_t).symm
  -- Step 5. The quadratic bounds.
  set c₁ := q₁ / C ^ 2
  set c₂ := (Fintype.card X + 1) * (p + 1)
  have h_lower : ∀ t, 0 ≤ t → ∀ x, c₁ * ‖x‖ ^ 2 ≤ x ⬝ᵥ (P t *ᵥ x) := by
    intro t ht x
    obtain ⟨hψ_i, hψ_eq⟩ := hψ_int t ht x
    have h_split := intervalIntegral.integral_Ioi_sub_Ioi hψ_i (by linarith : t ≤ t + 1)
    have h_tail : 0 ≤ ∫ σ in Ioi (t + 1), ψ t x σ := setIntegral_nonneg measurableSet_Ioi
      fun σ _ => (mul_nonneg hq₁.le (sq_nonneg _)).trans (hψ_nonneg t x σ)
    calc c₁ * ‖x‖ ^ 2
        = ∫ _σ in t..t + 1, c₁ * ‖x‖ ^ 2 := by simp
      _ ≤ ∫ σ in t..t + 1, ψ t x σ := by
          refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
            ((hψ_cont t x).intervalIntegrable _ _) fun σ hσ => ?_
          have h := h_grow t σ hσ x
          calc c₁ * ‖x‖ ^ 2
              = q₁ * (‖x‖ / C) ^ 2 := by simp only [c₁]; field_simp
            _ ≤ q₁ * ‖Φ σ t *ᵥ x‖ ^ 2 := by
                gcongr
                rwa [div_le_iff₀ hC, mul_comm]
            _ ≤ ψ t x σ := hψ_nonneg t x σ
      _ ≤ x ⬝ᵥ (P t *ᵥ x) := by linarith
  have h_upper : ∀ t, 0 ≤ t → ∀ x, x ⬝ᵥ (P t *ᵥ x) ≤ c₂ * ‖x‖ ^ 2 := fun t ht x =>
    calc x ⬝ᵥ (P t *ᵥ x)
        ≤ Fintype.card X * ‖P t‖ * ‖x‖ ^ 2 := MatrixAlgebra.dotProduct_mulVec_le _ _
      _ ≤ c₂ * ‖x‖ ^ 2 := by
          gcongr
          exact mul_le_mul (by linarith) (by linarith [hP_bdd t ht]) (norm_nonneg _)
            (by positivity)
  -- Step 6. `V(t, x) = xᵀ P(t) x` is an exponential Lyapunov function.
  set V : ℝ → (X → ℝ) → ℝ := fun t x => x ⬝ᵥ (P t *ᵥ x)
  have hV_diff : ∀ t (x : X → ℝ), DifferentiableAt ℝ (Function.uncurry V) (t, x) :=
    fun t x => differentiableAt_dotProduct_mulVec (hP_deriv t).differentiableAt x
  refine ⟨P, fun t _ => hP_deriv t, fun t => ?_, ⟨p, hP_bdd⟩, ⟨Filter.univ_mem,
    fun t _ x _ => hV_diff t x, two_pos, c₁, by positivity, c₂, mul_pos (by positivity)
    (by linarith), q₁, hq₁, fun t ht x _ => ?_⟩⟩
  · -- `P` is symmetric because `Q` is.
    have hR_symm : (R t)ᵀ = R t := by
      have hG_symm : ∀ τ, (G τ)ᵀ = G τ := fun τ => by
        simp only [G, transpose_mul, transpose_transpose, hQ_symm, Matrix.mul_assoc]
      have h_int_T : ∀ (f : ℝ → Matrix X X ℝ) (μ : Measure ℝ), Integrable f μ →
          (∫ τ, f τ ∂μ)ᵀ = ∫ τ, (f τ)ᵀ ∂μ := fun f μ hf => (T.integral_comp_comm hf).symm
      simp only [R, R₀, transpose_sub, intervalIntegral, h_int_T _ _ hG_int,
        h_int_T _ _ hG_cont.integrableOn_Ioc, hG_symm]
    simp only [P, transpose_mul, transpose_transpose, hR_symm, Matrix.mul_assoc]
  -- The bounds, and the decrease computed along the solution from `(t, x)`.
  simp only [sub_zero, Real.rpow_two]
  refine ⟨h_lower t ht x, h_upper t ht x, ?_⟩
  set φ := homogeneousResponse s.A t x
  have hφ := ContinuousLTV.isTrajectoryOn_homogeneousResponse s hA t x
  have hφ_t : homogeneousResponse s.A t x t = x := by simp
  -- By uniqueness, `V(τ, φ(τ)) = ∫_τ^∞ ψ = ∫_t^∞ ψ - ∫_t^τ ψ`.
  have h_along : ∀ τ ∈ Ici t, V τ (φ τ) =
      (∫ σ in Ioi t, ψ t x σ) - ∫ σ in t..τ, ψ t x σ := by
    intro τ hτ
    have hτ' : t ≤ τ := hτ
    have h_shift : ψ τ (φ τ) = ψ t x := funext fun σ => by
      simp only [ψ, φ, homogeneousResponse, mulVec_mulVec, ← hΦ_def, Matrix.mul_assoc, hΦ_mul]
    rw [show V τ (φ τ) = φ τ ⬝ᵥ (P τ *ᵥ φ τ) from rfl, (hψ_int τ (ht.trans hτ') (φ τ)).2,
      h_shift, ← intervalIntegral.integral_Ioi_sub_Ioi (hψ_int t ht x).1 hτ', sub_sub_cancel]
  have h_eq := hφ.lieDerivative_eq_of_eq_add_integral (hV_diff t (φ t))
    (ψ := fun σ => -ψ t x σ) (by fun_prop) fun τ hτ => by
      rw [h_along τ hτ, intervalIntegral.integral_neg, sub_eq_add_neg]
  rw [hφ_t] at h_eq
  calc s.toContinuousSystem.zeroInput.lieDerivative V t x ()
      = -ψ t x t := h_eq
    _ ≤ -(q₁ * ‖x‖ ^ 2) := by
        simpa [ψ, hΦ_self] using neg_le_neg (hQ_pos t x)

end LinearSystems

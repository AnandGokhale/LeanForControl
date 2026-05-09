theorem linear_system_stability (A : Matrix (Fin n) (Fin n) ℝ) :
    IsStable (linearSystem A) 0 ↔
    (∀ λ ∈ A.eigenvalues ℂ, λ.re ≤ 0) ∧
    (∀ λ ∈ A.eigenvalues ℂ, λ.re = 0 →
      A.algebraicMultiplicity λ ≥ 2 →
      (A - λ • 1).rank = n - A.algebraicMultiplicity λ) := by
  -- Use exp(At) = P exp(Jt) P⁻¹ decomposition
  -- Stable ↔ ‖exp(At)‖ bounded ↔ eigenvalue condition
  sorry

theorem linear_system_asymp_stable (A : Matrix (Fin n) (Fin n) ℝ) :
    IsGloballyAsymptoticallyStable (linearSystem A) 0 ↔
    ∀ λ ∈ A.eigenvalues ℂ, λ.re < 0 := by
  sorry


-- PA + AᵀP = -Q
def LyapunovEquation (A P Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P * A + Aᵀ * P = -Q

theorem lyapunov_equation_hurwitz
    (A : Matrix (Fin n) (Fin n) ℝ) :
    IsHurwitz A ↔
    ∀ Q : Matrix (Fin n) (Fin n) ℝ, Q.PosDef →
    ∃! P : Matrix (Fin n) (Fin n) ℝ,
      P.PosDef ∧ LyapunovEquation A P Q := by
  constructor
  · -- Necessity: construct P = ∫₀^∞ exp(Aᵀt) Q exp(At) dt
    intro hA Q hQ
    use Matrix.integral_lyapunov A Q  -- needs definition
    constructor
    · -- Show P is positive definite
      -- xᵀPx = 0 → exp(At)x ≡ 0 → x = 0
      sorry
    · constructor
      · -- Show P satisfies the equation by differentiating
        sorry
      · -- Uniqueness: (P-P̃)A + Aᵀ(P-P̃) = 0 → P = P̃
        sorry
  · -- Sufficiency from Theorem 4.1
    sorry


theorem lyapunov_indirect_method
    (f : E → E) (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A = fderiv ℝ f 0) :
    -- Part 1
    (∀ λ ∈ A.eigenvalues ℂ, λ.re < 0) →
    IsAsymptoticallyStable (⟨f, sorry⟩) 0) ∧
    -- Part 2
    (∃ λ ∈ A.eigenvalues ℂ, λ.re > 0) →
    ¬ IsStable (⟨f, sorry⟩) 0) := by
  -- Proof uses: f = Ax + g(x), ‖g(x)‖/‖x‖ → 0
  -- For Part 1: use Lyapunov equation P from Thm 4.6
  --   V(x) = xᵀPx, show V̇ negative definite near 0
  -- For Part 2: use Chetaev-style argument
  sorry



-- State transition matrix Φ(t,t₀)
-- This requires substantial ODE theory infrastructure

theorem uniform_asymp_stable_iff_transition_matrix
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hΦ : IsStateTransitionMatrix A Φ) :
    IsGloballyUniformlyAsymptoticallyStable (⟨fun t x => A t *ᵥ x, sorry⟩) 0 ↔
    ∃ k λ : ℝ, 0 < k ∧ 0 < λ ∧
      ∀ t t₀, t ≥ t₀ → ‖Φ t t₀‖ ≤ k * Real.exp (-λ * (t - t₀)) := sorry



theorem lyapunov_function_exists_for_exp_stable_ltv ... := sorry

theorem lyapunov_indirect_nonautonomous
    (f : ℝ → E → E)
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ t, A t = fderiv ℝ (f t) 0) :
    IsExponentiallyStable (⟨fun t x => A t *ᵥ x, sorry⟩) 0 →
    IsExponentiallyStable (⟨f, sorry⟩) 0 := sorry

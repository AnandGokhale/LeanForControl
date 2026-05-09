theorem uniform_ultimate_boundedness
    (V : ℝ → E → ℝ) (α₁ α₂ : ℝ≥0 → ℝ≥0) (W₃ : E → ℝ) (μ r : ℝ)
    (h1 : ∀ t x, α₁ ‖x‖ ≤ V t x ∧ V t x ≤ α₂ ‖x‖)
    (h2 : ∀ t x, ‖x‖ ≥ μ → Vdot t x ≤ -W₃ x)
    (hμr : μ < α₂⁻¹ (α₁ r)) :
    ∃ β : ℝ≥0 → ℝ≥0 → ℝ≥0, IsClassKL β ∧
    ∀ (φ : ℝ → E), ...
      IsUniformlyUltimatelyBounded φ (α₁⁻¹ (α₂ μ)) := sorry

def IsInputToStateStable (sys : NonautonomousSystem n m) : Prop :=
  ∃ (β : ℝ≥0 → ℝ≥0 → ℝ≥0) (γ : ℝ≥0 → ℝ≥0),
    IsClassKL β ∧ IsClassK γ ∧
    ∀ x₀ u t, t ≥ 0 →
      ‖φ(t; x₀, u)‖ ≤ β ‖x₀‖ t +
        γ (⨆ τ ∈ Set.Icc 0 t, ‖u τ‖)

theorem iss_of_iss_lyapunov_function
    (V : ℝ → E → ℝ) (α₁ α₂ : ℝ≥0 → ℝ≥0) (ρ : ℝ≥0 → ℝ≥0) (W₃ : E → ℝ)
    (h1 : ∀ t x, α₁ ‖x‖ ≤ V t x ∧ V t x ≤ α₂ ‖x‖)
    (h2 : ∀ t x u, ‖x‖ ≥ ρ ‖u‖ → Vdot t x u ≤ -W₃ x)
    (hα : IsClassKInf α₁) (hα₂ : IsClassKInf α₂) (hρ : IsClassK ρ) :
    IsInputToStateStable sys := sorry

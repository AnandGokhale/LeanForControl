-- Lemma 4.2: closure properties
lemma classK_inverse_classK (hα : IsClassK α) :
    IsClassK (Function.invFun α) := sorry

lemma classK_comp_classK (hα : IsClassK α) (hβ : IsClassK β) :
    IsClassK (α ∘ β) := sorry

-- Lemma 4.3: bounding positive definite functions
lemma classK_bounds_of_pos_def
    (V : E → ℝ) (hV : IsPositiveDefiniteOn V D 0)
    (hD : IsOpen D) (r : ℝ) (hr : Metric.ball 0 r ⊆ D) :
    ∃ α₁ α₂ : ℝ≥0 → ℝ≥0,
      IsClassK α₁ ∧ IsClassK α₂ ∧
      ∀ x ∈ Metric.ball 0 r,
        α₁ ‖x‖ ≤ V x ∧ V x ≤ α₂ ‖x‖ := sorry

-- Lemma 4.4: scalar comparison ODE
lemma classKL_solution_of_classK_ode
    (α : ℝ≥0 → ℝ≥0) (hα : IsClassK α) (hα_lip : LocallyLipschitz α) :
    ∃ σ : ℝ≥0 → ℝ≥0 → ℝ≥0, IsClassKL σ ∧
    ∀ y₀ ≥ 0, IsSolutionOf (fun y => -α y) (fun t => σ y₀ t) := sorry




-- Nonautonomous system
structure NonautonomousSystem (n : ℕ) where
  f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  hf_pw_cts : -- piecewise continuous in t
  hf_lip : ∀ t, LocallyLipschitz (f t)



-- Theorem 4.8: Uniform stability
theorem uniform_stability_of_lyapunov
    (V : ℝ → E → ℝ) -- time-dependent Lyapunov function
    (W₁ W₂ : E → ℝ) (hW₁ : IsPositiveDefinite W₁) (hW₂ : IsPositiveDefinite W₂)
    (h_sandwich : ∀ t x, W₁ x ≤ V t x ∧ V t x ≤ W₂ x)
    (hVdot : ∀ t x, ∂V/∂t + ∇V · f t x ≤ 0) :
    IsUniformlyStable sys 0 := sorry

-- Theorem 4.9: Uniform asymptotic stability
theorem uniform_asymp_stability_of_lyapunov
    -- same hypotheses + W₃ positive definite with V̇ ≤ -W₃(x)
    := sorry

-- Theorem 4.10: Exponential stability
theorem exponential_stability_of_lyapunov
    (k₁ k₂ k₃ a : ℝ) (hk : 0 < k₁) ...
    (h1 : ∀ t x, k₁ * ‖x‖^a ≤ V t x ∧ V t x ≤ k₂ * ‖x‖^a)
    (h2 : ∀ t x, Vdot t x ≤ -k₃ * ‖x‖^a) :
    IsExponentiallyStable sys 0 := sorry

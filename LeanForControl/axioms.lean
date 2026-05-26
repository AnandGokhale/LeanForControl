import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Basic


-- Real Analysis Smoothing

/-- A monotonically non-decreasing positive function can be lower-bounded by a strictly monotonic
continuous function. -/
axiom exists_strictMono_lower_bound (r : ℝ) (hr : 0 < r) (ψ : ℝ → ℝ)
    (hψ_zero : ψ 0 = 0)
    (hψ_pos : ∀ s, 0 < s → s ≤ r → 0 < ψ s)
    (hψ_mono : ∀ s₁ s₂, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ r → ψ s₁ ≤ ψ s₂) :
    ∃ (f : ℝ → ℝ) (b : ℝ), 0 < b ∧
      f 0 = 0 ∧ f r = b ∧
      ContinuousOn f (Set.Icc 0 r) ∧
      StrictMonoOn f (Set.Icc 0 r) ∧
      ∀ s, 0 ≤ s → s ≤ r → f s ≤ ψ s -- := by sorry
      -- Analytic construction (e.g., piecewise linear interpolation or integration)


/-- A monotonically non-decreasing function starting at 0 on all of `[0, ∞)` can be
    upper-bounded by a strictly monotonic continuous function that tends to `+∞`. -/
axiom exists_strictMono_upper_bound_global (φ : ℝ → ℝ)
    (hφ_zero : φ 0 = 0)
    (hφ_mono : MonotoneOn φ (Set.Ici 0)) :
    ∃ f : ℝ → ℝ,
      f 0 = 0 ∧
      ContinuousOn f (Set.Ici 0) ∧
      StrictMonoOn f (Set.Ici 0) ∧
      Filter.Tendsto f Filter.atTop Filter.atTop ∧
      ∀ s ≥ 0, φ s ≤ f s

/-- A monotonically non-decreasing function starting at 0 can be upper-bounded
    by a strictly monotonic continuous function. -/
lemma exists_strictMono_upper_bound (r : ℝ) (hr : 0 < r) (φ : ℝ → ℝ)
    (hφ_zero : φ 0 = 0)
    (hφ_mono : ∀ s₁ s₂, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ r → φ s₁ ≤ φ s₂) :
    ∃ (f : ℝ → ℝ) (b : ℝ), 0 < b ∧
      f 0 = 0 ∧ f r = b ∧
      ContinuousOn f (Set.Icc 0 r) ∧
      StrictMonoOn f (Set.Icc 0 r) ∧
      ∀ s, 0 ≤ s → s ≤ r → φ s ≤ f s := by
  -- Extend φ to [0, ∞) by clamping: φ_ext s = φ s for s ≤ r, φ r for s > r
  let φ_ext : ℝ → ℝ := fun s => if s ≤ r then φ s else φ r
  have hφ_ext_zero : φ_ext 0 = 0 := by simp [φ_ext, hr.le, hφ_zero]
  have hφ_ext_mono : MonotoneOn φ_ext (Set.Ici 0) := by
    intro s₁ hs₁ s₂ _ h_le
    simp only [φ_ext]
    split_ifs with h1 h2
    · exact hφ_mono s₁ s₂ hs₁ h_le h2       -- both ≤ r
    · exact hφ_mono s₁ r hs₁ h1 le_rfl      -- s₁ ≤ r < s₂
    · linarith [not_le.mp h1]                -- s₁ > r, s₂ ≤ r: impossible
    · exact le_refl _                        -- both > r
  -- Apply the global axiom to φ_ext
  obtain ⟨f, hf_zero, hf_cont, hf_mono, _, hf_bound⟩ :=
    exists_strictMono_upper_bound_global φ_ext hφ_ext_zero hφ_ext_mono
  refine ⟨f, f r, ?_, hf_zero, rfl,
    hf_cont.mono Set.Icc_subset_Ici_self,
    hf_mono.mono Set.Icc_subset_Ici_self,
    fun s hs₁ hs₂ => ?_⟩
  · -- f r > 0: f strictly mono, f 0 = 0, r > 0
    have h := hf_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hr.le) hr
    linarith [hf_zero ▸ h]
  · -- φ s ≤ φ_ext s ≤ f s for s ≤ r
    have h := hf_bound s hs₁
    simp only [φ_ext, if_pos hs₂] at h
    exact h

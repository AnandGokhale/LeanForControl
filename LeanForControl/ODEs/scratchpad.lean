import LeanForControl.ODEs.ODE_properties

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Real Interval

namespace ODE_properties_scratch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {t₀ t₁ : ℝ} {f g : ℝ → E → E}
variable {y z : ℝ → E} {y₀ z₀ : E} {L μ : ℝ}

example (ht : t₀ ≤ t₁)
    (hL : 0 < L)
    (hμ : 0 < μ)
    (hy : IsIntegralSolution t₀ t₁ y y₀ f)
    (hz : IsIntegralSolution t₀ t₁ z z₀ (fun s x => f s x + g s x))
    (hy_cont : ContinuousOn y (Icc t₀ t₁))
    (hz_cont : ContinuousOn z (Icc t₀ t₁))
    (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hgz : IntervalIntegrable (fun s => g s (z s)) volume t₀ t₁)
    (hLip : ∀ t ∈ Icc t₀ t₁, LipschitzWith ⟨L, hL.le⟩ (f t))
    (hg : ∀ t ∈ Icc t₀ t₁, ∀ x : E, ‖g t x‖ ≤ μ) :
    ∀ t ∈ Icc t₀ t₁,
      ‖y t - z t‖ ≤ ‖y₀ - z₀‖ * rexp (L * (t - t₀)) + (μ / L) * (rexp (L * (t - t₀)) - 1) := by
  exact continuous_dependence_ODE ht hL hμ hy hz hy_cont hz_cont hf_cont hgz hLip hg

variable {α ε : ℝ}
variable {hα : 0 < α}
variable {hαε : α * (1 + 1 / L) * Real.exp (L * (t₁ - t₀)) ≤ ε}
variable {hg_cont : Continuous (fun p : ℝ × E => g p.1 p.2)}
variable {hz₀ : ‖z₀ - y₀‖ ≤ α}

example (ht : t₀ ≤ t₁)
    (hL : 0 < L)
    (hα : 0 < α)
    (hαε : α * (1 + 1 / L) * Real.exp (L * (t₁ - t₀)) ≤ ε)
    (hy : IsIntegralSolution t₀ t₁ y y₀ f)
    (hz : IsIntegralSolution t₀ t₁ z z₀ (fun s x => f s x + g s x))
    (hy_cont : ContinuousOn y (Icc t₀ t₁))
    (hz_cont : ContinuousOn z (Icc t₀ t₁))
    (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hg_cont : Continuous (fun p : ℝ × E => g p.1 p.2))
    (hLip : ∀ t ∈ Set.Icc t₀ t₁, LipschitzWith ⟨L, hL.le⟩ (f t))
    (hg : ∀ t ∈ Set.Icc t₀ t₁, ∀ x : E, ‖g t x‖ ≤ α)
    (hz₀ : ‖z₀ - y₀‖ ≤ α) :
    ∀ t ∈ Set.Icc t₀ t₁, ‖y t - z t‖ ≤ ε := by
  exact continuous_dependence_parameters ht hL hα hαε hy hz hy_cont hz_cont hf_cont hg_cont hLip hg hz₀

end ODE_properties_scratch

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.PicardLindelof
import LeanForControl.ODEs.ODE_properties
import LeanForControl.Stability.Autonomous
import LeanForControl.Stability.LyapunovIndirect.DefsForward

/-!
# Stability on finite forward solution segments

This file adapts the Lyapunov first-exit argument to finite solution segments and
records the local solution segment supplied by Picard--Lindelöf for a `C¹` vector
field.  These results avoid the vacuity of quantifying only over solutions defined
on all of `ℝ`.

Reference: Khalil, *Nonlinear Systems*.
-/

open Set Filter Topology

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Consequences and compatibility -/

/-- A finite forward solution segment of a continuous field is an integral solution
(`IsIntegralSolution`, the integral formulation used by the `ODEs/` and
`LinearSystems/Solutions/` tracks), anchored at `0` with initial value `φ 0`.

The continuity of `φ` that the integral formulation needs comes for free from the curve
hypothesis. See `isIntegralSolution_iff_isIntegralCurveOn_Icc` for the general statement. -/
theorem IsIntegralCurveOn.isIntegralSolution_of_continuous
    {φ : ℝ → ℝⁿ} {f : ℝⁿ → ℝⁿ} {T : ℝ} (hT : 0 ≤ T)
    (hφ : IsTrajectoryOn φ f 0 T) (hf : Continuous f) :
    IsIntegralSolution 0 T φ (φ 0) (fun _ y => f y) :=
  (isIntegralSolution_iff_isIntegralCurveOn_Icc hT
    (hf.comp_continuousOn (fun s hs => (hφ s hs).continuousWithinAt))).mpr hφ

/-- Local exponential stability on finite forward segments implies forward
Lyapunov stability.

Reference: Khalil, *Nonlinear Systems*.
-/
theorem ForwardLocallyExponentiallyStable.forwardLyapunovStable
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (h : ForwardLocallyExponentiallyStable f x_eq) :
    ForwardLyapunovStable f x_eq := by
  rcases h with ⟨r, C, a, hr, hC, ha, hdecay⟩
  intro ε hε
  refine ⟨min r (ε / C), ?_, ?_⟩
  · positivity
  intro t₀ t₁ φ hφ hφ0 t ht
  have ht0 : t₀ ≤ t := ht.1
  have hexp : Real.exp (-a * (t - t₀)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hinit : ‖φ t₀ - x_eq‖ < ε / C := lt_of_lt_of_le hφ0 (min_le_right _ _)
  calc
    ‖φ t - x_eq‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x_eq‖ :=
      hdecay t₀ t₁ φ hφ (lt_of_lt_of_le hφ0 (min_le_left _ _)) t ht
    _ ≤ C * 1 * ‖φ t₀ - x_eq‖ := by gcongr
    _ < ε := by
      rw [mul_one, ← lt_div_iff₀' hCpos]
      simpa [mul_comm] using hinit

/-- A fixed escape radius witnessed from arbitrarily small initial perturbations on
finite forward segments implies forward instability.

Reference: Khalil, *Nonlinear Systems*.
-/
theorem forwardUnstable_of_fixed_escape
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {ε : ℝ} (hε : 0 < ε)
    (hescape : ∀ δ > 0, ∃ (T : ℝ) (φ : ℝ → ℝⁿ) (t : ℝ),
      IsTrajectoryOn φ f 0 T ∧ ‖φ 0 - x_eq‖ < δ ∧
        t ∈ Icc (0 : ℝ) T ∧ ε ≤ ‖φ t - x_eq‖) :
    ForwardUnstable f x_eq := by
  intro hstable
  obtain ⟨δ, hδ, hstay⟩ := hstable ε hε
  obtain ⟨T, φ, t, hφ, hφ0, ht, hfar⟩ := hescape δ hδ
  exact (not_lt_of_ge hfar) (hstay 0 T φ hφ hφ0 t ht)

/-! ## Lyapunov first-exit infrastructure -/

/-- A `C¹` vector field admits a nontrivial finite forward solution segment from
every point at which it is `C¹`.

Reference: the Picard--Lindelöf local existence theorem.
-/
theorem ContDiffAt.exists_isIntegralCurveOn_Icc
    {f : ℝⁿ → ℝⁿ} {x₀ : ℝⁿ} (hf : ContDiffAt ℝ 1 f x₀) :
    ∃ (T : ℝ) (φ : ℝ → ℝⁿ), 0 < T ∧ φ 0 = x₀ ∧
      IsTrajectoryOn φ f 0 T := by
  obtain ⟨φ, hφ0, ε, hε, hφ⟩ :=
    hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  refine ⟨ε / 2, φ, by positivity, hφ0, ?_⟩
  intro t ht
  have htIoo : t ∈ Ioo (0 - ε) (0 + ε) := by
    constructor <;> norm_num at * <;> linarith
  exact (hφ t htIoo).hasDerivWithinAt

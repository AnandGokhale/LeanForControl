import LeanForControl.Stability.Continuous.LyapunovFunctions
import LeanForControl.ODEs.Sensitivity
import LeanForControl.Comparison.Massera
import LeanForControl.Comparison.ClassKL
import LeanForControl.Analysis.FrechetDerivative
import LeanForControl.Analysis.Norm
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Architect

/-!
# `Stability.Continuous.Converse` — converse Lyapunov theorems

Exponential stability has a quadratic Lyapunov function: from the exponential estimate of the
trajectories, `V(t, x) = ∫_t^{t+δ} ‖φ(τ; t, x) - x_eq‖² dτ` is sandwiched between multiples of
`‖x - x_eq‖²`, decreases along trajectories at a quadratic rate, and has gradient of size
`O(‖x - x_eq‖)`.  The gradient bound is what makes `V` robust: it is how a perturbation of the
vector field, such as an input, enters `V̇`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Section 4.7, Theorem 4.14.

## Main results

* `exists_quadraticLyapunov_of_exponentialEstimate` — Khalil's Theorem 4.14 on a ball: an
  exponential Lyapunov function with exponent `2` (`IsExponentialLyapunovFunction`) and a
  gradient bound.
* `exists_quadraticLyapunov_of_globallyExponentiallyStable` — its global case: an exponential
  Lyapunov function with exponent `2` (`IsExponentialLyapunovFunction`) and a gradient bound.
* `exists_lyapunov_of_KLBounded` — Khalil's Theorem 4.16: a class `KL` estimate gives a strict
  uniform Lyapunov function with a class `K` gradient bound,
  `V(t, x) = ∫_0^∞ G(‖φ(t + σ; t, x) - x_eq‖²) dσ` with `G` from Massera's lemma.

## Differences from Khalil

* The equilibrium is a general `x_eq`; Khalil places it at the origin.
* A `ContinuousSystem` is defined for all times, and the hypotheses (equilibrium, `C¹`,
  Lipschitz) are asked for every `t ∈ ℝ` rather than `t ≥ 0`: differentiability of `V` at
  `t = 0` involves solutions from slightly negative initial times.
* Khalil's bounded Jacobian is replaced by the Lipschitz bound it is used for; for `C¹` `f` the
  two are equivalent.
* The local theorem cuts the field off outside a ball (a smooth bump `χ`, `f̃ = χ f`) and runs
  the global construction for `f̃`; solutions from `D₀` never see the cut.
* The constants are cruder than Khalil's: `c₁ = δe^{-2Lδ}`, `c₂ = δk²`, `c₄ = 2kδe^{Lδ}`.
* The exponential estimate is assumed, as everywhere in this library, on trajectory segments
  starting in `D₀`.
* Khalil's rate `λ` is written `γ`, as in `LocallyExponentiallyStable`.
* Khalil's last clause, that `V` can be taken independent of `t` for a time-invariant system, is
  not stated yet.
-/

open Set Metric Filter
open scoped Interval NNReal

namespace ContinuousSystem

variable {Y : Type*} {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Ingredients -/

/-- **Appending time to the state.**  If `φ (t, x)` solves `ẋ = f(t, x)` from `x` at time `t`,
then `σ ↦ (t + σ, φ (t, x) (t + σ))` solves the autonomous system `ż = (1, f(z))` from `(t, x)`. -/
private lemma isIntegralCurveOn_timeAugmented {f : ℝ → ℝⁿ → ℝⁿ} {φ : ℝ × ℝⁿ → ℝ → ℝⁿ}
    (hφ : ∀ p, IsIntegralCurveOn (φ p) f (Ici p.1)) (z : ℝ × ℝⁿ) (δ : ℝ) :
    IsIntegralCurveOn (fun σ => (z.1 + σ, φ z (z.1 + σ)))
      (fun _ w => ((1 : ℝ), f w.1 w.2)) (Icc 0 δ) := fun σ hσ => by
  have hshift : HasDerivWithinAt (fun σ => z.1 + σ) 1 (Icc 0 δ) σ :=
    (hasDerivWithinAt_id σ _).const_add z.1
  have hφσ := (hφ z (z.1 + σ) (by simpa using hσ.1)).scomp σ hshift
    fun u hu => by simpa using hu.1
  exact hshift.prodMk (by simpa using hφσ)

/-- **Solutions are differentiable and locally Lipschitz in their initial time and state.**  On
`[0, δ]`, `z ↦ (z.1 + σ, φ z (z.1 + σ))` has derivative `Φ σ` at `z₀`, with `Φ` continuous in
`σ`: the variational solution of the time-augmented system (`hasFDerivAt_of_isIntegralCurveOn`).
Near `z₀` these maps are `e^{Kδ}`-Lipschitz (`IsIntegralCurveOn.exists_dist_le_of_contDiff`). -/
private lemma exists_hasFDerivAt_flow {f : ℝ → ℝⁿ → ℝⁿ}
    (hf : ContDiff ℝ 1 (fun p : ℝ × ℝⁿ => f p.1 p.2)) {φ : ℝ × ℝⁿ → ℝ → ℝⁿ}
    (hφ0 : ∀ p, φ p p.1 = p.2) (hφ : ∀ p, IsIntegralCurveOn (φ p) f (Ici p.1))
    {δ : ℝ} (hδ : 0 ≤ δ) (z₀ : ℝ × ℝⁿ) :
    (∃ Φ : ℝ → (ℝ × ℝⁿ) →L[ℝ] (ℝ × ℝⁿ), ContinuousOn Φ (Icc 0 δ) ∧ ∀ σ ∈ Icc 0 δ,
      HasFDerivAt (fun z : ℝ × ℝⁿ => (z.1 + σ, φ z (z.1 + σ))) (Φ σ) z₀) ∧
    ∃ K : ℝ≥0, ∃ ρ > 0, ∀ z ∈ ball z₀ ρ, ∀ z' ∈ ball z₀ ρ, ∀ σ ∈ Icc 0 δ,
      ‖(z.1 + σ, φ z (z.1 + σ)) - (z'.1 + σ, φ z' (z'.1 + σ))‖ ≤ dist z z' * Real.exp (K * δ) := by
  set g : ℝ × ℝⁿ → ℝ × ℝⁿ := fun z => (1, f z.1 z.2)
  have hg : ContDiff ℝ 1 g := contDiff_const.prodMk hf
  have hΨ0 : ∀ z : ℝ × ℝⁿ, (z.1 + 0, φ z (z.1 + 0)) = z := fun z => by simp [hφ0]
  have hΨ := fun z => isIntegralCurveOn_timeAugmented hφ z δ
  obtain ⟨Φ, hΦ0, hΦ⟩ := (hΨ z₀).exists_variational hg hδ
  refine ⟨⟨Φ, hΦ.continuousOn, fun σ hσ =>
    hasFDerivAt_of_isIntegralCurveOn hg hΨ hΨ0 hΦ0 hΦ hσ⟩, ?_⟩
  obtain ⟨K, ρ, hρ, h_sep⟩ := (hΨ z₀).exists_dist_le_of_contDiff hg
  refine ⟨K, ρ, hρ, fun z hz z' hz' σ hσ => ?_⟩
  have h := h_sep _ _ (hΨ z) (hΨ z') (by simpa [hφ0] using hz) (by simpa [hφ0] using hz') σ hσ
  beta_reduce at h
  rw [hΨ0, hΨ0, dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ.2 K.coe_nonneg)) dist_nonneg)

/-- **The integral of the squared distance along solutions is differentiable** in the initial time
and state.  With `φ (t, x)` the solution of `ẋ = f(t, x)` from `x` at time `t`, the map
`(t, x) ↦ ∫₀^δ ‖φ (t, x) (t + σ) - x_eq‖² dσ` is differentiable, provided `f` is `C¹`.

Appending time to the state turns the solutions into those of the autonomous `C¹` system
`ż = (1, f(z))`, differentiable in the initial state (`hasFDerivAt_of_isIntegralCurveOn`) and
locally Lipschitz in it (`IsIntegralCurveOn.exists_dist_le_of_contDiff`); differentiate under the
integral sign. -/
private lemma differentiableAt_integral_norm_sq {f : ℝ → ℝⁿ → ℝⁿ}
    (hf : ContDiff ℝ 1 (fun p : ℝ × ℝⁿ => f p.1 p.2)) {φ : ℝ × ℝⁿ → ℝ → ℝⁿ}
    (hφ0 : ∀ p, φ p p.1 = p.2) (hφ : ∀ p, IsIntegralCurveOn (φ p) f (Ici p.1))
    {δ : ℝ} (hδ : 0 < δ) (x_eq : ℝⁿ) (z₀ : ℝ × ℝⁿ) :
    DifferentiableAt ℝ (fun z : ℝ × ℝⁿ => ∫ σ in (0 : ℝ)..δ, ‖φ z (z.1 + σ) - x_eq‖ ^ 2) z₀ := by
  -- Step 1. With time appended to the state, `Ψ z σ = (z.1 + σ, φ z (z.1 + σ))` is
  -- differentiable at `z₀` with derivative `Φ σ`, and `e^{Kδ}`-Lipschitz near `z₀`.
  set Ψ : ℝ × ℝⁿ → ℝ → ℝ × ℝⁿ := fun z σ => (z.1 + σ, φ z (z.1 + σ))
  obtain ⟨⟨Φ, hΦ_cont, h_flow⟩, K, ρ, hρ, h_sep'⟩ := exists_hasFDerivAt_flow hf hφ0 hφ hδ.le z₀
  have hΨ_cont : ∀ z, ContinuousOn (Ψ z) (Icc 0 δ) := fun z =>
    (isIntegralCurveOn_timeAugmented hφ z δ).continuousOn
  -- Step 2. Each integrand is differentiable at `z₀`, through the flow derivative `Φ`.
  set F : ℝ × ℝⁿ → ℝ → ℝ := fun z σ => ‖(Ψ z σ).2 - x_eq‖ ^ 2
  set F' : ℝ → (ℝ × ℝⁿ) →L[ℝ] ℝ := fun σ =>
    2 • (innerSL ℝ ((Ψ z₀ σ).2 - x_eq)).comp ((ContinuousLinearMap.snd ℝ ℝ ℝⁿ).comp (Φ σ))
  have hF' : ∀ σ ∈ Icc 0 δ, HasFDerivAt (fun z => F z σ) (F' σ) z₀ := fun σ hσ => by
    have h_snd : HasFDerivAt (fun z => (Ψ z σ).2 - x_eq)
        ((ContinuousLinearMap.snd ℝ ℝ ℝⁿ).comp (Φ σ)) z₀ :=
      (hasFDerivAt_snd.comp z₀ (h_flow σ hσ)).sub_const x_eq
    exact h_snd.norm_sq
  -- Step 3. A uniform Lipschitz bound in `z` near `z₀`: the integrand is bounded by `R` there.
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuous_snd.comp_continuousOn (hΨ_cont z₀)).sub continuousOn_const)
  set R := B + ρ * Real.exp (K * δ)
  set C := 2 * R * Real.exp (K * δ)
  have h_R : ∀ z ∈ ball z₀ ρ, ∀ σ ∈ Icc 0 δ, ‖(Ψ z σ).2 - x_eq‖ ≤ R := fun z hz σ hσ =>
    calc ‖(Ψ z σ).2 - x_eq‖
        ≤ ‖(Ψ z σ).2 - (Ψ z₀ σ).2‖ + ‖(Ψ z₀ σ).2 - x_eq‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖Ψ z σ - Ψ z₀ σ‖ + B := add_le_add (norm_snd_le (Ψ z σ - Ψ z₀ σ)) (hB σ hσ)
      _ ≤ dist z z₀ * Real.exp (K * δ) + B :=
          add_le_add (h_sep' z hz z₀ (mem_ball_self hρ) σ hσ) le_rfl
      _ ≤ ρ * Real.exp (K * δ) + B :=
          add_le_add (mul_le_mul_of_nonneg_right (mem_ball.mp hz).le (Real.exp_pos _).le) le_rfl
      _ = R := add_comm _ _
  have h_lip : ∀ σ ∈ Icc 0 δ,
      LipschitzOnWith (Real.nnabs C) (fun z => F z σ) (ball z₀ ρ) := fun σ hσ =>
    LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => by
      set a := (Ψ z σ).2 - x_eq
      set b := (Ψ z' σ).2 - x_eq
      have hab : ‖a - b‖ ≤ dist z z' * Real.exp (K * δ) :=
        calc ‖a - b‖ = ‖(Ψ z σ - Ψ z' σ).2‖ := by simp [a, b]
          _ ≤ ‖Ψ z σ - Ψ z' σ‖ := norm_snd_le _
          _ ≤ dist z z' * Real.exp (K * δ) := h_sep' z hz z' hz' σ hσ
      have hR0 : 0 ≤ R := (norm_nonneg a).trans (h_R z hz σ hσ)
      calc dist (F z σ) (F z' σ)
          = |‖a‖ ^ 2 - ‖b‖ ^ 2| := Real.dist_eq _ _
        _ ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := abs_norm_sq_sub_norm_sq_le a b
        _ ≤ (R + R) * ‖a - b‖ := by
            gcongr
            exacts [h_R z hz σ hσ, h_R z' hz' σ hσ]
        _ ≤ (R + R) * (dist z z' * Real.exp (K * δ)) :=
            mul_le_mul_of_nonneg_left hab (by linarith)
        _ = Real.nnabs C * dist z z' := by
            rw [Real.coe_nnabs, abs_of_nonneg (by positivity)]
            ring
  -- Step 4. Differentiate under the integral sign.
  have hIoc : Ι (0 : ℝ) δ ⊆ Icc 0 δ := by
    rw [uIoc_of_le hδ.le]
    exact Ioc_subset_Icc_self
  have hF_cont : ∀ z, ContinuousOn (F z) (Icc 0 δ) := fun z =>
    ((continuous_snd.comp_continuousOn (hΨ_cont z)).sub continuousOn_const).norm.pow 2
  have hF'_cont : ContinuousOn F' (Icc 0 δ) :=
    (((innerSL ℝ).continuous.comp_continuousOn
      ((continuous_snd.comp_continuousOn (hΨ_cont z₀)).sub continuousOn_const)).clm_comp
        (continuousOn_const.clm_comp hΦ_cont)).const_smul _
  exact (intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip (μ := MeasureTheory.volume)
    (bound := fun _ => C) (ball_mem_nhds z₀ hρ)
    (Eventually.of_forall fun z => (hF_cont z).mono hIoc |>.aestronglyMeasurable measurableSet_uIoc)
    ((hF_cont z₀).intervalIntegrable_of_Icc hδ.le)
    ((hF'_cont.mono hIoc).aestronglyMeasurable measurableSet_uIoc)
    (Eventually.of_forall fun σ hσ => h_lip σ (hIoc hσ)) intervalIntegrable_const
    (Eventually.of_forall fun σ hσ => hF' σ (hIoc hσ))).2.differentiableAt

/-- **The derivative of `V` along the system** is computed along the solution itself
(`IsIntegralCurveOn.lieDerivative_eq_of_hasDerivWithinAt`): `V̇(t, x)` is the right derivative of
`τ ↦ V(τ, φ(τ))` at `t`.  By uniqueness, `V(τ, φ(τ))` is
`∫_{τ-t}^{τ-t+δ} ‖φ(t + σ) - x_eq‖² dσ`, whose derivative is `‖φ(t + δ) - x_eq‖² - ‖x - x_eq‖²`. -/
private lemma lieDerivative_integral_norm_sq {f : ℝ → ℝⁿ → ℝⁿ}
    (hf : ContDiff ℝ 1 (fun p : ℝ × ℝⁿ => f p.1 p.2)) {φ : ℝ × ℝⁿ → ℝ → ℝⁿ}
    (hφ0 : ∀ p, φ p p.1 = p.2) (hφ : ∀ p, IsIntegralCurveOn (φ p) f (Ici p.1))
    (hφ_uniq : ∀ p (β : ℝ → ℝⁿ), β p.1 = p.2 → IsIntegralCurveOn β f (Ici p.1) →
      EqOn β (φ p) (Ici p.1))
    {δ : ℝ} (hδ : 0 < δ) (x_eq : ℝⁿ) (t : ℝ) (x : ℝⁿ) :
    _root_.lieDerivative (fun t x => ∫ σ in (0 : ℝ)..δ, ‖φ (t, x) (t + σ) - x_eq‖ ^ 2) f t x =
      ‖φ (t, x) (t + δ) - x_eq‖ ^ 2 - ‖x - x_eq‖ ^ 2 := by
  set V : ℝ → ℝⁿ → ℝ := fun t x => ∫ σ in (0 : ℝ)..δ, ‖φ (t, x) (t + σ) - x_eq‖ ^ 2
  have hφ0' : φ (t, x) t = x := hφ0 (t, x)
  -- Step 1. Along the solution, `V(τ, φ(τ)) = ∫_{τ-t}^{τ-t+δ} w`, with `w(σ) = ‖φ(t + σ) - x_eq‖²`
  -- extended continuously to `σ < 0`.
  set w : ℝ → ℝ := fun σ => ‖φ (t, x) (t + max σ 0) - x_eq‖ ^ 2
  have hw : Continuous w :=
    (((hφ (t, x)).continuousOn.comp_continuous (continuous_const.add (continuous_id.max
      continuous_const)) fun σ => by simp).sub continuous_const).norm.pow 2
  have h_along : ∀ τ ∈ Ici t, V τ (φ (t, x) τ) =
      (∫ σ in (0 : ℝ)..(τ - t) + δ, w σ) - ∫ σ in (0 : ℝ)..τ - t, w σ := by
    intro τ hτ
    have hτ' : t ≤ τ := hτ
    -- By uniqueness, the solution from `(τ, φ(τ))` is the solution from `(t, x)`.
    have h_cocycle : EqOn (φ (t, x)) (φ (τ, φ (t, x) τ)) (Ici τ) :=
      hφ_uniq (τ, φ (t, x) τ) (φ (t, x)) rfl ((hφ (t, x)).mono (Ici_subset_Ici.mpr hτ'))
    calc V τ (φ (t, x) τ)
        = ∫ σ in (0 : ℝ)..δ, ‖φ (τ, φ (t, x) τ) (τ + σ) - x_eq‖ ^ 2 := rfl
      _ = ∫ σ in (0 : ℝ)..δ, w (σ + (τ - t)) := by
          refine intervalIntegral.integral_congr fun σ hσ => ?_
          rw [uIcc_of_le hδ.le] at hσ
          simp only [w, max_eq_left (show 0 ≤ σ + (τ - t) by linarith [hσ.1])]
          rw [← h_cocycle (show τ + σ ∈ Ici τ by simp [hσ.1])]
          ring_nf
      _ = ∫ σ in τ - t..δ + (τ - t), w σ := by
          rw [intervalIntegral.integral_comp_add_right, zero_add]
      _ = (∫ σ in (0 : ℝ)..(τ - t) + δ, w σ) - ∫ σ in (0 : ℝ)..τ - t, w σ := by
          rw [add_comm δ, intervalIntegral.integral_interval_sub_left
            (hw.intervalIntegrable _ _) (hw.intervalIntegrable _ _)]
  -- Step 2. By the fundamental theorem of calculus, that has derivative `w(δ) - w(0)` at `t`.
  have h_W : HasDerivAt (fun τ => (∫ σ in (0 : ℝ)..(τ - t) + δ, w σ) - ∫ σ in (0 : ℝ)..τ - t, w σ)
      (w δ - w 0) t := by
    have h₂ : HasDerivAt (fun τ => ∫ σ in (0 : ℝ)..τ - t, w σ) (w 0) t := by
      simpa using hw.hasDerivAt_integral_comp (hasDerivAt_const t 0) ((hasDerivAt_id t).sub_const t)
    have h₁ : HasDerivAt (fun τ => ∫ σ in (0 : ℝ)..(τ - t) + δ, w σ) (w δ) t := by
      simpa using hw.hasDerivAt_integral_comp (hasDerivAt_const t 0)
        (((hasDerivAt_id t).sub_const t).add_const δ)
    exact h₁.sub h₂
  have h_W' : HasDerivWithinAt (fun τ => V τ (φ (t, x) τ)) (w δ - w 0) (Ici t) t :=
    h_W.hasDerivWithinAt.congr (fun τ hτ => h_along τ hτ) (h_along t self_mem_Ici)
  -- Step 3. That right derivative is the Lie derivative.
  have h_lie := (hφ (t, x)).lieDerivative_eq_of_hasDerivWithinAt (V := V)
    (differentiableAt_integral_norm_sq hf hφ0 hφ hδ x_eq (t, φ (t, x) t)) h_W'
  rw [hφ0'] at h_lie
  rw [h_lie]
  simp [w, hφ0', max_eq_left hδ.le]

/-- **Solutions separate at most exponentially in the initial state** (Gronwall): the solutions
from `(t, y)` and `(t, y')` stay within `‖y - y'‖ e^{Lσ}` of each other after time `σ`. -/
private lemma dist_flow_le {f : ℝ → ℝⁿ → ℝⁿ} {L : ℝ≥0} (h_lip : ∀ τ, LipschitzWith L (f τ))
    {φ : ℝ × ℝⁿ → ℝ → ℝⁿ} (hφ0 : ∀ p, φ p p.1 = p.2)
    (hφ : ∀ p, IsIntegralCurveOn (φ p) f (Ici p.1)) (t : ℝ) (y y' : ℝⁿ) {σ : ℝ} (hσ : 0 ≤ σ) :
    dist (φ (t, y) (t + σ)) (φ (t, y') (t + σ)) ≤ dist y y' * Real.exp (L * σ) := by
  have h := dist_le_of_isIntegralCurveOn_Icc h_lip
    ((hφ (t, y)).mono Icc_subset_Ici_self) ((hφ (t, y')).mono Icc_subset_Ici_self)
    (t + σ) ⟨by linarith, le_rfl⟩
  rwa [show φ (t, y) t = y from hφ0 (t, y), show φ (t, y') t = y' from hφ0 (t, y'),
    add_sub_cancel_left] at h

/-- **The gradient of `V` is `O(‖x - x_eq‖)`.**  Near `x`, `V(t, ·)` is Lipschitz with constant
`2kδe^{Lδ}(‖x - x_eq‖ + r)`: solutions from `y` and `y'` separate at most like `e^{Lσ}‖y - y'‖`
and stay within `k‖y - x_eq‖` of `x_eq`.  Letting `r → 0` bounds the derivative. -/
private lemma norm_fderiv_integral_norm_sq_le {f : ℝ → ℝⁿ → ℝⁿ} {L : ℝ≥0}
    (h_lip : ∀ τ, LipschitzWith L (f τ)) {φ : ℝ × ℝⁿ → ℝ → ℝⁿ}
    (hφ0 : ∀ p, φ p p.1 = p.2) (hφ : ∀ p, IsIntegralCurveOn (φ p) f (Ici p.1))
    {δ : ℝ} (hδ : 0 < δ) {x_eq : ℝⁿ} {k : ℝ} (hk : 0 < k) {t : ℝ} {U : Set ℝⁿ} (hU : IsOpen U)
    (h_upper : ∀ y ∈ U, ∀ τ : ℝ, t ≤ τ → ‖φ (t, y) τ - x_eq‖ ≤ k * ‖y - x_eq‖)
    {x : ℝⁿ} (hx : x ∈ U) :
    ‖fderiv ℝ (fun y => ∫ σ in (0 : ℝ)..δ, ‖φ (t, y) (t + σ) - x_eq‖ ^ 2) x‖ ≤
      2 * (k * δ * Real.exp (L * δ)) * ‖x - x_eq‖ := by
  set A := k * δ * Real.exp (L * δ)
  have hA : 0 < A := by positivity
  obtain ⟨r_U, hr_U, h_ball_U⟩ := Metric.isOpen_iff.mp hU x hx
  -- Solutions from `y` and `y'` separate at most like `e^{Lσ}`.
  have h_sep : ∀ y y' : ℝⁿ, ∀ σ ∈ Icc 0 δ,
      ‖φ (t, y) (t + σ) - φ (t, y') (t + σ)‖ ≤ ‖y - y'‖ * Real.exp (L * δ) := by
    intro y y' σ hσ
    have h := dist_flow_le h_lip hφ0 hφ t y y' hσ.1
    rw [dist_eq_norm, dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ.2 L.coe_nonneg)) (norm_nonneg _))
  -- On a ball of radius `r` inside `U`, `V(t, ·)` is `2A(‖x - x_eq‖ + r)`-Lipschitz.
  have h_ball : ∀ r > 0, r ≤ r_U →
      ‖fderiv ℝ (fun y => ∫ σ in (0 : ℝ)..δ, ‖φ (t, y) (t + σ) - x_eq‖ ^ 2) x‖
        ≤ 2 * A * (‖x - x_eq‖ + r) := by
    intro r hr hr_le
    have hU_ball : ∀ z ∈ ball x r, z ∈ U := fun z hz => h_ball_U (ball_subset_ball hr_le hz)
    have hR : 0 ≤ ‖x - x_eq‖ + r := by positivity
    refine (norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds x hr)
      (C := (2 * A * (‖x - x_eq‖ + r)).toNNReal) ?_).trans
        (by rw [Real.coe_toNNReal _ (by positivity)])
    refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
    have h_near : ∀ z ∈ ball x r, ‖z - x_eq‖ ≤ ‖x - x_eq‖ + r := fun z hz =>
      calc ‖z - x_eq‖ ≤ ‖z - x‖ + ‖x - x_eq‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ‖x - x_eq‖ + r := by linarith [(mem_ball_iff_norm.mp hz).le]
    -- The integrand changes by at most `2k(‖x - x_eq‖ + r) e^{Lδ} ‖y - y'‖`.
    have h_pt : ∀ σ ∈ Ι (0 : ℝ) δ,
        ‖‖φ (t, y) (t + σ) - x_eq‖ ^ 2 - ‖φ (t, y') (t + σ) - x_eq‖ ^ 2‖ ≤
        2 * k * (‖x - x_eq‖ + r) * (‖y - y'‖ * Real.exp (L * δ)) := by
      intro σ hσ
      rw [uIoc_of_le hδ.le] at hσ
      set a := φ (t, y) (t + σ) - x_eq
      set b := φ (t, y') (t + σ) - x_eq
      have ha : ‖a‖ ≤ k * (‖x - x_eq‖ + r) :=
        (h_upper y (hU_ball y hy) _ (by linarith [hσ.1])).trans (by gcongr; exact h_near y hy)
      have hb : ‖b‖ ≤ k * (‖x - x_eq‖ + r) :=
        (h_upper y' (hU_ball y' hy') _ (by linarith [hσ.1])).trans
          (by gcongr; exact h_near y' hy')
      have hab : ‖a - b‖ ≤ ‖y - y'‖ * Real.exp (L * δ) := by
        simpa [a, b] using h_sep y y' σ (Ioc_subset_Icc_self hσ)
      calc ‖‖a‖ ^ 2 - ‖b‖ ^ 2‖
          ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := abs_norm_sq_sub_norm_sq_le a b
        _ ≤ (k * (‖x - x_eq‖ + r) + k * (‖x - x_eq‖ + r)) * ‖a - b‖ := by gcongr
        _ ≤ (k * (‖x - x_eq‖ + r) + k * (‖x - x_eq‖ + r)) *
              (‖y - y'‖ * Real.exp (L * δ)) := by gcongr
        _ = 2 * k * (‖x - x_eq‖ + r) * (‖y - y'‖ * Real.exp (L * δ)) := by ring
    have h_int : ∀ z : ℝⁿ, IntervalIntegrable (fun σ => ‖φ (t, z) (t + σ) - x_eq‖ ^ 2)
        MeasureTheory.volume 0 δ := fun z => by
      have hc : ContinuousOn (φ (t, z)) (Ici t) := (hφ (t, z)).continuousOn
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hδ.le]
      fun_prop (disch := intro σ hσ; simp only [mem_Ici]; linarith [hσ.1])
    calc dist (∫ σ in (0 : ℝ)..δ, ‖φ (t, y) (t + σ) - x_eq‖ ^ 2)
          (∫ σ in (0 : ℝ)..δ, ‖φ (t, y') (t + σ) - x_eq‖ ^ 2)
        = ‖∫ σ in (0 : ℝ)..δ,
            (‖φ (t, y) (t + σ) - x_eq‖ ^ 2 - ‖φ (t, y') (t + σ) - x_eq‖ ^ 2)‖ := by
          rw [dist_eq_norm, intervalIntegral.integral_sub (h_int y) (h_int y')]
      _ ≤ 2 * k * (‖x - x_eq‖ + r) * (‖y - y'‖ * Real.exp (L * δ)) * |δ - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const h_pt
      _ = (2 * A * (‖x - x_eq‖ + r)).toNNReal * dist y y' := by
          rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, sub_zero,
            abs_of_pos hδ]
          ring
  -- Let `r → 0`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  calc ‖fderiv ℝ (fun y => ∫ σ in (0 : ℝ)..δ, ‖φ (t, y) (t + σ) - x_eq‖ ^ 2) x‖
      ≤ 2 * A * (‖x - x_eq‖ + min (ε / (2 * A)) r_U) :=
        h_ball _ (lt_min (by positivity) hr_U) (min_le_right _ _)
    _ ≤ 2 * A * (‖x - x_eq‖ + ε / (2 * A)) := by gcongr; exact min_le_left _ _
    _ = 2 * A * ‖x - x_eq‖ + ε := by field_simp

/-- **The construction**, for a globally Lipschitz `C¹` field: if solutions starting in an open
set `U` at times `t ≥ 0` obey the exponential estimate, then
`V(t, x) = ∫₀^δ ‖φ(t + σ; t, x) - x_eq‖² dσ`, with `δ = ln(2k² + 1)/(2γ)`, is differentiable
everywhere and is a quadratic Lyapunov function on `U` with gradient `O(‖x - x_eq‖)`.  Both
converse theorems are this lemma: the global one with `U = ℝⁿ`, the local one for a cut-off
field. -/
private lemma exists_quadraticLyapunov_of_estimateOn {f : ℝ → ℝⁿ → ℝⁿ}
    (hf : ContDiff ℝ 1 (fun p : ℝ × ℝⁿ => f p.1 p.2)) {L : ℝ≥0}
    (hf_lip : ∀ t, LipschitzWith L (f t)) {x_eq : ℝⁿ} (h_eq : ∀ t, f t x_eq = 0)
    {U : Set ℝⁿ} (hU : IsOpen U) {k γ : ℝ} (hk : 0 < k) (hγ : 0 < γ)
    (h_exp : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ U, ∀ y : ℝ → ℝⁿ, y t = x → IsIntegralCurveOn y f (Ici t) →
      ∀ τ, t ≤ τ → ‖y τ - x_eq‖ ≤ k * ‖x - x_eq‖ * Real.exp (-γ * (τ - t))) :
    ∃ V : ℝ → ℝⁿ → ℝ, (∀ t x, DifferentiableAt ℝ (Function.uncurry V) (t, x)) ∧
      ∃ c₁ > 0, ∃ c₂ > 0, ∃ c₄ > 0, ∀ t : ℝ, 0 ≤ t → ∀ x ∈ U,
        c₁ * ‖x - x_eq‖ ^ 2 ≤ V t x ∧ V t x ≤ c₂ * ‖x - x_eq‖ ^ 2 ∧
        _root_.lieDerivative V f t x ≤ -(1 / 2 * ‖x - x_eq‖ ^ 2) ∧
        ‖fderiv ℝ (V t) x‖ ≤ c₄ * ‖x - x_eq‖ := by
  -- Step 1. Solutions from every initial time and state.
  choose φ hφ0 hφ hφ_uniq using fun p : ℝ × ℝⁿ =>
    exists_isIntegralCurveOn_Ici hf.continuous hf_lip p.1 p.2
  -- Step 2. The exponential estimate along the solutions from `U`.
  have h_upper : ∀ t, 0 ≤ t → ∀ x ∈ U, ∀ τ, t ≤ τ →
      ‖φ (t, x) τ - x_eq‖ ≤ k * ‖x - x_eq‖ * Real.exp (-γ * (τ - t)) := fun t ht x hx =>
    h_exp t ht x hx (φ (t, x)) (hφ0 (t, x)) (hφ (t, x))
  have h_upper' : ∀ t, 0 ≤ t → ∀ x ∈ U, ∀ τ, t ≤ τ → ‖φ (t, x) τ - x_eq‖ ≤ k * ‖x - x_eq‖ :=
    fun t ht x hx τ hτ => (h_upper t ht x hx τ hτ).trans (mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (by nlinarith)))
  -- Step 3. The horizon `δ`, chosen so that `k² e^{-2γδ} ≤ 1/2`.
  set δ := Real.log (2 * k ^ 2 + 1) / (2 * γ)
  have hδ : 0 < δ := div_pos (Real.log_pos (by nlinarith)) (by positivity)
  have h_decay : k ^ 2 * Real.exp (-(2 * γ) * δ) ≤ 1 / 2 := by
    have h_exp_δ : Real.exp (-(2 * γ) * δ) = (2 * k ^ 2 + 1)⁻¹ := by
      rw [show -(2 * γ) * δ = -Real.log (2 * k ^ 2 + 1) by simp only [δ]; field_simp,
        Real.exp_neg, Real.exp_log (by positivity)]
    rw [h_exp_δ, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  -- Step 4. `V(t, x) = ∫₀^δ ‖φ(t + σ; t, x) - x_eq‖² dσ`.
  set V : ℝ → ℝⁿ → ℝ := fun t x => ∫ σ in (0 : ℝ)..δ, ‖φ (t, x) (t + σ) - x_eq‖ ^ 2
  have h_int : ∀ (t : ℝ) (x : ℝⁿ), IntervalIntegrable (fun σ => ‖φ (t, x) (t + σ) - x_eq‖ ^ 2)
      MeasureTheory.volume 0 δ := fun t x => by
    have hc : ContinuousOn (φ (t, x)) (Ici t) := (hφ (t, x)).continuousOn
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hδ.le]
    fun_prop (disch := intro σ hσ; simp only [mem_Ici]; linarith [hσ.1])
  refine ⟨V, fun t x => differentiableAt_integral_norm_sq hf hφ0 hφ hδ x_eq (t, x),
    δ * Real.exp (-(2 * L) * δ), by positivity, δ * k ^ 2, by positivity,
    2 * (k * δ * Real.exp (L * δ)), by positivity, fun t ht x hx => ⟨?_, ?_, ?_, ?_⟩⟩
  · -- The lower bound: solutions decay no faster than `e^{-Lσ}`.
    calc δ * Real.exp (-(2 * L) * δ) * ‖x - x_eq‖ ^ 2
        = ∫ σ in (0 : ℝ)..δ, ‖x - x_eq‖ ^ 2 * Real.exp (-(2 * L) * δ) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
      _ ≤ V t x := intervalIntegral.integral_mono_on hδ.le intervalIntegrable_const (h_int t x)
          fun σ hσ =>
          calc ‖x - x_eq‖ ^ 2 * Real.exp (-(2 * L) * δ)
              ≤ ‖x - x_eq‖ ^ 2 * Real.exp (-(2 * L) * (t + σ - t)) :=
                mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
                  rw [show t + σ - t = σ by ring]
                  nlinarith [mul_nonneg L.coe_nonneg (sub_nonneg.mpr hσ.2)])) (by positivity)
            _ ≤ ‖φ (t, x) (t + σ) - x_eq‖ ^ 2 := by
                have h := ((hφ (t, x)).mono Icc_subset_Ici_self).norm_sub_mul_exp_le (t := t)
                  (τ := t + σ) (by linarith [hσ.1]) (fun τ _ => h_eq τ) (fun τ _ => hf_lip τ)
                rw [show φ (t, x) t = x from hφ0 (t, x)] at h
                calc ‖x - x_eq‖ ^ 2 * Real.exp (-(2 * L) * (t + σ - t))
                    = (‖x - x_eq‖ * Real.exp (-(L * (t + σ - t)))) ^ 2 := by
                      rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
                  _ ≤ _ := pow_le_pow_left₀ (by positivity) h 2
  · -- The upper bound: solutions stay within `k‖x - x_eq‖` of `x_eq`.
    calc V t x
        ≤ ∫ σ in (0 : ℝ)..δ, k ^ 2 * ‖x - x_eq‖ ^ 2 :=
          intervalIntegral.integral_mono_on hδ.le (h_int t x) intervalIntegrable_const
          fun σ hσ =>
          calc ‖φ (t, x) (t + σ) - x_eq‖ ^ 2
              ≤ (k * ‖x - x_eq‖) ^ 2 := by
                gcongr
                exact h_upper' t ht x hx _ (by linarith [hσ.1])
            _ = k ^ 2 * ‖x - x_eq‖ ^ 2 := by ring
      _ = δ * k ^ 2 * ‖x - x_eq‖ ^ 2 := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
  · -- The decrease: `V̇ = ‖φ(t + δ) - x_eq‖² - ‖x - x_eq‖² ≤ (k² e^{-2γδ} - 1) ‖x - x_eq‖²`.
    rw [lieDerivative_integral_norm_sq hf hφ0 hφ hφ_uniq hδ x_eq t x]
    calc ‖φ (t, x) (t + δ) - x_eq‖ ^ 2 - ‖x - x_eq‖ ^ 2
        ≤ (k * ‖x - x_eq‖ * Real.exp (-γ * (t + δ - t))) ^ 2 - ‖x - x_eq‖ ^ 2 := by
          gcongr
          exact h_upper t ht x hx _ (by linarith)
      _ = k ^ 2 * Real.exp (-(2 * γ) * δ) * ‖x - x_eq‖ ^ 2 - ‖x - x_eq‖ ^ 2 := by
          rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
          ring_nf
      _ ≤ 1 / 2 * ‖x - x_eq‖ ^ 2 - ‖x - x_eq‖ ^ 2 := by gcongr
      _ = -(1 / 2 * ‖x - x_eq‖ ^ 2) := by ring
  · -- The gradient bound.
    exact norm_fderiv_integral_norm_sq_le hf_lip hφ0 hφ hδ hk hU (h_upper' t ht) hx

/-- **The cut-off field.**  If `f` is `C¹` and `L`-Lipschitz on the ball `D` of radius `r`, with
`f(t, x_eq) = 0`, then for `ρ₁ < r` there is a `C¹` field `fχ`, globally Lipschitz in `x`
uniformly in `t` and bounded by `L r`, vanishing at `x_eq` and equal to `f` on the closed ball of
radius `ρ₁`: `fχ = χ f` with `χ` a smooth bump equal to `1` on that ball. -/
private lemma exists_cutoff {s : ContinuousSystem ℝⁿ Unit Y} {x_eq : ℝⁿ} {r ρ₁ : ℝ} {L : ℝ≥0}
    (hρ₁ : 0 < ρ₁) (hρ₁r : ρ₁ < r) (h_eq : ∀ t : ℝ, s.F t x_eq () = 0)
    (hf : ContDiffOn ℝ 1 (fun p : ℝ × ℝⁿ => s.F p.1 p.2 ()) (univ ×ˢ ball x_eq r))
    (hL : ∀ t : ℝ, LipschitzOnWith L (fun x => s.F t x ()) (ball x_eq r)) :
    ∃ fχ : ℝ → ℝⁿ → ℝⁿ, ContDiff ℝ 1 (fun p : ℝ × ℝⁿ => fχ p.1 p.2) ∧
      (∃ L' : ℝ≥0, ∀ t, LipschitzWith L' (fχ t)) ∧ (∀ t y, ‖fχ t y‖ ≤ L * r) ∧
      (∀ t, fχ t x_eq = 0) ∧ ∀ t, ∀ y ∈ closedBall x_eq ρ₁, fχ t y = s.F t y () := by
  have hr : 0 < r := hρ₁.trans hρ₁r
  -- A smooth cutoff `χ`, equal to `1` on the `ρ₁`-ball and `0` outside the `ρ₂`-ball.
  set ρ₂ := (ρ₁ + r) / 2
  have hρ₂ : ρ₂ < r := by simp only [ρ₂]; linarith
  let χ : ContDiffBump x_eq := ⟨ρ₁, ρ₂, hρ₁, by simp only [ρ₂]; linarith⟩
  obtain ⟨M, hM⟩ := ContDiff.lipschitzWith_of_hasCompactSupport χ.hasCompactSupport
    (χ.contDiff (n := 1)) one_ne_zero
  have hχ_zero : ∀ y ∉ ball x_eq r, χ y = 0 := fun y hy =>
    χ.zero_of_le_dist (hρ₂.le.trans (not_lt.mp (by rwa [mem_ball] at hy)))
  have h_bound : ∀ t, ∀ y ∈ ball x_eq r, ‖s.F t y ()‖ ≤ L * r := fun t y hy =>
    calc ‖s.F t y ()‖
        = dist (s.F t y ()) (s.F t x_eq ()) := by rw [h_eq t, dist_zero_right]
      _ ≤ L * dist y x_eq := (hL t).dist_le_mul y hy x_eq (mem_ball_self hr)
      _ ≤ L * r := by gcongr; exact (mem_ball.mp hy).le
  set fχ : ℝ → ℝⁿ → ℝⁿ := fun t y => χ y • s.F t y ()
  refine ⟨fχ, ?_, ⟨L + M * (L * r.toNNReal), fun t => ?_⟩, fun t y => ?_,
    fun t => by simp [fχ, h_eq t], fun t y hy => by simp [fχ, χ.one_of_mem_closedBall hy]⟩
  · refine contDiff_iff_contDiffAt.mpr fun p => ?_
    by_cases hp : p.2 ∈ ball x_eq r
    · exact ((χ.contDiff.comp contDiff_snd).contDiffAt).smul
        (hf.contDiffAt (prod_mem_nhds univ_mem (isOpen_ball.mem_nhds hp)))
    · -- Outside the `ρ₂`-ball the cut-off field vanishes identically.
      refine contDiffAt_const (c := (0 : ℝⁿ)).congr_of_eventuallyEq ?_
      have h_far : ρ₂ < dist p.2 x_eq := hρ₂.trans_le (not_lt.mp (by rwa [mem_ball] at hp))
      filter_upwards [(isOpen_lt continuous_const
        ((continuous_snd.dist continuous_const))).mem_nhds h_far] with q hq
      simp [fχ, χ.zero_of_le_dist hq.le]
  · exact lipschitzWith_smul_of_lipschitzOnWith hM
      (fun y => by rw [abs_of_nonneg χ.nonneg]; exact χ.le_one) hχ_zero (hL t)
      fun y hy => (h_bound t y hy).trans_eq (by rw [NNReal.coe_mul, Real.coe_toNNReal _ hr.le])
  · by_cases hy : y ∈ ball x_eq r
    · calc ‖fχ t y‖
          = |χ y| * ‖s.F t y ()‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * (L * r) := by
            gcongr
            · rw [abs_of_nonneg χ.nonneg]; exact χ.le_one
            · exact h_bound t y hy
        _ = L * r := one_mul _
    · simp only [fχ, hχ_zero y hy, zero_smul, norm_zero]
      positivity

/-- **Solutions of the cut-off field obey the estimate.**  Let `fχ = f` on the closed ball of
radius `ρ₁`, and let trajectories of `f` from `D₀ = B(x_eq, r₀)` at times `t₀ ≥ 0` obey an
estimate `‖x(t) - x_eq‖ ≤ E(x(t₀), t₀, t)` that stays below `ρ₁`.  Then a solution of `fχ` from
`D₀` never reaches the `ρ₁`-sphere: up to the first time it would, it is a trajectory of `f`, so
the estimate keeps it inside.  It therefore obeys the estimate for all time. -/
private lemma estimate_of_cutoff {s : ContinuousSystem ℝⁿ Unit Y} {x_eq : ℝⁿ} {ρ₁ r₀ : ℝ}
    {fχ : ℝ → ℝⁿ → ℝⁿ} (h_agree : ∀ t, ∀ y ∈ closedBall x_eq ρ₁, fχ t y = s.F t y ())
    {E : ℝⁿ → ℝ → ℝ → ℝ} (hE : ∀ x ∈ ball x_eq r₀, ∀ t τ, t ≤ τ → E x t τ < ρ₁)
    (h_est : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → ℝⁿ),
      s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < r₀ →
        ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ E (x t₀) t₀ t) :
    ∀ t : ℝ, 0 ≤ t → ∀ x ∈ ball x_eq r₀, ∀ y : ℝ → ℝⁿ, y t = x →
      IsIntegralCurveOn y fχ (Ici t) → ∀ τ, t ≤ τ → ‖y τ - x_eq‖ ≤ E x t τ := by
  intro t ht x hx y hy0 hy τ hτ
  have hx' : ‖x - x_eq‖ < r₀ := mem_ball_iff_norm.mp hx
  -- On a stretch inside the `ρ₁`-ball, `y` is a trajectory of `f`.
  have h_traj : ∀ σ, (∀ u ∈ Icc t σ, ‖y u - x_eq‖ ≤ ρ₁) →
      s.IsTrajectoryOn (fun _ => ()) y (Icc t σ) := fun σ h_in u hu =>
    ((hy u hu.1).mono Icc_subset_Ici_self).congr_deriv
      (h_agree u (y u) (mem_closedBall_iff_norm.mpr (h_in u hu)))
  have h_bound : ∀ σ, (∀ u ∈ Icc t σ, ‖y u - x_eq‖ ≤ ρ₁) → t ≤ σ →
      ‖y σ - x_eq‖ ≤ E x t σ := fun σ h_in hσ => by
    have h := h_est t ht σ y (h_traj σ h_in) (by rw [hy0]; exact hx') σ ⟨hσ, le_rfl⟩
    rwa [hy0] at h
  -- The initial state is inside: the estimate on the one-point segment.
  have h_start : ‖y t - x_eq‖ < ρ₁ := by
    have h := h_est t ht t (fun _ => x)
      (fun σ _ => HasFDerivWithinAt.of_subsingleton (subsingleton_Icc_of_ge le_rfl)) hx' t
      ⟨le_rfl, le_rfl⟩
    rw [hy0]
    exact h.trans_lt (hE x hx t t le_rfl)
  -- `y` never reaches the `ρ₁`-sphere.
  have h_inside : ∀ σ ∈ Icc t τ, ‖y σ - x_eq‖ < ρ₁ := by
    intro σ hσ
    by_contra h_out
    obtain ⟨σ', hσ', hσ'_eq, h_before⟩ := exists_first_sphere_hit
      ((hy.mono Icc_subset_Ici_self).continuousOn) h_start hσ (not_lt.mp h_out)
    linarith [h_bound σ' h_before hσ'.1, hE x hx t σ' hσ'.1]
  exact h_bound τ (fun u hu => (h_inside u hu).le) hτ

/-- **Converse Lyapunov theorem for exponential stability.**  Let `x_eq` be an equilibrium of
`ẋ = f(t, x)`, with `f` continuously differentiable and `f(t, ·)` Lipschitz on the ball `D` of
radius `r`, uniformly in `t`.  If trajectories starting in the ball `D₀` of radius `r₀ < r / k`
obey `‖x(t) - x_eq‖ ≤ k ‖x(t₀) - x_eq‖ e^{-γ(t - t₀)}`, there is an exponential Lyapunov
function with exponent `2` on `D₀` whose gradient is `O(‖x - x_eq‖)` there.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.14. -/
@[blueprint "thm:continuousSystem-exists-quadraticLyapunov-of-exponentialEstimate"
  (title := "Converse Lyapunov theorem for exponential stability")
  (statement := /-- Let $x_{\mathrm{eq}}$ be an equilibrium of $\dot x = f(t, x)$ on
    $\mathbb{R}^n$, $f(t, x_{\mathrm{eq}}) = 0$ for all $t$, with $f$ continuously
    differentiable on $\mathbb{R} \times D$, $D = \{x : \|x - x_{\mathrm{eq}}\| < r\}$, and
    $f(t, \cdot)$ $L$-Lipschitz on $D$ for all $t$ (for $C^1$ $f$, equivalently
    $\|\partial f / \partial x\| \le L$ there).  Let
    $k, \gamma, r_0 > 0$ with $r_0 < r / k$, $D_0 = \{x : \|x - x_{\mathrm{eq}}\| < r_0\}$, and
    suppose every trajectory on a segment $[t_0, t_1]$, $t_0 \ge 0$, with
    $x(t_0) \in D_0$ satisfies
    \[
      \|x(t) - x_{\mathrm{eq}}\| \le k\,\|x(t_0) - x_{\mathrm{eq}}\|\,e^{-\gamma (t - t_0)}
      \qquad \forall\, t \in [t_0, t_1].
    \]
    Then there is an exponential Lyapunov function $V$ with exponent $2$ on $D_0$
    (\cref{def:continuousSystem-isExponentialLyapunovFunction}), that is, with
    \[
      c_1 \|x - x_{\mathrm{eq}}\|^2 \le V(t, x) \le c_2 \|x - x_{\mathrm{eq}}\|^2, \qquad
      \frac{\partial V}{\partial t} + \frac{\partial V}{\partial x} f(t, x)
        \le -c_3 \|x - x_{\mathrm{eq}}\|^2
    \]
    for $t \ge 0$ and $x \in D_0$, and $c_4 > 0$ with
    $\|\partial V / \partial x\| \le c_4 \|x - x_{\mathrm{eq}}\|$ there.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.14.  Differences:
    \begin{itemize} \item $f$ is $C^1$ and Lipschitz for all $t \in \mathbb{R}$, not only
    $t \ge 0$: differentiability of $V$ at $t = 0$ involves solutions from negative initial
    times. \item The Lipschitz bound replaces Khalil's equivalent Jacobian bound. \item The
    estimate is assumed on trajectory segments. \end{itemize} -/)
  (proof := /-- Cut the field off outside the ball: with $\chi$ a smooth bump equal to $1$ on the
    ball of radius $\rho_1$, $k r_0 < \rho_1 < r$, and vanishing near the sphere of radius $r$,
    $\tilde f = \chi f$ is $C^1$ and globally Lipschitz in $x$, uniformly in $t$, and agrees
    with $f$ on the $\rho_1$-ball.  A solution of $\tilde f$ from $D_0$ never reaches the
    $\rho_1$-sphere: up to the first time it would, it is a solution of $f$, so Khalil's
    estimate keeps it within $k r_0 < \rho_1$.  It is therefore a solution of $f$, and obeys the
    estimate for all time.  The construction of
    \cref{thm:continuousSystem-exists-quadraticLyapunov-of-globallyExponentiallyStable}, run for
    $\tilde f$ from $D_0$, gives $V$; on $D_0$, where $\tilde f = f$, its derivative along
    $\tilde f$ is its derivative along $f$. -/)]
theorem exists_quadraticLyapunov_of_exponentialEstimate {s : ContinuousSystem ℝⁿ Unit Y}
    {x_eq : ℝⁿ} {r k γ r₀ : ℝ}
    (h_eq : ∀ t : ℝ, s.F t x_eq () = 0)
    (hf : ContDiffOn ℝ 1 (fun p : ℝ × ℝⁿ => s.F p.1 p.2 ()) (univ ×ˢ ball x_eq r))
    (h_lip : ∃ L : ℝ≥0, ∀ t : ℝ, LipschitzOnWith L (fun x => s.F t x ()) (ball x_eq r))
    (hk : 0 < k) (hγ : 0 < γ) (hr₀ : 0 < r₀) (hr₀r : r₀ < r / k)
    (h_exp : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → ℝⁿ),
      s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < r₀ →
        ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ k * ‖x t₀ - x_eq‖ * Real.exp (-γ * (t - t₀))) :
    ∃ V : ℝ → ℝⁿ → ℝ, s.IsExponentialLyapunovFunction V x_eq (ball x_eq r₀) 2 ∧
      ∃ c₄ > 0, ∀ t : ℝ, 0 ≤ t → ∀ x ∈ ball x_eq r₀, ‖fderiv ℝ (V t) x‖ ≤ c₄ * ‖x - x_eq‖ := by
  obtain ⟨L, hL⟩ := h_lip
  have hkr₀ : k * r₀ < r := by rw [lt_div_iff₀ hk] at hr₀r; linarith
  -- Step 1. The cut-off field `fχ`, equal to `f` on the ball of radius `ρ₁ ∈ (k r₀, r)`.
  set ρ₁ := (k * r₀ + r) / 2 with hρ₁_def
  have hρ₁ : k * r₀ < ρ₁ := by rw [hρ₁_def]; linarith
  obtain ⟨fχ, hfχ, ⟨L', hfχ_lip⟩, -, hfχ_eq, h_agree⟩ := exists_cutoff (ρ₁ := ρ₁)
    ((by positivity : 0 < k * r₀).trans hρ₁) (by rw [hρ₁_def]; linarith) h_eq hf hL
  -- Step 2. Starting in `D₀`, the estimate stays below `k r₀ < ρ₁`, so solutions of `fχ` obey it.
  have h_exp' := estimate_of_cutoff h_agree
    (E := fun x t τ => k * ‖x - x_eq‖ * Real.exp (-γ * (τ - t)))
    (fun x hx t τ hτ =>
      calc k * ‖x - x_eq‖ * Real.exp (-γ * (τ - t))
          ≤ k * ‖x - x_eq‖ := mul_le_of_le_one_right (by positivity)
            (Real.exp_le_one_iff.mpr (by nlinarith))
        _ < k * r₀ := mul_lt_mul_of_pos_left (mem_ball_iff_norm.mp hx) hk
        _ < ρ₁ := hρ₁) h_exp
  -- `D₀` lies inside the `ρ₁`-ball: the estimate on a one-point segment.
  have h_small : ∀ x ∈ ball x_eq r₀, ‖x - x_eq‖ < ρ₁ := fun x hx => by
    have h := h_exp 0 le_rfl 0 (fun _ => x)
      (fun σ _ => HasFDerivWithinAt.of_subsingleton (subsingleton_Icc_of_ge le_rfl))
      (mem_ball_iff_norm.mp hx) 0 ⟨le_rfl, le_rfl⟩
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at h
    calc ‖x - x_eq‖ ≤ k * ‖x - x_eq‖ := h
      _ < k * r₀ := mul_lt_mul_of_pos_left (mem_ball_iff_norm.mp hx) hk
      _ < ρ₁ := hρ₁
  -- Step 3. The construction for the cut-off field; on `D₀` its `V̇` is that of `f`.
  obtain ⟨V, hV_diff, c₁, hc₁, c₂, hc₂, c₄, hc₄, hV⟩ :=
    exists_quadraticLyapunov_of_estimateOn hfχ hfχ_lip hfχ_eq isOpen_ball hk hγ h_exp'
  refine ⟨V, ⟨ball_mem_nhds x_eq hr₀, fun t _ x _ => hV_diff t x, two_pos, c₁, hc₁, c₂, hc₂,
    1 / 2, by norm_num, fun t ht x hx => ?_⟩, c₄, hc₄, fun t ht x hx => (hV t ht x hx).2.2.2⟩
  obtain ⟨h_lower, h_upper, h_lie, -⟩ := hV t ht x hx
  rw [Real.rpow_two]
  refine ⟨h_lower, h_upper, ?_⟩
  change fderiv ℝ (Function.uncurry V) (t, x) (1, s.F t x ()) ≤ _
  rw [← h_agree t x (mem_closedBall_iff_norm.mpr (h_small x hx).le)]
  exact h_lie

/-- **Converse Lyapunov theorem for global exponential stability**: if `f` is continuously
differentiable and `f(t, ·)` is `L`-Lipschitz on `ℝⁿ` for every `t`, and `x_eq` is globally
exponentially stable, there is an exponential Lyapunov function with exponent `2` on all of `ℝⁿ`
whose gradient is `O(‖x - x_eq‖)`.

The function is Khalil's `V(t, x) = ∫_t^{t+δ} ‖φ(τ; t, x) - x_eq‖² dτ`, written as
`∫₀^δ ‖φ(t + σ; t, x) - x_eq‖² dσ` so that the limits do not move.  Khalil asks for a bounded
Jacobian; the proof only uses `L` as a Lipschitz constant, so that is the hypothesis here (for `C¹`
`f` the two are equivalent).  It is asked for every `t ∈ ℝ`, not only `t ≥ 0`: differentiability of
`V` at `t = 0` involves solutions from slightly negative initial times.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.14, global case. -/
@[blueprint "thm:continuousSystem-exists-quadraticLyapunov-of-globallyExponentiallyStable"
  (title := "Converse Lyapunov theorem for global exponential stability")
  (statement := /-- Let $x_{\mathrm{eq}}$ be an equilibrium of $\dot x = f(t, x)$ on
    $\mathbb{R}^n$, with $f$ continuously differentiable on $\mathbb{R} \times \mathbb{R}^n$ and
    $f(t, \cdot)$ $L$-Lipschitz for every $t \in \mathbb{R}$ (for $C^1$ $f$, equivalently
    $\|\partial f / \partial x\| \le L$).  If
    $x_{\mathrm{eq}}$ is globally exponentially stable
    (\cref{def:continuousSystem-globallyExponentiallyStable}), there is an exponential Lyapunov
    function $V$ with exponent $2$ on $\mathbb{R}^n$
    (\cref{def:continuousSystem-isExponentialLyapunovFunction}) and $c_4 > 0$ with
    $\|\partial V / \partial x\| \le c_4 \|x - x_{\mathrm{eq}}\|$ for all $t \ge 0$ and
    $x \in \mathbb{R}^n$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.14, global case.
    Differences: \begin{itemize} \item The Lipschitz bound replaces Khalil's equivalent Jacobian
    bound, and is asked for all $t \in \mathbb{R}$: differentiability of $V$ at $t = 0$ involves
    solutions from negative initial times.
    \item The constants are $c_1 = \delta e^{-2L\delta}$, $c_2 = \delta k^2$ and
    $c_4 = 2k\delta e^{L\delta}$, cruder than Khalil's. \end{itemize} -/)
  (proof := /-- Solutions $\phi(\tau; t, x)$ exist from every $(t, x)$, since $f$ is globally
    Lipschitz in $x$.  Let $V(t, x) = \int_0^\delta \|\phi(t + \sigma; t, x) -
    x_{\mathrm{eq}}\|^2\,d\sigma$ with $\delta = \ln(2k^2 + 1)/(2\gamma)$.  The exponential
    estimate and the lower bound $\|\phi(\tau) - x_{\mathrm{eq}}\|^2 \ge e^{-2L(\tau - t)}
    \|x - x_{\mathrm{eq}}\|^2$ sandwich $V$.  $V$ is differentiable: appending time to the state,
    solutions are differentiable in their initial data
    (\cref{thm:hasFDerivAt-of-isIntegralCurveOn}) and locally Lipschitz in it
    (\cref{lem:isIntegralCurveOn-exists-dist-le-of-contDiff}), so the integral can be
    differentiated under the integral sign.  Along a solution, uniqueness gives
    $V = \int_h^{h+\delta}\|\phi(t + \sigma) - x_{\mathrm{eq}}\|^2 d\sigma$, so
    $\dot V = \|\phi(t + \delta) - x_{\mathrm{eq}}\|^2 - \|x - x_{\mathrm{eq}}\|^2 \le
    (k^2 e^{-2\gamma\delta} - 1)\|x - x_{\mathrm{eq}}\|^2 \le -\tfrac12\|x - x_{\mathrm{eq}}\|^2$.
    Finally, solutions from nearby states separate at most like $e^{L\sigma}$, which makes
    $V(t, \cdot)$ locally Lipschitz with constant $\approx 2k\delta e^{L\delta}
    \|x - x_{\mathrm{eq}}\|$. -/)]
theorem exists_quadraticLyapunov_of_globallyExponentiallyStable
    {s : ContinuousSystem ℝⁿ Unit Y} {x_eq : ℝⁿ}
    (h_eq : ∀ t : ℝ, s.F t x_eq () = 0)
    (hf : ContDiff ℝ 1 (fun p : ℝ × ℝⁿ => s.F p.1 p.2 ()))
    (h_lip : ∃ L : ℝ≥0, ∀ t : ℝ, LipschitzWith L (fun x => s.F t x ()))
    (h_ges : s.GloballyExponentiallyStable x_eq) :
    ∃ V : ℝ → ℝⁿ → ℝ, s.IsExponentialLyapunovFunction V x_eq univ 2 ∧
      ∃ c₄ > 0, ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖fderiv ℝ (V t) x‖ ≤ c₄ * ‖x - x_eq‖ := by
  obtain ⟨L, hf_lip⟩ := h_lip
  obtain ⟨k, hk, γ, hγ, h_exp⟩ := h_ges
  obtain ⟨V, hV_diff, c₁, hc₁, c₂, hc₂, c₄, hc₄, hV⟩ :=
    exists_quadraticLyapunov_of_estimateOn hf hf_lip h_eq isOpen_univ hk hγ
      fun t ht x _ y hy0 hy τ hτ => by
        have h := h_exp t ht τ y (hy.mono Icc_subset_Ici_self) τ ⟨hτ, le_rfl⟩
        rwa [hy0] at h
  refine ⟨V, ⟨univ_mem, fun t _ x _ => hV_diff t x, two_pos, c₁, hc₁, c₂, hc₂, 1 / 2,
    by norm_num, fun t ht x hx => ?_⟩, c₄, hc₄, fun t ht x => (hV t ht x (mem_univ x)).2.2.2⟩
  obtain ⟨h_lower, h_upper, h_lie, -⟩ := hV t ht x hx
  rw [Real.rpow_two]
  exact ⟨h_lower, h_upper, h_lie⟩

/-! ## Uniform asymptotic stability -/

open MeasureTheory

/-- **The rate fed to Massera's lemma.**  `ĝ(σ) = β(r₀, max(σ - 1, 0)) + r₀ e^{1 - σ}`: it
dominates `β(ρ, σ')` for `ρ ≤ r₀` and `σ' ≥ max(σ - 1, 0)` (solutions started up to one time unit
early), it is at least `r₀` for `σ ≤ 1`, and it is positive, continuous and strictly decreasing
to `0`. -/
private noncomputable def klRate {a : ℝ} (β : ClassKL a) (r₀ σ : ℝ) : ℝ :=
  β.toFun r₀ (max (σ - 1) 0) + r₀ * Real.exp (1 - σ)

private lemma klRate_spec {a r₀ : ℝ} (β : ClassKL a) (hr₀ : 0 < r₀) (hr₀a : r₀ < a) :
    (∀ σ, 0 < klRate β r₀ σ) ∧ Continuous (klRate β r₀) ∧ StrictAnti (klRate β r₀) ∧
      Tendsto (klRate β r₀) atTop (nhds 0) ∧
      (∀ ρ ∈ Icc 0 r₀, ∀ σ σ', 0 ≤ σ' → max (σ - 1) 0 ≤ σ' → β.toFun ρ σ' ≤ klRate β r₀ σ) ∧
      ∀ σ, σ ≤ 1 → r₀ ≤ klRate β r₀ σ := by
  have hr₀_mem : r₀ ∈ Ico 0 a := ⟨hr₀.le, hr₀a⟩
  have hβ_nonneg : ∀ σ, 0 ≤ β.toFun r₀ (max (σ - 1) 0) := fun σ =>
    β.nonneg r₀ hr₀_mem _ (le_max_right _ _)
  refine ⟨fun σ => add_pos_of_nonneg_of_pos (hβ_nonneg σ) (by positivity), ?_, ?_, ?_, ?_, ?_⟩
  · exact (β.continuous.comp_continuous (continuous_const.prodMk
      ((continuous_id.sub continuous_const).max continuous_const))
        fun σ => ⟨hr₀_mem, mem_Ici.2 (le_max_right _ _)⟩).add
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.sub continuous_id)))
  · intro σ₁ σ₂ h
    have h_β : β.toFun r₀ (max (σ₂ - 1) 0) ≤ β.toFun r₀ (max (σ₁ - 1) 0) :=
      β.anti_s_mono hr₀_mem (mem_Ici.2 (le_max_right _ _)) (mem_Ici.2 (le_max_right _ _))
        (max_le_max (by linarith) le_rfl)
    have h_exp : r₀ * Real.exp (1 - σ₂) < r₀ * Real.exp (1 - σ₁) :=
      mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (by linarith)) hr₀
    exact add_lt_add_of_le_of_lt h_β h_exp
  · have h_β : Tendsto (fun σ => β.toFun r₀ (max (σ - 1) 0)) atTop (nhds 0) :=
      (β.tendsto_zero_s hr₀_mem).comp (tendsto_atTop_mono (fun σ => le_max_left _ _)
        (tendsto_atTop_add_const_right _ (-1) tendsto_id))
    have h_exp : Tendsto (fun σ => r₀ * Real.exp (1 - σ)) atTop (nhds 0) := by
      have h := (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (r₀ * Real.exp 1))
      rw [mul_zero] at h
      refine h.congr fun σ => ?_
      rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg]
    simpa using h_β.add h_exp
  · intro ρ hρ σ σ' hσ' h
    have hρ_mem : ρ ∈ Ico 0 a := ⟨hρ.1, hρ.2.trans_lt hr₀a⟩
    calc β.toFun ρ σ'
        ≤ β.toFun r₀ σ' := β.mono_r hρ_mem hr₀_mem hσ' hρ.2
      _ ≤ β.toFun r₀ (max (σ - 1) 0) := β.anti_s_mono hr₀_mem (mem_Ici.2 (le_max_right _ _)) hσ' h
      _ ≤ klRate β r₀ σ := le_add_of_nonneg_right (by positivity)
  · intro σ hσ
    calc r₀
        ≤ r₀ * Real.exp (1 - σ) := le_mul_of_one_le_right hr₀.le (Real.one_le_exp (by linarith))
      _ ≤ klRate β r₀ σ := le_add_of_nonneg_left (hβ_nonneg σ)

/-- **Solutions from nearby initial times and states stay nearby**: with `f(t, ·)` `L`-Lipschitz
and `‖f‖ ≤ B`, the solutions from `z` and `z'`, compared after the same elapsed time `σ`, differ
by at most `(2B + 1) e^{Lσ} dist(z, z')`.  Run both to the later initial time (speed `B`), then
apply Gronwall. -/
private lemma norm_flow_sub_flow_le {f : ℝ → ℝⁿ → ℝⁿ} {L : ℝ≥0}
    (hf_lip : ∀ t, LipschitzWith L (f t)) {B : ℝ} (hf_bdd : ∀ t y, ‖f t y‖ ≤ B)
    {φ : ℝ × ℝⁿ → ℝ → ℝⁿ} (hφ0 : ∀ p, φ p p.1 = p.2)
    (hφ : ∀ p, IsIntegralCurveOn (φ p) f (Ici p.1)) (z z' : ℝ × ℝⁿ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖φ z (z.1 + σ) - φ z' (z'.1 + σ)‖ ≤ (2 * B + 1) * Real.exp (L * σ) * dist z z' := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf_bdd 0 0)
  have h_exp : 1 ≤ Real.exp (L * σ) := Real.one_le_exp (by positivity)
  -- The case where `z` starts first.
  have h_one : ∀ z z' : ℝ × ℝⁿ, z.1 ≤ z'.1 →
      ‖φ z (z.1 + σ) - φ z' (z'.1 + σ)‖ ≤ (2 * B + 1) * Real.exp (L * σ) * dist z z' := by
    intro z z' h
    set d := dist z z'
    have hdt : z'.1 - z.1 ≤ d := by
      have := le_max_left (dist z.1 z'.1) (dist z.2 z'.2)
      rw [← Prod.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)] at this
      exact this
    have hdx : ‖z.2 - z'.2‖ ≤ d := by
      rw [← dist_eq_norm]
      exact (le_max_right _ _).trans_eq Prod.dist_eq.symm
    have hd : 0 ≤ d := dist_nonneg
    -- `φ z` runs from `z.1` to `z'.1` at speed `B`.
    have h_speed : ∀ σ' τ, z.1 ≤ σ' → z.1 ≤ τ → ‖φ z τ - φ z σ'‖ ≤ B * |τ - σ'| :=
      fun σ' τ h₁ h₂ => (hφ z).norm_sub_le (convex_Ici _) (fun _ _ => hf_bdd _ _) h₁ h₂
    have h_gron : ‖φ z (z'.1 + σ) - φ z' (z'.1 + σ)‖ ≤
        ‖φ z z'.1 - z'.2‖ * Real.exp (L * σ) := by
      have h := dist_le_of_isIntegralCurveOn_Icc hf_lip
        ((hφ z).mono (Icc_subset_Ici_iff (by linarith) |>.2 h))
        ((hφ z').mono Icc_subset_Ici_self) (z'.1 + σ) ⟨by linarith, le_rfl⟩
      rwa [dist_eq_norm, dist_eq_norm, hφ0 z', add_sub_cancel_left] at h
    calc ‖φ z (z.1 + σ) - φ z' (z'.1 + σ)‖
        ≤ ‖φ z (z.1 + σ) - φ z (z'.1 + σ)‖ + ‖φ z (z'.1 + σ) - φ z' (z'.1 + σ)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ B * d + (B * d + d) * Real.exp (L * σ) := by
          gcongr
          · calc ‖φ z (z.1 + σ) - φ z (z'.1 + σ)‖
                ≤ B * |z.1 + σ - (z'.1 + σ)| := h_speed _ _ (by linarith) (by linarith)
              _ ≤ B * d := by
                  gcongr
                  rw [abs_le]; constructor <;> linarith
          · refine h_gron.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
            calc ‖φ z z'.1 - z'.2‖
                ≤ ‖φ z z'.1 - z.2‖ + ‖z.2 - z'.2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
              _ ≤ B * d + d := by
                  gcongr
                  calc ‖φ z z'.1 - z.2‖
                      = ‖φ z z'.1 - φ z z.1‖ := by rw [hφ0 z]
                    _ ≤ B * |z'.1 - z.1| := h_speed _ _ le_rfl h
                    _ ≤ B * d := by gcongr; rw [abs_of_nonneg (by linarith)]; exact hdt
      _ ≤ (2 * B + 1) * Real.exp (L * σ) * d := by nlinarith [mul_nonneg hB hd]
  rcases le_total z.1 z'.1 with h | h
  · exact h_one z z' h
  · rw [norm_sub_rev, dist_comm]
    exact h_one z' z h

/-- **Solutions from near `(t₀, x₀)` obey the rate `ĝ`**, for `t₀ ≥ 0` and `x₀ ∈ D₀`: on a small
ball around `(t₀, x₀)` every solution satisfies `‖φ(z.1 + σ) - x_eq‖ ≤ ĝ(σ)`.  From a nonnegative
initial time this is the class `KL` estimate; from a slightly negative one, the solution reaches
time `0` still inside `D₀` and obeys the estimate from there. -/
private lemma norm_flow_le_klRate {f : ℝ → ℝⁿ → ℝⁿ} {B : ℝ} (hf_bdd : ∀ t y, ‖f t y‖ ≤ B)
    {φ : ℝ × ℝⁿ → ℝ → ℝⁿ} (hφ0 : ∀ p, φ p p.1 = p.2)
    (hφ : ∀ p, IsIntegralCurveOn (φ p) f (Ici p.1)) {x_eq : ℝⁿ} {a r₀ : ℝ} (β : ClassKL a)
    (hr₀ : 0 < r₀) (hr₀a : r₀ < a)
    (h_KL : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ ball x_eq r₀, ∀ y : ℝ → ℝⁿ, y t = x →
      IsIntegralCurveOn y f (Ici t) → ∀ τ, t ≤ τ → ‖y τ - x_eq‖ ≤ β.toFun ‖x - x_eq‖ (τ - t))
    {z₀ : ℝ × ℝⁿ} (ht₀ : 0 ≤ z₀.1) (hx₀ : z₀.2 ∈ ball x_eq r₀) :
    ∃ ε > 0, ∀ z ∈ ball z₀ ε, ∀ σ, 0 ≤ σ → ‖φ z (z.1 + σ) - x_eq‖ ≤ klRate β r₀ σ := by
  obtain ⟨-, -, -, -, h_rate, h_rate_one⟩ := klRate_spec β hr₀ hr₀a
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf_bdd 0 0)
  set ρ := ‖z₀.2 - x_eq‖
  have hρ : ρ < r₀ := mem_ball_iff_norm.mp hx₀
  set ε := min 1 ((r₀ - ρ) / (B + 2))
  have hε : 0 < ε := lt_min one_pos (div_pos (by linarith) (by linarith))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε_room : ρ + (B + 1) * ε < r₀ := by
    have h : ε * (B + 2) ≤ r₀ - ρ := (le_div_iff₀ (by linarith)).1 (min_le_right _ _)
    nlinarith
  refine ⟨ε, hε, fun z hz σ hσ => ?_⟩
  have hz' : dist z.1 z₀.1 < ε ∧ dist z.2 z₀.2 < ε := by
    rw [mem_ball, Prod.dist_eq] at hz; exact max_lt_iff.1 hz
  have ht : z₀.1 - ε < z.1 := by have := hz'.1; rw [Real.dist_eq, abs_lt] at this; linarith
  have hx : ‖z.2 - x_eq‖ < ρ + ε :=
    calc ‖z.2 - x_eq‖
        ≤ ‖z.2 - z₀.2‖ + ρ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε + ρ := by rw [← dist_eq_norm]; linarith [hz'.2]
      _ = ρ + ε := add_comm _ _
  have hx_r₀ : ‖z.2 - x_eq‖ < r₀ := by nlinarith
  have h_speed := fun {τ₁ τ₂ : ℝ} (h₁ : z.1 ≤ τ₁) (h₂ : z.1 ≤ τ₂) =>
    (hφ z).norm_sub_le (convex_Ici _) (fun _ _ => hf_bdd _ _) h₁ h₂
  rcases le_or_gt 0 z.1 with hz1 | hz1
  · -- From a nonnegative initial time: the estimate itself.
    have h := h_KL z.1 hz1 z.2 (mem_ball_iff_norm.mpr hx_r₀) (φ z) (hφ0 z) (hφ z) (z.1 + σ)
      (by linarith)
    rw [add_sub_cancel_left] at h
    exact h.trans (h_rate _ ⟨norm_nonneg _, hx_r₀.le⟩ σ σ hσ (max_le (by linarith) hσ))
  · -- From a negative initial time `z.1 > -ε`: at time `0` the solution is still in `D₀`.
    have hz1' : -ε < z.1 := by linarith
    have h_y₀ : ‖φ z 0 - x_eq‖ < r₀ :=
      calc ‖φ z 0 - x_eq‖
          ≤ ‖φ z 0 - φ z z.1‖ + ‖z.2 - x_eq‖ := by
            rw [← hφ0 z]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ B * ε + ‖z.2 - x_eq‖ := by
            gcongr
            refine (h_speed le_rfl hz1.le).trans ?_
            gcongr
            rw [abs_le]; constructor <;> linarith
        _ < r₀ := by nlinarith
    rcases le_or_gt 0 (z.1 + σ) with hτ | hτ
    · have h := h_KL 0 le_rfl (φ z 0) (mem_ball_iff_norm.mpr h_y₀) (φ z) rfl
        ((hφ z).mono (Ici_subset_Ici.2 hz1.le)) (z.1 + σ) hτ
      rw [sub_zero] at h
      exact h.trans (h_rate _ ⟨norm_nonneg _, h_y₀.le⟩ σ _ hτ (max_le (by linarith) hτ))
    · -- Before time `0`, within one time unit: the solution has barely moved.
      have hσ1 : σ ≤ 1 := by linarith
      calc ‖φ z (z.1 + σ) - x_eq‖
          ≤ ‖φ z (z.1 + σ) - φ z z.1‖ + ‖z.2 - x_eq‖ := by
            rw [← hφ0 z]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ B * ε + ‖z.2 - x_eq‖ := by
            gcongr
            refine (h_speed le_rfl (by linarith)).trans ?_
            gcongr
            rw [add_sub_cancel_left, abs_of_nonneg hσ]; linarith
        _ ≤ r₀ := by nlinarith
        _ ≤ klRate β r₀ σ := h_rate_one σ hσ1

/-- **`G(β(ρ, ·)²)` is integrable** for `ρ ≤ r₀`, dominated by `G(ĝ²)`. -/
private lemma integrableOn_comp_classKL {a r₀ : ℝ} (β : ClassKL a) (hr₀ : 0 < r₀)
    (hr₀a : r₀ < a) {G : ClassKInfty}
    (hGg_int : IntegrableOn (fun σ => G (klRate β r₀ σ ^ 2)) (Ioi 0)) {ρ : ℝ}
    (hρ : ρ ∈ Icc 0 r₀) :
    IntegrableOn (fun σ => G (β.toFun ρ σ ^ 2)) (Ioi 0) := by
  obtain ⟨-, -, -, -, hĝ_ge, -⟩ := klRate_spec β hr₀ hr₀a
  have hρ_mem : ρ ∈ Ico 0 a := ⟨hρ.1, hρ.2.trans_lt hr₀a⟩
  have hβ_cont : ContinuousOn (fun σ => β.toFun ρ σ) (Ici 0) :=
    β.continuous.comp (continuousOn_const.prodMk continuousOn_id) fun σ hσ => ⟨hρ_mem, hσ⟩
  refine Integrable.mono' hGg_int
    (((G.continuous.comp (hβ_cont.pow 2) fun σ _ => mem_Ici.2 (sq_nonneg _)).mono
      Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun σ hσ => ?_)
  have hσ' : 0 ≤ σ := le_of_lt hσ
  rw [Real.norm_of_nonneg (G.maps_to (mem_Ici.2 (sq_nonneg _)))]
  exact G.mono (sq_nonneg _) (pow_le_pow_left₀ (β.nonneg ρ hρ_mem σ hσ')
    (hĝ_ge ρ hρ σ σ hσ' (max_le (by linarith) hσ')) 2)

/-- **`G(‖φ(t + σ; t, x) - x_eq‖²)` is integrable** for `t ≥ 0` and `x ∈ D₀`, dominated by
`G(β(‖x - x_eq‖, σ)²)` through the class `KL` estimate. -/
private lemma integrableOn_comp_flow {f : ℝ → ℝⁿ → ℝⁿ} {φ : ℝ × ℝⁿ → ℝ → ℝⁿ}
    (hφ0 : ∀ p, φ p p.1 = p.2) (hφ : ∀ p, IsIntegralCurveOn (φ p) f (Ici p.1)) {x_eq : ℝⁿ}
    {a r₀ : ℝ} (β : ClassKL a) (hr₀ : 0 < r₀) (hr₀a : r₀ < a)
    (h_KL : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ ball x_eq r₀, ∀ y : ℝ → ℝⁿ, y t = x →
      IsIntegralCurveOn y f (Ici t) → ∀ τ, t ≤ τ → ‖y τ - x_eq‖ ≤ β.toFun ‖x - x_eq‖ (τ - t))
    {G : ClassKInfty} (hGg_int : IntegrableOn (fun σ => G (klRate β r₀ σ ^ 2)) (Ioi 0))
    {t : ℝ} (ht : 0 ≤ t) {x : ℝⁿ} (hx : x ∈ ball x_eq r₀) :
    IntegrableOn (fun σ => G (‖φ (t, x) (t + σ) - x_eq‖ ^ 2)) (Ioi 0) := by
  have h_cont : ContinuousOn (fun σ => G (‖φ (t, x) (t + σ) - x_eq‖ ^ 2)) (Ioi 0) :=
    G.continuous.comp ((((hφ (t, x)).continuousOn.comp
      (continuousOn_const.add continuousOn_id) fun σ hσ =>
        mem_Ici.2 (le_add_of_nonneg_right (le_of_lt hσ))).sub continuousOn_const).norm.pow 2)
      fun σ _ => mem_Ici.2 (sq_nonneg _)
  refine Integrable.mono' (integrableOn_comp_classKL β hr₀ hr₀a hGg_int
      ⟨norm_nonneg _, (mem_ball_iff_norm.mp hx).le⟩)
    (h_cont.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun σ hσ => ?_)
  have h := h_KL t ht x hx (φ (t, x)) (hφ0 (t, x)) (hφ (t, x)) (t + σ)
    (by linarith [mem_Ioi.1 hσ])
  rw [add_sub_cancel_left] at h
  rw [Real.norm_of_nonneg (G.maps_to (mem_Ici.2 (sq_nonneg _)))]
  exact G.mono (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg _) h 2)

/-- **The gradient rate** `A(ρ, σ) = 2 G'(β(ρ, σ)²) β(ρ, σ) e^{Lσ}`: by the chain rule, the
state derivative of `G(‖φ(t + σ; t, x) - x_eq‖²)` is at most `A(‖x - x_eq‖, σ)`. -/
private noncomputable def gradRate {a : ℝ} (β : ClassKL a) (G' : ClassKInfty) (L : ℝ≥0)
    (ρ σ : ℝ) : ℝ :=
  2 * G' (β.toFun ρ σ ^ 2) * β.toFun ρ σ * Real.exp (L * σ)

/-- For `ρ ≤ r₀`, the gradient rate is nonnegative, dominated by `2ĝ(0) G'(ĝ²) e^{Lσ}`,
continuous, and integrable. -/
private lemma gradRate_spec {a r₀ : ℝ} (β : ClassKL a) (hr₀ : 0 < r₀) (hr₀a : r₀ < a)
    {G' : ClassKInfty} {L : ℝ≥0}
    (hG'g_int : IntegrableOn (fun σ => G' (klRate β r₀ σ ^ 2) * Real.exp (L * σ)) (Ioi 0))
    {ρ : ℝ} (hρ : ρ ∈ Icc 0 r₀) :
    (∀ σ, 0 ≤ σ → 0 ≤ gradRate β G' L ρ σ ∧
      gradRate β G' L ρ σ ≤ 2 * klRate β r₀ 0 * (G' (klRate β r₀ σ ^ 2) * Real.exp (L * σ))) ∧
    ContinuousOn (gradRate β G' L ρ) (Ici 0) ∧ IntegrableOn (gradRate β G' L ρ) (Ioi 0) := by
  obtain ⟨-, -, hĝ_anti, -, hĝ_ge, -⟩ := klRate_spec β hr₀ hr₀a
  have hρ_mem : ρ ∈ Ico 0 a := ⟨hρ.1, hρ.2.trans_lt hr₀a⟩
  have hG'_nonneg : ∀ r, 0 ≤ r → 0 ≤ G' r := fun r hr => G'.maps_to hr
  have hβ_cont : ContinuousOn (fun σ => β.toFun ρ σ) (Ici 0) :=
    β.continuous.comp (continuousOn_const.prodMk continuousOn_id) fun σ hσ => ⟨hρ_mem, hσ⟩
  have h_nonneg : ∀ σ, 0 ≤ σ → 0 ≤ gradRate β G' L ρ σ := fun σ hσ =>
    mul_nonneg (mul_nonneg (mul_nonneg two_pos.le (hG'_nonneg _ (sq_nonneg _)))
      (β.nonneg ρ hρ_mem σ hσ)) (Real.exp_pos _).le
  have h_le : ∀ σ, 0 ≤ σ → gradRate β G' L ρ σ ≤
      2 * klRate β r₀ 0 * (G' (klRate β r₀ σ ^ 2) * Real.exp (L * σ)) := fun σ hσ => by
    have hβ_nonneg := β.nonneg ρ hρ_mem σ hσ
    have hβ : β.toFun ρ σ ≤ klRate β r₀ σ := hĝ_ge ρ hρ σ σ hσ (max_le (by linarith) hσ)
    have hG'β := G'.mono (sq_nonneg _) (pow_le_pow_left₀ hβ_nonneg hβ 2)
    calc gradRate β G' L ρ σ
        ≤ 2 * G' (klRate β r₀ σ ^ 2) * klRate β r₀ 0 * Real.exp (L * σ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hG'β two_pos.le)
            (hβ.trans (hĝ_anti.antitone hσ)) hβ_nonneg
              (mul_nonneg two_pos.le (hG'_nonneg _ (sq_nonneg _)))) (Real.exp_pos _).le
      _ = 2 * klRate β r₀ 0 * (G' (klRate β r₀ σ ^ 2) * Real.exp (L * σ)) := by ring
  have h_cont : ContinuousOn (gradRate β G' L ρ) (Ici 0) :=
    ((continuousOn_const.mul (G'.continuous.comp (hβ_cont.pow 2)
      fun σ _ => mem_Ici.2 (sq_nonneg _))).mul hβ_cont).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  refine ⟨fun σ hσ => ⟨h_nonneg σ hσ, h_le σ hσ⟩, h_cont, ?_⟩
  exact Integrable.mono' (hG'g_int.const_mul (2 * klRate β r₀ 0))
    ((h_cont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun σ hσ => by
      rw [Real.norm_of_nonneg (h_nonneg σ (le_of_lt hσ))]
      exact h_le σ (le_of_lt hσ))

/-- **The gradient bound is class `K`**: `α₄(ρ) = ∫_0^∞ A(ρ, σ) dσ + ρ` is a class `K` function
on `[0, r₀]` dominating `∫_0^∞ A(ρ, σ) dσ`. -/
private lemma exists_classK_ge_integral_gradRate {a r₀ : ℝ} (β : ClassKL a) (hr₀ : 0 < r₀)
    (hr₀a : r₀ < a) {G' : ClassKInfty} {L : ℝ≥0}
    (hG'g_int : IntegrableOn (fun σ => G' (klRate β r₀ σ ^ 2) * Real.exp (L * σ)) (Ioi 0)) :
    ∃ b₄ : ℝ, ∃ α₄ : ClassK r₀ b₄, ∀ ρ ∈ Icc 0 r₀,
      ∫ σ in Ioi 0, gradRate β G' L ρ σ ≤ α₄.toFun ρ := by
  have hIcc_Ico : ∀ ρ ∈ Icc 0 r₀, ρ ∈ Ico 0 a := fun ρ hρ => ⟨hρ.1, hρ.2.trans_lt hr₀a⟩
  have h_spec := fun ρ (hρ : ρ ∈ Icc 0 r₀) => gradRate_spec β hr₀ hr₀a hG'g_int hρ
  have h_mono : ∀ ρ ∈ Icc 0 r₀, ∀ ρ' ∈ Icc 0 r₀, ρ ≤ ρ' → ∀ σ, 0 ≤ σ →
      gradRate β G' L ρ σ ≤ gradRate β G' L ρ' σ := by
    intro ρ hρ ρ' hρ' h σ hσ
    have hβ_nonneg := β.nonneg ρ (hIcc_Ico ρ hρ) σ hσ
    have hβρ := β.mono_r (hIcc_Ico ρ hρ) (hIcc_Ico ρ' hρ') hσ h
    have hG'ρ := G'.mono (sq_nonneg _) (pow_le_pow_left₀ hβ_nonneg hβρ 2)
    exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hG'ρ two_pos.le)
      hβρ hβ_nonneg (mul_nonneg two_pos.le (G'.maps_to (mem_Ici.2 (sq_nonneg _)))))
        (Real.exp_pos _).le
  set α₄f : ℝ → ℝ := fun ρ => (∫ σ in Ioi 0, gradRate β G' L ρ σ) + ρ
  have hα₄_zero : α₄f 0 = 0 := by
    simp only [α₄f, add_zero]
    exact setIntegral_eq_zero_of_forall_eq_zero fun σ hσ => by
      simp [gradRate, β.map_zero_r (le_of_lt hσ)]
  have hα₄_cont : ContinuousOn α₄f (Icc 0 r₀) :=
    (continuousOn_of_dominated
      (bound := fun σ => 2 * klRate β r₀ 0 * (G' (klRate β r₀ σ ^ 2) * Real.exp (L * σ)))
      (fun ρ hρ => (((h_spec ρ hρ).2.1).mono Ioi_subset_Ici_self).aestronglyMeasurable
        measurableSet_Ioi)
      (fun ρ hρ => ae_restrict_of_forall_mem measurableSet_Ioi fun σ hσ => by
        rw [Real.norm_of_nonneg ((h_spec ρ hρ).1 σ (le_of_lt hσ)).1]
        exact ((h_spec ρ hρ).1 σ (le_of_lt hσ)).2) (hG'g_int.const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun σ hσ => by
        have hβr : ContinuousOn (fun ρ => β.toFun ρ σ) (Icc 0 r₀) :=
          (β.continuous_r (le_of_lt hσ)).mono fun ρ hρ => hIcc_Ico ρ hρ
        exact ((continuousOn_const.mul (G'.continuous.comp (hβr.pow 2)
          fun ρ _ => mem_Ici.2 (sq_nonneg _))).mul hβr).mul continuousOn_const)).add
      continuousOn_id
  have hα₄_mono : StrictMonoOn α₄f (Icc 0 r₀) := fun ρ hρ ρ' hρ' h =>
    add_lt_add_of_le_of_lt (setIntegral_mono_on (h_spec ρ hρ).2.2 (h_spec ρ' hρ').2.2
      measurableSet_Ioi fun σ hσ => h_mono ρ hρ ρ' hρ' h.le σ (le_of_lt hσ)) h
  have hα₄_pos : 0 < α₄f r₀ := add_pos_of_nonneg_of_pos
    (setIntegral_nonneg measurableSet_Ioi fun σ hσ =>
      ((h_spec r₀ ⟨hr₀.le, le_rfl⟩).1 σ (le_of_lt hσ)).1) hr₀
  exact ⟨_, ClassK.of_strictMono hr₀ hα₄_pos α₄f hα₄_zero rfl hα₄_cont hα₄_mono,
    fun ρ hρ => le_add_of_nonneg_right hρ.1⟩

/-- **Differentiation under the integral sign.**  At `t ≥ 0` and `x ∈ D₀`,
`(t, x) ↦ ∫_0^∞ G(‖φ(t + σ; t, x) - x_eq‖²) dσ` has a derivative whose state part is at most
`∫_0^∞ A(‖x - x_eq‖, σ) dσ` (`gradRate`).  Near `(t, x)`, solutions obey the rate `ĝ`
(`norm_flow_le_klRate`) and separate at most like `(2B + 1) e^{Lσ}` (`norm_flow_sub_flow_le`),
so the integrands are Lipschitz with the constant `2ĝ(0)(2B + 1) G'(ĝ²) e^{Lσ}`, integrable by
Massera's lemma.  In the state alone they separate like `e^{Lσ}` (`dist_flow_le`). -/
private lemma hasFDerivAt_integral_comp_flow {f : ℝ → ℝⁿ → ℝⁿ}
    (hf : ContDiff ℝ 1 (fun p : ℝ × ℝⁿ => f p.1 p.2)) {L : ℝ≥0}
    (hf_lip : ∀ t, LipschitzWith L (f t)) {B : ℝ} (hf_bdd : ∀ t y, ‖f t y‖ ≤ B)
    {φ : ℝ × ℝⁿ → ℝ → ℝⁿ} (hφ0 : ∀ p, φ p p.1 = p.2)
    (hφ : ∀ p, IsIntegralCurveOn (φ p) f (Ici p.1)) {x_eq : ℝⁿ} {a r₀ : ℝ} (β : ClassKL a)
    (hr₀ : 0 < r₀) (hr₀a : r₀ < a)
    (h_KL : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ ball x_eq r₀, ∀ y : ℝ → ℝⁿ, y t = x →
      IsIntegralCurveOn y f (Ici t) → ∀ τ, t ≤ τ → ‖y τ - x_eq‖ ≤ β.toFun ‖x - x_eq‖ (τ - t))
    {G G' : ClassKInfty} (hG : ∀ r, 0 ≤ r → HasDerivAt G (G' r) r)
    (hGg_int : IntegrableOn (fun σ => G (klRate β r₀ σ ^ 2)) (Ioi 0))
    (hG'g_int : IntegrableOn (fun σ => G' (klRate β r₀ σ ^ 2) * Real.exp (L * σ)) (Ioi 0))
    {t : ℝ} (ht : 0 ≤ t) {x : ℝⁿ} (hx : x ∈ ball x_eq r₀) :
    ∃ V' : (ℝ × ℝⁿ) →L[ℝ] ℝ, HasFDerivAt (Function.uncurry fun t x =>
        ∫ σ in Ioi 0, G (‖φ (t, x) (t + σ) - x_eq‖ ^ 2)) V' (t, x) ∧
      ‖V'.comp (ContinuousLinearMap.inr ℝ ℝ ℝⁿ)‖ ≤
        ∫ σ in Ioi 0, gradRate β G' L ‖x - x_eq‖ σ := by
  set ĝ := klRate β r₀
  obtain ⟨hĝ_pos, -, hĝ_anti, -, -, -⟩ := klRate_spec β hr₀ hr₀a
  have hĝ_le : ∀ σ, 0 ≤ σ → ĝ σ ≤ ĝ 0 := fun σ hσ => hĝ_anti.antitone hσ
  have hG'_nonneg : ∀ r, 0 ≤ r → 0 ≤ G' r := fun r hr => G'.maps_to hr
  -- The derivative of `y ↦ G(‖y - x_eq‖²)`, by the chain rule:
  -- `D(y) = G'(‖y - x_eq‖²) • 2⟪y - x_eq, ·⟫`.
  set D : ℝⁿ → ℝⁿ →L[ℝ] ℝ := fun y => G' (‖y - x_eq‖ ^ 2) • 2 • innerSL ℝ (y - x_eq)
  have hD : ∀ y, HasFDerivAt (fun y => G (‖y - x_eq‖ ^ 2)) (D y) y := fun y =>
    ((hG _ (sq_nonneg _)).comp_hasFDerivAt y
      ((hasFDerivAt_id y).sub_const x_eq).norm_sq).congr_fderiv (by simp [D])
  have hD_cont : Continuous D :=
    (G'.continuous.comp_continuous ((continuous_id.sub continuous_const).norm.pow 2)
      fun y => mem_Ici.2 (sq_nonneg _)).smul
      (((innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)).const_smul 2)
  have hD_norm : ∀ y, ‖D y‖ = 2 * G' (‖y - x_eq‖ ^ 2) * ‖y - x_eq‖ := fun y => by
    rw [norm_smul, RCLike.norm_nsmul ℝ, innerSL_apply_norm,
      Real.norm_of_nonneg (hG'_nonneg _ (sq_nonneg _)), nsmul_eq_mul]
    push_cast
    ring
  -- The integrand `F(z, σ) = G(‖φ(z.1 + σ; z) - x_eq‖²)`.
  set u : ℝ × ℝⁿ → ℝ → ℝⁿ := fun z σ => φ z (z.1 + σ)
  set F : ℝ × ℝⁿ → ℝ → ℝ := fun z σ => G (‖u z σ - x_eq‖ ^ 2)
  have hu_cont : ∀ z, ContinuousOn (u z) (Ici 0) := fun z =>
    (hφ z).continuousOn.comp (continuousOn_const.add continuousOn_id)
      fun σ hσ => mem_Ici.2 (le_add_of_nonneg_right hσ)
  have hF_meas : ∀ z, AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) := fun z =>
    ((G.continuous.comp (((hu_cont z).sub continuousOn_const).norm.pow 2)
      fun σ _ => mem_Ici.2 (sq_nonneg _)).mono Ioi_subset_Ici_self).aestronglyMeasurable
        measurableSet_Ioi
  -- Each integrand is differentiable in the initial data, with derivative continuous in `σ`.
  have h_u_diff : ∀ z₀ σ, 0 ≤ σ →
      HasFDerivAt (fun z => u z σ) (fderiv ℝ (fun z => u z σ) z₀) z₀ := fun z₀ σ hσ => by
    obtain ⟨⟨Φ, -, hΦ⟩, -⟩ := exists_hasFDerivAt_flow hf hφ0 hφ hσ z₀
    exact (hasFDerivAt_snd.comp z₀ (hΦ σ ⟨hσ, le_rfl⟩)).differentiableAt.hasFDerivAt
  set F' : ℝ × ℝⁿ → ℝ → (ℝ × ℝⁿ) →L[ℝ] ℝ := fun z₀ σ =>
    (D (u z₀ σ)).comp (fderiv ℝ (fun z => u z σ) z₀)
  have hF_deriv : ∀ z₀ σ, 0 ≤ σ → HasFDerivAt (fun z => F z σ) (F' z₀ σ) z₀ :=
    fun z₀ σ hσ => HasFDerivAt.comp (g := fun y => G (‖y - x_eq‖ ^ 2)) z₀ (hD (u z₀ σ))
      (h_u_diff z₀ σ hσ)
  have hDu_cont : ∀ z₀, ContinuousOn (fun σ => fderiv ℝ (fun z => u z σ) z₀) (Ioi 0) := by
    intro z₀ σ₀ hσ₀
    obtain ⟨⟨Φ, hΦ_cont, hΦ⟩, -⟩ :=
      exists_hasFDerivAt_flow hf hφ0 hφ (δ := σ₀ + 1) (by linarith [mem_Ioi.1 hσ₀]) z₀
    have h_at : ContinuousAt (fun σ => (ContinuousLinearMap.snd ℝ ℝ ℝⁿ).comp (Φ σ)) σ₀ :=
      (continuousOn_const.clm_comp hΦ_cont).continuousAt (Icc_mem_nhds hσ₀ (lt_add_one σ₀))
    refine (h_at.congr ?_).continuousWithinAt
    filter_upwards [Ioo_mem_nhds hσ₀ (lt_add_one σ₀)] with σ hσ
    exact ((hasFDerivAt_snd.comp z₀ (hΦ σ ⟨hσ.1.le, hσ.2.le⟩)).fderiv).symm
  have hF'_cont : ∀ z₀, ContinuousOn (F' z₀) (Ioi 0) := fun z₀ =>
    (hD_cont.comp_continuousOn ((hu_cont z₀).mono Ioi_subset_Ici_self)).clm_comp (hDu_cont z₀)
  -- Near `(t, x)`, the integrands are Lipschitz with an integrable constant: Massera's bound.
  set bound : ℝ → ℝ := fun σ => 2 * ĝ 0 * (2 * B + 1) * (G' (ĝ σ ^ 2) * Real.exp (L * σ))
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf_bdd 0 0)
  have hbound_nonneg : ∀ σ, 0 ≤ bound σ := fun σ =>
    mul_nonneg (mul_nonneg (mul_nonneg two_pos.le (hĝ_pos 0).le) (by linarith))
      (mul_nonneg (hG'_nonneg _ (sq_nonneg _)) (Real.exp_pos _).le)
  obtain ⟨ε, hε, h_near⟩ := norm_flow_le_klRate hf_bdd hφ0 hφ β hr₀ hr₀a h_KL
    (z₀ := (t, x)) ht hx
  have h_lip : ∀ σ ∈ Ioi (0 : ℝ),
      LipschitzOnWith (Real.nnabs (bound σ)) (fun z => F z σ) (ball (t, x) ε) := by
    intro σ hσ
    have hσ' : 0 ≤ σ := le_of_lt hσ
    refine LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => ?_
    set p := u z σ - x_eq
    set q := u z' σ - x_eq
    have hp : ‖p‖ ≤ ĝ σ := h_near z hz σ hσ'
    have hq : ‖q‖ ≤ ĝ σ := h_near z' hz' σ hσ'
    have hpq : ‖p - q‖ ≤ (2 * B + 1) * Real.exp (L * σ) * dist z z' := by
      rw [sub_sub_sub_cancel_right]
      exact norm_flow_sub_flow_le hf_lip hf_bdd hφ0 hφ z z' hσ'
    rw [Real.coe_nnabs, abs_of_nonneg (hbound_nonneg σ), Real.dist_eq]
    calc |G (‖p‖ ^ 2) - G (‖q‖ ^ 2)|
        ≤ G' (ĝ σ ^ 2) * |‖p‖ ^ 2 - ‖q‖ ^ 2| := by
          -- The mean value bound: on `[0, ĝ(σ)²]`, `G' ≤ G'(ĝ(σ)²)`.
          simpa [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
            (f := G.toFun) (f' := G'.toFun) (s := Icc 0 (ĝ σ ^ 2))
            (fun r hr => (hG r hr.1).hasDerivWithinAt)
            (fun r hr => by
              rw [Real.norm_eq_abs, abs_of_nonneg (G'.maps_to hr.1)]
              exact G'.mono hr.1 hr.2)
            (convex_Icc 0 _) ⟨sq_nonneg ‖q‖, pow_le_pow_left₀ (norm_nonneg _) hq 2⟩
            ⟨sq_nonneg ‖p‖, pow_le_pow_left₀ (norm_nonneg _) hp 2⟩
      _ ≤ G' (ĝ σ ^ 2) * ((‖p‖ + ‖q‖) * ‖p - q‖) :=
          mul_le_mul_of_nonneg_left (abs_norm_sq_sub_norm_sq_le p q)
            (hG'_nonneg _ (sq_nonneg _))
      _ ≤ G' (ĝ σ ^ 2) * ((ĝ 0 + ĝ 0) * ((2 * B + 1) * Real.exp (L * σ) * dist z z')) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (add_le_add (hp.trans (hĝ_le σ hσ'))
            (hq.trans (hĝ_le σ hσ'))) hpq (norm_nonneg _)
              (add_nonneg (hĝ_pos 0).le (hĝ_pos 0).le)) (hG'_nonneg _ (sq_nonneg _))
      _ = bound σ * dist z z' := by simp only [bound]; ring
  obtain ⟨hF'_int, h_deriv⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume.restrict (Ioi 0)) (F := F) (F' := F' (t, x)) (x₀ := (t, x)) (bound := bound)
    (ball_mem_nhds (t, x) hε) (Eventually.of_forall hF_meas)
    (integrableOn_comp_flow hφ0 hφ β hr₀ hr₀a h_KL hGg_int ht hx)
    ((hF'_cont (t, x)).aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi h_lip) (hG'g_int.const_mul _)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun σ hσ => hF_deriv (t, x) σ (le_of_lt hσ))
  refine ⟨_, h_deriv, ?_⟩
  -- The state part: restriction to state directions, as a continuous linear map.
  set Rc : ((ℝ × ℝⁿ) →L[ℝ] ℝ) →L[ℝ] (ℝⁿ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ ℝⁿ (ℝ × ℝⁿ) ℝ).flip (ContinuousLinearMap.inr ℝ ℝ ℝⁿ)
  have hRc : ∀ T, Rc T = T.comp (ContinuousLinearMap.inr ℝ ℝ ℝⁿ) := fun T => rfl
  have h_pt : ∀ σ ∈ Ioi (0 : ℝ), ‖Rc (F' (t, x) σ)‖ ≤ gradRate β G' L ‖x - x_eq‖ σ := by
    intro σ hσ
    have hσ' : 0 ≤ σ := le_of_lt hσ
    -- `y ↦ φ(t + σ; t, y)` is `e^{Lσ}`-Lipschitz (Gronwall).
    have h_lipx : LipschitzWith (Real.toNNReal (Real.exp (L * σ))) (fun y => u (t, y) σ) :=
      LipschitzWith.of_dist_le_mul fun y y' => by
        rw [Real.coe_toNNReal _ (Real.exp_pos _).le, mul_comm]
        exact dist_flow_le hf_lip hφ0 hφ t y y' hσ'
    have h_comp : Rc (F' (t, x) σ) =
        (D (u (t, x) σ)).comp (fderiv ℝ (fun y => u (t, y) σ) x) := by
      rw [hRc]
      simp only [F', ContinuousLinearMap.comp_assoc]
      congr 1
      exact (fderiv_eq_fderiv_uncurry_comp_inr (V := fun t' y => u (t', y) σ)
        (h_u_diff (t, x) σ hσ').differentiableAt).symm
    have hu : ‖u (t, x) σ - x_eq‖ ≤ β.toFun ‖x - x_eq‖ σ := by
      have h := h_KL t ht x hx (φ (t, x)) (hφ0 (t, x)) (hφ (t, x)) (t + σ) (by linarith)
      rwa [add_sub_cancel_left] at h
    have hG'u := G'.mono (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg _) hu 2)
    rw [h_comp]
    calc ‖(D (u (t, x) σ)).comp (fderiv ℝ (fun y => u (t, y) σ) x)‖
        ≤ ‖D (u (t, x) σ)‖ * ‖fderiv ℝ (fun y => u (t, y) σ) x‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (2 * G' (‖u (t, x) σ - x_eq‖ ^ 2) * ‖u (t, x) σ - x_eq‖) * Real.exp (L * σ) := by
          refine mul_le_mul (hD_norm _).le ?_ (norm_nonneg _)
            (mul_nonneg (mul_nonneg two_pos.le (hG'_nonneg _ (sq_nonneg _))) (norm_nonneg _))
          have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) h_lipx
          rwa [Real.coe_toNNReal _ (Real.exp_pos _).le] at h
      _ ≤ gradRate β G' L ‖x - x_eq‖ σ :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hG'u two_pos.le)
            hu (norm_nonneg _) (mul_nonneg two_pos.le (hG'_nonneg _ (sq_nonneg _))))
              (Real.exp_pos _).le
  calc ‖(∫ σ in Ioi 0, F' (t, x) σ).comp (ContinuousLinearMap.inr ℝ ℝ ℝⁿ)‖
      = ‖∫ σ in Ioi 0, Rc (F' (t, x) σ)‖ := by rw [Rc.integral_comp_comm hF'_int, hRc]
    _ ≤ ∫ σ in Ioi 0, gradRate β G' L ‖x - x_eq‖ σ := norm_integral_le_of_norm_le
        (gradRate_spec β hr₀ hr₀a hG'g_int
          ⟨norm_nonneg _, (mem_ball_iff_norm.mp hx).le⟩).2.2
        (ae_restrict_of_forall_mem measurableSet_Ioi h_pt)

/-- **`V` is bounded below** by `G(e^{-2L} ‖x - x_eq‖²)`: solutions decay no faster than
`e^{-Lσ}` (`IsIntegralCurveOn.norm_sub_mul_exp_le`), and `V` is at least its integral over
`(0, 1]`. -/
private lemma le_integral_comp_flow {f : ℝ → ℝⁿ → ℝⁿ} {L : ℝ≥0}
    (hf_lip : ∀ t, LipschitzWith L (f t)) {x_eq : ℝⁿ} (h_eq : ∀ t, f t x_eq = 0)
    {φ : ℝ × ℝⁿ → ℝ → ℝⁿ} (hφ0 : ∀ p, φ p p.1 = p.2)
    (hφ : ∀ p, IsIntegralCurveOn (φ p) f (Ici p.1)) {G : ClassKInfty} {t : ℝ} {x : ℝⁿ}
    (hF_int : IntegrableOn (fun σ => G (‖φ (t, x) (t + σ) - x_eq‖ ^ 2)) (Ioi 0)) :
    G (Real.exp (-(2 * L)) * ‖x - x_eq‖ ^ 2) ≤
      ∫ σ in Ioi 0, G (‖φ (t, x) (t + σ) - x_eq‖ ^ 2) := by
  have h_pt : ∀ σ ∈ Ioc (0 : ℝ) 1,
      G (Real.exp (-(2 * L)) * ‖x - x_eq‖ ^ 2) ≤ G (‖φ (t, x) (t + σ) - x_eq‖ ^ 2) :=
    fun σ hσ => by
      have h := ((hφ (t, x)).mono Icc_subset_Ici_self).norm_sub_mul_exp_le (t := t)
        (τ := t + σ) (by linarith [hσ.1]) (fun τ _ => h_eq τ) (fun τ _ => hf_lip τ)
      rw [show φ (t, x) t = x from hφ0 (t, x), add_sub_cancel_left] at h
      refine G.mono (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) ?_
      calc Real.exp (-(2 * L)) * ‖x - x_eq‖ ^ 2
          ≤ ‖x - x_eq‖ ^ 2 * Real.exp (-(2 * L) * σ) := by
            rw [mul_comm]
            gcongr
            nlinarith [L.coe_nonneg, hσ.2]
        _ = (‖x - x_eq‖ * Real.exp (-(L * σ))) ^ 2 := by
            rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
        _ ≤ ‖φ (t, x) (t + σ) - x_eq‖ ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  calc G (Real.exp (-(2 * L)) * ‖x - x_eq‖ ^ 2)
      = ∫ _σ in Ioc (0 : ℝ) 1, G (Real.exp (-(2 * L)) * ‖x - x_eq‖ ^ 2) := by simp
    _ ≤ ∫ σ in Ioc (0 : ℝ) 1, G (‖φ (t, x) (t + σ) - x_eq‖ ^ 2) :=
        setIntegral_mono_on (continuousOn_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
          (hF_int.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc h_pt
    _ ≤ ∫ σ in Ioi 0, G (‖φ (t, x) (t + σ) - x_eq‖ ^ 2) := setIntegral_mono_set hF_int
        (ae_restrict_of_forall_mem measurableSet_Ioi fun σ _ => G.maps_to (mem_Ici.2 (sq_nonneg _)))
        Ioc_subset_Ioi_self.eventuallyLE

/-- **The derivative of `V` along the system** is `-G(‖x - x_eq‖²)`.  Along the solution from
`(t, x)`, uniqueness gives `V(τ, φ(τ)) = ∫_{τ - t}^∞ w`, with `w(σ) = G(‖φ(t + σ) - x_eq‖²)`
extended continuously to `σ < 0`; its right derivative at `t` is `-w(0)`
(`IsIntegralCurveOn.lieDerivative_eq_of_hasDerivWithinAt`). -/
private lemma lieDerivative_integral_comp_flow {f : ℝ → ℝⁿ → ℝⁿ} {φ : ℝ × ℝⁿ → ℝ → ℝⁿ}
    (hφ0 : ∀ p, φ p p.1 = p.2) (hφ : ∀ p, IsIntegralCurveOn (φ p) f (Ici p.1))
    (hφ_uniq : ∀ p (β : ℝ → ℝⁿ), β p.1 = p.2 → IsIntegralCurveOn β f (Ici p.1) →
      EqOn β (φ p) (Ici p.1))
    {x_eq : ℝⁿ} {G : ClassKInfty} {t : ℝ} {x : ℝⁿ}
    (hF_int : IntegrableOn (fun σ => G (‖φ (t, x) (t + σ) - x_eq‖ ^ 2)) (Ioi 0))
    (h_diff : DifferentiableAt ℝ (Function.uncurry fun t x =>
      ∫ σ in Ioi 0, G (‖φ (t, x) (t + σ) - x_eq‖ ^ 2)) (t, x)) :
    _root_.lieDerivative (fun t x => ∫ σ in Ioi 0, G (‖φ (t, x) (t + σ) - x_eq‖ ^ 2)) f t x =
      -G (‖x - x_eq‖ ^ 2) := by
  set V : ℝ → ℝⁿ → ℝ := fun t x => ∫ σ in Ioi 0, G (‖φ (t, x) (t + σ) - x_eq‖ ^ 2)
  have hy0 : φ (t, x) t = x := hφ0 (t, x)
  set w : ℝ → ℝ := fun σ => G (‖φ (t, x) (t + max σ 0) - x_eq‖ ^ 2)
  have hw : Continuous w := G.continuous.comp_continuous
    ((((hφ (t, x)).continuousOn.comp_continuous
      (continuous_const.add (continuous_id.max continuous_const))
        fun σ => mem_Ici.2 (le_add_of_nonneg_right (le_max_right _ _))).sub
          continuous_const).norm.pow 2) fun σ => mem_Ici.2 (sq_nonneg _)
  have hw_int : IntegrableOn w (Ioi 0) :=
    hF_int.congr_fun (fun σ hσ => by
      change G (‖φ (t, x) (t + σ) - x_eq‖ ^ 2) = G (‖φ (t, x) (t + max σ 0) - x_eq‖ ^ 2)
      rw [max_eq_left (le_of_lt hσ)]) measurableSet_Ioi
  have h_along : ∀ τ ∈ Ici t,
      V τ (φ (t, x) τ) = (∫ s in Ioi 0, w s) - ∫ s in (0 : ℝ)..τ - t, w s := by
    intro τ hτ
    have hτ' : t ≤ τ := hτ
    have h_cocycle : EqOn (φ (t, x)) (φ (τ, φ (t, x) τ)) (Ici τ) :=
      hφ_uniq (τ, φ (t, x) τ) (φ (t, x)) rfl ((hφ (t, x)).mono (Ici_subset_Ici.2 hτ'))
    calc V τ (φ (t, x) τ)
        = ∫ σ in Ioi 0, w (σ + (τ - t)) := setIntegral_congr_fun measurableSet_Ioi
          fun σ hσ => by
            have h1 : t + max (σ + (τ - t)) 0 = τ + σ := by
              rw [max_eq_left (by linarith [mem_Ioi.1 hσ])]; ring
            change G (‖φ (τ, φ (t, x) τ) (τ + σ) - x_eq‖ ^ 2) =
              G (‖φ (t, x) (t + max (σ + (τ - t)) 0) - x_eq‖ ^ 2)
            rw [h1, ← h_cocycle (mem_Ici.2 (le_add_of_nonneg_right (le_of_lt hσ)))]
      _ = ∫ s in Ioi (τ - t), w s := by simpa using setIntegral_Ioi_comp_add_right w 0 (τ - t)
      _ = (∫ s in Ioi 0, w s) - ∫ s in (0 : ℝ)..τ - t, w s := by
          rw [← intervalIntegral.integral_Ioi_sub_Ioi hw_int (sub_nonneg.2 hτ'),
            sub_sub_cancel]
  have h := (hφ (t, x)).lieDerivative_eq_of_eq_add_integral (V := V) (by rw [hy0]; exact h_diff)
    (ψ := fun σ => -w (σ - t)) (by fun_prop) fun τ hτ => by
      rw [h_along τ hτ, intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_right,
        sub_self, sub_eq_add_neg]
  rw [hy0] at h
  rw [h]
  simp [w, hy0]

/-- **The construction for uniform asymptotic stability**, for a `C¹` field, globally Lipschitz in
`x` uniformly in `t` and bounded, whose solutions from `D₀ = B(x_eq, r₀)` at times `t ≥ 0` obey a
class `KL` estimate.  With `G` from Massera's lemma,
`V(t, x) = ∫_0^∞ G(‖φ(t + σ; t, x) - x_eq‖²) dσ` is differentiable on `[0, ∞) × D₀`, vanishes at
`x_eq`, is sandwiched between positive definite functions, decreases at the rate
`G(‖x - x_eq‖²)`, and has gradient bounded by a class `K` function of `‖x - x_eq‖`. -/
private lemma exists_lyapunov_of_KLBoundedOn {f : ℝ → ℝⁿ → ℝⁿ}
    (hf : ContDiff ℝ 1 (fun p : ℝ × ℝⁿ => f p.1 p.2)) {L : ℝ≥0}
    (hf_lip : ∀ t, LipschitzWith L (f t)) {B : ℝ} (hf_bdd : ∀ t y, ‖f t y‖ ≤ B)
    {x_eq : ℝⁿ} (h_eq : ∀ t, f t x_eq = 0) {a r₀ : ℝ} (β : ClassKL a) (hr₀ : 0 < r₀)
    (hr₀a : r₀ < a)
    (h_KL : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ ball x_eq r₀, ∀ y : ℝ → ℝⁿ, y t = x →
      IsIntegralCurveOn y f (Ici t) → ∀ τ, t ≤ τ → ‖y τ - x_eq‖ ≤ β.toFun ‖x - x_eq‖ (τ - t)) :
    ∃ V : ℝ → ℝⁿ → ℝ,
      (∀ t : ℝ, 0 ≤ t → ∀ x ∈ ball x_eq r₀, DifferentiableAt ℝ (Function.uncurry V) (t, x)) ∧
      (∀ t : ℝ, 0 ≤ t → V t x_eq = 0) ∧
      ∃ W₁ W₂ W₃ : ℝⁿ → ℝ, IsPositiveDefiniteOn W₁ x_eq (ball x_eq r₀) ∧
        IsPositiveDefiniteOn W₂ x_eq (ball x_eq r₀) ∧
        IsPositiveDefiniteOn W₃ x_eq (ball x_eq r₀) ∧
        (∀ t : ℝ, 0 ≤ t → ∀ x ∈ ball x_eq r₀, W₁ x ≤ V t x ∧ V t x ≤ W₂ x ∧
          _root_.lieDerivative V f t x ≤ -W₃ x) ∧
        ∃ b₄ : ℝ, ∃ α₄ : ClassK r₀ b₄, ∀ t : ℝ, 0 ≤ t → ∀ x ∈ ball x_eq r₀,
          ‖fderiv ℝ (V t) x‖ ≤ α₄.toFun ‖x - x_eq‖ := by
  have hball_mem : ∀ x ∈ ball x_eq r₀, ‖x - x_eq‖ ∈ Icc 0 r₀ := fun x hx =>
    ⟨norm_nonneg _, (mem_ball_iff_norm.mp hx).le⟩
  have hIcc_Ico : ∀ ρ ∈ Icc 0 r₀, ρ ∈ Ico 0 a := fun ρ hρ => ⟨hρ.1, hρ.2.trans_lt hr₀a⟩
  -- Step 1. Solutions from every initial time and state.
  choose φ hφ0 hφ hφ_uniq using fun p : ℝ × ℝⁿ =>
    exists_isIntegralCurveOn_Ici hf.continuous hf_lip p.1 p.2
  -- Step 2. Massera's lemma for `g = ĝ²` and `h(s) = e^{Ls}`.
  set ĝ := klRate β r₀
  obtain ⟨hĝ_pos, hĝ_cont, hĝ_anti, hĝ_lim, hĝ_ge, -⟩ := klRate_spec β hr₀ hr₀a
  obtain ⟨G, G', hG, k₁, -, k₂, -, hMassera⟩ := ClassKInfty.massera
    (g := fun σ => ĝ σ ^ 2) (h := fun σ => Real.exp (L * σ))
    (fun σ _ => pow_pos (hĝ_pos σ) 2) (hĝ_cont.pow 2).continuousOn
    (fun σ₁ _ σ₂ _ h => pow_lt_pow_left₀ (hĝ_anti h) (hĝ_pos σ₂).le two_ne_zero)
    (by simpa using hĝ_lim.pow 2) (fun σ _ => Real.exp_pos _)
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    (fun σ₁ _ σ₂ _ h => Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h L.coe_nonneg))
  obtain ⟨hGg_int, -, hG'g_int, -⟩ := hMassera (fun σ => ĝ σ ^ 2) (hĝ_cont.pow 2).continuousOn
    fun σ _ => ⟨sq_nonneg _, le_rfl⟩
  -- Step 3. `V(t, x) = ∫_0^∞ G(‖φ(t + σ; t, x) - x_eq‖²) dσ`, finite on `[0, ∞) × D₀`.
  set V : ℝ → ℝⁿ → ℝ := fun t x => ∫ σ in Ioi 0, G (‖φ (t, x) (t + σ) - x_eq‖ ^ 2)
  have hF_int : ∀ t, 0 ≤ t → ∀ x ∈ ball x_eq r₀,
      IntegrableOn (fun σ => G (‖φ (t, x) (t + σ) - x_eq‖ ^ 2)) (Ioi 0) := fun t ht x hx =>
    integrableOn_comp_flow hφ0 hφ β hr₀ hr₀a h_KL hGg_int ht hx
  -- Step 4. `V` is differentiable on `[0, ∞) × D₀`, with the gradient bound
  -- `‖∂V/∂x‖ ≤ ∫_0^∞ A(‖x - x_eq‖, σ) dσ ≤ α₄(‖x - x_eq‖)`.
  have hV_deriv := fun t (ht : 0 ≤ t) x (hx : x ∈ ball x_eq r₀) =>
    hasFDerivAt_integral_comp_flow hf hf_lip hf_bdd hφ0 hφ β hr₀ hr₀a h_KL hG hGg_int
      hG'g_int ht hx
  have hV_diff : ∀ t, 0 ≤ t → ∀ x ∈ ball x_eq r₀,
      DifferentiableAt ℝ (Function.uncurry V) (t, x) := fun t ht x hx =>
    (hV_deriv t ht x hx).choose_spec.1.differentiableAt
  obtain ⟨b₄, α₄, hα₄⟩ := exists_classK_ge_integral_gradRate β hr₀ hr₀a hG'g_int
  have h_grad : ∀ t, 0 ≤ t → ∀ x ∈ ball x_eq r₀, ‖fderiv ℝ (V t) x‖ ≤ α₄.toFun ‖x - x_eq‖ := by
    intro t ht x hx
    obtain ⟨V', hV', hV'_le⟩ := hV_deriv t ht x hx
    rw [fderiv_eq_fderiv_uncurry_comp_inr (V := V) hV'.differentiableAt,
      (hV' : HasFDerivAt (Function.uncurry V) V' (t, x)).fderiv]
    exact hV'_le.trans (hα₄ _ (hball_mem x hx))
  -- Step 5. `V(t, x_eq) = 0`: the solution from `x_eq` stays there.
  have hV_zero : ∀ t, 0 ≤ t → V t x_eq = 0 := fun t _ => by
    have h_const : EqOn (fun _ => x_eq) (φ (t, x_eq)) (Ici t) :=
      hφ_uniq (t, x_eq) (fun _ => x_eq) rfl fun τ _ => by
        simpa [h_eq τ] using hasDerivWithinAt_const τ (Ici t) x_eq
    refine setIntegral_eq_zero_of_forall_eq_zero fun σ hσ => ?_
    change G (‖φ (t, x_eq) (t + σ) - x_eq‖ ^ 2) = 0
    rw [← h_const (mem_Ici.2 (le_add_of_nonneg_right (le_of_lt hσ)))]
    simp [G.map_zero]
  -- Step 6. The bounds: below, solutions decay no faster than `e^{-Lσ}`; above, the class `KL`
  -- estimate.
  set W₁ : ℝⁿ → ℝ := fun x => G (Real.exp (-(2 * L)) * ‖x - x_eq‖ ^ 2)
  have h_lower : ∀ t, 0 ≤ t → ∀ x ∈ ball x_eq r₀, W₁ x ≤ V t x := fun t ht x hx =>
    le_integral_comp_flow hf_lip h_eq hφ0 hφ (hF_int t ht x hx)
  set W₂ : ℝⁿ → ℝ := fun x => ∫ σ in Ioi 0, G (β.toFun ‖x - x_eq‖ σ ^ 2)
  have hGβ_le : ∀ ρ ∈ Icc 0 r₀, ∀ σ, 0 ≤ σ → G (β.toFun ρ σ ^ 2) ≤ G (ĝ σ ^ 2) :=
    fun ρ hρ σ hσ => G.mono (sq_nonneg _) (pow_le_pow_left₀ (β.nonneg ρ (hIcc_Ico ρ hρ) σ hσ)
      (hĝ_ge ρ hρ σ σ hσ (max_le (by linarith) hσ)) 2)
  have h_upper : ∀ t, 0 ≤ t → ∀ x ∈ ball x_eq r₀, V t x ≤ W₂ x := fun t ht x hx =>
    setIntegral_mono_on (hF_int t ht x hx)
      (integrableOn_comp_classKL β hr₀ hr₀a hGg_int (hball_mem x hx)) measurableSet_Ioi
      fun σ hσ => by
        have h := h_KL t ht x hx (φ (t, x)) (hφ0 (t, x)) (hφ (t, x)) (t + σ)
          (by linarith [mem_Ioi.1 hσ])
        rw [add_sub_cancel_left] at h
        exact G.mono (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg _) h 2)
  have hW₁ : IsPositiveDefiniteOn W₁ x_eq (ball x_eq r₀) :=
    G.isPositiveDefiniteOn.comp (IsPositiveDefiniteOn.comp
      (g := fun r => Real.exp (-(2 * L)) * r ^ 2)
      ⟨by fun_prop, by simp, fun r hr hne => by
        have : 0 < r := lt_of_le_of_ne hr (Ne.symm hne)
        positivity⟩
      (isPositiveDefiniteOn_norm_sub x_eq _))
  have hW₂ : IsPositiveDefiniteOn W₂ x_eq (ball x_eq r₀) := by
    refine ⟨continuousOn_of_dominated (bound := fun σ => G (ĝ σ ^ 2))
      (fun x hx => (integrableOn_comp_classKL β hr₀ hr₀a hGg_int
        (hball_mem x hx)).aestronglyMeasurable)
      (fun x hx => ae_restrict_of_forall_mem measurableSet_Ioi fun σ hσ => by
        rw [Real.norm_of_nonneg (G.maps_to (mem_Ici.2 (sq_nonneg _)))]
        exact hGβ_le _ (hball_mem x hx) σ (le_of_lt hσ)) hGg_int
      (ae_restrict_of_forall_mem measurableSet_Ioi fun σ hσ =>
        G.continuous.comp ((((β.continuous_r (le_of_lt hσ)).comp
          (continuous_id.sub continuous_const).norm.continuousOn fun x hx =>
            ⟨norm_nonneg _, (mem_ball_iff_norm.mp hx).trans hr₀a⟩)).pow 2)
          fun x _ => mem_Ici.2 (sq_nonneg _)), ?_, fun x hx hne => ?_⟩
    · exact setIntegral_eq_zero_of_forall_eq_zero fun σ hσ => by
        simp [β.map_zero_r (le_of_lt hσ), G.map_zero]
    · exact (hW₁.2.2 x hx hne).trans_le ((h_lower 0 le_rfl x hx).trans (h_upper 0 le_rfl x hx))
  -- Step 7. Along solutions, `V̇ = -G(‖x - x_eq‖²)`.
  have h_lie : ∀ t, 0 ≤ t → ∀ x ∈ ball x_eq r₀,
      _root_.lieDerivative V f t x = -G (‖x - x_eq‖ ^ 2) := fun t ht x hx =>
    lieDerivative_integral_comp_flow hφ0 hφ hφ_uniq (hF_int t ht x hx) (hV_diff t ht x hx)
  exact ⟨V, hV_diff, hV_zero, W₁, W₂, fun x => G (‖x - x_eq‖ ^ 2), hW₁, hW₂,
    G.isPositiveDefiniteOn.comp (IsPositiveDefiniteOn.comp (g := fun r => r ^ 2)
      ⟨by fun_prop, by simp, fun r hr hne => by
        have : 0 < r := lt_of_le_of_ne hr (Ne.symm hne)
        positivity⟩
      (isPositiveDefiniteOn_norm_sub x_eq _)),
    fun t ht x hx => ⟨h_lower t ht x hx, h_upper t ht x hx, (h_lie t ht x hx).le⟩, _, α₄,
    h_grad⟩

/-- **Converse Lyapunov theorem for uniform asymptotic stability.**  Let `x_eq` be an
equilibrium of `ẋ = f(t, x)` with `f` continuously differentiable and Lipschitz on the ball
`D = B(x_eq, r)`, uniformly in `t`, and let the trajectories from `D₀ = B(x_eq, r₀)` satisfy the
class `KL` estimate `‖x(t) - x_eq‖ ≤ β(‖x(t₀) - x_eq‖, t - t₀)`, with `β(r₀, 0) < r`.  Then
there is a strict uniform Lyapunov function `V` on `D₀` (`IsStrictUniformLyapunovFunction`) and
a class `K` function `α₄` on `[0, r₀)` with `‖∂V/∂x(t, x)‖ ≤ α₄(‖x - x_eq‖)`.

The function is `V(t, x) = ∫_0^∞ G(‖φ(t + σ; t, x) - x_eq‖²) dσ`, with `G` from Massera's lemma
(`ClassKInfty.massera`).  Its bounds `G(e^{-2L}‖x - x_eq‖²) ≤ V ≤ ∫_0^∞ G(β(‖x - x_eq‖, σ)²) dσ`
and `V̇ = -G(‖x - x_eq‖²)` are recorded as the positive definite bounds of the structure, from
which `IsPositiveDefiniteOn.exists_classK_bounds` recovers class `K` bounds.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.16.  Differences:
- The integrand is `G(‖φ - x_eq‖²)` rather than `G(‖φ - x_eq‖)`: the square is smooth at the
  equilibrium, so no separate argument is needed there.
- Massera's lemma is applied to `ĝ(σ)² = (β(r₀, max(σ - 1, 0)) + r₀ e^{1 - σ})²` rather than to
  `β(r₀, σ)`: it is strictly decreasing, and it also dominates solutions started up to one time
  unit before `t = 0`, which differentiability at `t = 0` involves.
- `V` is differentiable rather than continuously differentiable, as in the Lyapunov structures.
- The sandwich and decrease bounds are positive definite functions (the Lyapunov structure)
  rather than class `K` functions of `‖x‖`.
- The bounds hold on the open ball `D₀`, where Khalil writes `‖x‖ ≤ r₀`.
- The hypotheses are asked for every `t ∈ ℝ`, as in
  `exists_quadraticLyapunov_of_exponentialEstimate`.
- The autonomous clause (`V` independent of `t`) is not stated yet. -/
@[blueprint "thm:continuousSystem-exists-lyapunov-of-KLBounded"
  (title := "Converse Lyapunov theorem for uniform asymptotic stability")
  (statement := /-- Let $x_{\mathrm{eq}}$ be an equilibrium of $\dot x = f(t, x)$ on
    $\mathbb{R}^n$, with $f$ continuously differentiable on $\mathbb{R} \times D$,
    $D = \{x : \|x - x_{\mathrm{eq}}\| < r\}$, and $f(t, \cdot)$ Lipschitz on $D$ uniformly in
    $t$.  Let $\beta$ be class $\mathcal{KL}$ (\cref{def:isClassKL}) and $r_0 > 0$ with
    $\beta(r_0, 0) < r$, and let every trajectory starting at $t_0 \ge 0$ in
    $D_0 = \{x : \|x - x_{\mathrm{eq}}\| < r_0\}$ satisfy
    $\|x(t) - x_{\mathrm{eq}}\| \le \beta(\|x(t_0) - x_{\mathrm{eq}}\|, t - t_0)$.  Then there is
    a strict uniform Lyapunov function $V$ on $D_0$
    (\cref{def:continuousSystem-isStrictUniformLyapunovFunction}) and a class $\mathcal{K}$
    function $\alpha_4$ on $[0, r_0)$ (\cref{def:isClassK}) with
    \[
      \Bigl\|\frac{\partial V}{\partial x}(t, x)\Bigr\| \le \alpha_4(\|x - x_{\mathrm{eq}}\|).
    \]

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.16.  Differences: the
    bounds on $V$ and $\dot V$ are positive definite functions rather than class $\mathcal{K}$
    functions of $\|x\|$ (equivalent on compact sub-balls, \cref{thm:lyapunov-class-K-bounds});
    $V$ is differentiable rather than $C^1$; the bounds hold on the open ball $D_0$; the
    hypotheses are asked for all $t \in \mathbb{R}$; the autonomous clause is not stated. -/)
  (proof := /-- Cut the field off outside a ball of radius between $\beta(r_0, 0)$ and $r$, as in
    \cref{thm:continuousSystem-exists-quadraticLyapunov-of-exponentialEstimate}: solutions from
    $D_0$ never see the cut, so they obey the estimate for all time.  Let
    \[
      V(t, x) = \int_0^\infty G(\|\varphi(t + \sigma; t, x) - x_{\mathrm{eq}}\|^2)\,d\sigma,
    \]
    with $G$ from Massera's lemma (\cref{lem:classKInfty-massera}) for
    $g = \hat g^2$, $\hat g(\sigma) = \beta(r_0, \max(\sigma - 1, 0)) + r_0 e^{1 - \sigma}$,
    and $h(\sigma) = e^{L\sigma}$.  Solutions from near $(t, x)$ obey $\hat g$ and separate at
    most like $e^{L\sigma}$, so the integrand is Lipschitz in $(t, x)$ with constant
    $\propto G'(\hat g^2) e^{L\sigma}$, integrable by Massera's lemma; differentiate under the
    integral sign.  The growth bound
    $\|\varphi - x_{\mathrm{eq}}\|^2 \ge e^{-2L\sigma}\|x - x_{\mathrm{eq}}\|^2$ gives
    $V \ge G(e^{-2L}\|x - x_{\mathrm{eq}}\|^2)$; the estimate gives
    $V \le \int_0^\infty G(\beta(\|x - x_{\mathrm{eq}}\|, \sigma)^2)\,d\sigma$; along the
    solution $V = \int_{\tau - t}^\infty G(\cdots)$, so
    $\dot V = -G(\|x - x_{\mathrm{eq}}\|^2)$
    (\cref{lem:isIntegralCurveOn-lieDerivative-eq-of-hasDerivWithinAt}); and Gronwall bounds the
    gradient by
    $\alpha_4(\rho) = \int_0^\infty 2G'(\beta(\rho, \sigma)^2)\beta(\rho, \sigma)e^{L\sigma}
    \,d\sigma + \rho$. -/)]
theorem exists_lyapunov_of_KLBounded {s : ContinuousSystem ℝⁿ Unit Y} {x_eq : ℝⁿ}
    {r r₀ a : ℝ} (h_eq : ∀ t : ℝ, s.F t x_eq () = 0)
    (hf : ContDiffOn ℝ 1 (fun p : ℝ × ℝⁿ => s.F p.1 p.2 ()) (univ ×ˢ ball x_eq r))
    (h_lip : ∃ L : ℝ≥0, ∀ t : ℝ, LipschitzOnWith L (fun x => s.F t x ()) (ball x_eq r))
    (β : ClassKL a) (hr₀ : 0 < r₀) (hr₀a : r₀ < a) (hβr : β.toFun r₀ 0 < r)
    (h_KL : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → ℝⁿ),
      s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < r₀ →
        ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ β.toFun ‖x t₀ - x_eq‖ (t - t₀)) :
    ∃ V : ℝ → ℝⁿ → ℝ, s.IsStrictUniformLyapunovFunction V x_eq (ball x_eq r₀) ∧
      ∃ b₄ : ℝ, ∃ α₄ : ClassK r₀ b₄,
        ∀ t : ℝ, 0 ≤ t → ∀ x ∈ ball x_eq r₀, ‖fderiv ℝ (V t) x‖ ≤ α₄.toFun ‖x - x_eq‖ := by
  obtain ⟨L, hL⟩ := h_lip
  have hr₀_mem : r₀ ∈ Ico 0 a := ⟨hr₀.le, hr₀a⟩
  have hβ_nn : 0 ≤ β.toFun r₀ 0 := β.nonneg r₀ hr₀_mem 0 le_rfl
  -- Step 1. The cut-off field `fχ`, equal to `f` on the ball of radius `ρ₁ ∈ (β(r₀, 0), r)`.
  set ρ₁ := (β.toFun r₀ 0 + r) / 2 with hρ₁_def
  have hβρ₁ : β.toFun r₀ 0 < ρ₁ := by rw [hρ₁_def]; linarith
  obtain ⟨fχ, hfχ, ⟨L', hfχ_lip⟩, hfχ_bdd, hfχ_eq, h_agree⟩ := exists_cutoff (ρ₁ := ρ₁)
    (hβ_nn.trans_lt hβρ₁) (by rw [hρ₁_def]; linarith) h_eq hf hL
  -- Step 2. From `D₀` the estimate stays below `β(r₀, 0) < ρ₁`, so solutions of `fχ` obey it.
  have hE : ∀ x ∈ ball x_eq r₀, ∀ t τ, t ≤ τ → β.toFun ‖x - x_eq‖ (τ - t) < ρ₁ := by
    intro x hx t τ hτ
    have hx_mem : ‖x - x_eq‖ ∈ Ico 0 a :=
      ⟨norm_nonneg _, (mem_ball_iff_norm.mp hx).trans hr₀a⟩
    calc β.toFun ‖x - x_eq‖ (τ - t)
        ≤ β.toFun ‖x - x_eq‖ 0 := β.anti_s_mono hx_mem (mem_Ici.2 le_rfl)
          (mem_Ici.2 (sub_nonneg.2 hτ)) (sub_nonneg.2 hτ)
      _ < β.toFun r₀ 0 := β.strict_mono_r 0 le_rfl hx_mem hr₀_mem (mem_ball_iff_norm.mp hx)
      _ < ρ₁ := hβρ₁
  have h_KL' := estimate_of_cutoff h_agree (E := fun x t τ => β.toFun ‖x - x_eq‖ (τ - t)) hE h_KL
  have h_small : ∀ x ∈ ball x_eq r₀, ‖x - x_eq‖ < ρ₁ := fun x hx => by
    have h := h_KL 0 le_rfl 0 (fun _ => x)
      (fun σ _ => HasFDerivWithinAt.of_subsingleton (subsingleton_Icc_of_ge le_rfl))
      (mem_ball_iff_norm.mp hx) 0 ⟨le_rfl, le_rfl⟩
    exact h.trans_lt (hE x hx 0 0 le_rfl)
  -- Step 3. The construction for the cut-off field; on `D₀` its `V̇` is that of `f`.
  obtain ⟨V, hV_diff, hV_zero, W₁, W₂, W₃, hW₁, hW₂, hW₃, hV, b₄, α₄, h_grad⟩ :=
    exists_lyapunov_of_KLBoundedOn hfχ hfχ_lip hfχ_bdd hfχ_eq β hr₀ hr₀a h_KL'
  have h_lie : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ ball x_eq r₀, s.lieDerivative V t x () ≤ -W₃ x := by
    intro t ht x hx
    change fderiv ℝ (Function.uncurry V) (t, x) (1, s.F t x ()) ≤ _
    rw [← h_agree t x (mem_closedBall_iff_norm.mpr (h_small x hx).le)]
    exact (hV t ht x hx).2.2
  exact ⟨V, ⟨⟨⟨ball_mem_nhds x_eq hr₀, hV_diff, hV_zero,
    ⟨W₁, hW₁, fun t ht x hx => (hV t ht x hx).1⟩,
    fun t ht x hx => (h_lie t ht x hx).trans (neg_nonpos.2 (hW₃.nonneg hx))⟩,
    ⟨W₂, hW₂, fun t ht x hx => (hV t ht x hx).2.1⟩⟩, ⟨W₃, hW₃, h_lie⟩⟩, b₄, α₄, h_grad⟩

end ContinuousSystem

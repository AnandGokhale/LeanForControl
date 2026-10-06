import LeanForControl.Analysis.Continuity
import LeanForControl.Stability.Autonomous
import LeanForControl.Stability.DefsChetaev
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.PicardLindelof
import Architect

/-!
# Chetaev instability on finite forward solution segments

This file develops a generic finite-forward version of Chetaev's instability
method. A smooth cutoff supplies solution segments on arbitrary finite
horizons. The quantitative theorem converts exponential certificate growth
into escape; the boundary-form theorem uses open-set retention and a compact
positive-minimum argument to obtain linear growth and escape.

Reference: Hahn, *Stability of Motion*; Khalil, *Nonlinear Systems*.
-/

open Filter Function Metric Set Topology
open scoped ContDiff NNReal Topology

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace NonlinearInstability

/-- A globally Lipschitz, globally bounded autonomous vector field has a solution
on every prescribed finite forward interval.

Reference: the Picard--Lindelöf theorem. -/
private theorem exists_forward_segment_of_lipschitz_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : E → E) (K L : ℝ≥0)
    (hg_lip : LipschitzWith K g) (hg_bound : ∀ x, ‖g x‖ ≤ L)
    {T : ℝ} (hT : 0 ≤ T) (x₀ : E) :
    ∃ φ : ℝ → E, φ 0 = x₀ ∧
      IsIntegralCurveOn φ (fun _ x => g x) (Icc 0 T) := by
  let t₀ : Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  let Tₙ : ℝ≥0 := ⟨T, hT⟩
  let a : ℝ≥0 := L * Tₙ
  have hpl : IsPicardLindelof (fun _ : ℝ ↦ g) t₀ x₀ a 0 L K := {
    lipschitzOnWith := by
      intro t ht
      exact hg_lip.lipschitzOnWith
    continuousOn := by
      intro x hx
      exact (continuous_const : Continuous (fun _ : ℝ ↦ g x)).continuousOn
    norm_le := by
      intro t ht x hx
      exact hg_bound x
    mul_max_le := by
      change (L : ℝ) * max (T - 0) (0 - 0) ≤ (a : ℝ) - 0
      simp only [sub_zero, max_eq_left hT, a, NNReal.coe_mul]
      change (L : ℝ) * T ≤ (L : ℝ) * T
      exact le_rfl
  }
  obtain ⟨φ, hφ0, hφ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨φ, hφ0, hφ⟩

/-- A `C¹` vector field can be globalized by a smooth bump without changing it
on a prescribed closed ball.  Consequently it has a solution on every finite
horizon whose derivative agrees with the original field whenever the solution
lies in that ball.

Reference: the smooth-cutoff proof of local continuation for ODEs. -/
private theorem exists_cutoff_forward_segment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → E) (hf : ContDiff ℝ 1 f) (x_eq : E)
    {ρ T : ℝ} (hρ : 0 < ρ) (hT : 0 ≤ T) (x₀ : E) :
    ∃ φ : ℝ → E, φ 0 = x₀ ∧ ContinuousOn φ (Icc 0 T) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ‖φ t - x_eq‖ ≤ ρ →
        HasDerivWithinAt φ (f (φ t)) (Icc 0 T) t := by
  let b : ContDiffBump x_eq := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  let g : E → E := fun x ↦ b x • f x
  have hg_c1 : ContDiff ℝ 1 g := by
    exact b.contDiff.smul hf
  have hg_compact : HasCompactSupport g := by
    exact b.hasCompactSupport.smul_right
  obtain ⟨K, hg_lip⟩ := hg_c1.lipschitzWith_of_hasCompactSupport hg_compact (by norm_num)
  obtain ⟨C, hC⟩ := hg_c1.continuous.bounded_above_of_compact_support hg_compact
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hC 0)
  let L : ℝ≥0 := ⟨C, hC0⟩
  obtain ⟨φ, hφ0, hφg⟩ :=
    exists_forward_segment_of_lipschitz_bounded g K L hg_lip
      (fun x ↦ by simpa [L] using hC x) hT x₀
  refine ⟨φ, hφ0, hφg.continuousOn, ?_⟩
  intro t ht hball
  have hb_one : b (φ t) = 1 := by
    apply b.one_of_mem_closedBall
    simpa [Metric.mem_closedBall, dist_eq_norm] using hball
  simpa [g, hb_one] using hφg t ht


/-- A differential Chetaev inequality on one forward segment integrates to an
exponential lower bound at the terminal time.

Reference: the integrating-factor proof of Grönwall's inequality. -/
private theorem exponential_lower_bound_on_forward_segment
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {φ : ℝ → ℝⁿ} {T α : ℝ}
    (hT : 0 ≤ T) (hV : ContDiff ℝ 1 V)
    (hφcont : ContinuousOn φ (Icc (0 : ℝ) T))
    (hφderiv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt φ (f (φ t)) (Icc 0 T) t)
    (hgrowth : ∀ t ∈ Icc (0 : ℝ) T,
      2 * α * V (φ t) ≤ fderiv ℝ V (φ t) (f (φ t))) :
    Real.exp (2 * α * T) * V (φ 0) ≤ V (φ T) := by
  let W : ℝ → ℝ := fun t ↦ Real.exp (-(2 * α) * t) * V (φ t)
  let W' : ℝ → ℝ := fun t ↦
    (Real.exp (-(2 * α) * t) * (-(2 * α))) * V (φ t) +
      Real.exp (-(2 * α) * t) * fderiv ℝ V (φ t) (f (φ t))
  have hWcont : ContinuousOn W (Icc (0 : ℝ) T) := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).continuousOn.mul
        (hV.continuous.comp_continuousOn hφcont)
  have hWderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt W (W' t) t := by
    intro t ht
    have hVφ : HasDerivAt (V ∘ φ) (fderiv ℝ V (φ t) (f (φ t))) t :=
      hasDerivAt_V_comp_traj (hV.differentiable (by norm_num)) hφderiv ht
    have hexp : HasDerivAt (fun s : ℝ ↦ Real.exp (-(2 * α) * s))
        (Real.exp (-(2 * α) * t) * (-(2 * α))) t := by
      simpa only [id, mul_one] using
        ((hasDerivAt_id t).const_mul (-(2 * α))).exp
    simpa [W, W', Function.comp_def] using hexp.mul hVφ
  have hWderiv_nonneg : ∀ t ∈ Ioo (0 : ℝ) T, 0 ≤ W' t := by
    intro t ht
    have hg := hgrowth t (Ioo_subset_Icc_self ht)
    have hepos := Real.exp_pos (-(2 * α) * t)
    dsimp [W']
    nlinarith
  have hWmono : MonotoneOn W (Icc (0 : ℝ) T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hWcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hWderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      simpa [(hWderiv t ht).deriv] using hWderiv_nonneg t ht
  have hWT := hWmono (left_mem_Icc.mpr hT) (right_mem_Icc.mpr hT) hT
  have hWT' : V (φ 0) ≤ Real.exp (-(2 * α) * T) * V (φ T) := by
    simpa [W] using hWT
  have hmul := mul_le_mul_of_nonneg_left hWT'
    (Real.exp_pos (2 * α * T)).le
  calc
    Real.exp (2 * α * T) * V (φ 0) ≤
        Real.exp (2 * α * T) *
          (Real.exp (-(2 * α) * T) * V (φ T)) := hmul
    _ = V (φ T) := by
      rw [← mul_assoc, ← Real.exp_add]
      rw [show 2 * α * T + -(2 * α) * T = 0 by ring]
      simp

/-- A uniform positive Lie-derivative bound on one forward segment gives a
linear lower bound for the certificate at the terminal time. -/
private theorem linear_lower_bound_on_forward_segment
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {φ : ℝ → ℝⁿ} {T gamma : ℝ}
    (hT : 0 ≤ T) (hV : ContDiff ℝ 1 V)
    (hφ : IsIntegralCurveOn φ (fun _ x ↦ f x) (Icc (0 : ℝ) T))
    (hLie : ∀ t ∈ Icc (0 : ℝ) T,
      gamma ≤ fderiv ℝ V (φ t) (f (φ t))) :
    V (φ 0) + gamma * T ≤ V (φ T) := by
  let W : ℝ → ℝ := fun t ↦ V (φ t) - gamma * t
  have hWmono : MonotoneOn W (Icc (0 : ℝ) T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
    · exact (hV.continuous.comp_continuousOn hφ.continuousOn).sub
        (continuous_const.mul continuous_id).continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      have hVφ := hasDerivAt_V_comp_traj (hV.differentiable (by norm_num)) hφ ht
      exact (hVφ.sub ((hasDerivAt_id t).const_mul gamma)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hVφ := hasDerivAt_V_comp_traj (hV.differentiable (by norm_num)) hφ ht
      have hWderiv : HasDerivAt W
          (fderiv ℝ V (φ t) (f (φ t)) - gamma) t := by
        simpa [W, Function.comp_def] using
          hVφ.sub ((hasDerivAt_id t).const_mul gamma)
      rw [hWderiv.deriv]
      have := hLie t (Ioo_subset_Icc_self ht)
      simpa using sub_nonneg.mpr this
  have := hWmono (left_mem_Icc.mpr hT) (right_mem_Icc.mpr hT) hT
  dsimp [W] at this
  linarith

/-- If the exponential lower bound at the terminal time exceeds the quadratic
upper bound on a ball, the segment must leave that ball.

The terminal-time contradiction of the Chetaev argument: exponential growth of `V` eventually
outruns the quadratic ceiling that holds inside the ball. -/
private theorem exists_radius_escape_on_segment
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq x₀ : ℝⁿ}
    {φ : ℝ → ℝⁿ} {T ρ α C : ℝ}
    (hT : 0 ≤ T) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hV : ContDiff ℝ 1 V) (hφ0 : φ 0 = x₀)
    (hφcont : ContinuousOn φ (Icc (0 : ℝ) T))
    (hφderiv : ∀ t ∈ Icc (0 : ℝ) T, ‖φ t - x_eq‖ ≤ ρ →
      HasDerivWithinAt φ (f (φ t)) (Icc 0 T) t)
    (hbound : ∀ x, ‖x - x_eq‖ ≤ ρ → |V x| ≤ C * ‖x - x_eq‖ ^ 2)
    (hgrowth : ∀ x, ‖x - x_eq‖ ≤ ρ →
      2 * α * V x ≤ fderiv ℝ V x (f x))
    (hlarge : C * ρ ^ 2 + 1 ≤ Real.exp (2 * α * T) * V x₀) :
    ∃ t ∈ Icc (0 : ℝ) T, ρ ≤ ‖φ t - x_eq‖ := by
  by_contra hnoexit
  push Not at hnoexit
  have hinside : ∀ t ∈ Icc (0 : ℝ) T, ‖φ t - x_eq‖ ≤ ρ :=
    fun t ht ↦ (hnoexit t ht).le
  have htraj : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt φ (f (φ t)) (Icc 0 T) t :=
    fun t ht ↦ hφderiv t ht (hinside t ht)
  have hscaled := exponential_lower_bound_on_forward_segment hT hV hφcont
    htraj (fun t ht ↦ hgrowth (φ t) (hinside t ht))
  rw [hφ0] at hscaled
  have hTmem : T ∈ Icc (0 : ℝ) T := right_mem_Icc.mpr hT
  have hVT_abs := hbound (φ T) (hinside T hTmem)
  have hnormsq : ‖φ T - x_eq‖ ^ 2 ≤ ρ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) hρ.le).2 (hinside T hTmem)
  have hVT_upper : V (φ T) ≤ C * ρ ^ 2 := by
    calc
      V (φ T) ≤ |V (φ T)| := le_abs_self _
      _ ≤ C * ‖φ T - x_eq‖ ^ 2 := hVT_abs
      _ ≤ C * ρ ^ 2 := mul_le_mul_of_nonneg_left hnormsq hC
  linarith

/-- The smooth-cutoff segment from a positive Chetaev seed reaches the boundary
of the certificate ball on some finite horizon.

The finite-continuation form of the escape argument: the cutoff field is globally Lipschitz, so
the segment extends as far as needed rather than stopping at a blow-up time. -/
private theorem exists_cutoff_segment_reaching_radius
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq x₀ : ℝⁿ}
    (hf : ContDiff ℝ 1 f) (hV : ContDiff ℝ 1 V)
    {ρ α C : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (hC : 0 ≤ C)
    (hVx₀ : 0 < V x₀)
    (hbound : ∀ x, ‖x - x_eq‖ ≤ ρ → |V x| ≤ C * ‖x - x_eq‖ ^ 2)
    (hgrowth : ∀ x, ‖x - x_eq‖ ≤ ρ →
      2 * α * V x ≤ fderiv ℝ V x (f x)) :
    ∃ (T : ℝ) (φ : ℝ → ℝⁿ) (t : ℝ),
      φ 0 = x₀ ∧ ContinuousOn φ (Icc (0 : ℝ) T) ∧
      (∀ s ∈ Icc (0 : ℝ) T, ‖φ s - x_eq‖ ≤ ρ →
        HasDerivWithinAt φ (f (φ s)) (Icc 0 T) s) ∧
      t ∈ Icc (0 : ℝ) T ∧ ρ ≤ ‖φ t - x_eq‖ := by
  have htend : Tendsto (fun t : ℝ ↦ Real.exp (2 * α * t) * V x₀) atTop atTop := by
    exact (Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by positivity))).atTop_mul_const hVx₀
  have heventually_large : ∀ᶠ t : ℝ in atTop,
      C * ρ ^ 2 + 1 ≤ Real.exp (2 * α * t) * V x₀ :=
    tendsto_atTop.1 htend (C * ρ ^ 2 + 1)
  obtain ⟨T, hlarge, hT⟩ :=
    (heventually_large.and (eventually_ge_atTop (1 : ℝ))).exists
  have hT0 : 0 ≤ T := by linarith
  obtain ⟨φ, hφ0, hφcont, hφderiv⟩ :=
    exists_cutoff_forward_segment f hf x_eq hρ hT0 x₀
  obtain ⟨t, ht, hfar⟩ := exists_radius_escape_on_segment hT0 hρ hC hV
    hφ0 hφcont hφderiv hbound hgrowth hlarge
  exact ⟨T, φ, t, hφ0, hφcont, hφderiv, ht, hfar⟩

/-- Cutoff solution segments which start arbitrarily close to the base point
and reach a fixed radius witness forward instability.

The first-exit reduction: a segment of the cutoff field agrees with the original field up to its
first exit from the ball, which is all instability needs. -/
private theorem unstable_of_cutoff_segment_escape
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsegments : ∀ δ > 0, ∃ (T : ℝ) (φ : ℝ → ℝⁿ) (t : ℝ),
      ‖φ 0 - x_eq‖ < min δ ρ ∧
      ContinuousOn φ (Icc (0 : ℝ) T) ∧
      (∀ s ∈ Icc (0 : ℝ) T, ‖φ s - x_eq‖ ≤ ρ →
        HasDerivWithinAt φ (f (φ s)) (Icc 0 T) s) ∧
      t ∈ Icc (0 : ℝ) T ∧ ρ ≤ ‖φ t - x_eq‖) :
    Unstable f x_eq := by
  apply unstable_of_fixed_escape hρ
  intro δ hδ
  obtain ⟨T, φ, t₁, hφ0, hφcont, hφderiv, ht₁, hfar⟩ := hsegments δ hδ
  have hφ0δ : ‖φ 0 - x_eq‖ < δ := hφ0.trans_le (min_le_left _ _)
  have hφ0ρ : ‖φ 0 - x_eq‖ < ρ := hφ0.trans_le (min_le_right _ _)
  obtain ⟨τ, hτT, hτeq, hstay⟩ :=
    exists_first_sphere_hit hφcont hφ0ρ ht₁ hfar
  have hφf : IsTrajectoryOn φ f 0 τ := by
    intro t ht
    exact (hφderiv t ⟨ht.1, ht.2.trans hτT.2⟩ (hstay t ht)).mono
      (Icc_subset_Icc_right hτT.2)
  exact ⟨τ, φ, τ, hφf, hφ0δ, ⟨hτT.1, le_rfl⟩, hτeq.ge⟩

private theorem exists_frontier_hit_on_interval
    {E : Type*} [TopologicalSpace E]
    {D : Set E} (hD : IsOpen D) {φ : ℝ → E} {t₀ t₁ : ℝ}
    (hφ : ContinuousOn φ (Icc t₀ t₁))
    (hstart : φ t₀ ∈ D) (hend : φ t₁ ∉ D) (ht : t₀ ≤ t₁) :
    ∃ t ∈ Icc t₀ t₁, φ t ∈ frontier D := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  let S : Set E := φ '' Icc t₀ t₁
  have hS : IsPreconnected S := isPreconnected_Icc.image φ hφ
  have hSD : (S ∩ D).Nonempty :=
    ⟨φ t₀, ⟨t₀, left_mem_Icc.mpr ht, rfl⟩, hstart⟩
  have hcl : closure D ∩ S ⊆ D := by
    intro x hx
    have hxnot : x ∉ frontier D := by
      rintro hxf
      obtain ⟨t, htI, rfl⟩ := hx.2
      exact hno t htI hxf
    rw [frontier, mem_diff] at hxnot
    simp only [not_and, not_not] at hxnot
    exact interior_subset (hxnot hx.1)
  have hall : S ⊆ D := hS.subset_of_closure_inter_subset hD hSD hcl
  exact hend (hall ⟨t₁, right_mem_Icc.mpr ht, rfl⟩)

private theorem exists_first_exit_open
    {E : Type*} [TopologicalSpace E]
    {D : Set E} (hD : IsOpen D) {φ : ℝ → E} {t₀ T t₁ : ℝ}
    (hφ : ContinuousOn φ (Icc t₀ T))
    (hstart : φ t₀ ∈ D) (ht₁ : t₁ ∈ Icc t₀ T) (hend : φ t₁ ∉ D) :
    ∃ τ ∈ Icc t₀ t₁, φ τ ∈ frontier D ∧
      ∀ s ∈ Ico t₀ τ, φ s ∈ D := by
  let S : Set ℝ := Icc t₀ t₁ ∩ φ ⁻¹' Dᶜ
  have hφ' : ContinuousOn φ (Icc t₀ t₁) :=
    hφ.mono (Icc_subset_Icc_right ht₁.2)
  have hSclosed : IsClosed S :=
    hφ'.preimage_isClosed_of_isClosed isClosed_Icc hD.isClosed_compl
  have hScompact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hSclosed inter_subset_left
  have hSne : S.Nonempty := ⟨t₁, ⟨⟨ht₁.1, le_rfl⟩, hend⟩⟩
  obtain ⟨τ, hτS, hτmin⟩ := hScompact.exists_isMinOn hSne continuousOn_id
  have hτI : τ ∈ Icc t₀ t₁ := hτS.1
  have hτout : φ τ ∉ D := hτS.2
  have hstay : ∀ s ∈ Ico t₀ τ, φ s ∈ D := by
    intro s hs
    by_contra hsout
    have hsS : s ∈ S := ⟨⟨hs.1, hs.2.le.trans hτI.2⟩, hsout⟩
    exact (not_le_of_gt hs.2) (hτmin hsS)
  obtain ⟨q, hqI, hqfront⟩ :=
    exists_frontier_hit_on_interval hD
      (hφ'.mono (Icc_subset_Icc_right hτI.2)) hstart hτout hτI.1
  have hqout : φ q ∉ D := by
    intro hqD
    have hdj : Disjoint D (frontier D) :=
      Set.disjoint_iff_inter_eq_empty.mpr hD.inter_frontier_eq
    exact Set.disjoint_left.1 hdj hqD hqfront
  have hqS : q ∈ S := ⟨⟨hqI.1, hqI.2.trans hτI.2⟩, hqout⟩
  have heq : q = τ := le_antisymm hqI.2 (hτmin hqS)
  exact ⟨τ, hτI, heq ▸ hqfront, hstay⟩

private theorem open_retention_of_deriv_nonneg
    {E : Type*} [TopologicalSpace E]
    {D : Set E} (hD : IsOpen D) {V : E → ℝ} {φ : ℝ → E} {t₀ T : ℝ}
    (hφ : ContinuousOn φ (Icc t₀ T))
    (hVφ : ContinuousOn (V ∘ φ) (Icc t₀ T))
    (hstart : φ t₀ ∈ D) (hVstart : 0 < V (φ t₀))
    (hfrontier : ∀ t ∈ Icc t₀ T, φ t ∈ frontier D → V (φ t) = 0)
    (hderiv : ∀ t ∈ Ioo t₀ T, φ t ∈ D →
      ∃ d : ℝ, HasDerivAt (V ∘ φ) d t ∧ 0 ≤ d) :
    ∀ t ∈ Icc t₀ T, φ t ∈ D := by
  intro t htI
  by_contra hout
  obtain ⟨τ, hτI, hτfront, hstay⟩ :=
    exists_first_exit_open hD hφ hstart htI hout
  have hmono : MonotoneOn (V ∘ φ) (Icc t₀ τ) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc t₀ τ)
      (hVφ.mono (Icc_subset_Icc_right (hτI.2.trans htI.2)))
    · intro s hs
      rw [interior_Icc] at hs
      obtain ⟨d, hd, _⟩ := hderiv s
        ⟨hs.1, hs.2.trans_le (hτI.2.trans htI.2)⟩ (hstay s ⟨hs.1.le, hs.2⟩)
      exact hd.differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      obtain ⟨d, hd, hd0⟩ := hderiv s
        ⟨hs.1, hs.2.trans_le (hτI.2.trans htI.2)⟩ (hstay s ⟨hs.1.le, hs.2⟩)
      simpa [hd.deriv] using hd0
  have hle : V (φ t₀) ≤ V (φ τ) :=
    hmono (left_mem_Icc.mpr hτI.1) (right_mem_Icc.mpr hτI.1) hτI.1
  rw [hfrontier τ ⟨hτI.1, hτI.2.trans htI.2⟩ hτfront] at hle
  linarith

/-- A seed with positive certificate value reaches the certificate sphere.

Boundary vanishing retains the solution in `D`. On the compact retained
superlevel set inside the closed ball, the Lie derivative is strictly positive
and hence has a positive minimum. -/
private theorem exists_cutoff_segment_reaching_radius_of_geometric_chetaev
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq x₀ : ℝⁿ} {D : Set ℝⁿ}
    (hf : ContDiff ℝ 1 f) (hV : ContDiff ℝ 1 V) (hD : IsOpen D)
    {rho : ℝ} (hrho : 0 < rho) (hx₀D : x₀ ∈ D) (hx₀rho : ‖x₀ - x_eq‖ < rho)
    (hVx₀ : 0 < V x₀)
    (hboundary : ∀ x ∈ frontier D, ‖x - x_eq‖ ≤ rho → V x = 0)
    (hLie_pos : ∀ x ∈ D, ‖x - x_eq‖ ≤ rho →
      0 < fderiv ℝ V x (f x)) :
    ∃ (T : ℝ) (φ : ℝ → ℝⁿ) (t : ℝ),
      φ 0 = x₀ ∧ ContinuousOn φ (Icc (0 : ℝ) T) ∧
      (∀ s ∈ Icc (0 : ℝ) T, ‖φ s - x_eq‖ ≤ rho →
        HasDerivWithinAt φ (f (φ s)) (Icc 0 T) s) ∧
      t ∈ Icc (0 : ℝ) T ∧ rho ≤ ‖φ t - x_eq‖ := by
  let L : ℝⁿ → ℝ := fun x ↦ fderiv ℝ V x (f x)
  let K : Set ℝⁿ := closure D ∩ closedBall x_eq rho ∩ {x | V x₀ ≤ V x}
  have hKcompact : IsCompact K := by
    exact ((isCompact_closedBall x_eq rho).inter_left isClosed_closure).inter_right
      (isClosed_le continuous_const hV.continuous)
  have hx₀K : x₀ ∈ K := by
    refine ⟨⟨subset_closure hx₀D,
      by simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hx₀rho.le⟩, ?_⟩
    exact (show V x₀ ≤ V x₀ from le_rfl)
  have hKsubD : K ⊆ D := by
    intro x hx
    by_contra hxD
    have hxfront : x ∈ frontier D := by
      rw [frontier, mem_diff]
      exact ⟨hx.1.1, fun hxint ↦ hxD (interior_subset hxint)⟩
    have hxzero : V x = 0 := hboundary x hxfront (by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hx.1.2)
    have hle : V x₀ ≤ V x := hx.2
    rw [hxzero] at hle
    linarith
  have hLcont : Continuous L := by
    exact (hV.continuous_fderiv (by norm_num)).clm_apply hf.continuous
  obtain ⟨x_min, hx_min_K, hx_min⟩ :=
    hKcompact.exists_isMinOn ⟨x₀, hx₀K⟩ hLcont.continuousOn
  let gamma : ℝ := L x_min
  have hgamma : 0 < gamma := by
    apply hLie_pos x_min (hKsubD hx_min_K)
    simpa [K, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hx_min_K.1.2
  obtain ⟨x_max, hx_max_ball, hx_max⟩ :=
    (isCompact_closedBall x_eq rho).exists_isMaxOn
      ⟨x_eq, Metric.mem_closedBall_self hrho.le⟩ hV.continuous.continuousOn
  let T : ℝ := (V x_max - V x₀ + 1) / gamma
  have hx₀_ball : x₀ ∈ closedBall x_eq rho := hx₀K.1.2
  have hnum : 0 < V x_max - V x₀ + 1 := by
    have := hx_max hx₀_ball
    change V x₀ ≤ V x_max at this
    linarith
  have hT : 0 ≤ T := (div_pos hnum hgamma).le
  obtain ⟨φ, hφ0, hφcont, hφderiv⟩ :=
    exists_cutoff_forward_segment f hf x_eq hrho hT x₀
  by_cases hexit : ∃ t ∈ Icc (0 : ℝ) T, rho ≤ ‖φ t - x_eq‖
  · obtain ⟨t, ht, hfar⟩ := hexit
    exact ⟨T, φ, t, hφ0, hφcont, hφderiv, ht, hfar⟩
  · push Not at hexit
    have hinside : ∀ t ∈ Icc (0 : ℝ) T, ‖φ t - x_eq‖ ≤ rho :=
      fun t ht ↦ (hexit t ht).le
    have htraj : IsIntegralCurveOn φ (fun _ x ↦ f x) (Icc (0 : ℝ) T) :=
      fun t ht ↦ hφderiv t ht (hinside t ht)
    have hstayD : ∀ t ∈ Icc (0 : ℝ) T, φ t ∈ D := by
      apply open_retention_of_deriv_nonneg hD hφcont
        (hV.continuous.comp_continuousOn hφcont) (by simpa [hφ0] using hx₀D)
        (by simpa [hφ0] using hVx₀)
      · intro t ht htfront
        exact hboundary (φ t) htfront (hinside t ht)
      · intro t ht htD
        have hd := hasDerivAt_V_comp_traj (hV.differentiable (by norm_num)) htraj ht
        exact ⟨_, hd, (hLie_pos (φ t) htD (hinside t (Ioo_subset_Icc_self ht))).le⟩
    have hVge : ∀ t ∈ Icc (0 : ℝ) T, V x₀ ≤ V (φ t) := by
      intro t ht
      have hlin := linear_lower_bound_on_forward_segment ht.1 hV
        (htraj.mono (Icc_subset_Icc_right ht.2))
        (fun s hs ↦ (hLie_pos (φ s) (hstayD s ⟨hs.1, hs.2.trans ht.2⟩)
          (hinside s ⟨hs.1, hs.2.trans ht.2⟩)).le)
      rw [hφ0] at hlin
      simpa using hlin
    have hmemK : ∀ t ∈ Icc (0 : ℝ) T, φ t ∈ K := by
      intro t ht
      exact ⟨⟨subset_closure (hstayD t ht),
        by simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hinside t ht⟩,
          hVge t ht⟩
    have hLie_gamma : ∀ t ∈ Icc (0 : ℝ) T,
        gamma ≤ fderiv ℝ V (φ t) (f (φ t)) := by
      intro t ht
      exact hx_min (hmemK t ht)
    have hlin := linear_lower_bound_on_forward_segment hT hV htraj hLie_gamma
    rw [hφ0] at hlin
    have hVTmax : V (φ T) ≤ V x_max :=
      hx_max (hmemK T (right_mem_Icc.mpr hT)).1.2
    have hgammaT : gamma * T = V x_max - V x₀ + 1 := by
      dsimp [T]
      field_simp
    linarith

/-- A Chetaev certificate on a fixed closed ball forces forward instability.

The frontier hypothesis produces positive seeds arbitrarily close to the base point.  A smooth
cutoff supplies a solution on a sufficiently long finite interval.  Boundary vanishing prevents
the solution from leaving the positive region before it reaches the certificate sphere, while
compactness bounds the strictly positive Lie derivative away from zero on the retained
superlevel set.

Reference: Khalil, *Nonlinear Systems*, 3rd ed. (Prentice Hall, 2002), Theorem 4.3,
p. 125 (Chetaev's instability theorem).  This boundary formulation follows the same
positive-superlevel escape argument, with an independently supplied open region instead of
the full positive set in a ball.  Here `f` and `V` are globally `C¹`, while sign and boundary
conditions are local to the closed ball.  The conclusion negates stability over all finite
forward segments; unlike Khalil's equilibrium theorem, no `f x_eq = 0` is assumed. -/
@[blueprint "thm:geometric-chetaev-unstable"
  (title := "Boundary-form Chetaev instability criterion")
  (statement := /-- Let $V$ be a Chetaev certificate on a fixed closed ball, with an open
    positive region whose frontier contains the base point. The certificate function and
    vector field are globally $C^1$, but sign and boundary conditions apply only in the ball.
    Then the base point is unstable with respect to all finite forward solution segments.
    No equilibrium hypothesis $f(x_{\rm eq})=0$ is assumed.

    Reference: Khalil, \emph{Nonlinear Systems}, 3rd ed. (Prentice Hall, 2002),
    Theorem 4.3, p. 125. This is a boundary formulation of Chetaev's escape argument,
    not a literal transcription: the textbook uses the full positive set in a ball
    and states instability of an equilibrium. -/)
  (proof := /-- Choose a positive seed near the frontier point.  Globalize the vector field by
    a smooth cutoff. Boundary vanishing retains the solution in the certificate region; on the
    compact retained superlevel set the positive Lie derivative has a positive minimum, forcing
    linear growth until the solution crosses the fixed certificate sphere. -/)]
theorem unstable_of_geometric_chetaev
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ} {rho : ℝ}
    (hf : ContDiff ℝ 1 f) (hC : IsChetaevFunction f V x_eq D rho) :
    Unstable f x_eq := by
  apply unstable_of_cutoff_segment_escape hC.hradius
  intro delta hdelta
  have hmin : 0 < min delta rho := lt_min hdelta hC.hradius
  obtain ⟨x₀, hx₀D, hdist⟩ :=
    Metric.mem_closure_iff.mp (frontier_subset_closure hC.hfrontier)
      (min delta rho) hmin
  have hx₀rho : ‖x₀ - x_eq‖ < rho := by
    rw [dist_eq_norm] at hdist
    exact (norm_sub_rev x_eq x₀ ▸ hdist).trans_le (min_le_right _ _)
  have hVx₀ : 0 < V x₀ := hC.hpos x₀ hx₀D hx₀rho.le
  obtain ⟨T, φ, t, hφ0, hφcont, hφderiv, ht, hfar⟩ :=
    exists_cutoff_segment_reaching_radius_of_geometric_chetaev hf hC.hV_c1
      hC.hD_open hC.hradius hx₀D hx₀rho hVx₀ hC.hboundary_zero hC.hLie_pos
  refine ⟨T, φ, t, ?_, hφcont, hφderiv, ht, hfar⟩
  rw [hφ0]
  rw [dist_eq_norm] at hdist
  simpa [norm_sub_rev] using hdist

/-- An exponentially increasing Chetaev function forces forward instability.

The `hseed` condition says that the positive set of `V` accumulates at the
base point.  The proof globalizes the vector field with a smooth cutoff,
follows the resulting solution to its first sphere crossing, and applies the
differential inequality to rule out remaining inside the sphere forever.

Reference: Khalil, *Nonlinear Systems*, 3rd ed. (Prentice Hall, 2002), Theorem 4.3,
p. 125, for Chetaev's instability method.  This quantitative variant uses a quadratic
bound and exponential Lie-derivative inequality instead of the textbook hypotheses;
it assumes global `C¹` regularity and concludes finite-segment instability of a base point
without an equilibrium hypothesis. It is not the statement of Theorem 4.3. -/
@[blueprint "thm:exponential-chetaev-unstable"
  (title := "Exponential Chetaev instability criterion")
  (statement := /-- Suppose the vector field $f$ and certificate $V$ are $C^1$,
    $V$ is quadratically bounded on a ball, its positive set accumulates at the
    base point, and its Lie derivative satisfies $\dot V\geq 2\alpha V$ there
    for some $\alpha>0$.
    Then the base point is unstable with respect to finite forward solution
    segments.

    Reference: Khalil, \emph{Nonlinear Systems}, 3rd ed. (Prentice Hall, 2002),
    Theorem 4.3, p. 125, for Chetaev's instability method. This is a quantitative variant,
    not the textbook statement. Regularity is global, the inequalities are local to the
    ball, and no equilibrium hypothesis is assumed.
  -/)
  (proof := /-- Globalize the vector field by a smooth cutoff, integrate the
    differential inequality on a sufficiently long finite segment, and stop
    the curve at its first crossing of the certificate ball. -/)]
theorem unstable_of_exponential_chetaev
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hf : ContDiff ℝ 1 f) (hV : ContDiff ℝ 1 V)
    {ρ α C : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖x - x_eq‖ ≤ ρ →
      |V x| ≤ C * ‖x - x_eq‖ ^ 2)
    (hgrowth : ∀ x, ‖x - x_eq‖ ≤ ρ →
      2 * α * V x ≤ fderiv ℝ V x (f x))
    (hseed : ∀ δ > 0, ∃ x, ‖x - x_eq‖ < min δ ρ ∧ 0 < V x) :
    Unstable f x_eq := by
  apply unstable_of_cutoff_segment_escape hρ
  intro δ hδ
  obtain ⟨x₀, hx₀, hVx₀⟩ := hseed δ hδ
  obtain ⟨T, φ, t₁, hφ0, hφcont, hφderiv, ht₁, hfar⟩ :=
    exists_cutoff_segment_reaching_radius hf hV hρ hα hC hVx₀ hbound hgrowth
  exact ⟨T, φ, t₁, by simpa [hφ0] using hx₀,
    hφcont, hφderiv, ht₁, hfar⟩

end NonlinearInstability

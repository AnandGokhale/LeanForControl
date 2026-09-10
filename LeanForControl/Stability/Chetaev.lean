import LeanForControl.Stability.Forward
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.PicardLindelof
import Architect

/-!
# Chetaev instability on finite forward solution segments

This file develops a generic finite-forward version of Chetaev's instability
method.  A smooth cutoff supplies solution segments on arbitrary finite
horizons, and a first-exit argument converts exponential growth of a scalar
certificate into forward instability.

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
      IsIntegralCurveOn φ (fun _ x ↦ g x) (Icc 0 T) := by
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

/-- A continuous curve that starts strictly inside a ball and later reaches its
complement has a first hitting time of the sphere.  Before that time it stays in
the closed ball.

Original: first-exit infrastructure for finite forward solution segments. -/
private theorem exists_first_sphere_hit
    {E : Type*} [NormedAddCommGroup E]
    {x_eq : E} {φ : ℝ → E} {ρ T t₁ : ℝ}
    (hφ : ContinuousOn φ (Icc 0 T))
    (h₀ : ‖φ 0 - x_eq‖ < ρ) (ht₁ : t₁ ∈ Icc (0 : ℝ) T)
    (hfar : ρ ≤ ‖φ t₁ - x_eq‖) :
    ∃ τ ∈ Icc (0 : ℝ) T, ‖φ τ - x_eq‖ = ρ ∧
      ∀ s ∈ Icc (0 : ℝ) τ, ‖φ s - x_eq‖ ≤ ρ := by
  let d : ℝ → ℝ := fun t ↦ ‖φ t - x_eq‖
  have hd : ContinuousOn d (Icc (0 : ℝ) T) :=
    continuous_norm.comp_continuousOn (hφ.sub continuousOn_const)
  have hd₁ : ContinuousOn d (Icc (0 : ℝ) t₁) := by
    exact hd.mono (Icc_subset_Icc_right ht₁.2)
  have hhit : ∃ s ∈ Icc (0 : ℝ) T, d s = ρ := by
    have hρmem : ρ ∈ Icc (d 0) (d t₁) := ⟨h₀.le, hfar⟩
    obtain ⟨s, hs, hsρ⟩ := (intermediate_value_Icc ht₁.1 hd₁) hρmem
    exact ⟨s, ⟨hs.1, hs.2.trans ht₁.2⟩, hsρ⟩
  let S : Set ℝ := Icc (0 : ℝ) T ∩ d ⁻¹' {ρ}
  have hS_closed : IsClosed S := by
    exact hd.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hS_compact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hS_closed inter_subset_left
  have hS_nonempty : S.Nonempty := by
    obtain ⟨s, hs, hsρ⟩ := hhit
    exact ⟨s, hs, hsρ⟩
  obtain ⟨τ, hτS, hτmin⟩ :=
    hS_compact.exists_isMinOn hS_nonempty continuousOn_id
  have hτIcc : τ ∈ Icc (0 : ℝ) T := hτS.1
  have hτeq : d τ = ρ := hτS.2
  refine ⟨τ, hτIcc, hτeq, ?_⟩
  intro s hs
  by_contra hnot
  have hρs : ρ < d s := lt_of_not_ge hnot
  have hslt : s < τ := by
    exact hs.2.lt_of_ne (fun h ↦ by subst s; exact (ne_of_lt hρs) hτeq.symm)
  have hds : ContinuousOn d (Icc (0 : ℝ) s) := by
    apply hd.mono
    intro q hq
    exact ⟨hq.1, hq.2.trans (hs.2.trans hτIcc.2)⟩
  have hρmem : ρ ∈ Icc (d 0) (d s) := ⟨h₀.le, hρs.le⟩
  obtain ⟨q, hq, hqρ⟩ := (intermediate_value_Icc hs.1 hds) hρmem
  have hqS : q ∈ S := by
    exact ⟨⟨hq.1, hq.2.trans (hs.2.trans hτIcc.2)⟩, hqρ⟩
  have hτq : τ ≤ q := hτmin hqS
  exact (not_lt_of_ge (hτq.trans hq.2)) hslt

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
    have hφt : HasDerivAt φ (f (φ t)) t :=
      (hφderiv t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
    have hVφ : HasDerivAt (V ∘ φ) (fderiv ℝ V (φ t) (f (φ t))) t := by
      exact (hV.differentiable (by norm_num) (φ t)).hasFDerivAt
        |>.comp_hasDerivAt t hφt
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

/-- If the exponential lower bound at the terminal time exceeds the quadratic
upper bound on a ball, the segment must leave that ball.

Original: terminal-time contradiction in the Chetaev argument. -/
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

Original: finite-continuation form of the Chetaev escape argument. -/
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

/-- Cutoff solution segments which start arbitrarily close to the equilibrium
and reach a fixed radius witness forward instability.

Original: first-exit reduction for locally valid differential equations. -/
private theorem forwardUnstable_of_cutoff_segment_escape
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsegments : ∀ δ > 0, ∃ (T : ℝ) (φ : ℝ → ℝⁿ) (t : ℝ),
      ‖φ 0 - x_eq‖ < min δ ρ ∧
      ContinuousOn φ (Icc (0 : ℝ) T) ∧
      (∀ s ∈ Icc (0 : ℝ) T, ‖φ s - x_eq‖ ≤ ρ →
        HasDerivWithinAt φ (f (φ s)) (Icc 0 T) s) ∧
      t ∈ Icc (0 : ℝ) T ∧ ρ ≤ ‖φ t - x_eq‖) :
    ForwardUnstable f x_eq := by
  apply forwardUnstable_of_fixed_escape hρ
  intro δ hδ
  obtain ⟨T, φ, t₁, hφ0, hφcont, hφderiv, ht₁, hfar⟩ := hsegments δ hδ
  have hφ0δ : ‖φ 0 - x_eq‖ < δ := hφ0.trans_le (min_le_left _ _)
  have hφ0ρ : ‖φ 0 - x_eq‖ < ρ := hφ0.trans_le (min_le_right _ _)
  obtain ⟨τ, hτT, hτeq, hstay⟩ :=
    exists_first_sphere_hit hφcont hφ0ρ ht₁ hfar
  have hφf : IsForwardTrajectoryOn φ f τ := by
    refine ⟨hτT.1, ?_⟩
    intro t ht
    exact (hφderiv t ⟨ht.1, ht.2.trans hτT.2⟩ (hstay t ht)).mono
      (Icc_subset_Icc_right hτT.2)
  exact ⟨τ, φ, τ, hφf, hφ0δ, ⟨hτT.1, le_rfl⟩, hτeq.ge⟩

/-- An exponentially increasing Chetaev function forces forward instability.

The `hseed` condition says that the positive cone of `V` accumulates at the
base point.  The proof globalizes the vector field with a smooth cutoff,
follows the resulting solution to its first sphere crossing, and applies the
differential inequality to rule out remaining inside the sphere forever.

Reference: Hahn, *Stability of Motion* (Chetaev's instability method). -/
@[blueprint "thm:exponential-chetaev-forward-unstable"
  (statement := /-- Suppose the vector field $f$ and certificate $V$ are $C^1$,
    $V$ is quadratically bounded on a ball, its positive set accumulates at the
    base point, and its Lie derivative satisfies $\dot V\geq 2\alpha V$ there
    for some $\alpha>0$.
    Then the base point is unstable with respect to finite forward solution
    segments. -/)
  (proof := /-- Globalize the vector field by a smooth cutoff, integrate the
    differential inequality on a sufficiently long finite segment, and stop
    the curve at its first crossing of the certificate ball. -/)]
theorem forwardUnstable_of_exponential_chetaev
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hf : ContDiff ℝ 1 f) (hV : ContDiff ℝ 1 V)
    {ρ α C : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖x - x_eq‖ ≤ ρ →
      |V x| ≤ C * ‖x - x_eq‖ ^ 2)
    (hgrowth : ∀ x, ‖x - x_eq‖ ≤ ρ →
      2 * α * V x ≤ fderiv ℝ V x (f x))
    (hseed : ∀ δ > 0, ∃ x, ‖x - x_eq‖ < min δ ρ ∧ 0 < V x) :
    ForwardUnstable f x_eq := by
  apply forwardUnstable_of_cutoff_segment_escape hρ
  intro δ hδ
  obtain ⟨x₀, hx₀, hVx₀⟩ := hseed δ hδ
  obtain ⟨T, φ, t₁, hφ0, hφcont, hφderiv, ht₁, hfar⟩ :=
    exists_cutoff_segment_reaching_radius hf hV hρ hα hC hVx₀ hbound hgrowth
  exact ⟨T, φ, t₁, by simpa [hφ0] using hx₀,
    hφcont, hφderiv, ht₁, hfar⟩

end NonlinearInstability

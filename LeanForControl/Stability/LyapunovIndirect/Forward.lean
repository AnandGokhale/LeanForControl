import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.PicardLindelof
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
  intro T φ hφ hφ0 t ht
  have ht0 : 0 ≤ t := ht.1
  have hexp : Real.exp (-a * t) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hinit : ‖φ 0 - x_eq‖ < ε / C := lt_of_lt_of_le hφ0 (min_le_right _ _)
  calc
    ‖φ t - x_eq‖ ≤ C * Real.exp (-a * t) * ‖φ 0 - x_eq‖ :=
      hdecay T φ hφ (lt_of_lt_of_le hφ0 (min_le_left _ _)) t ht
    _ ≤ C * 1 * ‖φ 0 - x_eq‖ := by gcongr
    _ < ε := by
      rw [mul_one, ← lt_div_iff₀' hCpos]
      simpa [mul_comm] using hinit

/-- A globally defined trajectory restricts to a finite forward solution segment.

Original: compatibility between the legacy global-trajectory API and the finite-segment API.
-/
theorem IsTrajectory.isForwardTrajectoryOn
    {f : ℝⁿ → ℝⁿ} {φ : ℝ → ℝⁿ} (hφ : IsTrajectory φ f)
    {T : ℝ} (hT : 0 ≤ T) : IsForwardTrajectoryOn φ f T := by
  refine ⟨hT, ?_⟩
  intro t _
  exact (hφ t).hasDerivWithinAt

/-- Forward Lyapunov stability implies the legacy stability predicate for global
trajectories.

Original: compatibility between the finite-segment and legacy APIs.
-/
theorem ForwardLyapunovStable.lyapunovStable
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (h : ForwardLyapunovStable f x_eq) :
    LyapunovStable f x_eq := by
  intro ε hε
  obtain ⟨δ, hδ, hstable⟩ := h ε hε
  refine ⟨δ, hδ, ?_⟩
  intro φ hφ hφ0 t ht
  exact hstable t φ (hφ.isForwardTrajectoryOn ht) hφ0 t ⟨ht, le_rfl⟩

/-- Local exponential stability on finite forward segments implies the legacy
local asymptotic-stability predicate for globally defined trajectories.

The compatibility direction is sound because every global trajectory restricts
to every finite interval `[0, t]`; the exponential estimate then forces
convergence as `t → ∞`.

Reference: Khalil, *Nonlinear Systems*.
-/
theorem ForwardLocallyExponentiallyStable.localAsymptoticStable
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (h : ForwardLocallyExponentiallyStable f x_eq) :
    LocalAsymptoticStable f x_eq := by
  refine ⟨h.forwardLyapunovStable.lyapunovStable, ?_⟩
  rcases h with ⟨r, C, a, hr, hC, ha, hbound⟩
  refine ⟨r, hr, ?_⟩
  intro φ hφ hφ0
  have hdecay : Tendsto (fun t : ℝ => Real.exp (-a * t)) atTop (nhds 0) := by
    have hscale : Tendsto (fun t : ℝ => a * t) atTop atTop := by
      exact tendsto_id.const_mul_atTop ha
    have hx := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
    convert hx using 1
    funext t
    simp [Function.comp_apply]
  have hscalar : Tendsto
      (fun t : ℝ => C * Real.exp (-a * t) * ‖φ 0 - x_eq‖) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hdecay).mul tendsto_const_nhds
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.mp hscalar) ε hε
  refine ⟨max T₀ 0, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := (le_max_right T₀ 0).trans ht
  have hsegment : IsForwardTrajectoryOn φ f t := hφ.isForwardTrajectoryOn ht0
  have hestimate := hbound t φ hsegment hφ0 t ⟨ht0, le_rfl⟩
  rw [dist_eq_norm]
  refine hestimate.trans_lt ?_
  have hnonneg : 0 ≤ C * Real.exp (-a * t) * ‖φ 0 - x_eq‖ := by positivity
  have hCnonneg : 0 ≤ C := zero_le_one.trans hC
  simpa [Real.dist_eq, abs_of_nonneg hnonneg, abs_of_nonneg hCnonneg] using
    hT₀ t ((le_max_left T₀ 0).trans ht)

/-- Instability in the legacy global-trajectory sense implies instability for finite
forward segments.

Original: contraposition of the compatibility implication.
-/
theorem unstable_implies_forwardUnstable
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (h : ¬ LyapunovStable f x_eq) :
    ForwardUnstable f x_eq := by
  intro hforward
  exact h hforward.lyapunovStable

/-- A fixed escape radius witnessed from arbitrarily small initial perturbations on
finite forward segments implies forward instability.

Reference: Khalil, *Nonlinear Systems*.
-/
theorem forwardUnstable_of_fixed_escape
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {ε : ℝ} (hε : 0 < ε)
    (hescape : ∀ δ > 0, ∃ (T : ℝ) (φ : ℝ → ℝⁿ) (t : ℝ),
      IsForwardTrajectoryOn φ f T ∧ ‖φ 0 - x_eq‖ < δ ∧
        t ∈ Icc (0 : ℝ) T ∧ ε ≤ ‖φ t - x_eq‖) :
    ForwardUnstable f x_eq := by
  intro hstable
  obtain ⟨δ, hδ, hstay⟩ := hstable ε hε
  obtain ⟨T, φ, t, hφ, hφ0, ht, hfar⟩ := hescape δ hδ
  exact (not_lt_of_ge hfar) (hstay T φ hφ hφ0 t ht)

/-! ## Lyapunov first-exit infrastructure -/

/-- Chain rule for a Lyapunov function along a finite forward solution segment.

Original: finite-segment form of `hasDerivAt_V_comp_traj`.
-/
lemma hasDerivWithinAt_V_comp_forwardTrajectoryOn
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {φ : ℝ → ℝⁿ} {T t : ℝ}
    (hV_diff : Differentiable ℝ V) (hφ : IsForwardTrajectoryOn φ f T)
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (V ∘ φ) (fderiv ℝ V (φ t) (f (φ t))) (Icc 0 T) t :=
  (hV_diff (φ t)).hasFDerivAt.comp_hasDerivWithinAt t (hφ.2 t ht)

/-- A finite forward solution segment is continuous on its interval of definition.

Original: convenience wrapper around continuity of integral curves.
-/
lemma IsForwardTrajectoryOn.continuousOn
    {f : ℝⁿ → ℝⁿ} {φ : ℝ → ℝⁿ} {T : ℝ}
    (hφ : IsForwardTrajectoryOn φ f T) : ContinuousOn φ (Icc (0 : ℝ) T) :=
  hφ.2.continuousOn

/-- A Lyapunov function is nonincreasing between two times of a finite forward
solution segment, provided the segment remains in the certificate domain.

Reference: Khalil, *Nonlinear Systems*.
-/
lemma V_nonincreasing_on_forwardTrajectoryOn
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq D)
    {φ : ℝ → ℝⁿ} {T a b : ℝ} (hφ : IsForwardTrajectoryOn φ f T)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hstay : ∀ t ∈ Icc a b, φ t ∈ D) : V (φ b) ≤ V (φ a) := by
  have hsub : Icc a b ⊆ Icc (0 : ℝ) T := fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩
  have hcurve : IsIntegralCurveOn φ (fun _ x => f x) (Icc a b) := hφ.2.mono hsub
  have hanti : AntitoneOn (V ∘ φ) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    · exact hV.hcont.continuousOn.comp hcurve.continuousOn hstay
    · intro t ht
      have ht' : t ∈ Icc a b := interior_subset ht
      rw [interior_Icc] at ht
      have hcurveAt : HasDerivAt φ (f (φ t)) t :=
        (hcurve t ht').hasDerivAt (Icc_mem_nhds ht.1 ht.2)
      exact ((hV.hV_diff (φ t)).hasFDerivAt.comp_hasDerivAt t hcurveAt).differentiableAt
        |>.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
      have hcurveAt : HasDerivAt φ (f (φ t)) t :=
        (hcurve t ht').hasDerivAt (Icc_mem_nhds ht.1 ht.2)
      rw [((hV.hV_diff (φ t)).hasFDerivAt.comp_hasDerivAt t hcurveAt).deriv]
      exact hV.hLie_nonpos (φ t) (hstay t ht')
  exact hanti (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab

/-- **Forward Lyapunov stability theorem.** A local Lyapunov function makes the
equilibrium stable with respect to every finite forward solution segment.

The proof uses the first time a segment reaches a small sphere around the
equilibrium, then contradicts monotonicity of the Lyapunov function.

Reference: Khalil, *Nonlinear Systems*.
-/
theorem forwardLyapunovStable_of_isLocalLyapunovFunction
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsLocalLyapunovFunction f V x_eq D) :
    ForwardLyapunovStable f x_eq := by
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp hV.hD_open x_eq hV.hD_mem
  set ε₀ := r / 2
  have hε₀_pos : 0 < ε₀ := by dsimp [ε₀]; linarith
  have hcBall_sub_D : Metric.closedBall x_eq ε₀ ⊆ D := by
    intro x hx
    apply hr_ball
    rw [Metric.mem_ball, Metric.mem_closedBall] at *
    dsimp [ε₀] at *
    linarith
  intro ε hε
  set ε' := min ε ε₀
  have hε'_pos : 0 < ε' := lt_min hε hε₀_pos
  have hε'_le_ε : ε' ≤ ε := min_le_left _ _
  have hcBall'_sub_D : Metric.closedBall x_eq ε' ⊆ D :=
    (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans hcBall_sub_D
  have hsphere'_sub_D : Metric.sphere x_eq ε' ⊆ D :=
    Metric.sphere_subset_closedBall.trans hcBall'_sub_D
  obtain ⟨x_min, hx_min_mem, hx_min_le⟩ :=
    (isCompact_sphere x_eq ε').exists_isMinOn
      (sphere_nonempty x_eq hn hε'_pos) hV.hcont.continuousOn
  set m := V x_min
  have hm_pos : 0 < m := by
    apply hV.hpos x_min (hsphere'_sub_D hx_min_mem)
    intro heq
    have hx := hx_min_mem
    rw [heq, Metric.mem_sphere, dist_self] at hx
    exact (ne_of_gt hε'_pos) hx.symm
  have hV_cont_at : ContinuousAt V x_eq := hV.hcont.continuousAt
  rw [Metric.continuousAt_iff] at hV_cont_at
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hV_cont_at m hm_pos
  set δ := min δ₀ ε'
  refine ⟨δ, lt_min hδ₀_pos hε'_pos, ?_⟩
  intro T φ hφ hφ0 t ht
  have hφ0ε' : ‖φ 0 - x_eq‖ < ε' := hφ0.trans_le (min_le_right _ _)
  have hV0_lt_m : V (φ 0) < m := by
    have hnear : dist (V (φ 0)) (V x_eq) < m := hδ₀ (by
      rw [dist_eq_norm]
      exact hφ0.trans_le (min_le_left _ _))
    simp only [Real.dist_eq, hV.hzero, sub_zero] at hnear
    exact (abs_lt.mp hnear).2
  by_contra hnot
  push Not at hnot
  have hge_ε' : ε' ≤ ‖φ t - x_eq‖ := hε'_le_ε.trans hnot
  set Q := {s : ℝ | s ∈ Icc (0 : ℝ) t ∧ ε' ≤ ‖φ s - x_eq‖}
  have hQ_nonempty : Q.Nonempty := ⟨t, ⟨ht.1, le_rfl⟩, hge_ε'⟩
  have hQ_bddBelow : BddBelow Q := ⟨0, fun s hs => hs.1.1⟩
  have hφ_cont : ContinuousOn (fun s => ‖φ s - x_eq‖) (Icc (0 : ℝ) t) :=
    (continuous_norm.comp_continuousOn
      ((hφ.continuousOn.mono (Icc_subset_Icc le_rfl ht.2)).sub continuousOn_const))
  have hQ_closed : IsClosed Q := by
    exact isClosed_Icc.isClosed_le continuousOn_const hφ_cont
  set Tstar := sInf Q
  have hTstar_mem : Tstar ∈ Q := hQ_closed.csInf_mem hQ_nonempty hQ_bddBelow
  have hTstar_pos : 0 < Tstar := by
    rcases lt_or_eq_of_le hTstar_mem.1.1 with hpos | hzero
    · exact hpos
    · exact False.elim ((not_le_of_gt hφ0ε') (by simpa [hzero] using hTstar_mem.2))
  have hlt_ε' : ∀ s : ℝ, 0 ≤ s → s < Tstar → ‖φ s - x_eq‖ < ε' := by
    intro s hs0 hsT
    by_contra hs
    push Not at hs
    have hs_le_t : s ≤ t := (le_of_lt hsT).trans hTstar_mem.1.2
    exact (not_le_of_gt hsT) (csInf_le hQ_bddBelow ⟨⟨hs0, hs_le_t⟩, hs⟩)
  have hTstar_eq : ‖φ Tstar - x_eq‖ = ε' := by
    apply le_antisymm _ hTstar_mem.2
    by_contra hlt
    push Not at hlt
    have hcont_sub : ContinuousOn (fun s => ‖φ s - x_eq‖) (Icc (0 : ℝ) Tstar) :=
      hφ_cont.mono (Icc_subset_Icc le_rfl hTstar_mem.1.2)
    obtain ⟨s₀, hs₀_mem, hs₀_val⟩ :=
      intermediate_value_Icc (le_of_lt hTstar_pos) hcont_sub
        ⟨le_of_lt hφ0ε', le_of_lt hlt⟩
    have hs₀_ge : Tstar ≤ s₀ := csInf_le hQ_bddBelow
      ⟨⟨hs₀_mem.1, hs₀_mem.2.trans hTstar_mem.1.2⟩, ge_of_eq hs₀_val⟩
    have hs₀_eq : s₀ = Tstar := le_antisymm hs₀_mem.2 hs₀_ge
    exact (not_lt_of_ge (le_of_eq (hs₀_eq ▸ hs₀_val))) hlt
  have hstay : ∀ s ∈ Icc (0 : ℝ) Tstar, φ s ∈ D := by
    intro s hs
    apply hcBall'_sub_D
    rw [Metric.mem_closedBall, dist_eq_norm]
    rcases eq_or_lt_of_le hs.2 with heq | hlt
    · subst s
      exact le_of_eq hTstar_eq
    · exact le_of_lt (hlt_ε' s hs.1 hlt)
  have hVT_le : V (φ Tstar) ≤ V (φ 0) :=
    V_nonincreasing_on_forwardTrajectoryOn hV hφ le_rfl (le_of_lt hTstar_pos)
      (hTstar_mem.1.2.trans ht.2) hstay
  have hVT_ge : m ≤ V (φ Tstar) :=
    hx_min_le (by rw [Metric.mem_sphere, dist_eq_norm]; exact hTstar_eq)
  linarith

/-- A `C¹` vector field admits a nontrivial finite forward solution segment from
every point at which it is `C¹`.

Reference: the Picard--Lindelöf local existence theorem.
-/
theorem ContDiffAt.exists_isForwardTrajectoryOn
    {f : ℝⁿ → ℝⁿ} {x₀ : ℝⁿ} (hf : ContDiffAt ℝ 1 f x₀) :
    ∃ (T : ℝ) (φ : ℝ → ℝⁿ), 0 < T ∧ φ 0 = x₀ ∧ IsForwardTrajectoryOn φ f T := by
  obtain ⟨φ, hφ0, ε, hε, hφ⟩ :=
    hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  refine ⟨ε / 2, φ, by positivity, hφ0, ?_⟩
  refine ⟨by positivity, ?_⟩
  intro t ht
  have htIoo : t ∈ Ioo (0 - ε) (0 + ε) := by
    constructor <;> norm_num at * <;> linarith
  exact (hφ t htIoo).hasDerivWithinAt

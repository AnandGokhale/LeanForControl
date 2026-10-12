import LeanForControl.Analysis.Continuity
import LeanForControl.Stability.Continuous.Defs
import LeanForControl.Stability.Continuous.LyapunovFunctions
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import LeanForControl.ODEs.PicardLindelof
import Architect

/-!
# Chetaev instability on finite forward solution segments

The geometric criterion retains a cutoff solution in a positive region and uses a positive
Lie-derivative minimum on a compact superlevel to force escape. The exponential criterion
is its corollary on the region `{V > 0}`.

Both conclude `s.Unstable`, the negation of `s.Stable`, rather than only failure of
`s.UniformlyStable`. Escape at initial time zero contradicts even a stability radius
depending on initial time. Neither theorem assumes an equilibrium or forward completeness.
The state equation is time-invariant (`s.F t x () = f x`); no condition on output is imposed.

Reference: Khalil, *Nonlinear Systems*, 3rd ed. (Prentice Hall, 2002), Theorem 4.3,
p. 125, for the positive-superlevel escape method.
-/

open Filter Function Metric Set Topology
open scoped ContDiff NNReal Topology

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace ContinuousSystem

/-- For a globally `C¹` vector field, `ρ > 0`, any finite endpoint `T`, and initial state `x₀`,
there is a curve starting at `x₀`, continuous on `[0, T]`, whose derivative equals `f(φ t)`
whenever it lies in the closed `ρ`-ball about `x_eq`. Outside the ball it solves a smooth
cutoff field, so it is not claimed to solve the original ODE on all of the interval.
For `T < 0` the specified interval is empty; the application below uses `T ≥ 0`.

Reference: the smooth-cutoff proof of local continuation for ODEs. -/
private theorem exists_cutoff_forward_segment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → E) (hf : ContDiff ℝ 1 f) (x_eq : E)
    {ρ T : ℝ} (hρ : 0 < ρ) (x₀ : E) :
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
  obtain ⟨φ, hφ0, hφg⟩ :=
    exists_isIntegralCurveOn_Icc (f := fun _ x ↦ g x) (K := K)
      (hg_lip.continuous.comp continuous_snd) (fun _ ↦ hg_lip) 0 T x₀
  refine ⟨φ, hφ0, hφg.continuousOn, ?_⟩
  intro t ht hball
  have hb_one : b (φ t) = 1 := by
    apply b.one_of_mem_closedBall
    simpa [Metric.mem_closedBall, dist_eq_norm] using hball
  simpa [g, hb_one] using hφg t ht

/-- For an input-free system with `s.F t x () = f x`, cutoff curves starting arbitrarily
close to the base point and reaching a fixed positive radius imply `s.Unstable x_eq`.

Restrict to the first sphere hit to obtain a system trajectory on `[0, τ]`. -/
private theorem unstable_of_cutoff_segment_escape {Y : Type*} {s : ContinuousSystem ℝⁿ Unit Y}
    {f : ℝⁿ → ℝⁿ} (hF : ∀ t x, s.F t x () = f x) {x_eq : ℝⁿ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsegments : ∀ δ > 0, ∃ (T : ℝ) (φ : ℝ → ℝⁿ) (t : ℝ),
      ‖φ 0 - x_eq‖ < min δ ρ ∧
      ContinuousOn φ (Icc (0 : ℝ) T) ∧
      (∀ s ∈ Icc (0 : ℝ) T, ‖φ s - x_eq‖ ≤ ρ →
        HasDerivWithinAt φ (f (φ s)) (Icc 0 T) s) ∧
      t ∈ Icc (0 : ℝ) T ∧ ρ ≤ ‖φ t - x_eq‖) :
    s.Unstable x_eq := by
  apply ContinuousSystem.unstable_of_escape hρ
  intro δ hδ
  obtain ⟨T, φ, t₁, hφ0, hφcont, hφderiv, ht₁, hfar⟩ := hsegments δ hδ
  have hφ0δ : ‖φ 0 - x_eq‖ < δ := hφ0.trans_le (min_le_left _ _)
  have hφ0ρ : ‖φ 0 - x_eq‖ < ρ := hφ0.trans_le (min_le_right _ _)
  obtain ⟨τ, hτT, hτeq, hstay⟩ :=
    exists_first_sphere_hit hφcont hφ0ρ ht₁ hfar
  have hφf : s.IsTrajectoryOn (fun _ => ()) φ (Icc 0 τ) := by
    intro t ht
    rw [ContinuousSystem.vectorField_apply, hF]
    exact (hφderiv t ⟨ht.1, ht.2.trans hτT.2⟩ (hstay t ht)).mono
      (Icc_subset_Icc_right hτT.2)
  exact ⟨τ, φ, τ, hφf, hφ0δ, ⟨hτT.1, le_rfl⟩, hτeq.ge⟩

/-- A continuous curve starting in an open region `D` with `V(φ t₀) > 0` stays
in `D` on `[t₀, T]` if `V ∘ φ` is continuous, vanishes at every boundary point
visited on that interval, and has nonnegative derivative at interior times while
the curve is in `D`. It cannot first exit through a zero-value boundary while
the certificate remains at least its positive initial value. No ODE assumption is needed. -/
private theorem curve_stays_in_open_of_nonneg_certificate_deriv
    {E : Type*} [TopologicalSpace E]
    {D : Set E} (hD : IsOpen D) {V : E → ℝ} {φ : ℝ → E} {t₀ T : ℝ}
    (hφ : ContinuousOn φ (Icc t₀ T))
    (hVφ : ContinuousOn (V ∘ φ) (Icc t₀ T))
    (hstart : φ t₀ ∈ D) (hVstart : 0 < V (φ t₀))
    (hboundary_zero : ∀ t ∈ Icc t₀ T, φ t ∈ frontier D → V (φ t) = 0)
    (hderiv : ∀ t ∈ Ioo t₀ T, φ t ∈ D →
      ∃ d : ℝ, HasDerivAt (V ∘ φ) d t ∧ 0 ≤ d) :
    ∀ t ∈ Icc t₀ T, φ t ∈ D := by
  intro t htI
  by_contra hout
  obtain ⟨τ, hτI, hτfront, hstay⟩ :=
    exists_first_boundary_hit_of_exit hD hφ hstart htI hout
  -- Up to the first boundary hit, the certificate is nondecreasing.
  have hderiv_before_exit : ∀ s ∈ Ioo t₀ τ,
      ∃ d : ℝ, HasDerivAt (V ∘ φ) d s ∧ 0 ≤ d := by
    intro s hs
    exact hderiv s ⟨hs.1, hs.2.trans_le (hτI.2.trans htI.2)⟩
      (hstay s ⟨hs.1.le, hs.2⟩)
  have hmono : MonotoneOn (V ∘ φ) (Icc t₀ τ) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc t₀ τ)
      (hVφ.mono (Icc_subset_Icc_right (hτI.2.trans htI.2)))
    · intro s hs
      rw [interior_Icc] at hs
      obtain ⟨d, hd, _⟩ := hderiv_before_exit s hs
      exact hd.differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      obtain ⟨d, hd, hd0⟩ := hderiv_before_exit s hs
      simpa [hd.deriv] using hd0
  have hle : V (φ t₀) ≤ V (φ τ) :=
    hmono (left_mem_Icc.mpr hτI.1) (right_mem_Icc.mpr hτI.1) hτI.1
  rw [hboundary_zero τ ⟨hτI.1, hτI.2.trans htI.2⟩ hτfront] at hle
  linarith

/-- A positive seed `x₀ ∈ D` in the closed `ρ`-ball determines a uniform constant
`γ > 0` such that `γ ≤ DV(x) f(x)` for every
`x ∈ closure D ∩ closedBall x_eq ρ` with `V x₀ ≤ V x`.
Assume global `C¹` regularity of `f` and `V`, boundary vanishing in the ball,
and strict positivity of the Lie derivative on `D` in the ball. The superlevel
set is compact and excludes `∂D` because its certificate values are positive. -/
private theorem exists_pos_lieDerivative_lower_bound_on_superlevel
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq x₀ : ℝⁿ} {D : Set ℝⁿ}
    (hf : ContDiff ℝ 1 f) (hV : ContDiff ℝ 1 V)
    {ρ : ℝ} (hx₀D : x₀ ∈ D) (hx₀ρ : ‖x₀ - x_eq‖ ≤ ρ)
    (hVx₀ : 0 < V x₀)
    (hboundary : ∀ x ∈ frontier D, ‖x - x_eq‖ ≤ ρ → V x = 0)
    (hLie_pos : ∀ x ∈ D, ‖x - x_eq‖ ≤ ρ →
      0 < fderiv ℝ V x (f x)) :
    ∃ γ > 0, ∀ x ∈ closure D, ‖x - x_eq‖ ≤ ρ → V x₀ ≤ V x →
      γ ≤ fderiv ℝ V x (f x) := by
  let lieDerivative : ℝⁿ → ℝ := fun x ↦ fderiv ℝ V x (f x)
  let superlevel : Set ℝⁿ := closure D ∩ closedBall x_eq ρ ∩ {x | V x₀ ≤ V x}
  have hsuperlevel_compact : IsCompact superlevel := by
    exact ((isCompact_closedBall x_eq ρ).inter_left isClosed_closure).inter_right
      (isClosed_le continuous_const hV.continuous)
  have hx₀_superlevel : x₀ ∈ superlevel := by
    refine ⟨⟨subset_closure hx₀D,
      by simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hx₀ρ⟩, ?_⟩
    exact (show V x₀ ≤ V x₀ from le_rfl)
  -- A positive superlevel cannot contain a boundary point, where V would be zero.
  have hsuperlevel_in_region : superlevel ⊆ D := by
    intro x hx
    by_contra hxD
    have hx_boundary : x ∈ frontier D := by
      rw [frontier, mem_diff]
      exact ⟨hx.1.1, fun hxint ↦ hxD (interior_subset hxint)⟩
    have hxzero : V x = 0 := hboundary x hx_boundary (by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hx.1.2)
    have hle : V x₀ ≤ V x := hx.2
    rw [hxzero] at hle
    linarith
  -- The continuous Lie derivative attains a strictly positive minimum there.
  have hLie_cont : Continuous lieDerivative := by
    exact (hV.continuous_fderiv (by norm_num)).clm_apply hf.continuous
  obtain ⟨x_min, hx_min_superlevel, hLie_min⟩ :=
    hsuperlevel_compact.exists_isMinOn ⟨x₀, hx₀_superlevel⟩ hLie_cont.continuousOn
  let γ : ℝ := lieDerivative x_min
  have hγ : 0 < γ := by
    apply hLie_pos x_min (hsuperlevel_in_region hx_min_superlevel)
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hx_min_superlevel.1.2
  refine ⟨γ, hγ, ?_⟩
  intro x hx_closure hx_ball hx_value
  apply hLie_min
  exact ⟨⟨hx_closure,
    by simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hx_ball⟩, hx_value⟩

/-- A solution segment of `ẋ = f(x)` starting in an open region `D` with positive
certificate value stays in `D`, and its certificate never falls below its initial
value, if the certificate vanishes at boundary points visited by the segment and
has nonnegative Lie derivative in `D` along the segment. Assume `V` is globally `C¹`.
Boundary retention is proved first, then the chain rule gives nondecrease. -/
private theorem solution_stays_in_region_and_above_initial_certificate
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {D : Set ℝⁿ} {φ : ℝ → ℝⁿ} {T : ℝ}
    (hD : IsOpen D) (hV : ContDiff ℝ 1 V)
    (hφ : IsIntegralCurveOn φ (fun _ x ↦ f x) (Icc (0 : ℝ) T))
    (hstart : φ 0 ∈ D) (hVstart : 0 < V (φ 0))
    (hboundary_zero : ∀ t ∈ Icc (0 : ℝ) T, φ t ∈ frontier D → V (φ t) = 0)
    (hLie_nonneg : ∀ t ∈ Icc (0 : ℝ) T, φ t ∈ D →
      0 ≤ fderiv ℝ V (φ t) (f (φ t))) :
    (∀ t ∈ Icc (0 : ℝ) T, φ t ∈ D) ∧
      ∀ t ∈ Icc (0 : ℝ) T, V (φ 0) ≤ V (φ t) := by
  have hstay_region : ∀ t ∈ Icc (0 : ℝ) T, φ t ∈ D := by
    apply curve_stays_in_open_of_nonneg_certificate_deriv hD hφ.continuousOn
      (hV.continuous.comp_continuousOn hφ.continuousOn) hstart hVstart hboundary_zero
    intro t ht htD
    have hcertificate_deriv := hφ.hasDerivWithinAt_lieDerivative
      (V := fun _ ↦ V) ((hV.differentiable one_ne_zero).comp differentiable_snd)
      (Ioo_subset_Icc_self ht)
    rw [lieDerivative_const (hV.differentiable one_ne_zero (φ t))] at hcertificate_deriv
    have hcertificate_deriv := hcertificate_deriv.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    exact ⟨_, hcertificate_deriv, hLie_nonneg t (Ioo_subset_Icc_self ht) htD⟩
  refine ⟨hstay_region, ?_⟩
  have hanti := hφ.antitoneOn_of_lieDerivative_nonpos (V := fun _ x ↦ -V x)
    (convex_Icc 0 T) ((hV.differentiable one_ne_zero).neg.comp differentiable_snd) (by
      intro t ht
      rw [interior_Icc] at ht
      rw [lieDerivative_const (V := fun x ↦ -V x)
        (hV.differentiable one_ne_zero (φ t)).neg, fderiv_fun_neg]
      simp only [ContinuousLinearMap.neg_apply]
      exact neg_nonpos.mpr (hLie_nonneg t (Ioo_subset_Icc_self ht)
        (hstay_region t (Ioo_subset_Icc_self ht))))
  intro t ht
  have hvalue := hanti (left_mem_Icc.mpr (ht.1.trans ht.2)) ht ht.1
  dsimp only at hvalue
  linarith

/-- For a positive seed `x₀ ∈ D` strictly inside the `ρ`-ball, `ρ > 0`,
there is a finite continuous cutoff curve starting at `x₀` that reaches distance
at least `ρ` from `x_eq`. Its derivative agrees with `f` whenever it is in the
closed ball. Assume globally `C¹` field and certificate, open `D`, boundary
vanishing in the ball, and strictly positive Lie derivative in `D` in the ball.

Choose a uniform positive Lie-derivative bound on the seed's compact superlevel
and a certificate ceiling on the ball. If the cutoff curve stayed in the ball,
boundary retention would keep it in that superlevel, and linear growth would
exceed the ceiling on a sufficiently long finite interval. -/
private theorem exists_cutoff_segment_reaching_radius_of_geometric_chetaev
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq x₀ : ℝⁿ} {D : Set ℝⁿ}
    (hf : ContDiff ℝ 1 f) (hV : ContDiff ℝ 1 V) (hD : IsOpen D)
    {ρ : ℝ} (hρ : 0 < ρ) (hx₀D : x₀ ∈ D) (hx₀ρ : ‖x₀ - x_eq‖ < ρ)
    (hVx₀ : 0 < V x₀)
    (hboundary : ∀ x ∈ frontier D, ‖x - x_eq‖ ≤ ρ → V x = 0)
    (hLie_pos : ∀ x ∈ D, ‖x - x_eq‖ ≤ ρ →
      0 < fderiv ℝ V x (f x)) :
    ∃ (T : ℝ) (φ : ℝ → ℝⁿ) (t : ℝ),
      φ 0 = x₀ ∧ ContinuousOn φ (Icc (0 : ℝ) T) ∧
      (∀ s ∈ Icc (0 : ℝ) T, ‖φ s - x_eq‖ ≤ ρ →
        HasDerivWithinAt φ (f (φ s)) (Icc 0 T) s) ∧
      t ∈ Icc (0 : ℝ) T ∧ ρ ≤ ‖φ t - x_eq‖ := by
  -- Fix the derivative floor on the seed's superlevel and a ceiling on the ball.
  obtain ⟨γ, hγ, hLie_lower⟩ :=
    exists_pos_lieDerivative_lower_bound_on_superlevel hf hV hx₀D hx₀ρ.le
      hVx₀ hboundary hLie_pos
  obtain ⟨x_max, hx_max_ball, hx_max⟩ :=
    (isCompact_closedBall x_eq ρ).exists_isMaxOn
      ⟨x_eq, Metric.mem_closedBall_self hρ.le⟩ hV.continuous.continuousOn
  -- Linear growth exceeds that ceiling by time T.
  let T : ℝ := (V x_max - V x₀ + 1) / γ
  have hx₀_ball : x₀ ∈ closedBall x_eq ρ := by
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hx₀ρ.le
  have hnum : 0 < V x_max - V x₀ + 1 := by
    have := hx_max hx₀_ball
    change V x₀ ≤ V x_max at this
    linarith
  have hT : 0 ≤ T := (div_pos hnum hγ).le
  obtain ⟨φ, hφ0, hφcont, hφderiv⟩ :=
    exists_cutoff_forward_segment f hf x_eq hρ (T := T) x₀
  by_cases hexit : ∃ t ∈ Icc (0 : ℝ) T, ρ ≤ ‖φ t - x_eq‖
  · obtain ⟨t, ht, hfar⟩ := hexit
    exact ⟨T, φ, t, hφ0, hφcont, hφderiv, ht, hfar⟩
  · push Not at hexit
    have hinside : ∀ t ∈ Icc (0 : ℝ) T, ‖φ t - x_eq‖ ≤ ρ :=
      fun t ht ↦ (hexit t ht).le
    have htraj : IsIntegralCurveOn φ (fun _ x ↦ f x) (Icc (0 : ℝ) T) :=
      fun t ht ↦ hφderiv t ht (hinside t ht)
    -- Without sphere escape, this is an original-field solution that stays in D
    -- and above the seed value, so the derivative floor applies at every time.
    obtain ⟨hstay_region, hV_nondecrease⟩ :=
      solution_stays_in_region_and_above_initial_certificate hD hV htraj
        (by simpa [hφ0] using hx₀D) (by simpa [hφ0] using hVx₀)
        (fun t ht ht_boundary ↦ hboundary (φ t) ht_boundary (hinside t ht))
        (fun t ht htD ↦ (hLie_pos (φ t) htD (hinside t ht)).le)
    have hLie_γ : ∀ t ∈ Icc (0 : ℝ) T,
        γ ≤ fderiv ℝ V (φ t) (f (φ t)) := by
      intro t ht
      apply hLie_lower (φ t) (subset_closure (hstay_region t ht)) (hinside t ht)
      simpa [hφ0] using hV_nondecrease t ht
    -- Apply the shared monotonicity theorem to W(t,x) = γ t - V(x).
    have hlinear_growth := htraj.antitoneOn_of_lieDerivative_nonpos
      (V := fun t x ↦ -V x + γ * t) (convex_Icc 0 T)
      (((hV.differentiable one_ne_zero).neg.comp differentiable_snd).add
        (differentiable_fst.const_mul γ)) (by
          intro t ht
          rw [interior_Icc] at ht
          rw [lieDerivative_add_mul (V := fun x ↦ -V x) γ
              (hV.differentiable one_ne_zero (φ t)).neg,
            fderiv_fun_neg]
          simp only [ContinuousLinearMap.neg_apply]
          linarith [hLie_γ t (Ioo_subset_Icc_self ht)])
    have hlin := hlinear_growth (left_mem_Icc.mpr hT) (right_mem_Icc.mpr hT) hT
    dsimp only at hlin
    rw [hφ0] at hlin
    have hterminal_ball : φ T ∈ closedBall x_eq ρ := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using
        hinside T (right_mem_Icc.mpr hT)
    have hVTmax : V (φ T) ≤ V x_max := hx_max hterminal_ball
    have hγT : γ * T = V x_max - V x₀ + 1 := by
      dsimp [T]
      field_simp
    linarith

/-- A Chetaev certificate on a fixed closed ball implies instability for an input-free
system with globally `C¹`, time-independent state equation `f`.

Reference: Khalil, *Nonlinear Systems*, 3rd ed., Theorem 4.3, p. 125, for the
positive-superlevel escape argument. -/
@[blueprint "thm:continuousSystem-geometric-chetaev-unstable"
  (title := "Geometric Chetaev instability criterion")
  (statement := /-- For an input-free system $\dot x=f(x)$ with $f$ globally $C^1$,
    a Chetaev certificate at $x_{\rm eq}$ (\cref{def:continuousSystem-isChetaevFunction})
    implies instability (\cref{def:continuousSystem-unstable}).

    Reference: Khalil, \emph{Nonlinear Systems}, 3rd ed., Theorem 4.3, p. 125. -/)
  (proof := /-- Choose a positive seed near the boundary point and continue a cutoff curve.
    Boundary vanishing retains it in the region. The Lie derivative has a positive minimum
    on its compact superlevel, forcing growth beyond the ball's certificate ceiling. -/)]
theorem unstable_of_geometric_chetaev {Y : Type*} {s : ContinuousSystem ℝⁿ Unit Y}
    {f : ℝⁿ → ℝⁿ} (hF : ∀ t x, s.F t x () = f x)
    {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ} {ρ : ℝ}
    (hf : ContDiff ℝ 1 f) (hC : s.IsChetaevFunction V x_eq D ρ) :
    s.Unstable x_eq := by
  apply unstable_of_cutoff_segment_escape hF hC.hradius
  intro δ hδ
  have hmin : 0 < min δ ρ := lt_min hδ hC.hradius
  obtain ⟨x₀, hx₀D, hdist⟩ :=
    Metric.mem_closure_iff.mp (frontier_subset_closure hC.hmem_boundary)
      (min δ ρ) hmin
  have hx₀ρ : ‖x₀ - x_eq‖ < ρ := by
    rw [dist_eq_norm] at hdist
    exact (norm_sub_rev x_eq x₀ ▸ hdist).trans_le (min_le_right _ _)
  have hVx₀ : 0 < V x₀ := hC.hpos x₀ hx₀D hx₀ρ.le
  have hLie_pos : ∀ x ∈ D, ‖x - x_eq‖ ≤ ρ →
      0 < fderiv ℝ V x (f x) := by
    intro x hxD hx_ball
    have hpositive := hC.hLie_pos 0 le_rfl x hxD hx_ball
    simpa only [ContinuousSystem.lieDerivative,
      lieDerivative_const (hC.hV_c1.differentiable one_ne_zero x), hF] using hpositive
  obtain ⟨T, φ, t, hφ0, hφcont, hφderiv, ht, hfar⟩ :=
    exists_cutoff_segment_reaching_radius_of_geometric_chetaev hf hC.hV_c1
      hC.hD_open hC.hradius hx₀D hx₀ρ hVx₀ hC.hboundary_zero hLie_pos
  refine ⟨T, φ, t, ?_, hφcont, hφderiv, ht, hfar⟩
  rw [hφ0]
  rw [dist_eq_norm] at hdist
  simpa [norm_sub_rev] using hdist


/-- A quadratic certificate bound, positive values arbitrarily near the base point, and
`DV(x) f(x) ≥ 2 α V(x)` with `α > 0` imply instability. Apply the geometric criterion
to the open positive set of `V`.

Reference: Khalil, *Nonlinear Systems*, 3rd ed., Theorem 4.3, p. 125. -/
@[blueprint "thm:exponential-chetaev-unstable"
  (title := "Exponential Chetaev instability criterion")
  (statement := /-- Suppose the vector field $f$ and certificate $V$ are $C^1$,
    $V$ is quadratically bounded on a ball, its positive set accumulates at the
    base point, and its Lie derivative satisfies $\dot V\geq 2\alpha V$ there
    for some $\alpha>0$.
    Then the base point is unstable
    (\cref{def:continuousSystem-unstable}) for any system whose state equation is
    $\dot x = f(x)$.

    Reference: Khalil, \emph{Nonlinear Systems}, 3rd ed. (Prentice Hall, 2002),
    Theorem 4.3, p. 125, for the method; this quantitative variant is not its statement.
  -/)
  (proof := /-- Take $D=\{V>0\}$. The quadratic bound gives $V(x_{\rm eq})=0$;
    the nearby positive seeds put $x_{\rm eq}$ in its closure. Continuity makes $V=0$
    on $\partial D$, and $\dot V\ge 2\alpha V>0$ in $D$ within the ball.
    Apply \cref{thm:continuousSystem-geometric-chetaev-unstable}. -/)]
theorem unstable_of_exponential_chetaev {Y : Type*} {s : ContinuousSystem ℝⁿ Unit Y}
    {f : ℝⁿ → ℝⁿ} (hF : ∀ t x, s.F t x () = f x) {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hf : ContDiff ℝ 1 f) (hV : ContDiff ℝ 1 V)
    {ρ α C : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖x - x_eq‖ ≤ ρ →
      |V x| ≤ C * ‖x - x_eq‖ ^ 2)
    (hgrowth : ∀ x, ‖x - x_eq‖ ≤ ρ →
      2 * α * V x ≤ fderiv ℝ V x (f x))
    (hseed : ∀ δ > 0, ∃ x, ‖x - x_eq‖ < min δ ρ ∧ 0 < V x) :
    s.Unstable x_eq := by
  let D : Set ℝⁿ := {x | 0 < V x}
  have hD_open : IsOpen D := isOpen_lt continuous_const hV.continuous
  have hVzero : V x_eq = 0 := by
    apply abs_nonpos_iff.mp
    calc
      |V x_eq| ≤ C * ‖x_eq - x_eq‖ ^ 2 := hbound x_eq (by simpa using hρ.le)
      _ ≤ C * 0 := mul_le_mul_of_nonneg_left (by simp) hC
      _ = 0 := mul_zero C
  have hclosure : x_eq ∈ closure D := Metric.mem_closure_iff.mpr (by
    intro ε hε
    obtain ⟨x, hx, hVx⟩ := hseed ε hε
    refine ⟨x, hVx, ?_⟩
    simpa [dist_eq_norm, norm_sub_rev] using hx.trans_le (min_le_left ε ρ))
  have hmem_boundary : x_eq ∈ frontier D := by
    rw [hD_open.frontier_eq]
    refine ⟨hclosure, ?_⟩
    change ¬ 0 < V x_eq
    simp [hVzero]
  have hboundary_zero : ∀ x ∈ frontier D, V x = 0 := by
    intro x hx
    exact (frontier_lt_subset_eq continuous_const hV.continuous hx).symm
  apply unstable_of_geometric_chetaev hF hf
  refine {
    hradius := hρ
    hD_open := hD_open
    hmem_boundary := hmem_boundary
    hV_c1 := hV
    hpos := fun _ hx _ ↦ hx
    hboundary_zero := fun x hx _ ↦ hboundary_zero x hx
    hLie_pos := ?_
  }
  intro t _ x hx hball
  rw [ContinuousSystem.lieDerivative, lieDerivative_const (hV.differentiable one_ne_zero x), hF]
  exact (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hα) hx).trans_le (hgrowth x hball)

end ContinuousSystem

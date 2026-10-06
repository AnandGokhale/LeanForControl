import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Basic
import Architect


/-!
# Smoothing of monotone functions

One `axiom` and two proved upper-majorant results. A Lyapunov function's sublevel data gives only
*monotone* bounds; the comparison-function machinery needs *strictly* monotone continuous ones.
These say the gap can always be closed, in either direction.

Discharging the remaining lower-bound axiom is open work. The upper majorant is constructed
by averaging over a multiplicative interval; the endpoint right-continuity assumption is
necessary because a continuous majorant vanishing at zero cannot dominate a jump there.
-/

private noncomputable def monotoneUpperAverage (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u in (1 : ℝ)..2, φ (max (x * u) 0)

/-- A monotonically non-decreasing positive function can be lower-bounded by a strictly monotonic
continuous function. -/
@[blueprint "lem:exists-strictMono-lower-bound"
  (title := "Class $\\mathcal{K}$ minorant of a positive monotone function") (latexEnv := "lemma")
  (statement := /-- \textbf{Assumed without proof.}  Let $r > 0$ and let
    $\psi : \mathbb{R} \to \mathbb{R}$ satisfy $\psi(0) = 0$, $\psi(s) > 0$ for
    $s \in (0, r]$, and $\psi$ nondecreasing on $[0, r]$.  Then there are $b > 0$ and a
    function $f$ with $f(0) = 0$, $f(r) = b$, $f$ continuous and strictly increasing on
    $[0, r]$, and $f(s) \le \psi(s)$ for all $s \in [0, r]$.

    That is: a positive nondecreasing function admits a class $\mathcal{K}$ minorant on any
    bounded interval.  This is what turns a positive-definite $V$ into the lower comparison
    bound of \cref{thm:lyapunov-class-K-bounds}. -/)]
axiom exists_strictMono_lower_bound (r : ℝ) (hr : 0 < r) (ψ : ℝ → ℝ)
    (hψ_zero : ψ 0 = 0)
    (hψ_pos : ∀ s, 0 < s → s ≤ r → 0 < ψ s)
    (hψ_mono : ∀ s₁ s₂, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ r → ψ s₁ ≤ ψ s₂) :
    ∃ (f : ℝ → ℝ) (b : ℝ), 0 < b ∧
      f 0 = 0 ∧ f r = b ∧
      ContinuousOn f (Set.Icc 0 r) ∧
      StrictMonoOn f (Set.Icc 0 r) ∧
      ∀ s, 0 ≤ s → s ≤ r → f s ≤ ψ s


/-- A monotonically non-decreasing function starting continuously at zero on `[0, ∞)` can be
upper-bounded by a strictly monotonic continuous function that tends to `+∞`. -/
@[blueprint "lem:exists-strictMono-upper-bound-global"
  (title := "Class $\\mathcal{K}_{\\infty}$ majorant of a monotone function") (latexEnv := "lemma")
  (statement := /-- Let $\varphi : \mathbb{R} \to \mathbb{R}$ satisfy $\varphi(0) = 0$,
    be right-continuous at zero, and be monotone on $[0, \infty)$.  Then there is an $f$
    with $f(0) = 0$, continuous and strictly increasing on $[0, \infty)$,
    $f(s) \to \infty$ as $s \to \infty$, and $\varphi(s) \le f(s)$ for all $s \ge 0$.

    That is: a nondecreasing function admits a class $\mathcal{K}_{\infty}$ majorant.  The
    unbounded domain is what distinguishes this from
    \cref{lem:exists-strictMono-upper-bound}, which it implies. -/)
  (proof := /-- Extend $\varphi$ monotonically to the negative half-line by clamping at zero,
    and average it over the multiplicative interval $[x,2x]$.  The average lies between
    $\varphi(x)$ and $\varphi(2x)$, is monotone, is continuous away from zero by continuity
    of the integral primitive, and tends to zero at the endpoint by right-continuity.
    Adding $x$ makes the majorant strictly increasing and unbounded. -/)]
theorem exists_strictMono_upper_bound_global (φ : ℝ → ℝ)
    (hφ_zero : φ 0 = 0)
    (hφ_mono : MonotoneOn φ (Set.Ici 0))
    (hφ_cont_zero : ContinuousWithinAt φ (Set.Ici 0) 0) :
    ∃ f : ℝ → ℝ,
      f 0 = 0 ∧
      ContinuousOn f (Set.Ici 0) ∧
      StrictMonoOn f (Set.Ici 0) ∧
      Filter.Tendsto f Filter.atTop Filter.atTop ∧
      ∀ s ≥ 0, φ s ≤ f s := by
  let φp : ℝ → ℝ := fun x => φ (max x 0)
  have hφp_mono : Monotone φp := by
    intro a b hab
    exact hφ_mono (Set.mem_Ici.mpr (le_max_right a 0))
      (Set.mem_Ici.mpr (le_max_right b 0)) (max_le_max_right 0 hab)
  have hφp_int : ∀ a b, IntervalIntegrable φp MeasureTheory.volume a b :=
    fun _ _ => hφp_mono.intervalIntegrable
  let F : ℝ → ℝ := fun x => ∫ t in 0..x, φp t
  have hF_cont : Continuous F := intervalIntegral.continuous_primitive hφp_int 0
  let g : ℝ → ℝ := monotoneUpperAverage φ
  have hg_zero : g 0 = 0 := by simp [g, monotoneUpperAverage, hφ_zero]
  have hg_eq_integral : ∀ {x : ℝ}, x ≠ 0 →
      g x = ∫ u in (1 : ℝ)..2, φp (x * u) := by
    intro x hx
    simp [g, φp, monotoneUpperAverage]
  have hg_eq_primitive : ∀ {x : ℝ}, x ≠ 0 →
      g x = x⁻¹ * (F (2 * x) - F x) := by
    intro x hx
    rw [hg_eq_integral hx, intervalIntegral.integral_comp_mul_left φp hx]
    rw [intervalIntegral.integral_interval_sub_left]
    · simp only [smul_eq_mul]
      congr 2 <;> ring
    all_goals exact hφp_mono.intervalIntegrable
  have hg_nonneg : ∀ x ≥ 0, 0 ≤ g x := by
    intro x hx
    rcases hx.eq_or_lt with rfl | hx
    · exact hg_zero.ge
    · rw [hg_eq_integral hx.ne']
      apply intervalIntegral.integral_nonneg
      · norm_num
      · intro u hu
        calc
          0 = φp 0 := by simp [φp, hφ_zero]
          _ ≤ φp (x * u) := hφp_mono (mul_nonneg hx.le (le_trans (by norm_num) hu.1))
  have hg_bound : ∀ x ≥ 0, φ x ≤ g x := by
    intro x hx
    rcases hx.eq_or_lt with rfl | hx
    · simp [hg_zero, hφ_zero]
    · rw [hg_eq_integral hx.ne']
      calc
        φ x = ∫ _ in (1 : ℝ)..2, φ x := by norm_num
        _ ≤ ∫ u in (1 : ℝ)..2, φp (x * u) := by
          apply intervalIntegral.integral_mono_on (by norm_num)
          · exact intervalIntegrable_const
          · exact (hφp_mono.comp
              (fun _ _ h => mul_le_mul_of_nonneg_left h hx.le)).intervalIntegrable
          · intro u hu
            rw [show φ x = φp x by simp [φp, hx.le]]
            exact hφp_mono (by simpa using mul_le_mul_of_nonneg_left hu.1 hx.le)
  have hg_mono : MonotoneOn g (Set.Ici 0) := by
    intro x hx y hy hxy
    rcases (Set.mem_Ici.mp hx).eq_or_lt with rfl | hx
    · simpa [hg_zero] using hg_nonneg y hy
    · have hypos : 0 < y := hx.trans_le hxy
      rw [hg_eq_integral hx.ne', hg_eq_integral hypos.ne']
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact (hφp_mono.comp (fun _ _ h => mul_le_mul_of_nonneg_left h hx.le)).intervalIntegrable
      · exact (hφp_mono.comp (fun _ _ h => mul_le_mul_of_nonneg_left h hypos.le)).intervalIntegrable
      · intro u hu
        exact hφp_mono (mul_le_mul_of_nonneg_right hxy (le_trans (by norm_num) hu.1))
  have hg_cont_pos : ∀ x, 0 < x → ContinuousAt g x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.ne'
    have hq_cont : ContinuousAt (fun y => y⁻¹ * (F (2 * y) - F y)) x :=
      (continuousAt_id.inv₀ hx0).mul
        ((hF_cont.continuousAt.comp (continuousAt_const.mul continuousAt_id)).sub
          hF_cont.continuousAt)
    apply hq_cont.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx0] with y hy
    exact hg_eq_primitive hy
  have hg_cont_zero : ContinuousWithinAt g (Set.Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hφδ⟩ := Metric.continuousWithinAt_iff.mp hφ_cont_zero ε hε
    refine ⟨δ / 2, half_pos hδ, ?_⟩
    intro x hx hxd
    have hx0 : 0 ≤ x := hx
    have hxlt : x < δ / 2 := by simpa [Real.dist_eq, abs_of_nonneg hx0] using hxd
    have h2x_mem : 2 * x ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (mul_nonneg (by norm_num) hx0)
    have h2x_dist : dist (2 * x) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg h2x_mem]
      linarith
    have hφ2x := hφδ h2x_mem h2x_dist
    have hupper : g x ≤ φ (2 * x) := by
      rcases hx0.eq_or_lt with rfl | hxpos
      · simp [hg_zero, hφ_zero]
      · rw [hg_eq_integral hxpos.ne']
        calc
          _ ≤ ∫ _ in (1 : ℝ)..2, φ (2 * x) := by
            apply intervalIntegral.integral_mono_on (by norm_num)
            · exact (hφp_mono.comp
                (fun _ _ h => mul_le_mul_of_nonneg_left h hxpos.le)).intervalIntegrable
            · exact intervalIntegrable_const
            · intro u hu
              rw [show φp (x * u) = φ (x * u) by
                simp [φp, mul_nonneg hxpos.le (le_trans (by norm_num) hu.1)]]
              exact hφ_mono (Set.mem_Ici.mpr (mul_nonneg hxpos.le (le_trans (by norm_num) hu.1)))
                h2x_mem (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hu.2 hxpos.le)
          _ = φ (2 * x) := by norm_num
    rw [hg_zero, Real.dist_eq, sub_zero, abs_of_nonneg (hg_nonneg x hx0)]
    exact hupper.trans_lt ((le_abs_self _).trans_lt (by simpa [hφ_zero, Real.dist_eq] using hφ2x))
  have hg_cont : ContinuousOn g (Set.Ici 0) := by
    intro x hx
    rcases (Set.mem_Ici.mp hx).eq_or_lt with rfl | hxpos
    · exact hg_cont_zero
    · exact (hg_cont_pos x hxpos).continuousWithinAt
  let f : ℝ → ℝ := fun x => x + g x
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · simp [f, hg_zero]
  · exact continuousOn_id.add hg_cont
  · intro x hx y hy hxy
    exact add_lt_add_of_lt_of_le hxy (hg_mono hx hy hxy.le)
  · rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨max b 0, fun x hx => ?_⟩
    change b ≤ x + g x
    exact (le_max_left b 0).trans <| hx.trans <| le_add_of_nonneg_right
      (hg_nonneg x ((le_max_right b 0).trans hx))
  · intro s hs
    exact (hg_bound s hs).trans (le_add_of_nonneg_left hs)

/-- A monotonically non-decreasing function starting continuously at zero on `[0, r]` can be
upper-bounded by a strictly monotonic continuous function.

This is proved by clamping `φ` beyond `r` and invoking the global upper-majorant theorem. -/
@[blueprint "lem:exists-strictMono-upper-bound"
  (title := "Class $\\mathcal{K}$ majorant on a bounded interval")
  (latexEnv := "lemma")
  (statement := /-- Let $r > 0$ and let $\varphi$ satisfy $\varphi(0) = 0$, be right-continuous
    at zero within $[0,r]$, and be monotone on $[0, r]$.  Then there are $b > 0$ and an $f$
    with $f(0) = 0$, $f(r) = b$, $f$ continuous and strictly increasing on $[0, r]$, and
    $\varphi(s) \le f(s)$ for all $s \in [0, r]$. -/)
  (proof := /-- Clamp $\varphi$ to $\varphi_{\mathrm{ext}}(s) = \varphi(\min(s, r))$, which
    is monotone on all of $[0,\infty)$ and still vanishes at $0$, and apply
    \cref{lem:exists-strictMono-upper-bound-global}.  Restricting the resulting majorant to
    $[0, r]$ gives $f$; $b = f(r) > 0$ because $f$ is strictly increasing from $f(0) = 0$. -/)]
lemma exists_strictMono_upper_bound (r : ℝ) (hr : 0 < r) (φ : ℝ → ℝ)
    (hφ_zero : φ 0 = 0)
    (hφ_mono : MonotoneOn φ (Set.Icc 0 r))
    (hφ_cont_zero : ContinuousWithinAt φ (Set.Icc 0 r) 0) :
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
    · exact hφ_mono ⟨hs₁, h_le.trans h2⟩ ⟨hs₁.trans h_le, h2⟩ h_le   -- both ≤ r
    · exact hφ_mono ⟨hs₁, h1⟩ ⟨hr.le, le_rfl⟩ h1                     -- s₁ ≤ r < s₂
    · linarith [not_le.mp h1]                -- s₁ > r, s₂ ≤ r: impossible
    · exact le_refl _                        -- both > r
  have hφ_ext_cont_zero : ContinuousWithinAt φ_ext (Set.Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.mp hφ_cont_zero ε hε
    refine ⟨min δ r, lt_min hδ hr, ?_⟩
    intro s hs hsd
    have hs0 : 0 ≤ s := hs
    have hslt : s < min δ r := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hs0] using hsd
    have hsle : s ≤ r := (hslt.trans_le (min_le_right δ r)).le
    rw [show φ_ext s = φ s by simp [φ_ext, hsle], show φ_ext 0 = φ 0 by simp [φ_ext, hr.le]]
    exact hcont ⟨hs0, hsle⟩ (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs0]
      exact hslt.trans_le (min_le_left δ r))
  -- Apply the proved global upper-majorant theorem to φ_ext
  obtain ⟨f, hf_zero, hf_cont, hf_mono, _, hf_bound⟩ :=
    exists_strictMono_upper_bound_global φ_ext hφ_ext_zero hφ_ext_mono hφ_ext_cont_zero
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

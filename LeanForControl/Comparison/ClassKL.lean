import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue

import LeanForControl.axioms
import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKInfty
import LeanForControl.Comparison.ClassL
import LeanForControl.Analysis.MonotoneFunctions

import Architect

open Set Filter Topology MeasureTheory intervalIntegral



-- ─── Class KL ─────────────────────────────────────────────────────────────────

/-! ### Class KL

A *class KL* function `β(r, s)` is class K in `r` for each fixed `s`, and for each
fixed `r` it is strictly decreasing in `s` and tends to zero as `s → ∞`.
It arises as the bound in asymptotic stability estimates: `‖x(t)‖ ≤ β(‖x₀‖, t)`. -/

/-- A class KL function `β : [0,a) × [0,∞) → ℝ`:
    class K in the first argument, antitone and tending to 0 in the second. -/
@[blueprint "def:isClassKL"
  (statement := /-- A \emph{class $\mathcal{KL}$} function on $[0,a) \times [0,\infty)$
    is continuous, class $\mathcal{K}$ in the first argument, and for each fixed $r > 0$
    is strictly decreasing and tends to $0$ as $s \to \infty$. It arises as the bound
    $\|x(t)\| \le \beta(\|x_0\|, t)$ in asymptotic stability estimates. -/)]
structure ClassKL (a : ℝ) where
  ha : 0 < a
  /-- The forward function of a class KL function. -/
  toFun : ℝ → ℝ → ℝ
  map_zero      : ∀ s ≥ 0, toFun 0 s = 0
  continuous    : ContinuousOn (Function.uncurry toFun) (Set.Ico 0 a ×ˢ Set.Ici 0)
  strict_mono_r : ∀ s ≥ 0, StrictMonoOn (fun r => toFun r s) (Set.Ico 0 a)
  nonneg        : ∀ r ∈ Set.Ico 0 a, ∀ s ≥ 0, 0 ≤ toFun r s
  anti_s        : ∀ r ∈ Set.Ico 0 a, AntitoneOn (fun s => toFun r s) (Set.Ici 0)
  tendsto_zero  : ∀ r ∈ Set.Ico 0 a,
      Filter.Tendsto (fun s => toFun r s) Filter.atTop (nhds 0)


-- ─── ClassKL Basic API ────────────────────────────────────────────────────────

@[simp]
theorem ClassKL.map_zero_r {a : ℝ} (β : ClassKL a) {s : ℝ} (hs : 0 ≤ s) :
    β.toFun 0 s = 0 :=
  β.map_zero s hs

@[simp]
theorem ClassKL.tendsto_zero_s {a : ℝ} (β : ClassKL a) {r : ℝ} (hr : r ∈ Set.Ico 0 a) :
    Filter.Tendsto (fun s => β.toFun r s) Filter.atTop (nhds 0) :=
  β.tendsto_zero r hr

@[gcongr]
theorem ClassKL.mono_r {a : ℝ} (β : ClassKL a) {r₁ r₂ : ℝ} {s : ℝ}
    (hr₁ : r₁ ∈ Set.Ico 0 a) (hr₂ : r₂ ∈ Set.Ico 0 a) (hs : 0 ≤ s)
    (h : r₁ ≤ r₂) : β.toFun r₁ s ≤ β.toFun r₂ s :=
  (β.strict_mono_r s hs).monotoneOn hr₁ hr₂ h

@[gcongr]
theorem ClassKL.anti_s_mono {a : ℝ} (β : ClassKL a) {r : ℝ} {s₁ s₂ : ℝ}
    (hr : r ∈ Set.Ico 0 a) (hs₁ : s₁ ∈ Set.Ici 0) (hs₂ : s₂ ∈ Set.Ici 0)
    (h : s₁ ≤ s₂) : β.toFun r s₂ ≤ β.toFun r s₁ :=
  β.anti_s r hr hs₁ hs₂ h

/-- Product of a class K function and a class L function is class KL.
    `β(r, s) = α(r) * γ(s)`. -/
noncomputable def ClassKL.mk_mul {a b : ℝ} (α : ClassK a b) (γ : ClassL) : ClassKL a where
  ha := α.ha
  toFun r s := α.toFun r * γ.toFun s
  map_zero s _ := by simp [α.map_zero]
  continuous := ContinuousOn.mul
    (α.continuous.comp continuous_fst.continuousOn (fun p hp => hp.1))
    (γ.continuous.comp continuous_snd.continuousOn (fun p hp => hp.2))
  strict_mono_r s hs x hx y hy hxy :=
    -- Strict monotonicity is preserved because γ(s) is strictly positive
    mul_lt_mul_of_pos_right (α.strict_mono hx hy hxy) (γ.pos s hs)
  nonneg r hr s hs :=
    mul_nonneg (α.maps_to hr).1 (γ.pos s hs).le
  anti_s r hr s₁ hs₁ s₂ hs₂ hs :=
    -- Reverses direction properly because α(r) ≥ 0
    mul_le_mul_of_nonneg_left (γ.anti hs₁ hs₂ hs) (α.maps_to hr).1
  tendsto_zero r hr := by
    -- The limit as s → ∞ of α(r) * γ(s) is α(r) * 0 = 0
    simpa only [mul_zero] using Filter.Tendsto.const_mul (α.toFun r) γ.tendsto_zero


-- /-- Pointwise min of a class KL and a class K function (in the r-argument) is class KL. -/
-- noncomputable def ClassKL.min_classK {a b : ℝ} (β : ClassKL a) (α : ClassK a b) : ClassKL a := by
--   sorry

/-- Sontag-style KL construction from a class K spatial bound and a singular class L time decay.
    `β(r, 0) = α(r)` and `β(r, s) = min(α(r), √(α(r) * U(s)))` for `s > 0`. -/
noncomputable def ClassKL.mk_singular_cap {a b : ℝ} (α : ClassK a b) (U : ClassLSingular) :
    ClassKL a where
  ha := α.ha

  toFun r s := if s = 0 then α.toFun r
               else min (α.toFun r) (Real.sqrt (α.toFun r * U.toFun s))

  map_zero s hs := by
    split_ifs with h0
    · exact α.map_zero
    · simp [α.map_zero]

  nonneg r hr s hs := by
    split_ifs with h0
    · exact (α.maps_to hr).1
    · exact le_min (α.maps_to hr).1 (Real.sqrt_nonneg _)

  strict_mono_r s hs := by
    split_ifs with h0
    · -- s = 0: β(r, 0) = α(r), strictly mono by hypothesis
      exact α.strict_mono
    · -- s > 0: both α(r) and √(α(r)*U(s)) are strictly increasing in r
      intro r₁ hr₁ r₂ hr₂ h_lt
      have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm h0)
      have h_α_lt : α.toFun r₁ < α.toFun r₂ := α.strict_mono hr₁ hr₂ h_lt
      exact min_lt_min h_α_lt (Real.sqrt_lt_sqrt
        (mul_nonneg (α.maps_to hr₁).1 (U.pos s hs_pos).le)
        (mul_lt_mul_of_pos_right h_α_lt (U.pos s hs_pos)))

  anti_s r hr s₁ hs₁ s₂ hs₂ hle := by
    rcases (Set.mem_Ici.mp hs₁).eq_or_lt with rfl | hs₁pos
    · rcases (Set.mem_Ici.mp hs₂).eq_or_lt with rfl | hs₂pos
      · exact le_rfl
      · simp only [if_true, if_neg hs₂pos.ne']
        exact min_le_left _ _
    · rcases (Set.mem_Ici.mp hs₂).eq_or_lt with rfl | hs₂pos
      · linarith
      · simp only [if_neg hs₁pos.ne', if_neg hs₂pos.ne']
        gcongr
        · exact (α.maps_to hr).1
        · exact U.anti (Set.mem_Ioi.mpr hs₁pos) (Set.mem_Ioi.mpr hs₂pos) hle

  tendsto_zero r hr := by
    have h_α : 0 ≤ α.toFun r := (α.maps_to hr).1
    apply (tendsto_min_sqrt_mul_zero h_α U.tendsto_zero).congr'
    filter_upwards [Filter.eventually_ne_atTop 0] with s hs
    exact (if_neg hs).symm

  continuous := by
    -- Strategy:
    -- • s > 0: nearby points also have s' > 0, so if_neg fires and β is a
    --   composition of continuous functions (α, U, sqrt, min).
    -- • s = 0, r = 0: squeeze β between 0 and α(p.1) → 0.
    -- • s = 0, r > 0: find buffer r₁ > r and use U.tendsto_top to get δ > 0
    --   such that U(s') ≥ α(r₁) for s' ∈ (0,δ). In Iio(r₁)×[0,δ), min = α(p.1)
    --   so β is locally just α, which is continuous.
    rintro ⟨r₀, s₀⟩ ⟨hr₀, hs₀⟩
    change ContinuousWithinAt (fun p : ℝ × ℝ => if p.2 = 0 then α.toFun p.1
      else min (α.toFun p.1) (Real.sqrt (α.toFun p.1 * U.toFun p.2)))
      (Set.Ico 0 a ×ˢ Set.Ici 0) (r₀, s₀)
    have hs_nn : 0 ≤ s₀ := hs₀
    have hr_nn : 0 ≤ r₀ := hr₀.1
    rcases eq_or_lt_of_le hs_nn with rfl | hs₀_pos
    · rcases eq_or_lt_of_le hr_nn with rfl | hr_pos
      · have h_bound : ∀ p ∈ Set.Ico 0 a ×ˢ Set.Ici 0,
            0 ≤ (if p.2 = 0 then α.toFun p.1 else min (α.toFun p.1)
                  (Real.sqrt (α.toFun p.1 * U.toFun p.2))) ∧
                (if p.2 = 0 then α.toFun p.1 else min (α.toFun p.1)
                  (Real.sqrt (α.toFun p.1 * U.toFun p.2))) ≤ α.toFun p.1 := by
          rintro ⟨r, s⟩ ⟨hr, hs⟩; dsimp only
          split_ifs
          · exact ⟨(α.maps_to hr).1, le_rfl⟩
          · exact ⟨le_min (α.maps_to hr).1 (Real.sqrt_nonneg _), min_le_left _ _⟩
        have h_tendsto_zero : Filter.Tendsto
              (fun _ : ℝ × ℝ => (0 : ℝ))
              (𝓝[Set.Ico 0 a ×ˢ Set.Ici 0] (0, 0)) (𝓝 0) :=
          tendsto_const_nhds
        have h_tendsto_alpha : Filter.Tendsto (fun p : ℝ × ℝ => α.toFun p.1)
          (𝓝[Set.Ico 0 a ×ˢ Set.Ici 0] (0, 0)) (𝓝 0) := by
          have h_cont_alpha : ContinuousWithinAt α.toFun (Set.Ico 0 a) 0 :=
            α.continuous 0 ⟨le_rfl, α.ha⟩
          have h_comp : ContinuousWithinAt (fun p : ℝ × ℝ => α.toFun p.1)
              (Ico 0 a ×ˢ Ici 0) (0, 0) :=
              ContinuousWithinAt.comp h_cont_alpha continuous_fst.continuousWithinAt
                (fun _ hp => hp.1)
          have h_tendsto : Tendsto (fun p : ℝ × ℝ => α.toFun p.1) (𝓝[Ico 0 a ×ˢ Ici 0] (0, 0))
              (𝓝 (α.toFun 0)) := h_comp
          simp only [α.map_zero] at h_tendsto
          exact h_tendsto
        --have h_eval : (if (0 : ℝ) = 0 then α.toFun 0 else _) = 0 := by simp [α.map_zero]
        rw [ContinuousWithinAt]
        simp only [α.map_zero]
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_tendsto_zero h_tendsto_alpha
        · filter_upwards [self_mem_nhdsWithin] with p hp; exact (h_bound p hp).1
        · filter_upwards [self_mem_nhdsWithin] with p hp; exact (h_bound p hp).2
      · -- r₀ > 0, s₀ = 0: U(s) blows up, so the min() caps at α(r).
        have h_cont_proxy : ContinuousWithinAt (fun p : ℝ × ℝ => α.toFun p.1)
          (Set.Ico 0 a ×ˢ Set.Ici 0) (r₀, 0) :=
          (α.continuous r₀ hr₀).comp continuous_fst.continuousWithinAt (fun _ hp => hp.1)
        refine ContinuousWithinAt.congr_of_eventuallyEq h_cont_proxy ?_ ?_
        · -- 1. Find a buffer radius r₁ slightly larger than r₀
          obtain ⟨r₁, hr₀_lt_r₁, hr₁_lt_a⟩ := exists_between hr₀.2
          have hr₁_Ico : r₁ ∈ Set.Ico 0 a := ⟨(hr₀.1.trans hr₀_lt_r₁.le), hr₁_lt_a⟩
          -- 2. Extract the filter blow-up property for U(s)
          have h_U_huge : ∀ᶠ s in 𝓝[>] 0, α.toFun r₁ < U.toFun s :=
            U.tendsto_top (eventually_gt_atTop (α.toFun r₁))
          -- The Golden Key: Convert 𝓝[>] 0 to standard 𝓝 0 with an implication
          have h_U_nhd : ∀ᶠ s in 𝓝 0, 0 < s → α.toFun r₁ < U.toFun s :=
            eventually_nhdsWithin_iff.mp h_U_huge
          -- 3. Push the 1D filters seamlessly into the 2D neighborhood! No δ needed.
          filter_upwards [
            continuous_fst.continuousWithinAt.eventually (Iio_mem_nhds hr₀_lt_r₁),
            continuous_snd.continuousWithinAt.eventually h_U_nhd,
            self_mem_nhdsWithin
          ] with p hp_x hp_U hp_domain
          -- 4. Evaluate the minimum inside this filter intersection
          have h_px_lt : p.1 < r₁ := hp_x
          have h_px_Ico : p.1 ∈ Set.Ico 0 a := hp_domain.1
          by_cases hy0 : p.2 = 0
          · simp [hy0]
          · simp only [hy0, if_false]
            have hy_pos : 0 < p.2 := lt_of_le_of_ne hp_domain.2 (Ne.symm hy0)
            -- Because p.2 > 0, the filter implication instantly gives us the bound
            have h_U_gt : α.toFun r₁ < U.toFun p.2 := hp_U hy_pos
            -- Prove local α(p.1) is strictly bounded by α(r₁)
            have h_alpha_px_lt : α.toFun p.1 < α.toFun r₁ :=
              α.strict_mono h_px_Ico hr₁_Ico h_px_lt
            -- Squash the minimum via nonlinear arithmetic over the square root
            have h_alpha_px_le_U : α.toFun p.1 ≤ U.toFun p.2 := h_alpha_px_lt.le.trans h_U_gt.le
            have h_px_pos : 0 ≤ α.toFun p.1 := (α.maps_to h_px_Ico).1
            apply min_eq_left
            have h_sq_le : α.toFun p.1 * α.toFun p.1 ≤ α.toFun p.1 * U.toFun p.2 :=
              mul_le_mul_of_nonneg_left h_alpha_px_le_U h_px_pos
            have h_sqrt : Real.sqrt (α.toFun p.1 * α.toFun p.1) ≤
              Real.sqrt (α.toFun p.1 * U.toFun p.2) :=
              Real.sqrt_le_sqrt h_sq_le
            rwa [Real.sqrt_mul_self h_px_pos] at h_sqrt
        · -- The evaluation at the exact point (r₀, 0)
          simp
    · have hs_ne : s₀ ≠ 0 := hs₀_pos.ne'
      refine ContinuousWithinAt.congr_of_eventuallyEq
        (f := fun p => min (α.toFun p.1)
          (Real.sqrt (α.toFun p.1 * U.toFun p.2))
          ) ?_ ?_ (by simp [hs_ne])
      · have h_alpha : ContinuousWithinAt (fun p : ℝ × ℝ => α.toFun p.1)
            (Set.Ico 0 a ×ˢ Set.Ici 0) (r₀, s₀) :=
          (α.continuous r₀ hr₀).comp continuous_fst.continuousWithinAt (fun _ hp => hp.1)
        have h_U_1d : ContinuousAt U.toFun s₀ :=
        (U.continuous s₀ hs₀_pos).continuousAt (Ioi_mem_nhds hs₀_pos)
        have h_U_2d : ContinuousWithinAt (fun p : ℝ × ℝ => U.toFun p.2)
          (Set.Ico 0 a ×ˢ Set.Ici 0) (r₀, s₀) :=
        h_U_1d.comp_continuousWithinAt continuous_snd.continuousWithinAt
        have h_mul := ContinuousWithinAt.mul h_alpha h_U_2d
        have h_sqrt := Real.continuous_sqrt.continuousAt.comp_continuousWithinAt h_mul
        exact continuous_min.continuousAt.tendsto.comp (h_alpha.tendsto.prodMk_nhds h_sqrt)
      · have h_snd : Filter.Tendsto (fun p : ℝ × ℝ => p.2)
            (𝓝[Set.Ico 0 a ×ˢ Set.Ici 0] (r₀, s₀)) (𝓝 s₀) :=
          continuous_snd.continuousWithinAt
        filter_upwards [h_snd.eventually (Ioi_mem_nhds hs₀_pos)] with p hp_pos
        exact if_neg hp_pos.ne'




theorem ClassKL.continuous_r {a : ℝ} (β : ClassKL a) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (fun r => β.toFun r s) (Set.Ico 0 a) :=
  (β.continuous.comp (continuousOn_id.prodMk (continuousOn_const))
    (fun _ hr => Set.mk_mem_prod hr hs)).congr (fun _ _ => rfl)


@[fun_prop]
theorem ClassKL.continuousOn_r {a : ℝ} (β : ClassKL a) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (fun r => β.toFun r s) (Set.Ico 0 a) := β.continuous_r hs




/-- Post-composing a class KL function with a class K∞ function yields class KL.
    (Applies `α` to the output of `β`.) -/
def ClassKL.comp_left_KInfty {a : ℝ} (β : ClassKL a) (α : ClassKInfty) : ClassKL a where
  ha            := β.ha
  toFun r s     := α.toFun (β.toFun r s)
  map_zero s hs := by simp only [β.map_zero s hs, α.map_zero]

  continuous s hs := by
    apply
    α.continuous.comp (β.continuous) (fun p hp => β.nonneg p.1 hp.1 p.2 hp.2)
    exact hs
  strict_mono_r s hs x hx y hy hxy :=
    α.strict_mono (β.nonneg x hx s hs) (β.nonneg y hy s hs)
      (β.strict_mono_r s hs hx hy hxy)
  nonneg r hr s hs := α.maps_to (β.nonneg r hr s hs)
  anti_s r hr s₁ hs₁ s₂ hs₂ hs :=
    α.strict_mono.monotoneOn (β.nonneg r hr s₂ hs₂) (β.nonneg r hr s₁ hs₁)
      (β.anti_s r hr hs₁ hs₂ hs)
  tendsto_zero r hr := by
    have hβ := β.tendsto_zero r hr
    have hβ_ici : ∀ᶠ s in Filter.atTop, β.toFun r s ∈ Set.Ici 0 := by
      filter_upwards [eventually_ge_atTop 0] with s hs
      exact β.nonneg r hr s hs
    have hβ_within := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun s => β.toFun r s) hβ hβ_ici
    have hα_cont := α.continuous.continuousWithinAt self_mem_Ici
    have h := hα_cont.tendsto.comp hβ_within
    rwa [α.map_zero] at h

/-- Post-composing a class KL function with a class K function yields class KL,
    provided the range of `β` is strictly within the domain of `α`. -/
def ClassKL.comp_left_K {a b c : ℝ} (β : ClassKL a) (α : ClassK b c)
    (h_range : ∀ r ∈ Set.Ico 0 a, ∀ s ≥ 0, β.toFun r s < b) : ClassKL a where
  ha            := β.ha
  toFun r s     := α.toFun (β.toFun r s)
  map_zero s hs := by simp only [β.map_zero s hs, α.map_zero]

  continuous := by
    apply α.continuous.comp β.continuous
    intro p hp
    exact ⟨β.nonneg p.1 hp.1 p.2 hp.2, h_range p.1 hp.1 p.2 hp.2⟩

  strict_mono_r s hs x hx y hy hxy :=
    α.strict_mono ⟨β.nonneg x hx s hs, h_range x hx s hs⟩
                  ⟨β.nonneg y hy s hs, h_range y hy s hs⟩
                  (β.strict_mono_r s hs hx hy hxy)

  nonneg r hr s hs := (α.maps_to ⟨β.nonneg r hr s hs, h_range r hr s hs⟩).1

  anti_s r hr s₁ hs₁ s₂ hs₂ hs :=
    α.strict_mono.monotoneOn ⟨β.nonneg r hr s₂ hs₂, h_range r hr s₂ hs₂⟩
                             ⟨β.nonneg r hr s₁ hs₁, h_range r hr s₁ hs₁⟩
                             (β.anti_s r hr hs₁ hs₂ hs)

  tendsto_zero r hr := by
    have hβ := β.tendsto_zero r hr
    have hβ_ico : ∀ᶠ s in Filter.atTop, β.toFun r s ∈ Set.Ico 0 b := by
      filter_upwards [eventually_ge_atTop 0] with s hs
      exact ⟨β.nonneg r hr s hs, h_range r hr s hs⟩
    have hβ_within := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun s => β.toFun r s) hβ hβ_ico
    have hα_cont := α.continuous.continuousWithinAt ⟨le_refl 0, α.ha⟩
    have h := hα_cont.tendsto.comp hβ_within
    rwa [α.map_zero] at h



/-- Pre-composing a class KL function with a class K function yields class KL.
    (Applies `α` to the first argument of `β`.) -/
def ClassKL.comp_right {a b : ℝ} (β : ClassKL b) (α : ClassK a b) : ClassKL a where
  ha            := α.ha
  toFun r s     := β.toFun (α.toFun r) s
  map_zero s hs := by simp only [α.map_zero, β.map_zero s hs]
  continuous s hs  := by
    apply β.continuous.comp
      ((α.continuous.comp continuousOn_fst (fun p hp => hp.1)).prodMk continuousOn_snd)
      (fun p hp => ⟨α.maps_to hp.1, hp.2⟩)
    exact hs

  strict_mono_r s hs x hx y hy hxy :=
    β.strict_mono_r s hs (α.maps_to hx) (α.maps_to hy) (α.strict_mono hx hy hxy)
  nonneg r hr s hs   := β.nonneg (α.toFun r) (α.maps_to hr) s hs
  anti_s r hr        := β.anti_s (α.toFun r) (α.maps_to hr)
  tendsto_zero r hr  := β.tendsto_zero (α.toFun r) (α.maps_to hr)




-- ─── Class KL Global ─────────────────────────────────────────────────────────

/-! ### Class KL Global

A *global class KL* function `β(r, s)` is like `ClassKL` but defined on all of
`[0, ∞) × [0, ∞)`: class K∞ in the first argument (continuous, strictly increasing,
zero at zero, radially unbounded), antitone and tending to 0 in the second. -/

/-- A global class KL function `β : [0,∞) × [0,∞) → ℝ`: class K∞ in the first argument,
    antitone and tending to 0 in the second. -/
@[blueprint "def:isClassKLGlobal"
  (statement := /-- A \emph{global class $\mathcal{KL}$} function is a map
    $\beta : [0,\infty) \times [0,\infty) \to \mathbb{R}$ that is class
    $\mathcal{K}_{\infty}$ in the first argument (continuous, strictly increasing,
    zero at zero, radially unbounded) and, for each fixed $r \ge 0$, is antitone
    and tends to $0$ as $s \to \infty$. -/)]
structure ClassKLGlobal where
  /-- The forward function. -/
  toFun : ℝ → ℝ → ℝ
  map_zero      : ∀ s ≥ 0, toFun 0 s = 0
  continuous    : ContinuousOn (Function.uncurry toFun) (Set.Ici 0 ×ˢ Set.Ici 0)
  strict_mono_r : ∀ s ≥ 0, StrictMonoOn (fun r => toFun r s) (Set.Ici 0)
  nonneg        : ∀ r ≥ 0, ∀ s ≥ 0, 0 ≤ toFun r s
  anti_s        : ∀ r ≥ 0, AntitoneOn (fun s => toFun r s) (Set.Ici 0)
  tendsto_zero  : ∀ r ≥ 0, Filter.Tendsto (fun s => toFun r s) Filter.atTop (nhds 0)
  --tendsto_atTop : Filter.Tendsto (fun r => toFun r 0) Filter.atTop Filter.atTop

theorem ClassKLGlobal.continuous_r {a : ℝ} (β : ClassKLGlobal) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (fun r => β.toFun r s) (Set.Ico 0 a) := by
  apply (β.continuous.comp (continuousOn_id.prodMk continuousOn_const)
        (fun x hx => Set.mk_mem_prod hx.1 hs)).congr
  intro x _
  simp



@[fun_prop]
theorem ClassKLGlobal.continuousOn_r {a} (β : ClassKLGlobal) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (fun r => β.toFun r s) (Set.Ico 0 a) :=  β.continuous_r hs



/-- Post-composing a global class KL function with a class K∞ function yields global class KL.
    (Applies `α` to the output of `β`.) -/
def ClassKLGlobal.comp_left (β : ClassKLGlobal) (α : ClassKInfty) : ClassKLGlobal where
  toFun r s     := α.toFun (β.toFun r s)
  map_zero s hs := by simp only [β.map_zero s hs, α.map_zero]
  continuous s hs := by
    apply α.continuous.comp (β.continuous) (fun p hp => β.nonneg p.1 hp.1 p.2 hp.2)
    exact hs
  strict_mono_r s hs x hx y hy hxy :=
    α.strict_mono (β.nonneg x hx s hs) (β.nonneg y hy s hs)
      (β.strict_mono_r s hs hx hy hxy)
  nonneg r hr s hs := α.maps_to (β.nonneg r hr s hs)
  anti_s r hr s₁ hs₁ s₂ hs₂ hs :=
    α.strict_mono.monotoneOn (β.nonneg r hr s₂ hs₂) (β.nonneg r hr s₁ hs₁)
      (β.anti_s r hr hs₁ hs₂ hs)
  tendsto_zero r hr := by
    have hβ := β.tendsto_zero r hr
    have hβ_ici : ∀ᶠ s in Filter.atTop, β.toFun r s ∈ Set.Ici 0 := by
      filter_upwards [eventually_ge_atTop 0] with s hs
      exact β.nonneg r hr s hs
    have hβ_within := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun s => β.toFun r s) hβ hβ_ici
    have hα_cont := α.continuous.continuousWithinAt self_mem_Ici
    have h := hα_cont.tendsto.comp hβ_within
    rwa [α.map_zero] at h
  -- tendsto_atTop := by
  --   have h_eq : (fun r => α.toFun (β.toFun r 0)) = α.toFun ∘ (fun r => β.toFun r 0) := rfl
  --   rw [h_eq]; exact α.tendsto_atTop.comp β.tendsto_atTop

/-- Product of a class K∞ function and a class L function is global class KL.
    `β(r, s) = α(r) * γ(s)`. -/
noncomputable def ClassKLGlobal.mk_mul (α : ClassKInfty) (γ : ClassL) : ClassKLGlobal where
  toFun r s     := α.toFun r * γ.toFun s
  map_zero s hs := by simp [α.map_zero]
  continuous    := ContinuousOn.mul
    (α.continuous.comp continuous_fst.continuousOn (fun p hp => hp.1))
    (γ.continuous.comp continuous_snd.continuousOn (fun p hp => hp.2))
  strict_mono_r s hs x hx y hy hxy :=
    mul_lt_mul_of_pos_right (α.strict_mono hx hy hxy) (γ.pos s hs)
  nonneg r hr s hs := mul_nonneg (α.maps_to hr) (γ.pos s hs).le
  anti_s r hr s₁ hs₁ s₂ hs₂ hs :=
    mul_le_mul_of_nonneg_left (γ.anti hs₁ hs₂ hs) (α.maps_to hr)
  tendsto_zero r hr := by
    simpa only [mul_zero] using Filter.Tendsto.const_mul (α.toFun r) γ.tendsto_zero

/-- Pointwise min of a global class KL and a class K∞ function (in the r-argument) is
    global class KL. -/
noncomputable def ClassKLGlobal.min_KInfty (β : ClassKLGlobal) (α : ClassKInfty) :
    ClassKLGlobal where
  toFun r s     := min (β.toFun r s) (α.toFun r)
  map_zero s hs := by rw [β.map_zero s hs, α.map_zero, min_self]
  continuous    := β.continuous.inf (α.continuous.comp continuous_fst.continuousOn
                    (fun p hp => hp.1))
  strict_mono_r s hs x hx y hy hxy := by
    apply lt_min
    · exact (min_le_left _ _).trans_lt (β.strict_mono_r s hs hx hy hxy)
    · exact (min_le_right _ _).trans_lt (α.strict_mono hx hy hxy)
  nonneg r hr s hs := le_min (β.nonneg r hr s hs) (α.maps_to hr)
  anti_s r hr s₁ hs₁ s₂ hs₂ hs :=
    min_le_min (β.anti_s r hr hs₁ hs₂ hs) le_rfl
  tendsto_zero r hr := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (β.tendsto_zero r hr)
    · filter_upwards [eventually_ge_atTop 0] with s hs
      exact le_min (β.nonneg r hr s hs) (α.maps_to hr)
    · filter_upwards [] with s; exact min_le_left _ _

/-- Pre-composing a global class KL function with a class K∞ function yields global class KL.
    (Applies `α` to the first argument of `β`.) -/
def ClassKLGlobal.comp_right (β : ClassKLGlobal) (α : ClassKInfty) : ClassKLGlobal where
  toFun r s     := β.toFun (α.toFun r) s
  map_zero s hs := by simp only [α.map_zero, β.map_zero s hs]
  continuous s hs :=   by
    apply β.continuous.comp
      ((α.continuous.comp continuousOn_fst (fun p hp => hp.1)).prodMk continuousOn_snd)
      (fun p hp => ⟨α.maps_to hp.1, hp.2⟩)
    exact hs
  strict_mono_r s hs x hx y hy hxy :=
    β.strict_mono_r s hs (α.maps_to hx) (α.maps_to hy) (α.strict_mono hx hy hxy)
  nonneg r hr s hs := β.nonneg (α.toFun r) (α.maps_to hr) s hs
  anti_s r hr        := β.anti_s (α.toFun r) (α.maps_to hr)
  tendsto_zero r hr  := β.tendsto_zero (α.toFun r) (α.maps_to hr)
  -- tendsto_atTop      := β.tendsto_atTop.comp α.tendsto_atTop

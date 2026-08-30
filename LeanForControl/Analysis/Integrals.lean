import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

import Architect

open MeasureTheory intervalIntegral Set Topology



open MeasureTheory intervalIntegral Real Set Filter

lemma ContinuousOn.integral_sub_adjacent_intervals {a t : ℝ} {μ : ℝ → ℝ} {s : ℝ}
    (hμ_t : ContinuousOn μ (Icc a t))
    (hs : s ∈ Icc a t) :
    (∫ τ in a..t, μ τ) - ∫ τ in a..s, μ τ = ∫ τ in s..t, μ τ := by
  linarith [intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hμ_t.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1)
    ((hμ_t.mono (Icc_subset_Icc_left hs.1)).intervalIntegrable_of_Icc hs.2)]


lemma intervalIntegral.norm_integral_le_of_norm_le_mul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → E} {v : ℝ → ℝ} {a b L : ℝ}
    (hab : a ≤ b)
    (hu_norm_int : IntervalIntegrable (fun s => ‖u s‖) volume a b)
    (hv_int : IntervalIntegrable v volume a b)
    (h_bound : ∀ s ∈ Icc a b, ‖u s‖ ≤ L * v s) :
    ‖∫ s in a..b, u s‖ ≤ L * ∫ s in a..b, v s := by
  calc ‖∫ s in a..b, u s‖
    _ ≤ ∫ s in a..b, ‖u s‖   := norm_integral_le_integral_norm hab
    _ ≤ ∫ s in a..b, L * v s := integral_mono_on hab hu_norm_int (hv_int.const_mul L) h_bound
    _ = L * ∫ s in a..b, v s := integral_const_mul L v

/-- `‖∫ a..b, u‖ ≤ C * (b - a)` from a uniform pointwise bound `‖u s‖ ≤ C` on `Icc a b`.
Hides the `uIoc`-to-`Icc` membership conversion required by Mathlib's
`norm_integral_le_of_norm_le_const`. -/
lemma intervalIntegral.norm_integral_le_const_mul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → E} {C : ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (h : ∀ s ∈ Icc a b, ‖u s‖ ≤ C) :
    ‖∫ s in a..b, u s‖ ≤ C * (b - a) := by
  have key : ‖∫ s in a..b, u s‖ ≤ C * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [uIoc_of_le hab] at hs
    exact h s ⟨hs.1.le, hs.2⟩
  rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at key

/-- The interval integral of a real constant equals `(b - a) * C`.
Convenience form of `intervalIntegral.integral_const` for `ℝ`, avoiding `•` notation. -/
lemma intervalIntegral.integral_const_eq {a b C : ℝ} :
    ∫ _ in a..b, C = (b - a) * C := by
  rw [intervalIntegral.integral_const, smul_eq_mul]


/-- The composition `s ↦ f(s, z(s))` is interval-integrable on `[t₀, t₁]` when `f` is
    jointly continuous and `z` is continuous on the interval. -/
lemma Continuous.intervalIntegrable_comp {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E → E} {z : ℝ → E}
    (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hz : ContinuousOn z (Icc t₀ t₁)) :
    IntervalIntegrable (fun s => f s (z s)) volume t₀ t₁ := by
  rw [← uIcc_of_le hle] at hz
  exact (hf_cont.comp_continuousOn
    (ContinuousOn.prodMk continuous_id.continuousOn hz)).intervalIntegrable



/-! ## Moving window integrals -/

/-- For any locally integrable `f`, the sliding half-window integral
    `η ↦ ∫ s in (η/2)..η, f s` is continuous on `(0, ∞)`. -/
@[blueprint "lem:continuousOnHalfWindowIntegral"
  (statement := /-- If $f$ is locally integrable on $(0,\infty)$, the map
    $\eta \mapsto \int_{\eta/2}^{\eta} f(s)\,ds$ is continuous on $(0,\infty)$. -/)]
lemma continuousOn_halfWindow_integral {f : ℝ → ℝ}
    (hf_int : ∀ a b, 0 < a → 0 < b → IntervalIntegrable f volume a b) :
    ContinuousOn (fun η => ∫ s in (η / 2)..η, f s) (Set.Ioi 0) := by
  intro η₀ hη₀
  -- We are on an open domain, so prove the stronger ContinuousAt
  apply ContinuousAt.continuousWithinAt
  have hη₀_pos : 0 < η₀ := hη₀
  -- Fixed window [A, B] = [η₀/4, 2η₀] around η₀ for the primitive bounds
  set A := η₀ / 4
  have hA_pos : 0 < A := by positivity
  have h_prim : ContinuousOn (fun x => ∫ s in A..x, f s) (Set.Icc A (2 * η₀)) := by
    have h := continuousOn_primitive_interval' (hf_int A (2 * η₀) hA_pos (by linarith))
      (left_mem_uIcc (b := (2 * η₀)))
    rwa [uIcc_of_le (by change η₀ / 4 ≤ 2 * η₀; linarith)] at h
  have hη₀_in : η₀ ∈ Set.Ioo A (2 * η₀) := ⟨by simp only [A]; linarith, by linarith⟩
  have hh_in  : η₀ / 2 ∈ Set.Ioo A (2 * η₀) := ⟨by simp only [A]; linarith, by linarith⟩
  have cont1 : ContinuousAt (fun η => ∫ s in A..η, f s) η₀ :=
    h_prim.continuousAt (Icc_mem_nhds hη₀_in.1 hη₀_in.2)
  have cont2 : ContinuousAt (fun η => ∫ s in A..(η / 2), f s) η₀ :=
    (h_prim.continuousAt (Icc_mem_nhds hh_in.1 hh_in.2)).comp
      (f := fun η : ℝ => η / 2) (continuous_id.div_const 2).continuousAt
  refine (cont1.sub cont2).congr ?_
  filter_upwards [Ioo_mem_nhds hη₀_in.1 hη₀_in.2] with η hη
  have hη_pos : 0 < η := hA_pos.trans hη.1
  linarith [integral_add_adjacent_intervals
    (hf_int A (η / 2) hA_pos (by linarith))
    (hf_int (η / 2) η (by linarith) hη_pos)]



/-- The scaled half-window average `η ↦ (2/η) * ∫ s in (η/2)..η, f s` is antitone on `(0, ∞)`
    whenever `f` is antitone on `(0, ∞)`. -/
@[blueprint "lem:antitoneOnHalfWindowAverage"
  (statement := /-- If $f$ is antitone on $(0,\infty)$, the map
    $\eta \mapsto \tfrac{2}{\eta}\int_{\eta/2}^{\eta} f(s)\,ds$ is antitone on $(0,\infty)$. -/)]
lemma antitoneOn_halfWindow_average {f : ℝ → ℝ}
    (hf_anti : AntitoneOn f (Set.Ioi 0))
    (hf_int : ∀ a b, 0 < a → 0 < b → IntervalIntegrable f volume a b) :
    AntitoneOn (fun η => (2 / η) * ∫ s in (η / 2)..η, f s) (Set.Ioi 0) := by
  intro η₁ hη₁ η₂ hη₂ h_le
  have hη₁_pos : (0 : ℝ) < η₁ := hη₁
  have hη₂_pos : (0 : ℝ) < η₂ := hη₂
  -- Rewrite: (2/η) * ∫ (η/2)..η, f = 2 * ∫ (1/2)..1, f(η·) via substitution s = η*t
  have hrw : ∀ η : ℝ, 0 < η → (2 / η) * ∫ s in (η / 2)..η, f s =
      2 * ∫ t in (1/2 : ℝ)..(1 : ℝ), f (η * t) := fun η hη => by
    have key : η • ∫ x in (1/2 : ℝ)..(1 : ℝ), f (η * x) =
        ∫ x in η * (1/2 : ℝ)..η * (1 : ℝ), f x := smul_integral_comp_mul_left f η
    simp only [smul_eq_mul, mul_one, show η * (1 / 2 : ℝ) = η / 2 from by ring] at key
    rw [← key, ← mul_assoc, div_mul_cancel₀ 2 hη.ne']
  dsimp only
  rw [hrw η₁ hη₁_pos, hrw η₂ hη₂_pos]
  -- Need: 2 * ∫ (1/2)..1, f(η₂·) ≤ 2 * ∫ (1/2)..1, f(η₁·)
  gcongr
  -- Integrability of f(ηᵢ·) on [1/2, 1]
  have mk_int : ∀ η : ℝ, 0 < η →
      IntervalIntegrable (fun t => f (η * t)) volume (1/2 : ℝ) 1 := fun η hη => by
    have h := (hf_int (η / 2) η (by linarith) hη).comp_mul_left (c := η)
    have heq1 : η / 2 / η = 1 / 2 := by field_simp
    rwa [heq1, div_self hη.ne'] at h
  -- Pointwise: f(η₂·t) ≤ f(η₁·t) for t ∈ [1/2, 1] since η₁·t ≤ η₂·t and f antitone
  refine integral_mono_on (by norm_num) (mk_int η₂ hη₂_pos) (mk_int η₁ hη₁_pos)
    fun t ht => hf_anti (mul_pos hη₁_pos (by linarith [ht.1]))
      (mul_pos hη₂_pos (by linarith [ht.1]))
      (by gcongr; linarith [ht.1])


/-- If `f` is nonneg, antitone on `(0, ∞)`, locally integrable, and tends to `0` at `+∞`,
    then the scaled half-window average `η ↦ (2/η) * ∫ s in (η/2)..η, f s` also tends to `0`
    at `+∞`. -/
@[blueprint "lem:tendstoHalfWindowAverageZero"
  (statement := /-- Let $f : \mathbb{R} \to \mathbb{R}$ be nonneg, antitone on $(0,\infty)$,
    locally integrable, and satisfy $f(s) \to 0$ as $s \to +\infty$.  Then
    $\tfrac{2}{\eta}\int_{\eta/2}^{\eta} f(s)\,ds \to 0$ as $\eta \to +\infty$. -/)]
lemma tendsto_halfWindow_average_zero {f : ℝ → ℝ}
    (hf_nonneg : ∀ s > 0, 0 ≤ f s)
    (hf_anti : AntitoneOn f (Set.Ioi 0))
    (hf_int : ∀ a b, 0 < a → 0 < b → IntervalIntegrable f volume a b)
    (hf_tendsto : Filter.Tendsto f Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun η => (2 / η) * ∫ s in (η / 2)..η, f s) Filter.atTop (nhds 0) := by
  -- Squeeze the average between 0 and f(η / 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (hf_tendsto.comp (tendsto_id.atTop_div_const zero_lt_two))
  · filter_upwards [Filter.eventually_gt_atTop 0] with η hη
    exact mul_nonneg (div_nonneg zero_le_two hη.le)
      (integral_nonneg (half_le_self hη.le) fun s hs =>
        hf_nonneg s ((half_pos hη).trans_le hs.1))
  · filter_upwards [Filter.eventually_gt_atTop 0] with η hη
    have h_half_pos : 0 < η / 2 := half_pos hη
    calc (2 / η) * ∫ s in (η / 2)..η, f s
        ≤ (2 / η) * ∫ s in (η / 2)..η, f (η / 2) := by
          gcongr
          exact integral_mono_on (half_le_self hη.le) (hf_int _ _ h_half_pos hη)
            intervalIntegral.intervalIntegrable_const fun s hs =>
            hf_anti h_half_pos (h_half_pos.trans_le hs.1) hs.1
      _ = f (η / 2) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          field_simp [hη.ne']; ring

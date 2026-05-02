import Mathlib

open MeasureTheory intervalIntegral Real Set Filter

/-!
# Gronwall's Inequality (Lemma A.1)

## Proof strategy (integrating-factor / variation of parameters)

Define:
  z(t) = ∫_a^t μ(s) y(s) ds
  v(t) = z(t) + Λ(t) − y(t) ≥ 0   (non-negative by hypothesis)
  M(t) = ∫_a^t μ(τ) dτ
  w(t) = exp(−M(t)) · z(t)         (integrating-factor transform)

By FTC + product rule:
  ẇ(t) = exp(−M(t)) · (μ(t)·y(t) − μ(t)·z(t))
        = exp(−M(t)) · μ(t) · (Λ(t) − v(t))
        ≤ exp(−M(t)) · μ(t) · Λ(t)   -- since exp, μ, v ≥ 0

Integrating from a (where w(a) = 0):
  w(t) ≤ ∫_a^t exp(−M(s)) μ(s) Λ(s) ds

Multiplying by exp(M(t)) and using exp(M(t))·exp(−M(s)) = exp(∫_s^t μ):
  z(t) ≤ ∫_a^t Λ(s) μ(s) exp(∫_s^t μ) ds
-/


lemma hasDerivAt_integral {a b : ℝ} {μ : ℝ → ℝ}
    (hμ : ContinuousOn μ (Icc a b)) (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun x ↦ ∫ τ in a..x, μ τ) (μ t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((hμ.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
    ((hμ.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
    (hμ.continuousAt (Icc_mem_nhds ht.1 ht.2))


lemma continuousOn_integral_Icc {a t : ℝ} {f : ℝ → ℝ}
    (hf_int : IntegrableOn f (Icc a t) volume) :
    ContinuousOn (fun s ↦ ∫ τ in a..s, f τ) (Icc a t) := by
  exact (intervalIntegral.continuousOn_primitive_Icc hf_int).congr (by
    intro s hs
    have hs' : a ≤ s := hs.1
    simp [intervalIntegral.integral_of_le hs']
    have hset : (∫ τ in Set.Ioc a s, f τ ∂volume) = ∫ τ in Set.Icc a s, f τ ∂volume := by
      have : volume ({a} : Set ℝ) = 0 := by simp
      refine setIntegral_congr_set ?_
      exact Ioc_ae_eq_Icc' this
    simp [hset]
  )


/-! ## General form -/

/-- **Gronwall's Inequality** (Lemma A.1, general form).

Let `Λ μ : ℝ → ℝ` be continuous on `[a,b]` with `μ ≥ 0`.
If `y : ℝ → ℝ` is continuous on `[a,b]` and satisfies
  `y t ≤ Λ t + ∫ s in a..t, μ s * y s`  for all `t ∈ [a,b]`,
then
  `y t ≤ Λ t + ∫ s in a..t, Λ s * μ s * exp (∫ τ in s..t, μ τ)`. -/
theorem gronwall_inequality
    {a b : ℝ} {Λ μ y : ℝ → ℝ}
    (hΛ : ContinuousOn Λ (Icc a b))
    (hμ : ContinuousOn μ (Icc a b))
    (hμ_nn : ∀ t ∈ Icc a b, 0 ≤ μ t)
    (hy : ContinuousOn y (Icc a b))
    (hineq : ∀ t ∈ Icc a b, y t ≤ Λ t + ∫ s in a..t, μ s * y s) :
    ∀ t ∈ Icc a b,
      y t ≤ Λ t + ∫ s in a..t, Λ s * μ s * exp (∫ τ in s..t, μ τ) := by
  -- ── Auxiliary functions ─────────────────────────────────────────
  let z : ℝ → ℝ := fun t => ∫ s in a..t, μ s * y s
  let M : ℝ → ℝ := fun t => ∫ τ in a..t, μ τ
  let w : ℝ → ℝ := fun t => exp (-M t) * z t
  -- ── Integrability conditions ─────────────────────────────────────
  have hμy_cont : ContinuousOn (fun s => μ s * y s) (Icc a b) := hμ.mul hy
  have hμy_ible : ∀ t ∈ Icc a b, IntervalIntegrable (fun s => μ s * y s) volume a t :=
    fun t ht =>
      (hμy_cont.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hμ_ible : ∀ t ∈ Icc a b, IntervalIntegrable μ volume a t :=
    fun t ht => (hμ.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hμΛ_ible : ∀ t ∈ Icc a b,
      IntervalIntegrable (fun s => exp (-M s) * (μ s * Λ s)) volume a t := fun t ht => by
    apply ContinuousOn.intervalIntegrable_of_Icc ht.1
    apply ContinuousOn.mul _ (hμ.mul hΛ |>.mono (Icc_subset_Icc_right ht.2))
    have hμ_int : IntegrableOn μ (Icc a t) volume := by
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      exact hμ.mono (Set.Icc_subset_Icc_right ht.2)
    have hM_cont : ContinuousOn M (Icc a t) := continuousOn_integral_Icc hμ_int
    have hnegM : ContinuousOn (fun s ↦ -M s) (Icc a t) :=
      hM_cont.neg
    have hexp : ContinuousOn Real.exp (Set.univ) :=
      continuous_exp.continuousOn
    exact ContinuousOn.rexp hnegM
  -- ── Non-negativity of v = z + Λ − y ────────────────────────────
  have hv_nn : ∀ t ∈ Icc a b, 0 ≤ z t + Λ t - y t := fun t ht => by
    have := hineq t ht; linarith
  -- ── Boundary values ─────────────────────────────────────────────
  have hz_a : z a = 0 := by simp [z]
  have hM_a : M a = 0 := by simp [M]
  have hw_a : w a = 0 := by simp [w, hM_a, hz_a]
  -- ── FTC derivatives ─────────────────────────────────────────────
  have hM_deriv : ∀ t ∈ Ioo a b, HasDerivAt M (μ t) t :=
    fun t ht => hasDerivAt_integral hμ t ht
  have hz_deriv : ∀ t ∈ Ioo a b, HasDerivAt z (μ t * y t) t := by
    intro t ht
    have ht_Icc : t ∈ Icc a b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_nhds : Icc a b ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_cont : ContinuousAt (fun s ↦ μ s * y s) t := hμy_cont.continuousAt h_nhds
    have h_int : IntervalIntegrable (fun s ↦ μ s * y s) volume a t := hμy_ible t ht_Icc
    have hμy_Ioo : ContinuousOn (fun s ↦ μ s * y s) (Ioo a b) := hμy_cont.mono Ioo_subset_Icc_self
    have h_meas : StronglyMeasurableAtFilter (fun s ↦ μ s * y s) (nhds t) volume :=
      hμy_Ioo.stronglyMeasurableAtFilter isOpen_Ioo t ht
    exact intervalIntegral.integral_hasDerivAt_right h_int h_meas h_cont
  -- ── Derivative of w via product rule ────────────────────────────
  -- ẇ(t) = exp(−M(t)) · (μ(t)·Λ(t) − μ(t)·v(t))
  have hw_deriv : ∀ t ∈ Ioo a b,
      HasDerivAt w (exp (-M t) * (μ t * Λ t - μ t * (z t + Λ t - y t))) t := by
    intro t ht
    have hMd := hM_deriv t ht
    have hzd := hz_deriv t ht
    -- d/dt [exp(−M t)] = −μ t · exp(−M t)
    have hexpd : HasDerivAt (fun t => exp (-M t)) (-μ t * exp (-M t)) t := by
      have h := hMd.neg.exp
      simp at h
      simpa [mul_comm] using h
    -- Product rule; simplify using y = z + Λ - v
    convert hexpd.mul hzd using 1; ring
  -- ── ẇ is bounded above ─────────────────────────────────────────
  -- Since exp > 0, μ ≥ 0, v ≥ 0: remove the −μ·v term
  have hw_upper : ∀ t ∈ Ioo a b,
      exp (-M t) * (μ t * Λ t - μ t * (z t + Λ t - y t))
      ≤ exp (-M t) * (μ t * Λ t) := by
    intro t ht
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (exp_pos _))
    nlinarith [hv_nn t ht', hμ_nn t ht']
  -- ── Integrate the bound to get an estimate on w ─────────────────
  -- w(a) = 0, ẇ ≤ exp(−M)·μ·Λ  ⟹  w(t) ≤ ∫_a^t exp(−M s)·μ s·Λ s ds
  have hw_bound : ∀ t ∈ Icc a b,
      w t ≤ ∫ s in a..t, exp (-M s) * (μ s * Λ s) := by
    intro t ht
    let w' := fun s ↦ rexp (-M s) * (μ s * Λ s - μ s * (z s + Λ s - y s))
    let g' := fun s ↦ rexp (-M s) * (μ s * Λ s)
    have hw_FTC : ∫ s in a..t, w' s = w t - w a := by
      -- Use the _of_le variant and pass a ≤ t (which is ht.1)
      apply integral_eq_sub_of_hasDerivAt_of_le ht.1
      · -- Needs ContinuousOn w (Icc a t)
        have hμ_int : IntegrableOn μ (Icc a t) volume := by
          apply ContinuousOn.integrableOn_compact isCompact_Icc
          exact hμ.mono (Set.Icc_subset_Icc_right ht.2)
        have hμy_int : IntegrableOn (fun s ↦ μ s * y s) (Icc a t) volume := by
          apply ContinuousOn.integrableOn_compact isCompact_Icc
          exact hμy_cont.mono (Set.Icc_subset_Icc_right ht.2)
        have hz_cont : ContinuousOn z (Icc a t) := continuousOn_integral_Icc hμy_int
        have hM_cont : ContinuousOn M (Icc a t) := continuousOn_integral_Icc hμ_int
        have hnegM_cont : ContinuousOn (fun s ↦ -M s) (Icc a t) := hM_cont.neg
        have hexp_cont : ContinuousOn (fun s ↦ rexp (-M s)) (Icc a t) :=
                Real.continuous_exp.comp_continuousOn hnegM_cont
        exact hexp_cont.mul hz_cont
      · -- Needs ∀ s ∈ Ioo a t, HasDerivAt w (w' s) s
        intro s hs
        -- Now hs is s ∈ Ioo a t, so hs.1 is strictly `a < s`
        have hs_Ioo : s ∈ Ioo a b := ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
        exact hw_deriv s hs_Ioo
      · -- Needs IntervalIntegrable w' volume a t
        have hμ_Icc : ContinuousOn μ (Icc a t) := hμ.mono (Set.Icc_subset_Icc_right ht.2)
        have hΛ_Icc : ContinuousOn Λ (Icc a t) := hΛ.mono (Set.Icc_subset_Icc_right ht.2)
        have hy_Icc : ContinuousOn y (Icc a t) := hy.mono (Set.Icc_subset_Icc_right ht.2)
        have hμ_int' : IntegrableOn μ (Icc a t) volume := by
          apply ContinuousOn.integrableOn_compact isCompact_Icc
          exact hμ_Icc
        have hM_cont : ContinuousOn M (Icc a t) := continuousOn_integral_Icc hμ_int'
        have hnegM : ContinuousOn (fun s ↦ -M s) (Icc a t) := hM_cont.neg
        have hexp_M : ContinuousOn (fun s ↦ rexp (-M s)) (Icc a t) := ContinuousOn.rexp hnegM
        have hμy_int : IntegrableOn (fun s ↦ μ s * y s) (Icc a t) volume := by
          apply ContinuousOn.integrableOn_compact isCompact_Icc
          exact hμy_cont.mono (Set.Icc_subset_Icc_right ht.2)
        have hz_cont : ContinuousOn z (Icc a t) := continuousOn_integral_Icc hμy_int
        have hw'_cont : ContinuousOn w' (Icc a t) :=
          hexp_M.mul ((hμ_Icc.mul hΛ_Icc).sub (hμ_Icc.mul ((hz_cont.add hΛ_Icc).sub hy_Icc)))
        exact hw'_cont.intervalIntegrable_of_Icc ht.1
    have hw_mono : ∫ s in a..t, w' s ≤ ∫ s in a..t, g' s := by
      --apply intervalIntegral.integral_mono (a := a) (b := t)
      apply intervalIntegral.integral_mono_on ht.1
      · -- Needs IntervalIntegrable w' (same as above)
        have hμ_Icc : ContinuousOn μ (Icc a t) := hμ.mono (Set.Icc_subset_Icc_right ht.2)
        have hΛ_Icc : ContinuousOn Λ (Icc a t) := hΛ.mono (Set.Icc_subset_Icc_right ht.2)
        have hy_Icc : ContinuousOn y (Icc a t) := hy.mono (Set.Icc_subset_Icc_right ht.2)
        have hμ_int' : IntegrableOn μ (Icc a t) volume := by
          apply ContinuousOn.integrableOn_compact isCompact_Icc
          exact hμ_Icc
        have hM_cont : ContinuousOn M (Icc a t) := continuousOn_integral_Icc hμ_int'
        have hnegM : ContinuousOn (fun s ↦ -M s) (Icc a t) := hM_cont.neg
        have hexp_M : ContinuousOn (fun s ↦ rexp (-M s)) (Icc a t) := ContinuousOn.rexp hnegM
        have hμy_int : IntegrableOn (fun s ↦ μ s * y s) (Icc a t) volume := by
          apply ContinuousOn.integrableOn_compact isCompact_Icc
          exact hμy_cont.mono (Set.Icc_subset_Icc_right ht.2)
        have hz_cont : ContinuousOn z (Icc a t) := continuousOn_integral_Icc hμy_int
        have hw'_cont : ContinuousOn w' (Icc a t) :=
          hexp_M.mul ((hμ_Icc.mul hΛ_Icc).sub (hμ_Icc.mul ((hz_cont.add hΛ_Icc).sub hy_Icc)))
        exact hw'_cont.intervalIntegrable_of_Icc ht.1
      · -- Needs IntervalIntegrable g' (you already have this exact hypothesis!)
        exact hμΛ_ible t ht
      · -- Show that w' ≤ g'
        intro s hs
        have hs_Icc : s ∈ Icc a b := ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (exp_pos _))
        nlinarith [hv_nn s hs_Icc, hμ_nn s hs_Icc]
    -- Step 3: Combine them using w(a) = 0
    rw [hw_a, sub_zero] at hw_FTC
    rw [← hw_FTC]
    exact hw_mono
  -- ── Multiply by exp(M t) and use exp(M t)·exp(−M s) = exp(∫_s^t μ) ──
  have hzt_bound : ∀ t ∈ Icc a b,
      z t ≤ ∫ s in a..t, Λ s * μ s * exp (∫ τ in s..t, μ τ) := by
    intro t ht
    have hw_le := hw_bound t ht
    have h_mul := mul_le_mul_of_nonneg_left hw_le (le_of_lt (Real.exp_pos (M t)))
    have h_LHS : rexp (M t) * w t = z t := by
      dsimp [w]
      calc rexp (M t) * (rexp (-M t) * z t)
        _ = (rexp (M t) * rexp (-M t)) * z t := by ring
        _ = rexp (M t + -M t) * z t := by rw [← Real.exp_add]
        _ = rexp 0 * z t := by congr 1; ring_nf
        _ = 1 * z t := by rw [Real.exp_zero]
        _ = z t := by ring
    rw [h_LHS] at h_mul
    have h_RHS : rexp (M t) * ∫ s in a..t, rexp (-M s) * (μ s * Λ s) =
                 ∫ s in a..t, Λ s * μ s * rexp (∫ τ in s..t, μ τ) := by
      -- Move exp(M t) inside the integral
      have h_pull_in : rexp (M t) * ∫ s in a..t, rexp (-M s) * (μ s * Λ s) =
                       ∫ s in a..t, rexp (M t) * (rexp (-M s) * (μ s * Λ s)) := by
        rw [← smul_eq_mul]
        rw [← intervalIntegral.integral_smul]
        simp_rw [smul_eq_mul]
      rw [h_pull_in]
      apply intervalIntegral.integral_congr
      intro s hs
      have hat : a ≤ t := ht.1
      have h_as : a ≤ s := by simpa [hat] using hs.1
      have h_st : s ≤ t := by simpa [hat] using hs.2
      have hs_Icc : s ∈ Icc a b := ⟨h_as, le_trans h_st ht.2⟩
      have h_int_as : IntervalIntegrable μ volume a s := hμ_ible s hs_Icc
      have h_int_st : IntervalIntegrable μ volume s t := by
        apply ContinuousOn.intervalIntegrable_of_Icc h_st
        apply hμ.mono
        intro x hx
        exact ⟨le_trans h_as hx.1, le_trans hx.2 ht.2⟩
      have h_add := intervalIntegral.integral_add_adjacent_intervals h_int_as h_int_st
      have h_interval_diff : M t - M s = ∫ τ in s..t, μ τ := by
        dsimp [M]
        linarith [h_add]
      calc rexp (M t) * (rexp (-M s) * (μ s * Λ s))
        _ = (rexp (M t) * rexp (-M s)) * (Λ s * μ s) := by ring
        _ = rexp (M t + -M s) * (Λ s * μ s) := by rw [← Real.exp_add]
        _ = Λ s * μ s * rexp (M t - M s) := by ring
        _ = Λ s * μ s * rexp (∫ τ in s..t, μ τ) := by rw [h_interval_diff]
    rw [h_RHS] at h_mul
    exact h_mul
  intro t ht
  linarith [hineq t ht, hzt_bound t ht]


/-! ## Special case 1: constant Λ -/

theorem gronwall_const_lambda
    {a b C : ℝ} {μ y : ℝ → ℝ}
    (hμ : ContinuousOn μ (Icc a b))
    (hμ_nn : ∀ t ∈ Icc a b, 0 ≤ μ t)
    (hy : ContinuousOn y (Icc a b))
    (hineq : ∀ t ∈ Icc a b, y t ≤ C + ∫ s in a..t, μ s * y s) :
    ∀ t ∈ Icc a b,
      y t ≤ C * rexp (∫ τ in a..t, μ τ) := by
  intro t ht
  -- 1. Get the unsimplified bound from your main theorem
  have hΛ : ContinuousOn (fun _ ↦ C) (Icc a b) := continuousOn_const
  have h_base := gronwall_inequality hΛ hμ hμ_nn hy hineq t ht
  -- 2. Define our primitives
  let M := fun x ↦ ∫ τ in a..x, μ τ
  let F := fun s ↦ -rexp (M t - M s)
  let f := fun s ↦ μ s * rexp (M t - M s)
  -- 3. Prove that F'(s) = f(s) using your new helper lemma and the chain rule
  have hF_deriv : ∀ s ∈ Ioo a t, HasDerivAt F (f s) s := by
    intro s hs
    -- hs is a < s < t. Map this to Ioo a b
    have hs_Ioo : s ∈ Ioo a b := ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
    have hM_deriv := hasDerivAt_integral hμ s hs_Ioo
    have h_inner : HasDerivAt (fun x ↦ M t - M x) (0 - μ s) s :=
      (hasDerivAt_const s (M t)).sub hM_deriv
    have h_exp : HasDerivAt (fun x ↦ rexp (M t - M x)) (rexp (M t - M s) * (0 - μ s)) s :=
      h_inner.exp
    have h_F_raw : HasDerivAt F (-(rexp (M t - M s) * (0 - μ s))) s :=
      h_exp.neg
    convert h_F_raw using 1
    dsimp[f]
    ring
  -- 4. Apply FTC to evaluate the integral
  have h_FTC : ∫ s in a..t, f s = F t - F a := by
    apply integral_eq_sub_of_hasDerivAt_of_le ht.1
    · -- ContinuousOn F (Icc a t)
      have hμ_Icc : ContinuousOn μ (Icc a t) := hμ.mono (Set.Icc_subset_Icc_right ht.2)
      have hμ_int : IntegrableOn μ (Icc a t) volume := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        exact hμ_Icc
      have hM_cont : ContinuousOn M (Icc a t) := continuousOn_integral_Icc hμ_int
      have h_inner : ContinuousOn (fun s ↦ M t - M s) (Icc a t) :=
        continuousOn_const.sub hM_cont
      have h_exp : ContinuousOn (fun s ↦ rexp (M t - M s)) (Icc a t) :=
        ContinuousOn.rexp h_inner
      exact h_exp.neg
    · exact hF_deriv
    · -- IntervalIntegrable f volume a t
      apply ContinuousOn.intervalIntegrable_of_Icc ht.1
      have hμ_Icc : ContinuousOn μ (Icc a t) := hμ.mono (Set.Icc_subset_Icc_right ht.2)
      have hμ_int : IntegrableOn μ (Icc a t) volume := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        exact hμ_Icc
      have hM_cont : ContinuousOn M (Icc a t) := continuousOn_integral_Icc hμ_int
      have h_inner : ContinuousOn (fun s ↦ M t - M s) (Icc a t) :=
        continuousOn_const.sub hM_cont
      have h_exp : ContinuousOn (fun s ↦ rexp (M t - M s)) (Icc a t) :=
        ContinuousOn.rexp h_inner
      exact hμ_Icc.mul h_exp
  -- 5. Evaluate the boundaries of F
  have hF_t : F t = -1 := by
    dsimp [F]
    rw [sub_self, Real.exp_zero]
  have hF_a : F a = -rexp (M t) := by
    dsimp [F, M]
    rw [intervalIntegral.integral_same, sub_zero]
  have hμ_ible : ∀ t ∈ Icc a b, IntervalIntegrable μ volume a t :=
    fun t ht => (hμ.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  -- 6. Substitute into your main inequality and do the final algebra!
  have h_integrand : ∀ s ∈ Icc a t, μ s * rexp (∫ τ in s..t, μ τ) = f s := by
    intro s hs
    have hs_Icc : s ∈ Icc a b := ⟨hs.1, le_trans hs.2 ht.2⟩
    have h_int_as : IntervalIntegrable μ volume a s := hμ_ible s hs_Icc
    have h_int_at : IntervalIntegrable μ volume a t := hμ_ible t ht
    -- Use interval addition: ∫_a^t = ∫_a^s + ∫_s^t  =>  ∫_s^t = M t - M s
    have hat : a ≤ t := ht.1
    have h_st : s ≤ t := by simpa [hat] using hs.2
    have h_as : a ≤ s := by simpa [hat] using hs.1
    have h_int_as : IntervalIntegrable μ volume a s := hμ_ible s hs_Icc
    have h_int_st : IntervalIntegrable μ volume s t := by
      apply ContinuousOn.intervalIntegrable_of_Icc h_st
      apply hμ.mono
      intro x hx
      exact ⟨le_trans h_as hx.1, le_trans hx.2 ht.2⟩
    have h_add := intervalIntegral.integral_add_adjacent_intervals h_int_as h_int_st
    have h_interval_diff : M t - M s = ∫ τ in s..t, μ τ := by
        dsimp [M]
        linarith [h_add]
    dsimp [f]
    congr 1
    rw [← h_interval_diff]
  have h_int_eval : (∫ s in a..t, C * μ s * rexp (∫ τ in s..t, μ τ)) = C * (rexp (M t) - 1) := by
    have hcongr : ∀ s ∈ Set.uIcc a t, C * μ s * rexp (∫ τ in s..t, μ τ) = C * f s :=
      fun s hs => by
        have hs' : s ∈ Icc a t := by rwa [Set.uIcc_of_le ht.1] at hs
        linear_combination C * h_integrand s hs'
    rw [intervalIntegral.integral_congr hcongr]
    rw [show ∫ s in a..t, C * f s = C * ∫ s in a..t, f s from by
      simp_rw [← smul_eq_mul (a := C)]
      exact intervalIntegral.integral_smul C f]
    rw [h_FTC, hF_t, hF_a]
    ring
  rw [h_int_eval] at h_base
  dsimp [M] at h_base
  calc y t
    _ ≤ C + C * (rexp (∫ τ in a..t, μ τ) - 1) := h_base
    _ = C * rexp (∫ τ in a..t, μ τ) := by ring


theorem gronwall_const
    {a b C μ : ℝ}
    (hμ_nn : 0 ≤ μ)
    {y : ℝ → ℝ}
    (hy : ContinuousOn y (Icc a b))
    (hineq : ∀ t ∈ Icc a b, y t ≤ C + ∫ s in a..t, μ * y s) :
    ∀ t ∈ Icc a b,
      y t ≤ C * rexp (μ * (t - a)) := by
    have hμ_cont : ContinuousOn (fun _ => μ) (Icc a b) := continuousOn_const
    have hμ_nn' : ∀ t ∈ Icc a b, 0 ≤ (fun _ => μ) t := fun t _ => hμ_nn
    -- rewrite hineq so the integrand matches the form μ s * y s
    have hineq' : ∀ t ∈ Icc a b, y t ≤ C + ∫ s in a..t, (fun _ => μ) s * y s := hineq
    have hbase := gronwall_const_lambda hμ_cont hμ_nn' hy hineq'
    intro t ht
    have hle := hbase t ht
    -- simplify ∫ τ in a..t, μ = μ * (t - a)
    have hsimp : ∫ τ in a..t, (fun _ => μ) τ = μ * (t - a) := by
      simp [mul_comm, intervalIntegral.integral_const]
    rw [hsimp] at hle
    exact hle

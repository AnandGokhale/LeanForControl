import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus



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


variable {a b : ℝ} {μ Λ y : ℝ → ℝ}
  (hμ : ContinuousOn μ (Icc a b)) (hΛ : ContinuousOn Λ (Icc a b))


/-
Wrapper for FTC
-/
lemma hasDerivAt_integral {a b : ℝ} {μ : ℝ → ℝ}
    (hμ : ContinuousOn μ (Icc a b)) (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun x ↦ ∫ τ in a..x, μ τ) (μ t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((hμ.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
    ((hμ.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
    (hμ.continuousAt (Icc_mem_nhds ht.1 ht.2))




lemma continuousOn_integral_Icc {a t : ℝ} {f : ℝ → ℝ} (h : a ≤ t)
    (hf_int : IntegrableOn f (Icc a t) volume) :
    ContinuousOn (fun s ↦ ∫ τ in a..s, f τ) (Icc a t) := by
  have hu : Set.uIcc a t = Set.Icc a t := Set.uIcc_of_le h
  rw [← hu] at hf_int ⊢
  exact intervalIntegral.continuousOn_primitive_interval hf_int


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
  intro t ht
  -- ── Auxiliary functions ─────────────────────────────────────────
  let z : ℝ → ℝ := fun t => ∫ s in a..t, μ s * y s
  let M : ℝ → ℝ := fun t => ∫ τ in a..t, μ τ
  let w : ℝ → ℝ := fun t => exp (-M t) * z t
  -- ── Consolidated Domain Properties for [a, t] ───────────────────
  have hat : a ≤ t := by grind
  have hIcc_t : Icc a t ⊆ Icc a b := by grind
  have hIoo_t : Ioo a t ⊆ Ioo a b := by grind
  -- ── Continuity and Integrability ───────────────────
  have hμ_t : ContinuousOn μ (Icc a t) := hμ.mono hIcc_t
  have hΛ_t : ContinuousOn Λ (Icc a t) := hΛ.mono hIcc_t
  have hy_t : ContinuousOn y (Icc a t) := hy.mono hIcc_t
  have hμy_cont : ContinuousOn (fun s => μ s * y s) (Icc a t) := by fun_prop
  have hμ_int : IntegrableOn μ (Icc a t) volume := hμ_t.integrableOn_compact isCompact_Icc
  have hμy_int : IntegrableOn (fun s => μ s * y s) (Icc a t) volume :=
    hμy_cont.integrableOn_compact isCompact_Icc
  have hM_cont : ContinuousOn M (Icc a t) := continuousOn_integral_Icc hat hμ_int
  have hz_cont : ContinuousOn z (Icc a t) := continuousOn_integral_Icc hat hμy_int
  have hexp_M : ContinuousOn (fun s ↦ rexp (-M s)) (Icc a t) := by fun_prop
  -- ── Non-negativity & Boundaries ──────────────────────────────────
  have hv_nn : ∀ s ∈ Icc a t, 0 ≤ z s + Λ s - y s := fun s hs => by
    have := hineq s (hIcc_t hs); linarith
  have hz_a : z a = 0 := by simp [z]
  have hM_a : M a = 0 := by simp [M]
  have hw_a : w a = 0 := by simp [w, hM_a, hz_a]
  -- ── FTC derivatives on (a, t) ───────────────────────────────────
  have hM_deriv : ∀ s ∈ Ioo a t, HasDerivAt M (μ s) s :=
    fun s hs => hasDerivAt_integral hμ s (hIoo_t hs)
  have hz_deriv : ∀ s ∈ Ioo a t, HasDerivAt z (μ s * y s) s :=
    fun s hs => hasDerivAt_integral (hμ.mul hy) s (hIoo_t hs)
  have hw_deriv : ∀ s ∈ Ioo a t,
      HasDerivAt w (exp (-M s) * (μ s * Λ s - μ s * (z s + Λ s - y s))) s := by
    intro s hs
    convert ((hM_deriv s hs).neg.exp.mul (hz_deriv s hs)) using 1
    dsimp; ring
  -- ── Integrate the bound to get an estimate on w ─────────────────
  have hw_bound : w t ≤ ∫ s in a..t, exp (-M s) * (μ s * Λ s) := by
    let w' := fun s ↦ rexp (-M s) * (μ s * Λ s - μ s * (z s + Λ s - y s))
    let g' := fun s ↦ rexp (-M s) * (μ s * Λ s)
    have hw'_cont : ContinuousOn w' (Icc a t) := by fun_prop
    have hg'_cont : ContinuousOn g' (Icc a t) := by fun_prop
    calc
      w t = w t - w a := by rw [hw_a, sub_zero]
      _ = ∫ s in a..t, w' s := by
        symm
        apply integral_eq_sub_of_hasDerivAt_of_le hat
        · exact hexp_M.mul hz_cont
        · exact hw_deriv
        · exact hw'_cont.intervalIntegrable_of_Icc hat
      _ ≤ ∫ s in a..t, g' s := by
        apply intervalIntegral.integral_mono_on hat
        · exact hw'_cont.intervalIntegrable_of_Icc hat
        · exact hg'_cont.intervalIntegrable_of_Icc hat
        · intro s hs
          dsimp [w', g']
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
          have := hμ_nn s (hIcc_t hs)
          have := hv_nn s hs
          nlinarith
  have h_interval_diff : ∀ s ∈ Icc a t, M t - M s = ∫ τ in s..t, μ τ := by
    intro s hs
    have h_int_as : IntervalIntegrable μ volume a s :=
      (hμ_t.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1
    have h_int_st : IntervalIntegrable μ volume s t :=
      (hμ_t.mono (Icc_subset_Icc_left hs.1)).intervalIntegrable_of_Icc hs.2
    dsimp [M]
    linarith [intervalIntegral.integral_add_adjacent_intervals h_int_as h_int_st]
  -- ── Multiply by exp(M t) ────────────────────────────────────────
  have hzt_bound : z t ≤ ∫ s in a..t, Λ s * μ s * exp (∫ τ in s..t, μ τ) := by
    calc
      z t = rexp (M t) * w t := by
        dsimp [w]; rw [← mul_assoc, ← Real.exp_add]; simp
      _ ≤ rexp (M t) * ∫ s in a..t, rexp (-M s) * (μ s * Λ s) := by
        apply mul_le_mul_of_nonneg_left hw_bound (le_of_lt (Real.exp_pos _))
      _ = ∫ s in a..t, rexp (M t) * (rexp (-M s) * (μ s * Λ s)) := by
        rw [← smul_eq_mul]
        rw [← intervalIntegral.integral_smul]
        simp_rw [smul_eq_mul]
      _ = ∫ s in a..t, Λ s * μ s * rexp (∫ τ in s..t, μ τ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hs_Icc : s ∈ Icc a t := by simpa [hat] using hs
        dsimp only
        rw [← h_interval_diff s hs_Icc]
        rw [← mul_assoc, ← Real.exp_add]
        ring_nf
  linarith [hineq t ht, hzt_bound]

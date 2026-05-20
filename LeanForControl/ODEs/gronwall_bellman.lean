import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Architect

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


/-
A wrapper for the Fundamental Theorem of Calculus.
Given a continuous function `μ` on `[a, b]`, this lemma proves that the
integral `x ↦ ∫ τ in a..x, μ τ` is differentiable at any interior point `t ∈ (a, b)`,
and its derivative is `μ t`.
-/


lemma hasDerivAt_integral {a b : ℝ} {μ : ℝ → ℝ}
    (hμ : ContinuousOn μ (Icc a b)) (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun x ↦ ∫ τ in a..x, μ τ) (μ t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((hμ.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
    ((hμ.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
    (hμ.continuousAt (Icc_mem_nhds ht.1 ht.2))


/-
Continuity of the integral function on a closed, ordered interval.
If a function `f` is integrable on `[a, t]`, the function defined by integrating `f`
from `a` to `s` is continuous for all `s ∈ [a, t]`.
This is a wrapper of `intervalIntegral.continuousOn_primitive_interval`
that avoids unordered interval (`uIcc`) issues by explicitly requiring `a ≤ t`.
-/



lemma continuousOn_integral_Icc {a t : ℝ} {f : ℝ → ℝ} (h : a ≤ t)
    (hf_int : IntegrableOn f (Icc a t) volume) :
    ContinuousOn (fun s ↦ ∫ τ in a..s, f τ) (Icc a t) := by
  have hu : Set.uIcc a t = Set.Icc a t := Set.uIcc_of_le h
  rw [← hu] at hf_int ⊢
  exact intervalIntegral.continuousOn_primitive_interval hf_int



private lemma interval_diff {a t : ℝ} {μ : ℝ → ℝ} {s : ℝ}
    (hμ_t : ContinuousOn μ (Icc a t))
    (hs : s ∈ Icc a t) :
    (∫ τ in a..t, μ τ) - ∫ τ in a..s, μ τ = ∫ τ in s..t, μ τ := by
  linarith [intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hμ_t.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1)
    ((hμ_t.mono (Icc_subset_Icc_left hs.1)).intervalIntegrable_of_Icc hs.2)]


/-! ## General form -/

/-
Gronwall-Bellman Inequality (Integral form with time-dependent coefficients).

This theorem provides an explicit upper bound for a function `y` that satisfies
a specific integral inequality. It is a fundamental tool in the analysis of
ordinary differential equations, often used to bound the growth of solutions or
prove uniqueness.

Let `Λ` and `μ` be continuous functions on `[a, b]`, with `μ` strictly non-negative.
If a continuous function `y` satisfies the integral inequality:
  `y t ≤ Λ t + ∫ s in a..t, μ s * y s`  for all `t ∈ [a, b]`
then `y` is bounded by:
  `y t ≤ Λ t + ∫ s in a..t, Λ s * μ s * exp (∫ τ in s..t, μ τ)`

-/


/-- **Lemma A.1** (Gronwall--Bellman). If $\Lambda, \mu$ are continuous on $[a,b]$ with
    $\mu \ge 0$, and $y$ is continuous satisfying
    $y(t) \le \Lambda(t) + \int_{a}^{t} \mu(s)\, y(s)\, ds$, then
    $y(t) \le \Lambda(t) + \int_{a}^{t} \Lambda(s)\,\mu(s)\,e^{\int_{s}^{t}\mu(\tau)\,d\tau}\,ds$.
-/
@[blueprint "thm:gronwall-bellman"
  (statement := /-- \textbf{Gronwall--Bellman inequality.}
    Let $\Lambda, \mu : [a,b] \to \mathbb{R}$ be continuous with $\mu \ge 0$, and let
    $y : [a,b] \to \mathbb{R}$ be continuous satisfying
    \[
      y(t) \;\le\; \Lambda(t) + \int_{a}^{t} \mu(s)\,y(s)\,\mathrm{d}s
      \qquad \forall\, t \in [a,b].
    \]
    Then
    \[
      y(t) \;\le\; \Lambda(t)
        + \int_{a}^{t} \Lambda(s)\,\mu(s)\,
            e^{\int_{s}^{t}\mu(\tau)\,\mathrm{d}\tau}\,\mathrm{d}s
      \qquad \forall\, t \in [a,b].
    \] -/)]
theorem gronwall_bellman_inequality {a b : ℝ} {Λ μ y : ℝ → ℝ}
    (hΛ : ContinuousOn Λ (Icc a b))
    (hμ : ContinuousOn μ (Icc a b))
    (hμ_nn : ∀ t ∈ Icc a b, 0 ≤ μ t)
    (hy : ContinuousOn y (Icc a b))
    (hineq : ∀ t ∈ Icc a b, y t ≤ Λ t + ∫ s in a..t, μ s * y s) :
    ∀ t ∈ Icc a b,
      y t ≤ Λ t + ∫ s in a..t, Λ s * μ s * exp (∫ τ in s..t, μ τ) := by
  intro t ht
  -- ── Notation and Continuity properties ──────────────────────────
  let z : ℝ → ℝ := fun t => ∫ s in a..t, μ s * y s
  let M : ℝ → ℝ := fun t => ∫ τ in a..t, μ τ
  have hμ_t : ContinuousOn μ (Icc a t) := hμ.mono (by grind)
  have hΛ_t : ContinuousOn Λ (Icc a t) := hΛ.mono (by grind)
  have hy_t : ContinuousOn y (Icc a t) := hy.mono (by grind)
  have hμy_int : IntegrableOn (fun s => μ s * y s) (Icc a t) volume :=
    (by fun_prop : ContinuousOn (fun s => μ s * y s) (Icc a t)).integrableOn_compact isCompact_Icc
  have hz_cont : ContinuousOn z (Icc a t) := continuousOn_integral_Icc ht.1 hμy_int
  have hexp_M : ContinuousOn (fun s ↦ rexp (-M s)) (Icc a t) := by
    have hM_cont := continuousOn_integral_Icc ht.1 (hμ_t.integrableOn_compact isCompact_Icc)
    fun_prop
  -- ── Integrate the bound to get an estimate on w ─────────────────
  have hw_bound : exp (-M t) * ∫ s in a..t, μ s * y s ≤ ∫ s in a..t, exp (-M s) * (μ s * Λ s) := by
    calc
      exp (-M t) * z t = exp (-M t) * z t - exp (-M a) * z a := by simp [z]
      _ = ∫ s in a..t, rexp (-M s) * (μ s * Λ s - μ s * (z s + Λ s - y s)) := by
        symm; apply integral_eq_sub_of_hasDerivAt_of_le ht.1
        · exact hexp_M.mul (continuousOn_integral_Icc ht.1 hμy_int)
        · intro s hs
          convert ((hasDerivAt_integral hμ s (by grind : s ∈ Ioo a b)).neg.exp.mul
            (hasDerivAt_integral (hμ.mul hy) s (by grind : s ∈ Ioo a b))) using 1
          dsimp; ring
        · exact (by fun_prop : ContinuousOn _ (Icc a t)).intervalIntegrable_of_Icc ht.1
      _ ≤ ∫ s in a..t, rexp (-M s) * (μ s * Λ s) := by
        apply intervalIntegral.integral_mono_on ht.1
        · exact ContinuousOn.intervalIntegrable_of_Icc ht.1 (by fun_prop)
        · exact ContinuousOn.intervalIntegrable_of_Icc ht.1 (by fun_prop)
        · intro s hs
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
          have := hμ_nn s (by grind : s ∈ Icc a b)
          have := hineq s (by grind : s ∈ Icc a b)
          nlinarith
  have h_interval_diff : ∀ s ∈ Icc a t, M t - M s = ∫ τ in s..t, μ τ :=
    fun s hs => interval_diff hμ_t hs
  -- ── Multiply by exp(M t) ────────────────────────────────────────
  have hzt_bound : z t ≤ ∫ s in a..t, Λ s * μ s * exp (∫ τ in s..t, μ τ) := by
    calc
      z t = rexp (M t) * exp (-M t) * ∫ s in a..t, μ s * y s := by
        simp[z, ← Real.exp_add]
      _ ≤ rexp (M t) * ∫ s in a..t, rexp (-M s) * (μ s * Λ s) := by
        nlinarith [hw_bound, Real.exp_pos (M t)]
      _ = ∫ s in a..t, rexp (M t) * (rexp (-M s) * (μ s * Λ s)) := by
        rw [← smul_eq_mul, ← intervalIntegral.integral_smul]
        simp_rw [smul_eq_mul]
      _ = ∫ s in a..t, Λ s * μ s * rexp (∫ τ in s..t, μ τ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp only
        rw [← h_interval_diff s (by simpa [ht.1] using hs)]
        rw [← mul_assoc, ← Real.exp_add]
        ring_nf
  linarith [hineq t ht, hzt_bound]


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
  have h_base := gronwall_bellman_inequality continuousOn_const hμ hμ_nn hy hineq t ht
  let M := fun x ↦ ∫ τ in a..x, μ τ
  have hμ_t : ContinuousOn μ (Icc a t) := hμ.mono (Icc_subset_Icc_right ht.2)
  have hM_cont : ContinuousOn M (Icc a t) :=
    continuousOn_integral_Icc ht.1 (hμ_t.integrableOn_compact isCompact_Icc)
  have h_interval_diff : ∀ s ∈ Icc a t, M t - M s = ∫ τ in s..t, μ τ :=
    fun s hs => interval_diff (hμ.mono (Icc_subset_Icc_right ht.2)) hs
  have h_int_eval : ∫ s in a..t, C * μ s * rexp (∫ τ in s..t, μ τ) = C * rexp (M t) - C := by
    have h_antideriv : ∀ s ∈ Ioo a t,
        HasDerivAt (fun s ↦ -C * rexp (M t - M s)) (C * μ s * rexp (M t - M s)) s := by
      intro s hs
      convert (((hasDerivAt_const s (M t)).sub
        (hasDerivAt_integral hμ s (Ioo_subset_Ioo le_rfl ht.2 hs))).exp.const_mul (-C)) using 1
      simp only [M]
      dsimp;ring
    have h_rw : ∫ s in a..t, C * μ s * rexp (∫ τ in s..t, μ τ)
              = ∫ s in a..t, C * μ s * rexp (M t - M s) := by
      apply intervalIntegral.integral_congr; intro s hs
      dsimp [M]
      rw [← h_interval_diff s (by simpa [uIcc_of_le ht.1] using hs)]
    rw [h_rw]
    have  := integral_eq_sub_of_hasDerivAt_of_le ht.1 (by fun_prop) h_antideriv
      ((by fun_prop : ContinuousOn (fun s => C * μ s * rexp (M t - M s))
        (Icc a t)).intervalIntegrable_of_Icc ht.1)
    simp [M] at this
    linarith
  simp only [M] at h_int_eval
  linarith [h_int_eval]



/-! ## Special case 1: constant Λ, μ -/

theorem gronwall_const
    {a b C μ : ℝ}
    (hμ_nn : 0 ≤ μ)
    {y : ℝ → ℝ}
    (hy : ContinuousOn y (Icc a b))
    (hineq : ∀ t ∈ Icc a b, y t ≤ C + ∫ s in a..t, μ * y s) :
    ∀ t ∈ Icc a b,
      y t ≤ C * rexp (μ * (t - a)) := by
    intro t ht
    have hbase := gronwall_const_lambda continuousOn_const (fun t _ => hμ_nn) hy hineq t ht
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at hbase
    exact hbase

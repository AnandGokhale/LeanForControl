import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Transform
import Mathlib.Order.Interval.Set.UnorderedInterval
import LeanForControl.ODEs.GronwallBellman
import LeanForControl.Analysis.Integrals
import LeanForControl.Analysis.IntegralCurves
import Architect

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Real Interval Pointwise Topology

/-!
# `ODEs.ODE_properties`

Existence and continuous-dependence theorems used throughout the stability track.

The integral formulation `IsIntegralSolution` and its dictionary with Mathlib's
`IsIntegralCurveOn` are general facts about ODE solutions with no control content; they live in
`Analysis/IntegralCurves.lean`, which this file imports.

## Main declarations

* `ContDiffAt.exists_isIntegralCurveOn_Icc` — local existence from a `C¹` field.
* `continuous_dependence_ODE` (Khalil, Theorem 3.4) — quantitative bound on `‖y(t) − z(t)‖`
  when `y` solves `ẏ = f` and `z` solves the perturbed system `ż = f + g`.
* `continuous_dependence_parameters` (Khalil, Theorem 3.5) — uniform `ε`-bound when both the
  initial perturbation `‖z₀ − y₀‖` and the forcing `‖g‖` are bounded by `α`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Chapter 3.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {t₀ t₁ : ℝ}
variable {f g : ℝ → E → E}
variable {y z : ℝ → E}
variable {y₀ z₀ : E}
variable {L μ : ℝ}

/-- A `C¹` vector field admits a nontrivial solution segment from every point at which it is
`C¹`. The anchor `0` is a construction choice, not a restriction: by time invariance a segment
from any anchor follows.

Reference: the Picard--Lindelöf local existence theorem. -/
@[blueprint "lem:contDiffAt-exists-isIntegralCurveOn-Icc"
  (title := "Local existence for a $C^{1}$ field")
  (latexEnv := "lemma")
  (statement := /-- Let $g$ be an autonomous field that is $C^1$ at $x_0$.  Then there is a
    $T > 0$ and a curve $\varphi$ with $\varphi(0) = x_0$ that is an integral curve of $g$ on
    $[0, T]$: a nontrivial solution segment exists from every point at which the field is
    $C^1$.

    The anchor $0$ is a construction choice rather than a restriction — by
    \cref{lem:isIntegralCurveOn-comp-add-autonomous} a segment from any other anchor
    follows.

    Reference: the Picard--Lindelöf local existence theorem.
  -/)
  (proof := /-- Picard--Lindel\"of local existence: being $C^1$ at $x_0$ gives a closed ball on
    which $g$ is Lipschitz, and hence a solution on some $(-\varepsilon, \varepsilon)$; take
    $T := \varepsilon/2$. -/)]
theorem ContDiffAt.exists_isIntegralCurveOn_Icc [CompleteSpace E]
    {g : E → E} {x₀ : E} (hg : ContDiffAt ℝ 1 g x₀) :
    ∃ (T : ℝ) (φ : ℝ → E), 0 < T ∧ φ 0 = x₀ ∧
      IsIntegralCurveOn φ (fun _ y => g y) (Icc 0 T) := by
  obtain ⟨φ, hφ0, ε, hε, hφ⟩ :=
    hg.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  refine ⟨ε / 2, φ, by positivity, hφ0, ?_⟩
  intro t ht
  have htIoo : t ∈ Ioo (0 - ε) (0 + ε) := by
    constructor <;> norm_num at * <;> linarith
  exact (hφ t htIoo).hasDerivWithinAt

/-- **Continuous dependence on initial states and parameters.**

If `y` is an integral solution of `ẏ = f(t, y)` and `z` is an integral solution of
`ż = f(t, z) + g(t, z)`, with `f` Lipschitz in the state with constant `L` and `g`
uniformly bounded by `μ`, then for `t` on either side of `t₀`:

  `‖y(t) − z(t)‖ ≤ ‖y₀ − z₀‖ · exp(L|t−t₀|) + (μ/L) · (exp(L|t−t₀|) − 1)`.

We work globally on the segment between `t₀` and `t₁` (rather than on a local domain
`W ⊂ ℝⁿ`) to avoid local-extension boilerplate.

Proof: the Gronwall bootstrap itself (integrability setup, base inequality, shift into
Gronwall form, apply `gronwall_const`) is inherently forward-marching — it is proved once, as
a fully generalized local fact `hforward`, and reused twice: directly for `t₀ ≤ t₁`, and via
the time-reflection `σ ↦ t₀ + t₁ - σ` (applied to `y, z, f, g`) for `t₁ ≤ t₀`, which turns the
backward instance into a forward one on `[t₁, t₀]`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 3.4. -/
@[blueprint "thm:continuous-dependence-ODE"
  (title := "Continuous dependence on initial states and parameters")
  (statement := /-- Khalil, Theorem 3.4.  Let $f$ be jointly continuous and $L$-Lipschitz in its
    state
    argument on the segment between $t_0$ and $t_1$, let $y$ be an integral solution of
    $\dot y = f(t,y)$ with
    $y(t_0) = y_0$, and let $z$ be an integral solution of the perturbed equation
    $\dot z = f(t,z) + g(t,z)$ with $z(t_0) = z_0$, where $\|g(t,x)\| \le \mu$.  Then for every
    $t$ on that segment,
    \[
      \|y(t) - z(t)\| \;\le\; \|y_0 - z_0\|\,e^{L|t-t_0|}
        \;+\; \frac{\mu}{L}\bigl(e^{L|t-t_0|} - 1\bigr).
    \]
    Two solutions may separate, but no faster than exponentially, at a rate set by the
    Lipschitz constant alone; the two error sources — a different starting point and a
    perturbed field — contribute additively.  The bound is stated on the unordered segment, so
    it runs in either time direction.

    The perturbation $g$ is assumed only bounded and integrable along $z$, never continuous, so
    $z$ need not be differentiable anywhere.  That is why the theorem is phrased over the
    integral formulation rather than the differential one. -/)
  (proof := /-- The forward case is a Gr\"onwall bootstrap.  Subtracting the two integral
    equations and applying the triangle inequality gives
    \[
      \|y(\tau) - z(\tau)\| \;\le\; \|y_0 - z_0\| + \mu(\tau - t_0)
        + L\int_{t_0}^{\tau}\|y(s) - z(s)\|\,\mathrm{d}s ,
    \]
    the Lipschitz hypothesis bounding the $f$-difference and the uniform bound on $g$ the rest.
    Adding $\mu/L$ to both sides absorbs the linear term $\mu(\tau - t_0)$ into the integral,
    putting the inequality in the shape \cref{lem:gronwall-const} expects, and Gr\"onwall
    delivers the exponential.

    That bootstrap is inherently forward-marching, so rather than repeat it for the backward
    case, reflect: \cref{lem:isIntegralSolution-reflect} sends
    $\sigma \mapsto t_0 + t_1 - \sigma$ and negates the field, turning the backward instance
    into a forward one on $[t_1, t_0]$ to which the same argument applies unchanged. -/)]
theorem continuous_dependence_ODE
    (hL : 0 < L)
    (hy : IsIntegralSolution t₀ t₁ y y₀ f)
    (hz : IsIntegralSolution t₀ t₁ z z₀ (fun s x => f s x + g s x))
    (hy_cont : ContinuousOn y (uIcc t₀ t₁))
    (hz_cont : ContinuousOn z (uIcc t₀ t₁))
    (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hgz : IntervalIntegrable (fun s => g s (z s)) volume t₀ t₁)
    (hLip : ∀ t ∈ uIcc t₀ t₁, LipschitzWith ⟨L, hL.le⟩ (f t))
    (hg : ∀ t ∈ uIcc t₀ t₁, ∀ x : E, ‖g t x‖ ≤ μ) :
    ∀ t ∈ uIcc t₀ t₁,
    ‖y t - z t‖ ≤ ‖y₀ - z₀‖ * rexp (L * |t - t₀|) + (μ / L) * (rexp (L * |t - t₀|) - 1) := by
  -- The forward-time Gronwall bootstrap (Khalil's original proof), fully generalized so
  -- it can be reused, unchanged, on the time-reflected data in the backward case below.
  have hforward : ∀ (a b : ℝ) (u v : ℝ → E) (F G : ℝ → E → E) (u0 v0 : E), a ≤ b →
      IsIntegralSolution a b u u0 F →
      IsIntegralSolution a b v v0 (fun s x => F s x + G s x) →
      ContinuousOn u (Icc a b) → ContinuousOn v (Icc a b) →
      Continuous (fun p : ℝ × E => F p.1 p.2) →
      IntervalIntegrable (fun s => G s (v s)) volume a b →
      (∀ t ∈ Icc a b, LipschitzWith ⟨L, hL.le⟩ (F t)) →
      (∀ t ∈ Icc a b, ∀ x : E, ‖G t x‖ ≤ μ) →
      ∀ t ∈ Icc a b,
        ‖u t - v t‖ ≤ ‖u0 - v0‖ * rexp (L * (t - a)) + (μ / L) * (rexp (L * (t - a)) - 1) := by
    intro a b u v F G u0 v0 hab hu hv hu_cont hv_cont hF_cont hGv hLip' hg'
    have hu' : ∀ t ∈ Icc a b, u t = u0 + ∫ s in a..t, F s (u s) :=
      fun t ht => hu t (by rw [uIcc_of_le hab]; exact ht)
    have hv' : ∀ t ∈ Icc a b, v t = v0 + ∫ s in a..t, (F s (v s) + G s (v s)) :=
      fun t ht => hv t (by rw [uIcc_of_le hab]; exact ht)
    -- ── 1. Global Integrability Setup ─────────────────────────────────────────
    have hu_cont' : ContinuousOn u (uIcc a b) := by rwa [uIcc_of_le hab]
    have hv_cont' : ContinuousOn v (uIcc a b) := by rwa [uIcc_of_le hab]
    have hu_int := hF_cont.intervalIntegrable_comp hu_cont'
    have hv_int := hF_cont.intervalIntegrable_comp hv_cont'
    have huv_int := (hu_cont.sub hv_cont).norm.intervalIntegrable_of_Icc (μ := volume) hab
    have hfuv_int := ((hF_cont.comp_continuousOn (continuousOn_id.prodMk hu_cont)).sub
                     (hF_cont.comp_continuousOn (continuousOn_id.prodMk
                     hv_cont))).norm.intervalIntegrable_of_Icc (μ := volume) hab
    -- ── 2. Base Inequality for every τ ────────────────────────────────────────
    have hineq_base : ∀ τ ∈ Icc a b, ‖u τ - v τ‖ ≤ ‖u0 - v0‖ + μ * (τ - a)
      + L * ∫ s in a..τ, ‖u s - v s‖ := by
      intro τ hτ
      have hsub : uIcc a τ ⊆ uIcc a b := uIcc_subset_uIcc_left (Icc_subset_uIcc hτ)
      have hu_sub := hu_int.mono_set hsub
      have hv_sub := hv_int.mono_set hsub
      have h_diff : u τ - v τ = (u0 - v0) +
        (∫ s in a..τ, F s (u s) - F s (v s)) - ∫ s in a..τ, G s (v s) := by
        rw [hu' τ hτ, hv' τ hτ, intervalIntegral.integral_add hv_sub (hGv.mono_set hsub),
            intervalIntegral.integral_sub hu_sub hv_sub]
        abel
      have h_g_bound : ‖∫ s in a..τ, G s (v s)‖ ≤ μ * (τ - a) :=
        intervalIntegral.norm_integral_le_const_mul hτ.1 fun s hs =>
          hg' s (Icc_subset_Icc_right hτ.2 hs) (v s)
      have h_lip_bound : ‖∫ s in a..τ, F s (u s) - F s (v s)‖ ≤ L * ∫ s in a..τ, ‖u s - v s‖ :=
        intervalIntegral.norm_integral_le_of_norm_le_mul hτ.1
          (hfuv_int.mono_set hsub)
          (huv_int.mono_set hsub)
          (fun s hs => by simpa [dist_eq_norm] using
            (hLip' s (Icc_subset_Icc_right hτ.2 hs)).dist_le_mul (u s) (v s))
      have h_tri1 := norm_sub_le ((u0 - v0) + ∫ s in a..τ, F s (u s) - F s (v s))
                                  (∫ s in a..τ, G s (v s))
      have h_tri2 := norm_add_le (u0 - v0) (∫ s in a..τ, F s (u s) - F s (v s))
      rw [h_diff]
      linarith [h_tri1, h_tri2, h_lip_bound, h_g_bound]
    -- ── 3. Shift into Gronwall Form ───────────────────────────────────────────
    have hshift : ∀ τ ∈ Icc a b, (‖u τ - v τ‖ + μ / L) ≤ (‖u0 - v0‖ + μ / L)
      + ∫ s in a..τ, L * (‖u s - v s‖ + μ / L) := by
      intro τ hτ
      have hv_sub2 := huv_int.mono_set (uIcc_subset_uIcc_left (Icc_subset_uIcc hτ))
      have h_int_eq : ∫ s in a..τ, L * (‖u s - v s‖ + μ / L) = (L * ∫ s in a..τ, ‖u s - v s‖)
        + μ * (τ - a) := by
        simp_rw [mul_add, mul_div_cancel₀ _ hL.ne']
        rw [intervalIntegral.integral_add (hv_sub2.const_mul L) intervalIntegrable_const]
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_eq]
        ring
      linarith [hineq_base τ hτ]
    -- ── 4. Apply Gronwall-Bellman ─────────────────────────────────────────────
    have hw_cont : ContinuousOn (fun τ => ‖u τ - v τ‖ + μ / L) (Icc a b) :=
      (hu_cont.sub hv_cont).norm.add continuousOn_const
    have hGron := gronwall_const hL.le hw_cont hshift
    intro t ht
    linarith [hGron t ht, hshift t ht, hineq_base t ht]
  rcases le_total t₀ t₁ with hle | hle
  · -- Forward case: `t₀ ≤ t₁`.
    intro t ht
    rw [uIcc_of_le hle] at hy_cont hz_cont hLip hg ht
    have hb := hforward t₀ t₁ y z f g y₀ z₀ hle hy hz hy_cont hz_cont hf_cont hgz hLip hg t ht
    rwa [abs_of_nonneg (sub_nonneg.mpr ht.1)]
  · -- Backward case: `t₁ ≤ t₀`. Reflect via `σ ↦ t₀ + t₁ - σ`, reducing to the forward case on
    -- `[t₁, t₀]` for `u σ := y (t₀+t₁-σ)`, `v σ := z (t₀+t₁-σ)`, `F r x := -f (t₀+t₁-r) x`,
    -- `G r x := -g (t₀+t₁-r) x`.
    have hrefl_mem : ∀ σ ∈ Icc t₁ t₀, t₀ + t₁ - σ ∈ uIcc t₀ t₁ := by
      intro σ hσ
      rw [uIcc_of_ge hle]
      constructor <;> linarith [hσ.1, hσ.2]
    have hu_sol := hy.reflect
    -- `reflect` negates the whole field; split that negation across the sum so the result has
    -- the `F + G` shape `hforward` expects.
    have hv_sol : IsIntegralSolution t₁ t₀ (fun σ => z (t₀ + t₁ - σ)) z₀
        (fun r x => (fun s x' => -f (t₀ + t₁ - s) x' + -g (t₀ + t₁ - s) x') r x) := by
      have hsplit : (fun r x => -((fun s x' => f s x' + g s x') (t₀ + t₁ - r) x))
          = (fun r x => -f (t₀ + t₁ - r) x + -g (t₀ + t₁ - r) x) := by
        funext r x; exact neg_add _ _
      exact hsplit ▸ hz.reflect
    have hu_cont : ContinuousOn (fun σ => y (t₀ + t₁ - σ)) (Icc t₁ t₀) :=
      hy_cont.comp (continuous_const.sub continuous_id).continuousOn hrefl_mem
    have hv_cont : ContinuousOn (fun σ => z (t₀ + t₁ - σ)) (Icc t₁ t₀) :=
      hz_cont.comp (continuous_const.sub continuous_id).continuousOn hrefl_mem
    have hF_cont : Continuous (fun p : ℝ × E => -f (t₀ + t₁ - p.1) p.2) :=
      (hf_cont.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)).neg
    have hGv_int : IntervalIntegrable (fun s => -g (t₀ + t₁ - s) (z (t₀ + t₁ - s))) volume t₁
        t₀ := by
      have heq : t₀ + t₁ - t₀ = t₁ := by ring
      have heq' : t₀ + t₁ - t₁ = t₀ := by ring
      have := (hgz.comp_sub_left (t₀ + t₁)).neg
      rwa [heq, heq'] at this
    have hLip' : ∀ t ∈ Icc t₁ t₀, LipschitzWith ⟨L, hL.le⟩ (fun x => -f (t₀ + t₁ - t) x) :=
      fun t ht => (hLip _ (hrefl_mem t ht)).neg
    have hg' : ∀ t ∈ Icc t₁ t₀, ∀ x : E, ‖(-g (t₀ + t₁ - t)) x‖ ≤ μ :=
      fun t ht x => by simpa using hg _ (hrefl_mem t ht) x
    have hb := hforward t₁ t₀ (fun σ => y (t₀ + t₁ - σ)) (fun σ => z (t₀ + t₁ - σ))
      (fun r x => -f (t₀ + t₁ - r) x) (fun r x => -g (t₀ + t₁ - r) x) y₀ z₀ hle hu_sol hv_sol
      hu_cont hv_cont hF_cont hGv_int hLip' hg'
    intro t ht
    rw [uIcc_of_ge hle] at ht
    have ht' : t₀ + t₁ - t ∈ Icc t₁ t₀ := by constructor <;> linarith [ht.1, ht.2]
    have hbt := hb (t₀ + t₁ - t) ht'
    dsimp only at hbt
    have heq : t₀ + t₁ - (t₀ + t₁ - t) = t := by ring
    rw [heq] at hbt
    have harith : t₀ + t₁ - t - t₁ = t₀ - t := by ring
    rw [harith] at hbt
    have habs : t₀ - t = |t - t₀| := by rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]; ring
    rwa [habs] at hbt

/-- **Continuous dependence on parameters.**

A uniform `ε`-bound: if `‖z₀ − y₀‖ ≤ α` and `‖g(t, x)‖ ≤ α` for all `t, x`, and
`α · (1 + 1/L) · exp(L(t₁−t₀)) ≤ ε`, then `‖y(t) − z(t)‖ ≤ ε` for all `t ∈ [t₀, t₁]`.

`λ`-dependence is modeled via the perturbation term `g` (i.e., `g t x = f_λ t x − f t x`).
The `α`-condition plays the role of `δ` from the classical statement.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 3.5. -/
@[blueprint "thm:continuous-dependence-parameters"
  (title := "Continuous dependence on parameters")
  (statement := /-- Khalil, Theorem 3.5.  If $y$ solves $\dot{y} = f(t,y)$ and $z$ solves
    $\dot{z} = f(t,z) + g(t,z)$ with $\|g(t,x)\| \le \alpha$ and $\|z_0 - y_0\| \le \alpha$, and
    $\alpha(1 + 1/L)e^{L(t_1-t_0)} \le \varepsilon$, then
    $\|y(t) - z(t)\| \le \varepsilon$ for all $t \in [t_0, t_1]$. -/)
  (proof := /-- Specialise \cref{thm:continuous-dependence-ODE} with $\mu = \alpha$ and
    $\|y_0 - z_0\| \le \alpha$: for $t \in [t_0, t_1]$ it gives
    $\|y(t) - z(t)\| \le \alpha e^{L(t-t_0)} + \frac{\alpha}{L}(e^{L(t-t_0)} - 1)
    = \alpha(1 + 1/L)e^{L(t-t_0)} - \alpha/L$.  Drop the $-\alpha/L$ and bound $e^{L(t-t_0)}$
    by $e^{L(t_1-t_0)}$ to get at most $\varepsilon$. -/)]
theorem continuous_dependence_parameters
    (ht : t₀ ≤ t₁)
    (hL : 0 < L)
    (hα : 0 < α)
    (hαε : α * (1 + 1 / L) * Real.exp (L * (t₁ - t₀)) ≤ ε)
    (hy : IsIntegralSolution t₀ t₁ y y₀ f)
    (hz : IsIntegralSolution t₀ t₁ z z₀ (fun s x => f s x + g s x))
    (hy_cont : ContinuousOn y (Set.Icc t₀ t₁))
    (hz_cont : ContinuousOn z (Set.Icc t₀ t₁))
    (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hg_cont : Continuous (fun p : ℝ × E => g p.1 p.2))
    (hLip : ∀ t ∈ Set.Icc t₀ t₁, LipschitzWith ⟨L, hL.le⟩ (f t))
    (hg   : ∀ t ∈ Set.Icc t₀ t₁, ∀ x : E, ‖g t x‖ ≤ α)
    (hz₀  : ‖z₀ - y₀‖ ≤ α) :
    ∀ t ∈ Set.Icc t₀ t₁, ‖y t - z t‖ ≤ ε := by
  intro t ht_mem
  have hy_cont' : ContinuousOn y (uIcc t₀ t₁) := by rw [uIcc_of_le ht]; exact hy_cont
  have hz_cont' : ContinuousOn z (uIcc t₀ t₁) := by rw [uIcc_of_le ht]; exact hz_cont
  have hLip' : ∀ t ∈ uIcc t₀ t₁, LipschitzWith ⟨L, hL.le⟩ (f t) := by
    rw [uIcc_of_le ht]; exact hLip
  have hg' : ∀ t ∈ uIcc t₀ t₁, ∀ x : E, ‖g t x‖ ≤ α := by rw [uIcc_of_le ht]; exact hg
  have ht_mem' : t ∈ uIcc t₀ t₁ := by rw [uIcc_of_le ht]; exact ht_mem
  have key := continuous_dependence_ODE hL hy hz hy_cont' hz_cont'
    hf_cont (hg_cont.intervalIntegrable_comp hz_cont') hLip' hg' t ht_mem'
  rw [abs_of_nonneg (sub_nonneg.mpr ht_mem.1)] at key
  have hyz₀ : ‖y₀ - z₀‖ ≤ α := by rwa [norm_sub_rev]
  have hexp_mono : Real.exp (L * (t - t₀)) ≤ Real.exp (L * (t₁ - t₀)) := by
    gcongr; linarith [ht_mem.2]
  calc ‖y t - z t‖
      ≤ ‖y₀ - z₀‖ * Real.exp (L * (t - t₀)) +
          α / L * (Real.exp (L * (t - t₀)) - 1) := key
    _ ≤ α * Real.exp (L * (t - t₀)) +
          α / L * (Real.exp (L * (t - t₀)) - 1) := by
          gcongr
    _ = α * (1 + 1 / L) * Real.exp (L * (t - t₀)) - α / L := by
          field_simp; ring
    _ ≤ α * (1 + 1 / L) * Real.exp (L * (t₁ - t₀)) - α / L := by
          gcongr
    _ ≤ α * (1 + 1 / L) * Real.exp (L * (t₁ - t₀)) := by
          linarith [div_nonneg hα.le hL.le]
    _ ≤ ε := hαε

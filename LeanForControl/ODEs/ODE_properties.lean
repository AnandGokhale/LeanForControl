import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Order.Interval.Set.UnorderedInterval
import LeanForControl.ODEs.GronwallBellman
import LeanForControl.Analysis.Integrals
import Architect

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Real Interval

/-!
# `ODEs.ODE_properties`

Core ODE definitions and continuous-dependence theorems used throughout the stability track.

## Main declarations

* `IsIntegralSolution` — integral formulation of an ODE solution on a time interval.
* `IntervalIntegrable_of_lipschitz` — integrability of `s ↦ f(s, z(s))` from joint continuity.
* `continuous_dependence_ODE` (Theorem 3.4) — quantitative bound on `‖y(t) − z(t)‖` when `y`
  solves `ẏ = f` and `z` solves the perturbed system `ż = f + g`.
* `continuous_dependence_parameters` (Theorem 3.5) — uniform `ε`-bound when both the initial
  perturbation `‖z₀ − y₀‖` and the forcing `‖g‖` are bounded by `α`.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An *integral solution* of `ẋ = F(t, x)` on `[t₀, t₁]` with initial value `x₀`:
    for every `t ∈ [t₀, t₁]`, `x(t) = x₀ + ∫_{t₀}^{t} F(s, x(s)) ds`. -/
@[blueprint "def:isIntegralSolution"
  (statement := /-- A function $x : [t_0, t_1] \to E$ is an \emph{integral solution}
    of $\dot{x} = F(t,x)$ with initial value $x_0$ when
    \[
      x(t) \;=\; x_0 + \int_{t_0}^{t} F(s,\, x(s))\,\mathrm{d}s
      \qquad \forall\, t \in [t_0, t_1].
    \] -/)]
def IsIntegralSolution (t₀ t₁ : ℝ) (x : ℝ → E) (x₀ : E) (F : ℝ → E → E) : Prop :=
  ∀ t ∈ Set.Icc t₀ t₁, x t = x₀ + ∫ s in t₀..t, F s (x s)

variable {t₀ t₁ : ℝ}
variable {f g : ℝ → E → E}
variable {y z : ℝ → E}
variable {y₀ z₀ : E}
variable {L μ : ℝ}

omit [NormedSpace ℝ E] in
/-- `s ↦ f(s, z(s))` is interval-integrable on `[t₀, t₁]` when `f` is jointly continuous
    and `z` is continuous on `[t₀, t₁]`. -/
lemma IntervalIntegrable_of_lipschitz {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
{f : ℝ → E → E} {z : ℝ → E}
(hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
  (hz : ContinuousOn z (Icc t₀ t₁)) :
  (IntervalIntegrable (fun s => f s (z s)) volume t₀ t₁)  := by
  rw [← Set.uIcc_of_le hle] at hz
  exact (hf_cont.comp_continuousOn
    (ContinuousOn.prodMk continuous_id.continuousOn hz)).intervalIntegrable

/-- **Theorem 3.4** (Continuous dependence on initial states and parameters).

If `y` is an integral solution of `ẏ = f(t, y)` and `z` is an integral solution of
`ż = f(t, z) + g(t, z)`, with `f` Lipschitz in the state with constant `L` and `g`
uniformly bounded by `μ`, then for all `t ∈ [t₀, t₁]`:

  `‖y(t) − z(t)‖ ≤ ‖y₀ − z₀‖ · exp(L(t−t₀)) + (μ/L) · (exp(L(t−t₀)) − 1)`.

We work globally on `[t₀, t₁]` (rather than on a local domain `W ⊂ ℝⁿ`) to avoid
local-extension boilerplate. -/
theorem continuous_dependence_ODE
    (ht : t₀ ≤ t₁) (hL : 0 < L)
    (hy : IsIntegralSolution t₀ t₁ y y₀ f)
    (hz : IsIntegralSolution t₀ t₁ z z₀ (fun s x => f s x + g s x))
    (hy_cont : ContinuousOn y (Icc t₀ t₁))
    (hz_cont : ContinuousOn z (Icc t₀ t₁))
    (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hgz : IntervalIntegrable (fun s => g s (z s)) volume t₀ t₁)
    (hLip : ∀ t ∈ Icc t₀ t₁, LipschitzWith ⟨L, hL.le⟩ (f t))
    (hg : ∀ t ∈ Icc t₀ t₁, ∀ x : E, ‖g t x‖ ≤ μ) :
    ∀ t ∈ Icc t₀ t₁,
    ‖y t - z t‖ ≤ ‖y₀ - z₀‖ * rexp (L * (t - t₀)) + (μ / L) * (rexp (L * (t - t₀)) - 1) := by
  -- ── 1. Global Integrability Setup ─────────────────────────────────────────
  have hy_int := hf_cont.intervalIntegrable_comp ht hy_cont
  have hz_int := hf_cont.intervalIntegrable_comp ht hz_cont
  have hyz_int := (hy_cont.sub hz_cont).norm.intervalIntegrable_of_Icc (μ := volume) ht
  have hfyz_int := ((hf_cont.comp_continuousOn (continuousOn_id.prodMk hy_cont)).sub
                   (hf_cont.comp_continuousOn (continuousOn_id.prodMk hz_cont))).norm.intervalIntegrable_of_Icc
                   (μ := volume) ht
  -- ── 2. Base Inequality for every τ ────────────────────────────────────────
  have hineq_base : ∀ τ ∈ Icc t₀ t₁, ‖y τ - z τ‖ ≤ ‖y₀ - z₀‖ + μ * (τ - t₀)
    + L * ∫ s in t₀..τ, ‖y s - z s‖ := by
    intro τ hτ
    have hu_sub : uIcc t₀ τ ⊆ uIcc t₀ t₁ := uIcc_subset_uIcc_left (Icc_subset_uIcc hτ)
    have hy_sub := hy_int.mono_set hu_sub
    have hz_sub := hz_int.mono_set hu_sub
    have h_diff : y τ - z τ = (y₀ - z₀) +
      (∫ s in t₀..τ, f s (y s) - f s (z s)) - ∫ s in t₀..τ, g s (z s) := by
      rw [hy τ hτ, hz τ hτ, intervalIntegral.integral_add hz_sub (hgz.mono_set hu_sub),
          intervalIntegral.integral_sub hy_sub hz_sub]
      abel
    have h_g_bound : ‖∫ s in t₀..τ, g s (z s)‖ ≤ μ * (τ - t₀) :=
      intervalIntegral.norm_integral_le_const_mul hτ.1 fun s hs =>
        hg s (Icc_subset_Icc_right hτ.2 hs) (z s)
    have h_lip_bound : ‖∫ s in t₀..τ, f s (y s) - f s (z s)‖ ≤ L * ∫ s in t₀..τ, ‖y s - z s‖ :=
      intervalIntegral.norm_integral_le_of_norm_le_mul hτ.1
        (hfyz_int.mono_set hu_sub)
        (hyz_int.mono_set hu_sub)
        (fun s hs => by simpa [dist_eq_norm] using
          (hLip s (Icc_subset_Icc_right hτ.2 hs)).dist_le_mul (y s) (z s))
    have h_tri1 := norm_sub_le ((y₀ - z₀) + ∫ s in t₀..τ, f s (y s) - f s (z s))
                                (∫ s in t₀..τ, g s (z s))
    have h_tri2 := norm_add_le (y₀ - z₀) (∫ s in t₀..τ, f s (y s) - f s (z s))
    rw [h_diff]
    linarith [h_tri1, h_tri2, h_lip_bound, h_g_bound]
  -- ── 3. Shift into Gronwall Form ───────────────────────────────────────────
  have hshift : ∀ τ ∈ Icc t₀ t₁, (‖y τ - z τ‖ + μ / L) ≤ (‖y₀ - z₀‖ + μ / L)
    + ∫ s in t₀..τ, L * (‖y s - z s‖ + μ / L) := by
    intro τ hτ
    have hz_sub := hyz_int.mono_set (uIcc_subset_uIcc_left (Icc_subset_uIcc hτ))
    have h_int_eq : ∫ s in t₀..τ, L * (‖y s - z s‖ + μ / L) = (L * ∫ s in t₀..τ, ‖y s - z s‖)
      + μ * (τ - t₀) := by
      simp_rw [mul_add, mul_div_cancel₀ _ hL.ne']
      rw [intervalIntegral.integral_add (hz_sub.const_mul L) intervalIntegrable_const]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_eq]
      ring
    linarith [hineq_base τ hτ]
  -- ── 4. Apply Gronwall-Bellman ─────────────────────────────────────────────
  have hw_cont : ContinuousOn (fun τ => ‖y τ - z τ‖ + μ / L) (Icc t₀ t₁) :=
    (hy_cont.sub hz_cont).norm.add continuousOn_const
  have hG := gronwall_const hL.le hw_cont hshift
  intro t ht
  linarith [hG t ht, hshift t ht, hineq_base t ht]

/-- **Theorem 3.5** (Continuous dependence on parameters).

A uniform `ε`-bound: if `‖z₀ − y₀‖ ≤ α` and `‖g(t, x)‖ ≤ α` for all `t, x`, and
`α · (1 + 1/L) · exp(L(t₁−t₀)) ≤ ε`, then `‖y(t) − z(t)‖ ≤ ε` for all `t ∈ [t₀, t₁]`.

`λ`-dependence is modeled via the perturbation term `g` (i.e., `g t x = f_λ t x − f t x`).
The `α`-condition plays the role of `δ` from the classical statement. -/
@[blueprint "thm:continuous-dependence-parameters"
  (statement := /-- \textbf{Theorem 3.5} (Continuous dependence on parameters).
    If $y$ solves $\dot{y} = f(t,y)$ and $z$ solves $\dot{z} = f(t,z) + g(t,z)$
    with $\|g(t,x)\| \le \alpha$ and $\|z_0 - y_0\| \le \alpha$, and
    $\alpha(1 + 1/L)e^{L(t_1-t_0)} \le \varepsilon$, then
    $\|y(t) - z(t)\| \le \varepsilon$ for all $t \in [t_0, t_1]$. -/)
  (proof := /-- Reduce to \cref{thm:gronwall-bellman} applied to $\|y-z\|$,
    using the $L$-Lipschitz bound on $f$ and the $\alpha$-bound on $g$. -/)]
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
  have key := continuous_dependence_ODE ht hL hy hz hy_cont hz_cont
    hf_cont (IntervalIntegrable_of_lipschitz ht hg_cont hz_cont) hLip hg t ht_mem
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

/-- **Picard-Lindelöf for scalar ODEs on compact intervals**.

    For a jointly continuous right-hand side `g : ℝ → ℝ → ℝ` that is globally
    Lipschitz in the state variable (uniformly in time), for any compact interval
    `[t₀, t₁]` and initial value `x₀ : ℝ`, there exists an integral solution `z`
    that is continuous and has right derivatives matching `g` on `[t₀, t₁)`.

    This is the scalar, compact-interval instance of the Picard-Lindelöf theorem,
    which holds because globally Lipschitz continuity prevents finite-time blowup. -/
axiom scalar_ode_exists_interval
    (g : ℝ → ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hg_cont : Continuous (Function.uncurry g))
    (hg_lip : ∀ t : ℝ, LipschitzWith ⟨L, hL.le⟩ (g t))
    {t₀ t₁ x₀ : ℝ} (ht : t₀ ≤ t₁) :
    ∃ z : ℝ → ℝ,
      IsIntegralSolution t₀ t₁ z x₀ g ∧
      ContinuousOn z (Set.Icc t₀ t₁) ∧
      ∀ s ∈ Set.Ico t₀ t₁, HasDerivWithinAt z (g s (z s)) (Set.Ici s) s

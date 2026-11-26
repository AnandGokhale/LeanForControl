import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Transform
import Mathlib.Order.Interval.Set.UnorderedInterval
import LeanForControl.ODEs.GronwallBellman
import LeanForControl.Analysis.AbsolutelyContinuous
import LeanForControl.Analysis.Integrals
import LeanForControl.Analysis.IntegralCurves
import LeanForControl.Analysis.LieDerivative
import Mathlib.Analysis.InnerProductSpace.Calculus
import Architect

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Real Interval Pointwise Topology NNReal

/-!
# `ODEs.ODE_properties`

Existence and continuous-dependence theorems used throughout the stability track.

The integral formulation `IsIntegralSolution` and its dictionary with Mathlib's
`IsIntegralCurveOn` are general facts about ODE solutions with no control content; they live in
`Analysis/IntegralCurves.lean`, which this file imports.

## Main declarations

* `ContDiffAt.exists_isIntegralCurveOn_Icc` — local existence from a `C¹` field.
* `IsIntegralSolution.norm_sub_le_mul_exp` — Grönwall separation of two integral solutions, with
  no regularity in time.
* `continuous_dependence_ODE` — quantitative bound on `‖y(t) − z(t)‖`
  when `y` solves `ẏ = f` and `z` solves the perturbed system `ż = f + g`.
* `continuous_dependence_parameters` — uniform `ε`-bound when both the
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

    The anchor $0$ is a construction choice rather than a restriction — an autonomous field has
    no preferred time origin, so translating the curve in time gives a segment from any other
    anchor.

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

/-- **Grönwall separation of two integral solutions.**  On `[a, b]`, let `u` be an integral
solution of `u̇ = F(t, u)` from `u₀` and `v` one of `v̇ = G(t, v)` from `v₀`, and suppose the two
fields, evaluated along the two solutions, differ by at most `K ‖u(t) - v(t)‖`.  Then
`‖u(t) - v(t)‖ ≤ ‖u₀ - v₀‖ e^{K(t - a)}` on `[a, b]`.

With `G = F` and `F` `K`-Lipschitz in the state this is separation of two solutions, and
uniqueness; with `v` constant at an equilibrium `c` of `G = 0` it bounds the growth of
`‖u(t) - c‖`.  No regularity in time is assumed: the integrability the argument needs is part of
being an integral solution.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), continuous dependence on initial states, in the
unperturbed case. -/
@[blueprint "thm:isIntegralSolution-norm-sub-le-mul-exp"
  (title := "Grönwall separation of two integral solutions")
  (statement := /-- Let $a \le b$ and $K \ge 0$, let $u$ be an integral solution
    (\cref{def:isIntegralSolution}) of $\dot u = F(t, u)$ on $[a, b]$ with initial value $u_0$
    and $v$ one of $\dot v = G(t, v)$ with initial value $v_0$, and suppose
    $\|F(t, u(t)) - G(t, v(t))\| \le K\,\|u(t) - v(t)\|$ for $t \in (a, b)$.  Then
    \[
      \|u(t) - v(t)\| \le \|u_0 - v_0\|\, e^{K(t - a)} \qquad \forall\, t \in [a, b].
    \]
    No regularity in time is assumed.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), continuous dependence on initial
    states, in the unperturbed case. -/)
  (proof := /-- Subtracting the integral equations,
    $\|u(t) - v(t)\| \le \|u_0 - v_0\| + \int_a^t K\,\|u - v\|$; the solutions are continuous
    (\cref{lem:isIntegralSolution-continuousOn}), so Gr\"onwall's inequality
    (\cref{lem:gronwall-const}) applies. -/)]
theorem IsIntegralSolution.norm_sub_le_mul_exp [CompleteSpace E] {a b K : ℝ} {u v : ℝ → E}
    {F G : ℝ → E → E} {u₀ v₀ : E} (hK : 0 ≤ K) (hab : a ≤ b)
    (hu : IsIntegralSolution a b u u₀ F) (hv : IsIntegralSolution a b v v₀ G)
    (hFG : ∀ t ∈ Ioo a b, ‖F t (u t) - G t (v t)‖ ≤ K * ‖u t - v t‖) :
    ∀ t ∈ Icc a b, ‖u t - v t‖ ≤ ‖u₀ - v₀‖ * rexp (K * (t - a)) := by
  have hw : ContinuousOn (fun t => ‖u t - v t‖) (Icc a b) := by
    rw [← uIcc_of_le hab]; exact (hu.continuousOn.sub hv.continuousOn).norm
  refine gronwall_const hK hw fun t ht => ?_
  have ht' : t ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ht
  obtain ⟨hFu, hu_t⟩ := hu t ht'
  obtain ⟨hGv, hv_t⟩ := hv t ht'
  calc ‖u t - v t‖ = ‖(u₀ - v₀) + ∫ s in a..t, (F s (u s) - G s (v s))‖ := by
        rw [hu_t, hv_t, intervalIntegral.integral_sub hFu hGv]; abel_nf
    _ ≤ ‖u₀ - v₀‖ + ∫ s in a..t, ‖F s (u s) - G s (v s)‖ :=
        (norm_add_le _ _).trans (by
          gcongr; exact intervalIntegral.norm_integral_le_integral_norm ht.1)
    _ ≤ ‖u₀ - v₀‖ + ∫ s in a..t, K * ‖u s - v s‖ := by
        gcongr
        exact intervalIntegral.integral_mono_on_of_le_Ioo ht.1 (hFu.sub hGv).norm
          (((hw.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1).const_mul K)
          fun s hs => hFG s ⟨hs.1, hs.2.trans_le ht.2⟩

/-- **Forward-time continuous dependence** (the Grönwall step behind
`continuous_dependence_ODE`).

On `[a, b]`, let `u` be an integral solution of `u̇ = F(t, u)` from
`u0`, and `v` one of the perturbed equation `v̇ = F(t, v) + G(t, v)` from `v0`, with `F`
`L`-Lipschitz in the state and `‖G‖ ≤ μ`.  No regularity in time is assumed: the integrability the
argument needs is part of being an integral solution.  Then for every `t ∈ [a, b]`

  `‖u(t) − v(t)‖ ≤ ‖u0 − v0‖ · exp(L(t − a)) + (μ/L) · (exp(L(t − a)) − 1)`.

It is stated for arbitrary data so that the backward case of `continuous_dependence_ODE` can
reuse it, unchanged, on the time-reflected data. -/
private lemma continuous_dependence_forward [CompleteSpace E] (hL : 0 < L) {a b : ℝ} {u v : ℝ → E}
    {F G : ℝ → E → E} {u0 v0 : E} (hu : IsIntegralSolution a b u u0 F)
    (hv : IsIntegralSolution a b v v0 (fun s x => F s x + G s x))
    (hLip : ∀ t ∈ Icc a b, LipschitzWith ⟨L, hL.le⟩ (F t))
    (hG : ∀ t ∈ Icc a b, ∀ x : E, ‖G t x‖ ≤ μ) :
    ∀ t ∈ Icc a b,
      ‖u t - v t‖ ≤ ‖u0 - v0‖ * rexp (L * (t - a)) + (μ / L) * (rexp (L * (t - a)) - 1) := by
  -- `u - v` is given by an integral, so `‖u - v‖` is absolutely continuous
  have hint : IntervalIntegrable (fun s => F s (u s) - (F s (v s) + G s (v s))) volume a b :=
    (hu b right_mem_uIcc).1.sub (hv b right_mem_uIcc).1
  have hua : u a = u0 := by simpa using (hu a left_mem_uIcc).2
  have hva : v a = v0 := by simpa using (hv a left_mem_uIcc).2
  have hw : ∀ t ∈ uIcc a b,
      (u t - v t) - (u a - v a) = ∫ s in a..t, F s (u s) - (F s (v s) + G s (v s)) := fun t ht => by
    rw [hua, hva, (hu t ht).2, (hv t ht).2, intervalIntegral.integral_sub (hu t ht).1 (hv t ht).1]
    abel
  have hac := (absolutelyContinuousOnInterval_of_sub_eq_integral hint hw).norm
  intro t ht
  -- Grönwall with forcing: almost everywhere, `‖u - v‖' ≤ L ‖u - v‖ + μ`
  have key := hac.le_gronwallBound_of_deriv_le (K := L) (ε := μ) ?_ t ht
  · rwa [gronwallBound_of_K_ne_0 hL.ne', hua, hva] at key
  filter_upwards [ae_hasDerivAt_of_sub_eq_integral hint hw, hac.ae_differentiableAt]
    with s hs hns hmem
  have hmem' := Ioo_subset_Icc_self hmem
  calc deriv (fun t => ‖u t - v t‖) s
      ≤ ‖F s (u s) - (F s (v s) + G s (v s))‖ := (le_abs_self _).trans
        ((hs hmem).abs_le_norm_of_norm (hns (Icc_subset_uIcc hmem')).hasDerivAt)
    _ = ‖(F s (u s) - F s (v s)) - G s (v s)‖ := by rw [sub_add_eq_sub_sub]
    _ ≤ L * ‖u s - v s‖ + μ := (norm_sub_le _ _).trans
        (add_le_add ((hLip s hmem').norm_sub_le _ _) (hG s hmem' _))

/-- **Continuous dependence on initial states and parameters.**

If `y` is an integral solution of `ẏ = f(t, y)` and `z` is an integral solution of
`ż = f(t, z) + g(t, z)`, with `f` Lipschitz in the state with constant `K > 0` and `g`
uniformly bounded by `μ`, then for `t` on either side of `t₀`:

  `‖y(t) − z(t)‖ ≤ ‖y₀ − z₀‖ · exp(K|t−t₀|) + (μ/K) · (exp(K|t−t₀|) − 1)`.

We work globally on the segment between `t₀` and `t₁` (rather than on a local domain
`W ⊂ ℝⁿ`) to avoid local-extension boilerplate.  No regularity in time is assumed, of `f` or of
`g`: the integrability the argument needs is part of being an integral solution, so the theorem
applies to Carathéodory solutions.

Differences from Khalil: he assumes `f` and `g` piecewise continuous in `t`; here they are
arbitrary in `t`.

Proof: the Grönwall step (`‖y − z‖` is absolutely continuous with derivative at most
`K ‖y − z‖ + μ` almost everywhere; apply
`AbsolutelyContinuousOnInterval.le_gronwallBound_of_deriv_le`) runs forward in time — it is proved
once, as the general private lemma `continuous_dependence_forward`, and reused twice: directly for
`t₀ ≤ t₁`, and via the time-reflection `σ ↦ t₀ + t₁ - σ` (applied to `y, z, f, g`) for
`t₁ ≤ t₀`, which turns the backward instance into a forward one on `[t₁, t₀]`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), the theorem on continuous dependence on initial
states and parameters. -/
@[blueprint "thm:continuous-dependence-ODE"
  (title := "Continuous dependence on initial states and parameters")
  (statement := /-- After Khalil, \emph{Nonlinear Systems} (3rd ed.).  Let $L > 0$ and let $f$
    be $L$-Lipschitz in its state argument on the segment between $t_0$ and $t_1$, with no
    regularity in time, let $y$ be an integral solution of $\dot y = f(t,y)$ with
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

    Neither $f$ nor $g$ is assumed continuous in time, so $y$ and $z$ need not be differentiable
    anywhere.  That is why the theorem is phrased over the integral formulation rather than the
    differential one. -/)
  (proof := /-- The forward case is Gr\"onwall's inequality with forcing.  Subtracting the two
    integral equations, $y - z$ is given by an integral, so $\|y - z\|$ is absolutely continuous
    (\cref{lem:absolutelyContinuousOnInterval-of-sub-eq-integral}) and, at almost every $t$,
    $y - z$ has derivative $f(t, y) - f(t, z) - g(t, z)$
    (\cref{lem:ae-hasDerivAt-of-sub-eq-integral}).  The norm of a curve changes no faster than
    the curve (\cref{lem:hasDerivAt-abs-le-norm-of-norm}), so almost everywhere
    \[
      \frac{\mathrm{d}}{\mathrm{d}t}\|y(t) - z(t)\| \;\le\; L\,\|y(t) - z(t)\| + \mu ,
    \]
    the Lipschitz hypothesis bounding the $f$-difference and the uniform bound on $g$ the rest;
    \cref{lem:absolutelyContinuousOnInterval-le-gronwallBound-of-deriv-le} delivers the bound.

    That argument runs forward in time, so rather than repeat it for the backward
    case, reflect: \cref{lem:isIntegralSolution-reflect} sends
    $\sigma \mapsto t_0 + t_1 - \sigma$ and negates the field, turning the backward instance
    into a forward one on $[t_1, t_0]$ to which the same argument applies unchanged. -/)]
theorem continuous_dependence_ODE [CompleteSpace E] {K : ℝ≥0}
    (hK : 0 < K)
    (hy : IsIntegralSolution t₀ t₁ y y₀ f)
    (hz : IsIntegralSolution t₀ t₁ z z₀ (fun s x => f s x + g s x))
    (hLip : ∀ t ∈ uIcc t₀ t₁, LipschitzWith K (f t))
    (hg : ∀ t ∈ uIcc t₀ t₁, ∀ x : E, ‖g t x‖ ≤ μ) :
    ∀ t ∈ uIcc t₀ t₁,
    ‖y t - z t‖ ≤ ‖y₀ - z₀‖ * rexp (K * |t - t₀|) + (μ / K) * (rexp (K * |t - t₀|) - 1) := by
  have hL : 0 < (K : ℝ) := NNReal.coe_pos.2 hK
  /- The Grönwall step `continuous_dependence_forward` only runs forward in time.  If
     `t₀ ≤ t₁` it applies directly.  If `t₁ ≤ t₀`, reflect time by `σ ↦ t₀ + t₁ − σ`: this swaps
     the endpoints and negates the fields, turning the backward problem into a forward one on
     `[t₁, t₀]`, where the elapsed time `σ − t₁` equals `|t − t₀|`. -/
  rcases le_total t₀ t₁ with hle | hle
  · -- Case 1 (forward, `t₀ ≤ t₁`): apply the forward lemma; there `|t − t₀| = t − t₀`.
    intro t ht
    rw [uIcc_of_le hle] at hLip hg ht
    have hb := continuous_dependence_forward hL hy hz hLip hg t ht
    rwa [abs_of_nonneg (sub_nonneg.mpr ht.1)]
  · -- Case 2 (backward, `t₁ ≤ t₀`): reflect time by `σ ↦ t₀ + t₁ - σ`, reducing to the forward
    -- case on `[t₁, t₀]` for `u σ := y (t₀+t₁-σ)`, `v σ := z (t₀+t₁-σ)`, `F r x := -f (t₀+t₁-r) x`,
    -- `G r x := -g (t₀+t₁-r) x`.
    -- The reflection maps `[t₁, t₀]` back onto the original segment.
    have hrefl_mem : ∀ σ ∈ Icc t₁ t₀, t₀ + t₁ - σ ∈ uIcc t₀ t₁ := by
      intro σ hσ
      rw [uIcc_of_ge hle]
      constructor <;> linarith [hσ.1, hσ.2]
    -- Step 2a. Transport every hypothesis to the reflected data.
    have hu_sol := hy.reflect
    -- `reflect` negates the whole field; split that negation across the sum so the result has
    -- the `F + G` shape the forward lemma expects.
    have hv_sol : IsIntegralSolution t₁ t₀ (fun σ => z (t₀ + t₁ - σ)) z₀
        (fun r x => (fun s x' => -f (t₀ + t₁ - s) x' + -g (t₀ + t₁ - s) x') r x) := by
      have hsplit : (fun r x => -((fun s x' => f s x' + g s x') (t₀ + t₁ - r) x))
          = (fun r x => -f (t₀ + t₁ - r) x + -g (t₀ + t₁ - r) x) := by
        funext r x; exact neg_add _ _
      exact hsplit ▸ hz.reflect
    have hLip' : ∀ t ∈ Icc t₁ t₀, LipschitzWith K (fun x => -f (t₀ + t₁ - t) x) :=
      fun t ht => (hLip _ (hrefl_mem t ht)).neg
    have hg' : ∀ t ∈ Icc t₁ t₀, ∀ x : E, ‖(-g (t₀ + t₁ - t)) x‖ ≤ μ :=
      fun t ht x => by simpa using hg _ (hrefl_mem t ht) x
    -- Step 2b. The forward lemma on `[t₁, t₀]`, for the reflected data.
    have hb := continuous_dependence_forward (u := fun σ => y (t₀ + t₁ - σ))
      (v := fun σ => z (t₀ + t₁ - σ)) (F := fun r x => -f (t₀ + t₁ - r) x)
      (G := fun r x => -g (t₀ + t₁ - r) x) hL hu_sol hv_sol hLip' hg'
    -- Step 2c. Read it back at `σ = t₀ + t₁ − t`, which reflects to `t` itself and has elapsed
    -- reflected time `σ − t₁ = t₀ − t = |t − t₀|` (as `t ≤ t₀`).
    intro t ht
    rw [uIcc_of_ge hle] at ht
    have hσ_mem : t₀ + t₁ - t ∈ Icc t₁ t₀ := by constructor <;> linarith [ht.1, ht.2]
    have hσ_back : t₀ + t₁ - (t₀ + t₁ - t) = t := by ring
    have hσ_elapsed : t₀ + t₁ - t - t₁ = |t - t₀| := by
      rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]; ring
    have hbt := hb (t₀ + t₁ - t) hσ_mem
    rwa [hσ_back, hσ_elapsed] at hbt

/-- **Continuous dependence on parameters.**

A uniform `ε`-bound: if `f` is Lipschitz in the state with constant `K > 0`, `‖z₀ − y₀‖ ≤ α` and
`‖g(t, x)‖ ≤ α` for all `t, x`, and `α · (1 + 1/K) · exp(K(t₁−t₀)) ≤ ε`, then
`‖y(t) − z(t)‖ ≤ ε` for all `t ∈ [t₀, t₁]`.

`λ`-dependence is modeled via the perturbation term `g` (i.e., `g t x = f_λ t x − f t x`).
The `α`-condition plays the role of `δ` from the classical statement.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), the theorem on continuous dependence on
parameters. -/
@[blueprint "thm:continuous-dependence-parameters"
  (title := "Continuous dependence on parameters")
  (statement := /-- After Khalil, \emph{Nonlinear Systems} (3rd ed.).  Let $t_0 \le t_1$,
    $L > 0$, and let $f$ be
    $L$-Lipschitz in its state argument on $[t_0, t_1]$.  If $y$ is an integral solution of
    $\dot{y} = f(t,y)$ from $y_0$ and $z$ one of
    $\dot{z} = f(t,z) + g(t,z)$ from $z_0$, with $\|g(t,x)\| \le \alpha$ and
    $\|z_0 - y_0\| \le \alpha$, and
    $\alpha(1 + 1/L)e^{L(t_1-t_0)} \le \varepsilon$, then
    $\|y(t) - z(t)\| \le \varepsilon$ for all $t \in [t_0, t_1]$. -/)
  (proof := /-- Specialise \cref{thm:continuous-dependence-ODE} with $\mu = \alpha$ and
    $\|y_0 - z_0\| \le \alpha$: for $t \in [t_0, t_1]$ it gives
    $\|y(t) - z(t)\| \le \alpha e^{L(t-t_0)} + \frac{\alpha}{L}(e^{L(t-t_0)} - 1)
    = \alpha(1 + 1/L)e^{L(t-t_0)} - \alpha/L$.  Drop the $-\alpha/L$ and bound $e^{L(t-t_0)}$
    by $e^{L(t_1-t_0)}$ to get at most $\varepsilon$. -/)]
theorem continuous_dependence_parameters [CompleteSpace E] {K : ℝ≥0}
    (ht : t₀ ≤ t₁)
    (hK : 0 < K)
    (hαε : α * (1 + 1 / K) * Real.exp (K * (t₁ - t₀)) ≤ ε)
    (hy : IsIntegralSolution t₀ t₁ y y₀ f)
    (hz : IsIntegralSolution t₀ t₁ z z₀ (fun s x => f s x + g s x))
    (hLip : ∀ t ∈ Set.Icc t₀ t₁, LipschitzWith K (f t))
    (hg : ∀ t ∈ Set.Icc t₀ t₁, ∀ x : E, ‖g t x‖ ≤ α)
    (hz₀ : ‖z₀ - y₀‖ ≤ α) :
    ∀ t ∈ Set.Icc t₀ t₁, ‖y t - z t‖ ≤ ε := by
  intro t ht_mem
  have hL : 0 < (K : ℝ) := NNReal.coe_pos.2 hK
  have hLip' : ∀ t ∈ uIcc t₀ t₁, LipschitzWith K (f t) := by
    rw [uIcc_of_le ht]; exact hLip
  have hg' : ∀ t ∈ uIcc t₀ t₁, ∀ x : E, ‖g t x‖ ≤ α := by rw [uIcc_of_le ht]; exact hg
  have ht_mem' : t ∈ uIcc t₀ t₁ := by rw [uIcc_of_le ht]; exact ht_mem
  have key := continuous_dependence_ODE hK hy hz hLip' hg' t ht_mem'
  rw [abs_of_nonneg (sub_nonneg.mpr ht_mem.1)] at key
  have hyz₀ : ‖y₀ - z₀‖ ≤ α := by rwa [norm_sub_rev]
  have hα : 0 ≤ α := (norm_nonneg _).trans hz₀
  have hexp_mono : Real.exp (K * (t - t₀)) ≤ Real.exp (K * (t₁ - t₀)) := by
    gcongr; linarith [ht_mem.2]
  calc ‖y t - z t‖
      ≤ ‖y₀ - z₀‖ * Real.exp (K * (t - t₀)) +
          α / K * (Real.exp (K * (t - t₀)) - 1) := key
    _ ≤ α * Real.exp (K * (t - t₀)) +
          α / K * (Real.exp (K * (t - t₀)) - 1) := by
          gcongr
    _ = α * (1 + 1 / K) * Real.exp (K * (t - t₀)) - α / K := by
          field_simp; ring
    _ ≤ α * (1 + 1 / K) * Real.exp (K * (t₁ - t₀)) - α / K := by
          gcongr
    _ ≤ α * (1 + 1 / K) * Real.exp (K * (t₁ - t₀)) := by
          linarith [div_nonneg hα hL.le]
    _ ≤ ε := hαε

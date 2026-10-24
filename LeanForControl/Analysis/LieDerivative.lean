import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import LeanForControl.Analysis.FrechetDerivative
import Architect

/-!
# The Lie derivative of a function along a vector field

For `V : ℝ → E → ℝ` and a time-dependent vector field `v : ℝ → E → E`, the Lie derivative of `V`
along `v` at `(t, x)` is

  `∂V/∂t (t, x) + ∂V/∂x (t, x) · v(t, x)`,

the derivative of `V` at `(t, x)` in the direction `(1, v(t, x))`.  It is the Lie derivative in
the strict sense of `V`, as a function on `ℝ × E`, along the autonomous field
`(t, x) ↦ (1, v(t, x))`; for a function `V(x)` of the state alone it is the familiar `∇V · v`.
Along an integral curve `γ` of `v` it is the rate of change of `t ↦ V(t, γ(t))`.

## Main declarations

* `lieDerivative V v t x` — the Lie derivative of `V` along `v`.
* `lieDerivative_const` — for `V` independent of `t`, it is the directional derivative
  `DV(x) v`; `lieDerivative_add_mul` adds a linear time term.
* `IsIntegralCurveOn.hasDerivWithinAt_lieDerivative` — the chain rule along an integral curve.
* `IsIntegralCurveOn.lieDerivative_eq_of_hasDerivWithinAt` — the Lie derivative is the right
  derivative of `V` along a forward integral curve, however that is computed.
* `lieDerivative_eq_add_fderiv_sub`, `lieDerivative_le_add_norm_fderiv_mul` — changing the field
  from `v` to `w` changes the Lie derivative by `∂V/∂x · (w - v)`.
* `IsIntegralCurveOn.antitoneOn_of_lieDerivative_nonpos` — a nonpositive Lie derivative along an
  integral curve on an interval makes `V` nonincreasing along it.
* `continuous_lieDerivative` — the Lie derivative along a continuous field of a `C¹` function
  is continuous.
-/

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Lie derivative of `V(t, x)` along the time-dependent vector field `v`:
`∂V/∂t + ∂V/∂x · v(t, x)`, the derivative of `V` at `(t, x)` in the direction `(1, v(t, x))`.
This is the Lie derivative of `V` on `ℝ × E` along the autonomous field `(t, x) ↦ (1, v(t, x))`. -/
@[blueprint "def:lieDerivative"
  (title := "Lie derivative along a vector field")
  (statement := /-- For $V : \mathbb{R} \times E \to \mathbb{R}$ and a time-dependent vector
    field $v : \mathbb{R} \times E \to E$, the \emph{Lie derivative of $V$ along $v$} is
    \[
      L_v V(t, x) = \frac{\partial V}{\partial t}(t, x)
        + \frac{\partial V}{\partial x}(t, x)\, v(t, x),
    \]
    the derivative of $V$ at $(t, x)$ in the direction $(1, v(t, x))$: the Lie derivative of
    $V$, as a function on $\mathbb{R} \times E$, along the autonomous field
    $(t, x) \mapsto (1, v(t, x))$. -/)]
noncomputable def lieDerivative (V : ℝ → E → ℝ) (v : ℝ → E → E) (t : ℝ) (x : E) : ℝ :=
  fderiv ℝ (Function.uncurry V) (t, x) (1, v t x)

/-- For `V` independent of time, the Lie derivative along `v` is the directional derivative
`DV(x) (v t x)`. -/
@[blueprint "lem:lieDerivative-const"
  (title := "Lie derivative of a time-invariant function")
  (latexEnv := "lemma")
  (statement := /-- If $V$ does not depend on $t$ and is differentiable at $x$, then
    $L_v V(t, x) = DV(x)\, v(t, x)$. -/)]
lemma lieDerivative_const {V : E → ℝ} {v : ℝ → E → E} {t : ℝ} {x : E}
    (hV : DifferentiableAt ℝ V x) :
    lieDerivative (fun _ => V) v t x = fderiv ℝ V x (v t x) := by
  have h : HasFDerivAt (Function.uncurry fun (_ : ℝ) => V)
      ((fderiv ℝ V x).comp (ContinuousLinearMap.snd ℝ ℝ E)) (t, x) :=
    hV.hasFDerivAt.comp (t, x) hasFDerivAt_snd
  simp [lieDerivative, h.fderiv]

/-- Adding the linear time term `c t` to a time-invariant `V` adds `c` to its Lie derivative.  This
is how a bound `L_v V ≤ -c` on a rate becomes monotonicity of `V + c t`. -/
@[blueprint "lem:lieDerivative-add-mul"
  (title := "Lie derivative of $V(x) + ct$")
  (latexEnv := "lemma")
  (statement := /-- If $V$ does not depend on $t$ and is differentiable at $x$, then the Lie
    derivative of $(t, x) \mapsto V(x) + ct$ along $v$ is $DV(x)\, v(t, x) + c$. -/)]
lemma lieDerivative_add_mul {V : E → ℝ} {v : ℝ → E → E} {t : ℝ} {x : E} (c : ℝ)
    (hV : DifferentiableAt ℝ V x) :
    lieDerivative (fun t x => V x + c * t) v t x = fderiv ℝ V x (v t x) + c := by
  have h : HasFDerivAt (Function.uncurry fun (t : ℝ) (x : E) => V x + c * t)
      ((fderiv ℝ V x).comp (ContinuousLinearMap.snd ℝ ℝ E) +
        c • ContinuousLinearMap.fst ℝ ℝ E) (t, x) :=
    (hV.hasFDerivAt.comp (t, x) hasFDerivAt_snd).add (hasFDerivAt_fst.const_mul c)
  simp [lieDerivative, h.fderiv]

/-- **Chain rule along an integral curve**: the rate of change of `t ↦ V(t, γ(t))` is the
Lie derivative of `V` along the field. -/
@[blueprint "lem:isIntegralCurveOn-hasDerivWithinAt-lieDerivative"
  (title := "Chain rule along an integral curve")
  (latexEnv := "lemma")
  (statement := /-- Let $\gamma$ be an integral curve of $v$ on $I$, and $V$ differentiable at
    $(t, \gamma(t))$ for $t \in I$.  Then for $t \in I$, within $I$,
    \[
      \frac{d}{dt}\, V(t, \gamma(t)) = L_v V(t, \gamma(t))
    \]
    (\cref{def:lieDerivative}). -/)]
lemma IsIntegralCurveOn.hasDerivWithinAt_lieDerivative {V : ℝ → E → ℝ} {v : ℝ → E → E}
    {γ : ℝ → E} {I : Set ℝ} (hγ : IsIntegralCurveOn γ v I)
    (hV : ∀ τ ∈ I, DifferentiableAt ℝ (Function.uncurry V) (τ, γ τ)) {t : ℝ} (ht : t ∈ I) :
    HasDerivWithinAt (fun τ => V τ (γ τ)) (lieDerivative V v t (γ t)) I t := by
  have h_pair : HasDerivWithinAt (fun τ => (τ, γ τ)) (1, v t (γ t)) I t :=
    (hasDerivWithinAt_id t I).prodMk (hγ t ht)
  exact (hV t ht).hasFDerivAt.comp_hasDerivWithinAt t h_pair

/-- **The Lie derivative read off along a solution**: if `V(τ, γ(τ))` has right derivative `w` at
`t` along a forward integral curve `γ` from `t`, then the Lie derivative at `(t, γ(t))` is `w`.
Useful when `V` along the solution has a closed form, such as an integral of the solution. -/
@[blueprint "lem:isIntegralCurveOn-lieDerivative-eq-of-hasDerivWithinAt"
  (title := "The Lie derivative along a solution")
  (latexEnv := "lemma")
  (statement := /-- Let $\gamma$ be an integral curve of $v$ on $[t, \infty)$, $V$ differentiable
    at $(t, \gamma(t))$, and let $\tau \mapsto V(\tau, \gamma(\tau))$ have right derivative $w$
    at $t$.  Then $L_v V(t, \gamma(t)) = w$. -/)
  (proof := /-- By \cref{lem:isIntegralCurveOn-hasDerivWithinAt-lieDerivative} the right
    derivative is also $L_v V(t, \gamma(t))$, and right derivatives are unique. -/)]
lemma IsIntegralCurveOn.lieDerivative_eq_of_hasDerivWithinAt {V : ℝ → E → ℝ} {v : ℝ → E → E}
    {γ : ℝ → E} {t w : ℝ} (hγ : IsIntegralCurveOn γ v (Ici t))
    (hV : DifferentiableAt ℝ (Function.uncurry V) (t, γ t))
    (hW : HasDerivWithinAt (fun τ => V τ (γ τ)) w (Ici t) t) :
    lieDerivative V v t (γ t) = w := by
  have h_pair : HasDerivWithinAt (fun τ => (τ, γ τ)) (1, v t (γ t)) (Ici t) t :=
    (hasDerivWithinAt_id t _).prodMk (hγ t self_mem_Ici)
  have h_chain : HasDerivWithinAt (fun τ => V τ (γ τ)) (lieDerivative V v t (γ t)) (Ici t) t :=
    HasFDerivAt.comp_hasDerivWithinAt (f := fun τ => (τ, γ τ)) t hV.hasFDerivAt h_pair
  exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Ici t) h_chain hW

/-- **Changing the field changes the Lie derivative by the state derivative**:
`L_w V(t, x) = L_v V(t, x) + ∂V/∂x(t, x) · (w(t, x) - v(t, x))`.  This is how a perturbation of the
vector field — a linearization remainder, an input — enters `V̇`. -/
@[blueprint "lem:lieDerivative-eq-add-fderiv-sub"
  (title := "Lie derivative along a perturbed field")
  (latexEnv := "lemma")
  (statement := /-- If $V$ is differentiable at $(t, x)$, then for any two fields $v$ and $w$,
    \[
      L_w V(t, x) = L_v V(t, x) + \frac{\partial V}{\partial x}(t, x)\,\bigl(w(t, x) - v(t, x)\bigr)
    \]
    (\cref{def:lieDerivative}). -/)
  (proof := /-- Linearity of the derivative of $V$ at $(t, x)$ in the direction
    $(1, w) = (1, v) + (0, w - v)$; its value on $(0, e)$ is the state derivative applied to
    $e$. -/)]
lemma lieDerivative_eq_add_fderiv_sub {V : ℝ → E → ℝ} {v w : ℝ → E → E} {t : ℝ} {x : E}
    (hV : DifferentiableAt ℝ (Function.uncurry V) (t, x)) :
    lieDerivative V w t x = lieDerivative V v t x + fderiv ℝ (V t) x (w t x - v t x) := by
  rw [fderiv_eq_fderiv_uncurry_comp_inr hV, ContinuousLinearMap.comp_apply, lieDerivative,
    lieDerivative, ← map_add]
  congr 1
  ext <;> simp

/-- The perturbation bound: `L_w V ≤ L_v V + ‖∂V/∂x‖ ‖w - v‖`. -/
lemma lieDerivative_le_add_norm_fderiv_mul {V : ℝ → E → ℝ} {v w : ℝ → E → E} {t : ℝ} {x : E}
    (hV : DifferentiableAt ℝ (Function.uncurry V) (t, x)) :
    lieDerivative V w t x ≤ lieDerivative V v t x + ‖fderiv ℝ (V t) x‖ * ‖w t x - v t x‖ := by
  rw [lieDerivative_eq_add_fderiv_sub (v := v) hV]
  exact add_le_add le_rfl ((le_abs_self _).trans
    (by rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _))

/-- `V` is continuous along an integral curve at whose points it is differentiable. -/
lemma IsIntegralCurveOn.continuousOn_comp {V : ℝ → E → ℝ} {v : ℝ → E → E}
    {γ : ℝ → E} {I : Set ℝ} (hγ : IsIntegralCurveOn γ v I)
    (hV : ∀ τ ∈ I, DifferentiableAt ℝ (Function.uncurry V) (τ, γ τ)) :
    ContinuousOn (fun τ => V τ (γ τ)) I := fun τ hτ =>
  ContinuousAt.comp_continuousWithinAt (g := Function.uncurry V) (f := fun σ => (σ, γ σ))
    (hV τ hτ).continuousAt (continuousWithinAt_id.prodMk (hγ.continuousOn τ hτ))

/-- A nonpositive Lie derivative along an integral curve on a convex set `s` (an interval) makes
`V` nonincreasing along it.  Only the interior of `s` is tested. -/
@[blueprint "lem:isIntegralCurveOn-antitoneOn-of-lieDerivative-nonpos"
  (title := "Nonpositive Lie derivative along an integral curve")
  (latexEnv := "lemma")
  (statement := /-- Let $\gamma$ be an integral curve of $v$ on an interval $s$, $V$
    differentiable at $(t, \gamma(t))$ for $t \in s$, and $L_v V(t, \gamma(t)) \le 0$ at every
    interior point $t$ of $s$.  Then $t \mapsto V(t, \gamma(t))$ is nonincreasing on $s$. -/)
  (proof := /-- The mean value theorem, with the derivative given by
    \cref{lem:isIntegralCurveOn-hasDerivWithinAt-lieDerivative}. -/)]
lemma IsIntegralCurveOn.antitoneOn_of_lieDerivative_nonpos {V : ℝ → E → ℝ} {v : ℝ → E → E}
    {γ : ℝ → E} {s : Set ℝ} (hγ : IsIntegralCurveOn γ v s) (hs : Convex ℝ s)
    (hV : ∀ τ ∈ s, DifferentiableAt ℝ (Function.uncurry V) (τ, γ τ))
    (h_nonpos : ∀ t ∈ interior s, lieDerivative V v t (γ t) ≤ 0) :
    AntitoneOn (fun τ => V τ (γ τ)) s :=
  antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => lieDerivative V v t (γ t)) hs
    (hγ.continuousOn_comp hV)
    (fun _ ht => (hγ.hasDerivWithinAt_lieDerivative hV (interior_subset ht)).mono interior_subset)
    h_nonpos

/-- **Integrating factor along an integral curve.**  If `L_v V ≤ -c V` along an integral curve on
`[t₀, t₁]`, then `V` decays at least like `e^{-c(t - t₀)}`: `e^{c t} V(t, γ(t))` does not
increase.  With `c < 0` this is a growth bound. -/
@[blueprint "lem:isIntegralCurveOn-le-exp-mul-of-lieDerivative-le"
  (title := "Exponential bound from a linear Lie-derivative bound")
  (latexEnv := "lemma")
  (statement := /-- Let $\gamma$ be an integral curve of $v$ on $[t_0, t_1]$, $V$ differentiable
    at $(t, \gamma(t))$ for $t \in [t_0, t_1]$, and $c \in \mathbb{R}$ with
    $L_v V(t, \gamma(t)) \le -c\, V(t, \gamma(t))$ for $t \in (t_0, t_1)$.  Then
    $V(t, \gamma(t)) \le e^{-c(t - t_0)}\, V(t_0, \gamma(t_0))$ on $[t_0, t_1]$. -/)
  (proof := /-- The derivative of $e^{c t} V(t, \gamma(t))$ is
    $e^{c t}\bigl(c V + L_v V\bigr) \le 0$
    (\cref{lem:isIntegralCurveOn-hasDerivWithinAt-lieDerivative}), so it does not increase. -/)]
lemma IsIntegralCurveOn.le_exp_mul_of_lieDerivative_le {V : ℝ → E → ℝ} {v : ℝ → E → E}
    {γ : ℝ → E} {c t₀ t₁ : ℝ} (hγ : IsIntegralCurveOn γ v (Icc t₀ t₁))
    (hV : ∀ τ ∈ Icc t₀ t₁, DifferentiableAt ℝ (Function.uncurry V) (τ, γ τ))
    (h_rate : ∀ τ ∈ Ioo t₀ t₁, lieDerivative V v τ (γ τ) ≤ -c * V τ (γ τ)) :
    ∀ t ∈ Icc t₀ t₁, V t (γ t) ≤ Real.exp (-c * (t - t₀)) * V t₀ (γ t₀) := by
  have h_anti : AntitoneOn (fun σ => Real.exp (c * σ) * V σ (γ σ)) (Icc t₀ t₁) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun σ => Real.exp (c * σ) * (c * V σ (γ σ) + lieDerivative V v σ (γ σ)))
      (convex_Icc t₀ t₁) ?_ (fun σ hσ => ?_) (fun σ hσ => ?_)
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
        (hγ.continuousOn_comp hV)
    · rw [interior_Icc] at hσ ⊢
      have he : HasDerivAt (fun σ => Real.exp (c * σ)) (Real.exp (c * σ) * c) σ := by
        simpa using ((hasDerivAt_id σ).const_mul c).exp
      convert he.hasDerivWithinAt.mul ((hγ.hasDerivWithinAt_lieDerivative hV
        (Ioo_subset_Icc_self hσ)).mono Ioo_subset_Icc_self) using 1
      ring
    · rw [interior_Icc] at hσ
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [h_rate σ hσ])
  intro t ht
  have h := h_anti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  simp only at h
  rw [show Real.exp (-c * (t - t₀)) = Real.exp (c * t₀) / Real.exp (c * t) by
      rw [← Real.exp_sub]; congr 1; ring,
    div_mul_eq_mul_div, le_div_iff₀ (Real.exp_pos _)]
  linarith [h, mul_comm (V t (γ t)) (Real.exp (c * t))]

/-- The Lie derivative along a continuous field of a `C¹` function is continuous in `(t, x)`. -/
@[blueprint "lem:continuous-lieDerivative"
  (title := "Continuity of the Lie derivative")
  (latexEnv := "lemma")
  (statement := /-- If $V$ is $C^1$ and $v$ is continuous, then $(t, x) \mapsto
    L_v V(t, x)$ is continuous. -/)]
lemma continuous_lieDerivative {V : ℝ → E → ℝ} {v : ℝ → E → E}
    (hV : ContDiff ℝ 1 (Function.uncurry V)) (hv : Continuous (Function.uncurry v)) :
    Continuous (fun p : ℝ × E => lieDerivative V v p.1 p.2) :=
  (hV.continuous_fderiv one_ne_zero).clm_apply (continuous_const.prodMk hv)

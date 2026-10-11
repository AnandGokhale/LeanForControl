import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.Basic
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
  `DV(x) v`.
* `IsIntegralCurveOn.hasDerivWithinAt_lieDerivative` — the chain rule along an integral curve.
* `IsIntegralCurveOn.antitoneOn_of_lieDerivative_nonpos` — a nonpositive derivative along an
  integral curve on `[a, b]` makes `V` nonincreasing along it.
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

/-- **Chain rule along an integral curve**: the rate of change of `t ↦ V(t, γ(t))` is the
Lie derivative of `V` along the field. -/
@[blueprint "lem:isIntegralCurveOn-hasDerivWithinAt-lieDerivative"
  (title := "Chain rule along an integral curve")
  (latexEnv := "lemma")
  (statement := /-- Let $V$ be differentiable and $\gamma$ an integral curve of $v$ on $I$.
    Then for $t \in I$, within $I$,
    \[
      \frac{d}{dt}\, V(t, \gamma(t)) = L_v V(t, \gamma(t))
    \]
    (\cref{def:lieDerivative}). -/)]
lemma IsIntegralCurveOn.hasDerivWithinAt_lieDerivative {V : ℝ → E → ℝ} {v : ℝ → E → E}
    {γ : ℝ → E} {I : Set ℝ} (hγ : IsIntegralCurveOn γ v I)
    (hV : Differentiable ℝ (Function.uncurry V)) {t : ℝ} (ht : t ∈ I) :
    HasDerivWithinAt (fun τ => V τ (γ τ)) (lieDerivative V v t (γ t)) I t := by
  have h_pair : HasDerivWithinAt (fun τ => (τ, γ τ)) (1, v t (γ t)) I t :=
    (hasDerivWithinAt_id t I).prodMk (hγ t ht)
  exact (hV (t, γ t)).hasFDerivAt.comp_hasDerivWithinAt t h_pair

/-- A nonpositive Lie derivative along an integral curve on `[a, b]` makes `V` nonincreasing along
it. -/
@[blueprint "lem:isIntegralCurveOn-antitoneOn-of-lieDerivative-nonpos"
  (title := "Nonpositive Lie derivative along an integral curve")
  (latexEnv := "lemma")
  (statement := /-- Let $V$ be differentiable and $\gamma$ an integral curve of $v$ on
    $[a, b]$ with $L_v V(t, \gamma(t)) \le 0$ for $t \in (a, b)$.  Then
    $t \mapsto V(t, \gamma(t))$ is nonincreasing on $[a, b]$. -/)
  (proof := /-- The mean value theorem, with the derivative given by
    \cref{lem:isIntegralCurveOn-hasDerivWithinAt-lieDerivative}. -/)]
lemma IsIntegralCurveOn.antitoneOn_of_lieDerivative_nonpos {V : ℝ → E → ℝ} {v : ℝ → E → E}
    {γ : ℝ → E} {a b : ℝ} (hγ : IsIntegralCurveOn γ v (Icc a b))
    (hV : Differentiable ℝ (Function.uncurry V))
    (h_nonpos : ∀ t ∈ Ioo a b, lieDerivative V v t (γ t) ≤ 0) :
    AntitoneOn (fun τ => V τ (γ τ)) (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => lieDerivative V v t (γ t))
    (convex_Icc a b)
    (hV.continuous.comp_continuousOn (continuousOn_id.prodMk hγ.continuousOn))
    (fun t ht => ?_) (fun t ht => ?_)
  · rw [interior_Icc] at ht ⊢
    exact (hγ.hasDerivWithinAt_lieDerivative hV (Ioo_subset_Icc_self ht)).mono Ioo_subset_Icc_self
  · rw [interior_Icc] at ht
    exact h_nonpos t ht

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

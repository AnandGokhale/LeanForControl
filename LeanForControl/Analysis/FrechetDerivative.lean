import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Convex
import Architect

/-!
# The Fréchet derivative

Facts about `HasFDerivAt` stated in the `ε`–`δ` form that nonlinear arguments consume, rather
than the little-o form Mathlib states them in. The linearization error
`f x - f x₀ - A (x - x₀)` is the object of interest: Lyapunov's indirect method works because
it is `o (‖x - x₀‖)`, and what the proofs need is an explicit radius on which it is small.
-/

open Filter Asymptotics
open scoped Topology

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Differentiability, in `ε`–`δ` form: the linearization error is bounded by `ε ‖x - x₀‖` on
an explicit ball around `x₀`. -/
@[blueprint "thm:frechet-linearization-error-bound"
  (title := "Quantitative linearization error bound")
  (statement := /-- Let $A$ be the Fréchet derivative of $f$ at $x_0$. For every
    $\varepsilon > 0$ there exists $\delta > 0$ such that
    \[
      \|x - x_0\| < \delta \;\Longrightarrow\;
        \|f(x) - f(x_0) - A(x - x_0)\| \le \varepsilon\,\|x - x_0\|.
    \]
    This is the $\varepsilon$--$\delta$ form of $f(x) - f(x_0) - A(x-x_0) = o(\|x-x_0\|)$. -/)]
theorem HasFDerivAt.exists_linearization_error_bound
    {f : E → F} {A : E →L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f A x₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x, ‖x - x₀‖ < δ →
      ‖f x - f x₀ - A (x - x₀)‖ ≤ ε * ‖x - x₀‖ := by
  have hsmall := hf.isLittleO.bound hε
  rw [Metric.eventually_nhds_iff] at hsmall
  rcases hsmall with ⟨δ, hδ, hbound⟩
  refine ⟨δ, hδ, fun x hx ↦ hbound ?_⟩
  simpa [dist_eq_norm] using hx

section Quadratic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **A Lipschitz derivative makes the linearization error quadratic**: if `Df` is `L`-Lipschitz on
a convex set containing `x₀` and `x`, then `‖f x - f x₀ - Df(x₀)(x - x₀)‖ ≤ L ‖x - x₀‖²`. -/
@[blueprint "thm:norm-sub-sub-fderiv-le-of-lipschitzOnWith"
  (title := "Quadratic linearization error")
  (statement := /-- Let $f$ be differentiable on a convex set $s$, with $Df$ $L$-Lipschitz on $s$.
    For $x_0, x \in s$,
    \[
      \|f(x) - f(x_0) - Df(x_0)(x - x_0)\| \le L\,\|x - x_0\|^2.
    \] -/)
  (proof := /-- On the segment from $x_0$ to $x$, the map $y \mapsto f(y) - Df(x_0)y$ has
    derivative $Df(y) - Df(x_0)$, of norm at most $L\|y - x_0\| \le L\|x - x_0\|$; apply the mean
    value inequality. -/)]
theorem norm_sub_sub_fderiv_le_of_lipschitzOnWith {f : E → F} {s : Set E} (hs : Convex ℝ s)
    (hf : ∀ y ∈ s, DifferentiableAt ℝ f y) {L : NNReal} (hL : LipschitzOnWith L (fderiv ℝ f) s)
    {x₀ x : E} (hx₀ : x₀ ∈ s) (hx : x ∈ s) :
    ‖f x - f x₀ - fderiv ℝ f x₀ (x - x₀)‖ ≤ L * ‖x - x₀‖ ^ 2 := by
  have h_seg : segment ℝ x₀ x ⊆ s := hs.segment_subset hx₀ hx
  -- `y ↦ f y - Df(x₀) y` has derivative `Df(y) - Df(x₀)`.
  have h_deriv : ∀ y ∈ segment ℝ x₀ x, HasFDerivAt (fun y => f y - fderiv ℝ f x₀ y)
      (fderiv ℝ f y - fderiv ℝ f x₀) y := fun y hy =>
    (hf y (h_seg hy)).hasFDerivAt.sub (fderiv ℝ f x₀).hasFDerivAt
  have h_mvt := (convex_segment x₀ x).norm_image_sub_le_of_norm_fderiv_le
    (f := fun y => f y - fderiv ℝ f x₀ y) (C := L * ‖x - x₀‖)
    (fun y hy => (h_deriv y hy).differentiableAt)
    (fun y hy => by
      rw [(h_deriv y hy).fderiv, ← dist_eq_norm]
      calc dist (fderiv ℝ f y) (fderiv ℝ f x₀)
          ≤ L * dist y x₀ := hL.dist_le_mul y (h_seg hy) x₀ hx₀
        _ ≤ L * ‖x - x₀‖ := by
            rw [dist_eq_norm]
            exact mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hy) L.coe_nonneg)
    (left_mem_segment ℝ x₀ x) (right_mem_segment ℝ x₀ x)
  calc ‖f x - f x₀ - fderiv ℝ f x₀ (x - x₀)‖
      = ‖(f x - fderiv ℝ f x₀ x) - (f x₀ - fderiv ℝ f x₀ x₀)‖ := by
        rw [map_sub]
        congr 1
        abel
    _ ≤ L * ‖x - x₀‖ * ‖x - x₀‖ := h_mvt
    _ = L * ‖x - x₀‖ ^ 2 := by ring

end Quadratic

section Partial

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The partial derivative in the state** of a function `V(t, x)` differentiable jointly at
`(t, x)` is its joint derivative restricted to state directions `(0, v)`. -/
theorem fderiv_eq_fderiv_uncurry_comp_inr {V : ℝ → E → F} {t : ℝ} {x : E}
    (h : DifferentiableAt ℝ (Function.uncurry V) (t, x)) :
    fderiv ℝ (V t) x = (fderiv ℝ (Function.uncurry V) (t, x)).comp
      (ContinuousLinearMap.inr ℝ ℝ E) :=
  (h.hasFDerivAt.comp x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))).fderiv

end Partial

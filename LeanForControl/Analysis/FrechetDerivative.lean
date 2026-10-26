import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import Architect

/-!
# The Fréchet derivative

Bounds on the linearization error `f x - f x₀ - Df(x₀)(x - x₀)` beyond Mathlib's pointwise
little-o (`HasFDerivAt.isLittleO`): uniform over a compact set for a `C¹` map, and quadratic for a
Lipschitz derivative.  Also the partial derivative of a function of `(t, x)` in `x`.
-/

open Filter Asymptotics Set
open scoped Topology

section Uniform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Metric

/-- **Uniform linearization error bound.**  On a compact set, a `C¹` map is uniformly close to its
linearization: for every `η > 0` there is one `r > 0` with
`‖g w - g z - Dg(z)(w - z)‖ ≤ η ‖w - z‖` whenever `z` is in the set and `‖w - z‖ < r`.  Unlike
the pointwise bound of `HasFDerivAt.isLittleO`, the radius does not depend on the base point. -/
@[blueprint "thm:contDiff-exists-uniform-linearization-error-bound"
  (title := "Uniform linearization error bound")
  (statement := /-- Let $g : E \to E$ be $C^1$ on a finite-dimensional space and $C \subseteq E$
    compact.  For every $\eta > 0$ there is $r > 0$ with
    \[
      \|g(w) - g(z) - Dg(z)(w - z)\| \le \eta\,\|w - z\|
    \]
    for all $z \in C$ and $\|w - z\| < r$. -/)
  (proof := /-- $Dg$ is uniformly continuous on the compact thickening of $C$ by $1$; take $r$
    below its modulus for $\eta$ and below $1$.  On the ball of radius $r$ about $z$,
    $\|Dg(u) - Dg(z)\| \le \eta$, and the mean value inequality bounds the remainder. -/)]
theorem ContDiff.exists_uniform_linearization_error_bound {g : E → E} (hg : ContDiff ℝ 1 g)
    {C : Set E} (hC : IsCompact C) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ z ∈ C, ∀ w, ‖w - z‖ < r → ‖g w - g z - fderiv ℝ g z (w - z)‖ ≤ η * ‖w - z‖ := by
  -- `Dg` is uniformly continuous on the compact thickening of `C` by `1`.
  obtain ⟨r₀, hr₀, hunif⟩ := Metric.uniformContinuousOn_iff.mp
    (hC.cthickening.uniformContinuousOn_of_continuous
      (hg.continuous_fderiv one_ne_zero).continuousOn) η hη
  have hr : 0 < min r₀ 1 := lt_min hr₀ one_pos
  refine ⟨min r₀ 1, hr, fun z hz w hw => ?_⟩
  -- On the ball of radius `min r₀ 1` about `z`, `‖Dg(u) - Dg(z)‖ ≤ η`: the mean value inequality.
  refine (convex_ball z (min r₀ 1)).norm_image_sub_le_of_norm_fderiv_le'
    (fun u _ => hg.differentiable one_ne_zero u) (fun u hu => ?_) (mem_ball_self hr)
    (mem_ball_iff_norm.mpr hw)
  rw [← dist_eq_norm]
  exact (hunif u ((ball_subset_closedBall.trans ((closedBall_subset_closedBall
    (min_le_right _ _)).trans (closedBall_subset_cthickening hz 1))) hu) z
    (self_subset_cthickening C hz) ((Metric.mem_ball.mp hu).trans_le (min_le_left _ _))).le

end Uniform

section Quadratic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **A Lipschitz derivative makes the linearization error quadratic**: if `f` has derivative `f'`
within a convex set `s` and `f'` is `L`-Lipschitz on `s`, then for `x₀, x ∈ s`,
`‖f x - f x₀ - f'(x₀)(x - x₀)‖ ≤ (L / 2) ‖x - x₀‖²`.

Along the segment `y = x₀ + τ (x - x₀)` the derivative error is at most `L τ ‖x - x₀‖`, whose
integral over `τ ∈ [0, 1]` is `(L / 2) ‖x - x₀‖²`. -/
@[blueprint "thm:convex-norm-image-sub-sub-le-of-lipschitzOnWith"
  (title := "Quadratic linearization error")
  (statement := /-- Let $f$ have derivative $f'$ within a convex set $s$, with $f'$ $L$-Lipschitz
    on $s$.  For $x_0, x \in s$,
    \[
      \|f(x) - f(x_0) - f'(x_0)(x - x_0)\| \le \tfrac{L}{2}\,\|x - x_0\|^2.
    \] -/)
  (proof := /-- With $h = x - x_0$, let
    $g(\tau) = f(x_0 + \tau h) - f(x_0) - \tau f'(x_0) h$ on $[0, 1]$.  Then $g(0) = 0$ and
    $\|g'(\tau)\| = \|(f'(x_0 + \tau h) - f'(x_0)) h\| \le L \tau \|h\|^2$, the derivative
    of $B(\tau) = \tfrac{L}{2} \tau^2 \|h\|^2$.  The norm comparison theorem gives
    $\|g(1)\| \le B(1)$. -/)]
theorem Convex.norm_image_sub_sub_le_of_lipschitzOnWith {f : E → F} {f' : E → E →L[ℝ] F}
    {s : Set E} (hs : Convex ℝ s) (hf : ∀ y ∈ s, HasFDerivWithinAt f (f' y) s y) {L : NNReal}
    (hf' : LipschitzOnWith L f' s) {x₀ x : E} (hx₀ : x₀ ∈ s) (hx : x ∈ s) :
    ‖f x - f x₀ - f' x₀ (x - x₀)‖ ≤ L / 2 * ‖x - x₀‖ ^ 2 := by
  -- The segment `τ ↦ x₀ + τ h`, `h = x - x₀`, stays in `s`.
  have hp_mem : MapsTo (fun τ : ℝ => x₀ + τ • (x - x₀)) (Icc 0 1) s := fun τ hτ =>
    hs.segment_subset hx₀ hx (by rw [segment_eq_image']; exact ⟨τ, hτ, rfl⟩)
  -- `g(τ) = f(x₀ + τ h) - f(x₀) - τ f'(x₀) h` has derivative `(f'(x₀ + τ h) - f'(x₀)) h`.
  have hg : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt
      (fun τ : ℝ => f (x₀ + τ • (x - x₀)) - f x₀ - τ • f' x₀ (x - x₀))
      (f' (x₀ + τ • (x - x₀)) (x - x₀) - f' x₀ (x - x₀)) (Icc 0 1) τ := by
    intro τ hτ
    have hp : HasDerivWithinAt (fun τ : ℝ => x₀ + τ • (x - x₀)) (x - x₀) (Icc 0 1) τ := by
      simpa using (((hasDerivAt_id τ).smul_const (x - x₀)).const_add x₀).hasDerivWithinAt
    have hlin : HasDerivWithinAt (fun τ : ℝ => τ • f' x₀ (x - x₀)) (f' x₀ (x - x₀))
        (Icc 0 1) τ := by
      simpa using ((hasDerivAt_id τ).smul_const (f' x₀ (x - x₀))).hasDerivWithinAt
    exact (((hf _ (hp_mem hτ)).comp_hasDerivWithinAt τ hp hp_mem).sub_const (f x₀)).sub hlin
  -- The derivative error is at most `L τ ‖h‖²`.
  have h_bound : ∀ τ ∈ Ico (0 : ℝ) 1,
      ‖f' (x₀ + τ • (x - x₀)) (x - x₀) - f' x₀ (x - x₀)‖ ≤ L * τ * ‖x - x₀‖ ^ 2 := by
    intro τ hτ
    calc ‖f' (x₀ + τ • (x - x₀)) (x - x₀) - f' x₀ (x - x₀)‖
        = ‖(f' (x₀ + τ • (x - x₀)) - f' x₀) (x - x₀)‖ := by rw [ContinuousLinearMap.sub_apply]
      _ ≤ ‖f' (x₀ + τ • (x - x₀)) - f' x₀‖ * ‖x - x₀‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * ‖x₀ + τ • (x - x₀) - x₀‖ * ‖x - x₀‖ := by
          gcongr
          rw [← dist_eq_norm, ← dist_eq_norm]
          exact hf'.dist_le_mul _ (hp_mem (Ico_subset_Icc_self hτ)) _ hx₀
      _ = L * τ * ‖x - x₀‖ ^ 2 := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ.1]
          ring
  -- Compare with `B(τ) = (L / 2) τ² ‖h‖²`, of derivative `L τ ‖h‖²`.
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun τ hτ => (hg τ hτ).continuousWithinAt)
    (fun τ hτ => (hg τ (Ico_subset_Icc_self hτ)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hτ))
    (B := fun τ => L / 2 * τ ^ 2 * ‖x - x₀‖ ^ 2) (B' := fun τ => L * τ * ‖x - x₀‖ ^ 2)
    (by simp)
    (fun τ => (((hasDerivAt_pow 2 τ).const_mul ((L : ℝ) / 2)).mul_const (‖x - x₀‖ ^ 2)).congr_deriv
      (by push_cast; ring))
    h_bound (right_mem_Icc.2 zero_le_one)
  simpa using h

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

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.Convex
import Architect

/-!
# The Fréchet derivative

Facts about `HasFDerivAt` stated in the `ε`–`δ` form that nonlinear arguments consume, rather
than the little-o form Mathlib states them in. The linearization error
`f x - f x₀ - A (x - x₀)` is the object of interest: Lyapunov's indirect method works because
it is `o (‖x - x₀‖)`, and what the proofs need is an explicit radius on which it is small.
-/

open Filter Asymptotics Set
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

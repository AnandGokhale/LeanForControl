import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.InnerProductSpace.Calculus
import Architect

/-!
# The Fréchet derivative

Bounds on the linearization error `f x - f x₀ - Df(x₀)(x - x₀)` beyond Mathlib's pointwise
little-o (`HasFDerivAt.isLittleO`): uniform over a compact set for a `C¹` map, and quadratic for a
Lipschitz derivative.  Also the partial derivative of a function of `(t, x)` in `x`, and the
derivative of a map read in other coordinates (`HasFDerivAt.conj`).
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

section Conj

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **A map in other coordinates**: if `f` has derivative `f'` at `x`, then `e ∘ f ∘ e⁻¹` has
derivative `e ∘ f' ∘ e⁻¹` at `e x`, for a continuous linear equivalence `e`.  Used with `e` the
identity of `ℝⁿ` between two norms, to move a derivative from one norm to the other. -/
theorem HasFDerivAt.conj (e : E ≃L[𝕜] F) {f : E → E} {f' : E →L[𝕜] E} {x : E}
    (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun z => e (f (e.symm z)))
      ((e : E →L[𝕜] F).comp (f'.comp (e.symm : F →L[𝕜] E))) (e x) :=
  e.comp_hasFDerivAt_iff.2 <| e.symm.comp_right_hasFDerivAt_iff.2 <| by simpa using hf

end Conj

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

section Directional

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **A bound on increments bounds the derivative**: if `φ (f (x + t v) - f x) ≤ t c` for small
`t > 0`, with `φ` continuous and positively homogeneous, then `φ (f' v) ≤ c`. -/
@[blueprint "lem:hasFDerivAt-apply-le-of-increment-le"
  (title := "Increment bounds bound the derivative")
  (statement := /-- Let $f$ have derivative $f'$ at $x$, let $C$ be a neighbourhood of $x$, and
    let $\varphi$ be continuous with $\varphi(a u) = a \varphi(u)$ for $a \ge 0$.  If
    $\varphi(f(x + t v) - f(x)) \le t c$ whenever $t > 0$ and $x + t v \in C$, then
    $\varphi(f'(x) v) \le c$. -/)
  (proof := /-- $\varphi$ of the difference quotient $(f(x + t v) - f(x))/t$ is at most $c$ for
    small $t > 0$ and tends to $\varphi(f'(x) v)$ as $t \to 0^+$. -/)]
theorem HasFDerivAt.apply_le_of_increment_le {f : E → F} {f' : E →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f f' x) {C : Set E} (hC : C ∈ 𝓝 x) {φ : F → ℝ} (hφ : Continuous φ)
    (hφa : ∀ a : ℝ, 0 ≤ a → ∀ u, φ (a • u) = a * φ u) (v : E) {c : ℝ}
    (h : ∀ t : ℝ, 0 < t → x + t • v ∈ C → φ (f (x + t • v) - f x) ≤ t * c) :
    φ (f' v) ≤ c := by
  have hd : HasDerivAt (fun t : ℝ => f (x + t • v)) (f' v) 0 := by
    simpa using hf.comp_hasDerivAt_of_eq (0 : ℝ)
      (((hasDerivAt_id 0).smul_const v).const_add x) (by simp)
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • v ∈ C :=
    nhdsWithin_le_nhds (((continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0
      x (by simp)).eventually hC)
  refine le_of_tendsto ((hφ.tendsto _).comp (hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0))) ?_
  filter_upwards [hmem, self_mem_nhdsWithin] with t ht (htp : 0 < t)
  simp only [Function.comp_apply, slope_def_module, sub_zero, zero_smul, add_zero]
  rw [hφa _ (inv_nonneg.2 htp.le), inv_mul_le_iff₀ htp]
  exact h t htp ht

end Directional

section InnerProduct

/-- **The gradient of a quadratic form**: `‖∂/∂x ⟪x, M x⟫‖ ≤ 2‖M‖‖x‖`. -/
@[blueprint "lem:norm-fderiv-inner-apply-self-le"
  (title := "Gradient of a quadratic form")
  (statement := /-- For a bounded operator $M$ on a real inner product space,
    $\bigl\|\partial_x \langle x, Mx \rangle\bigr\| \le 2\|M\|\|x\|$. -/)
  (proof := /-- The derivative is $z \mapsto \langle x, Mz \rangle + \langle z, Mx \rangle$;
    apply Cauchy--Schwarz to each term. -/)]
theorem norm_fderiv_inner_apply_self_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (M : E →L[ℝ] E) (x : E) :
    ‖fderiv ℝ (fun y => inner ℝ y (M y)) x‖ ≤ 2 * ‖M‖ * ‖x‖ := by
  have h : HasFDerivAt (fun y => inner ℝ y (M y))
      ((fderivInnerCLM ℝ (x, M x)).comp ((ContinuousLinearMap.id ℝ E).prod M)) x :=
    (hasFDerivAt_id x).inner ℝ M.hasFDerivAt
  rw [h.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, fderivInnerCLM_apply, Real.norm_eq_abs]
  calc |inner ℝ x (M z) + inner ℝ z (M x)|
      ≤ ‖x‖ * ‖M z‖ + ‖z‖ * ‖M x‖ :=
        (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _)
          (abs_real_inner_le_norm _ _))
    _ ≤ ‖x‖ * (‖M‖ * ‖z‖) + ‖z‖ * (‖M‖ * ‖x‖) :=
        add_le_add (mul_le_mul_of_nonneg_left (M.le_opNorm z) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (M.le_opNorm x) (norm_nonneg _))
    _ = 2 * ‖M‖ * ‖x‖ * ‖z‖ := by ring

end InnerProduct

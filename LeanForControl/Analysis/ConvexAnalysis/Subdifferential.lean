import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# `Analysis.ConvexAnalysis.Subdifferential` — closed convex proper functions and subgradients

An extended-real-valued function `R : X → ℝ ∪ {+∞}` is represented as a pair: a function
`R : X → ℝ` and its effective domain `D : Set X`, with `R = +∞` off `D` understood.  Values of `R`
off `D` are never used.  Mathlib has no convexity for extended-real-valued functions; in this form
Mathlib's `ConvexOn` applies directly.  An indicator function `ι_C` is `R = 0`, `D = C`; a finite
`R` has `D = univ`.

* `IsClosedConvexProper R D` — `D` nonempty, `R` convex on `D`, closed sublevel sets.  These are
  properness, convexity and lower semicontinuity of the extended function.
* `subdifferential R D z` — the subgradients of `R` at `z`; empty off `D`.
* `ConvexOn.gradient_mem_subdifferential` — the first-order inequality: the gradient of a
  differentiable convex function is a subgradient.
* `inner_sub_sub_nonneg_of_mem_subdifferential` — the subdifferential is monotone.
* `neg_gradient_mem_subdifferential_of_isMinOn`, `isMinOn_add_iff_neg_gradient_mem_subdifferential`
  — the composite Fermat rule: necessity, and the characterisation for convex `E`.
-/

open scoped RealInnerProductSpace Gradient

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- `R`, with effective domain `D`, is *closed, convex and proper*: `D` is nonempty, `R` is convex
on `D`, and its sublevel sets are closed. -/
structure IsClosedConvexProper (R : X → ℝ) (D : Set X) : Prop where
  nonempty : D.Nonempty
  convexOn : ConvexOn ℝ D R
  isClosed_sublevel : ∀ c : ℝ, IsClosed {x ∈ D | R x ≤ c}

/-- The *subdifferential* of `R` (with domain `D`) at `z`: the subgradients `s` with
`R z + ⟪s, y - z⟫ ≤ R y` for all `y ∈ D`.  Empty off `D`. -/
def subdifferential (R : X → ℝ) (D : Set X) (z : X) : Set X :=
  {s | z ∈ D ∧ ∀ y ∈ D, R z + ⟪s, y - z⟫ ≤ R y}

/-- **First-order inequality.**  The gradient of a convex function differentiable at `x` is a
subgradient there: `E x + ⟪∇E x, y - x⟫ ≤ E y` for all `y ∈ s`. -/
theorem ConvexOn.gradient_mem_subdifferential [CompleteSpace X] {E : X → ℝ} {s : Set X} {x : X}
    (hE : ConvexOn ℝ s E) (hx : x ∈ s) (hd : DifferentiableAt ℝ E x) :
    ∇ E x ∈ subdifferential E s x := by
  refine ⟨hx, fun y hy => ?_⟩
  -- The slope of `E` from `x` towards `y` is at most `E y - E x`, and tends to `⟪∇E x, y - x⟫`.
  have h_slope : ⟪∇ E x, y - x⟫ ≤ E y - E x := by
    rw [inner_gradient_left hd]
    refine le_of_tendsto (hd.hasFDerivAt.hasLineDerivAt (y - x)).tendsto_slope_zero_right ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with θ hθ
    rw [smul_eq_mul, inv_mul_le_iff₀ hθ.1]
    calc E (x + θ • (y - x)) - E x = E ((1 - θ) • x + θ • y) - E x := by
          congr 2; module
      _ ≤ (1 - θ) * E x + θ * E y - E x := by
          gcongr
          exact hE.2 hx hy (sub_nonneg.2 hθ.2.le) hθ.1.le (sub_add_cancel 1 θ)
      _ = θ * (E y - E x) := by ring
  linarith

/-- **Monotonicity of the subdifferential.**  For subgradients `sp ∈ ∂R(p)` and `sq ∈ ∂R(q)`,
`⟪sp - sq, p - q⟫ ≥ 0`. -/
theorem inner_sub_sub_nonneg_of_mem_subdifferential {R : X → ℝ} {D : Set X} {p q sp sq : X}
    (hp : sp ∈ subdifferential R D p) (hq : sq ∈ subdifferential R D q) :
    0 ≤ ⟪sp - sq, p - q⟫ := by
  have h₁ := hp.2 q hq.1
  have h₂ := hq.2 p hp.1
  rw [← neg_sub p q, inner_neg_right] at h₁
  rw [inner_sub_left]
  linarith

/-- **Fermat rule, necessity.**  If `x ∈ D` minimizes `E + R` over `D`, with `R` convex on `D` and
`E` differentiable at `x`, then `-∇E(x) ∈ ∂R(x)`.  No convexity of `E` is needed. -/
theorem neg_gradient_mem_subdifferential_of_isMinOn [CompleteSpace X] {E R : X → ℝ} {D : Set X}
    {x : X} (hR : ConvexOn ℝ D R) (hd : DifferentiableAt ℝ E x) (hx : x ∈ D)
    (hmin : IsMinOn (fun y => E y + R y) D x) : -∇ E x ∈ subdifferential R D x := by
  refine ⟨hx, fun y hy => ?_⟩
  -- Along the segment towards `y`, `E + R` does not drop below its value at `x`; the slope of
  -- `E` tends to `⟪∇E x, y - x⟫` and that of `R` is at most `R y - R x`.
  have h_slope : 0 ≤ ⟪∇ E x, y - x⟫ + (R y - R x) := by
    rw [inner_gradient_left hd]
    refine ge_of_tendsto ((hd.hasFDerivAt.hasLineDerivAt (y - x)).tendsto_slope_zero_right.add
      tendsto_const_nhds) ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with θ hθ
    have h_R : R (x + θ • (y - x)) ≤ (1 - θ) * R x + θ * R y := by
      rw [show x + θ • (y - x) = (1 - θ) • x + θ • y by module]
      exact hR.2 hx hy (sub_nonneg.2 hθ.2.le) hθ.1.le (sub_add_cancel 1 θ)
    have h_min : E x + R x ≤ E (x + θ • (y - x)) + R (x + θ • (y - x)) :=
      hmin (hR.1.add_smul_sub_mem hx hy ⟨hθ.1.le, hθ.2.le⟩)
    rw [smul_eq_mul, show θ⁻¹ * (E (x + θ • (y - x)) - E x) + (R y - R x)
      = θ⁻¹ * (E (x + θ • (y - x)) - E x + θ * (R y - R x)) by
        rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hθ.1.ne', one_mul]]
    exact mul_nonneg (inv_nonneg.2 hθ.1.le) (by linarith)
  rw [inner_neg_left]
  linarith

/-- **Composite Fermat rule.**  For `E` convex and differentiable and `R` convex on `D`, `x`
minimizes `E + R` over `D` if and only if `-∇E(x) ∈ ∂R(x)`. -/
theorem isMinOn_add_iff_neg_gradient_mem_subdifferential [CompleteSpace X] {E R : X → ℝ}
    {D : Set X} {x : X} (hE : ConvexOn ℝ D E) (hR : ConvexOn ℝ D R)
    (hd : DifferentiableAt ℝ E x) :
    (x ∈ D ∧ IsMinOn (fun y => E y + R y) D x) ↔ -∇ E x ∈ subdifferential R D x := by
  constructor
  · rintro ⟨hx, hmin⟩
    exact neg_gradient_mem_subdifferential_of_isMinOn hR hd hx hmin
  · intro h
    refine ⟨h.1, fun y hy => ?_⟩
    have h_E := (hE.gradient_mem_subdifferential h.1 hd).2 y hy
    have h_R := h.2 y hy
    rw [inner_neg_left] at h_R
    change E x + R x ≤ E y + R y
    linarith

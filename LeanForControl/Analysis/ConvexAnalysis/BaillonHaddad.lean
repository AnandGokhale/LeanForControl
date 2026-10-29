import LeanForControl.Analysis.ConvexAnalysis.Subdifferential
import LeanForControl.Analysis.FrechetDerivative

/-!
# `Analysis.ConvexAnalysis.BaillonHaddad` — cocoercivity of smooth convex gradients

**Baillon–Haddad theorem** (one direction): the gradient of a differentiable convex function that
is `ℓ`-Lipschitz is `1/ℓ`-cocoercive,

    ‖∇E(x) - ∇E(y)‖² ≤ ℓ ⟪∇E(x) - ∇E(y), x - y⟫.

The proof combines the descent lemma `Convex.norm_image_sub_sub_le_of_lipschitzOnWith` with the
first-order inequality `ConvexOn.gradient_mem_subdifferential` into the sharpened first-order
inequality `ConvexOn.add_inner_add_norm_sq_div_le`, and adds it at `(x, y)` and `(y, x)`.
-/

open scoped RealInnerProductSpace Gradient

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- **Sharpened first-order inequality.**  If `E` is convex and differentiable and `∇E` is
`ℓ`-Lipschitz with `ℓ > 0`, then
`E x + ⟪∇E x, y - x⟫ + ‖∇E y - ∇E x‖² / (2ℓ) ≤ E y`. -/
theorem ConvexOn.add_inner_add_norm_sq_div_le {E : X → ℝ} {ℓ : NNReal}
    (hE : ConvexOn ℝ Set.univ E) (hd : Differentiable ℝ E) (hL : LipschitzWith ℓ (∇ E))
    (hℓ : 0 < ℓ) (x y : X) :
    E x + ⟪∇ E x, y - x⟫ + ‖∇ E y - ∇ E x‖ ^ 2 / (2 * ℓ) ≤ E y := by
  -- Compare at the gradient step `z = y - ∇(E - ⟪∇E x, ·⟫)(y) / ℓ` from `y`.
  set g := ∇ E y - ∇ E x
  set z := y - (ℓ : ℝ)⁻¹ • g
  -- Descent lemma at `y`: `E z ≤ E y + ⟪∇E y, z - y⟫ + ℓ/2 ‖z - y‖²`.
  have h_descent : E z ≤ E y + ⟪∇ E y, z - y⟫ + ℓ / 2 * ‖z - y‖ ^ 2 := by
    have h_fderiv : fderiv ℝ E = (InnerProductSpace.toDual ℝ X) ∘ ∇ E := by
      funext w; simp [gradient]
    have := convex_univ.norm_image_sub_sub_le_of_lipschitzOnWith (L := ℓ)
      (fun w _ => (hd w).hasFDerivAt.hasFDerivWithinAt)
      (by rw [h_fderiv]
          simpa using (InnerProductSpace.toDual ℝ X).isometry.lipschitz.comp hL)
      (Set.mem_univ y) (Set.mem_univ z)
    rw [← inner_gradient_left (hd y)] at this
    linarith [le_abs_self (E z - E y - ⟪∇ E y, z - y⟫),
      Real.norm_eq_abs (E z - E y - ⟪∇ E y, z - y⟫)]
  -- First-order inequality at `x`: `E x + ⟪∇E x, z - x⟫ ≤ E z`.
  have h_first := (hE.gradient_mem_subdifferential (Set.mem_univ x) (hd x)).2 z (Set.mem_univ z)
  have hzy : z - y = -((ℓ : ℝ)⁻¹ • g) := by simp [z]
  have hzx : z - x = (y - x) - (ℓ : ℝ)⁻¹ • g := by simp only [z]; abel
  have hn : ‖(ℓ : ℝ)⁻¹‖ = (ℓ : ℝ)⁻¹ := Real.norm_of_nonneg (inv_nonneg.2 (NNReal.coe_nonneg ℓ))
  rw [hzy, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, hn] at h_descent
  rw [hzx, inner_sub_right, real_inner_smul_right] at h_first
  have hgg : ⟪∇ E y, g⟫ - ⟪∇ E x, g⟫ = ‖g‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have hℓ' : (0 : ℝ) < ℓ := hℓ
  have h_sq : (ℓ : ℝ) / 2 * ((ℓ : ℝ)⁻¹ * ‖g‖) ^ 2 = ‖g‖ ^ 2 / (2 * ℓ) := by
    field_simp
  have h_cross : (ℓ : ℝ)⁻¹ * ⟪∇ E y, g⟫ - (ℓ : ℝ)⁻¹ * ⟪∇ E x, g⟫ = ‖g‖ ^ 2 / ℓ := by
    rw [← mul_sub, hgg, inv_mul_eq_div]
  have h_half : ‖g‖ ^ 2 / ℓ = 2 * (‖g‖ ^ 2 / (2 * ℓ)) := by field_simp
  linarith

/-- **Baillon–Haddad.**  If `E` is convex and differentiable and `∇E` is `ℓ`-Lipschitz, then
`∇E` is `1/ℓ`-cocoercive: `‖∇E x - ∇E y‖² ≤ ℓ ⟪∇E x - ∇E y, x - y⟫`. -/
theorem ConvexOn.baillon_haddad {E : X → ℝ} {ℓ : NNReal} (hE : ConvexOn ℝ Set.univ E)
    (hd : Differentiable ℝ E) (hL : LipschitzWith ℓ (∇ E)) (x y : X) :
    ‖∇ E x - ∇ E y‖ ^ 2 ≤ ℓ * ⟪∇ E x - ∇ E y, x - y⟫ := by
  rcases eq_zero_or_pos ℓ with rfl | hℓ
  · -- A `0`-Lipschitz gradient is constant.
    have h : ∇ E x = ∇ E y := by simpa using hL.dist_le_mul x y
    simp [h]
  -- Add the sharpened first-order inequality at `(x, y)` and at `(y, x)`.
  have hxy := hE.add_inner_add_norm_sq_div_le hd hL hℓ x y
  have hyx := hE.add_inner_add_norm_sq_div_le hd hL hℓ y x
  rw [norm_sub_rev (∇ E y)] at hxy
  have hℓ' : (0 : ℝ) < ℓ := hℓ
  have h_inner : ⟪∇ E x, y - x⟫ + ⟪∇ E y, x - y⟫ = -⟪∇ E x - ∇ E y, x - y⟫ := by
    rw [inner_sub_left, ← neg_sub x y, inner_neg_right]; ring
  have h_half : ‖∇ E x - ∇ E y‖ ^ 2 / (2 * ℓ) + ‖∇ E x - ∇ E y‖ ^ 2 / (2 * ℓ)
      = ‖∇ E x - ∇ E y‖ ^ 2 / ℓ := by field_simp; ring
  have h_div : ‖∇ E x - ∇ E y‖ ^ 2 / ℓ ≤ ⟪∇ E x - ∇ E y, x - y⟫ := by linarith
  rwa [div_le_iff₀ hℓ', mul_comm] at h_div

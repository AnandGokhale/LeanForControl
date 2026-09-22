import LeanForControl.Stability.LyapunovIndirect.DefsLyapunov
import LeanForControl.Stability.LyapunovIndirect.FrechetRemainder
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
# Quadratic Lyapunov functions

This file proves the analytic properties of matrix quadratic forms needed by the
indirect Lyapunov method.

Reference: Khalil, *Nonlinear Systems*.
-/

namespace LinearSystems

open Matrix Set Metric
open scoped RealInnerProductSpace ContDiff

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The identity matrix is positive definite, including in dimension zero.

Reference: the defining property of a positive-definite matrix. -/
lemma posDef_one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simp
  · intro x hx
    simpa using (dotProduct_star_self_pos_iff.mpr hx)

/-- A matrix quadratic form is smooth.

Original: analytic infrastructure for the standard quadratic Lyapunov construction. -/
lemma matrixQuadratic_contDiff (P : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ ∞ (matrixQuadratic P) := by
  exact contDiff_id.inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) P).contDiff

/-- A positive-definite matrix has a positive quadratic form away from zero.

Reference: the defining property of a positive-definite matrix. -/
lemma matrixQuadratic_pos (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    {x : ℝⁿ} (hx : x ≠ 0) : 0 < matrixQuadratic P x := by
  rw [matrixQuadratic, Matrix.inner_toEuclideanCLM]
  apply hP.dotProduct_mulVec_pos
  simpa using hx

/-- A matrix quadratic form is homogeneous of degree two.

Original: normalization infrastructure for positive-definite quadratic forms. -/
lemma matrixQuadratic_smul (P : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (x : ℝⁿ) :
    matrixQuadratic P (a • x) = a ^ 2 * matrixQuadratic P x := by
  simp only [matrixQuadratic, map_smul, real_inner_smul_left, real_inner_smul_right,
    pow_two]
  ring

/-- The absolute value of a real matrix quadratic form is bounded by the
operator norm times the squared vector norm; no definiteness is required.

Reference: the Cauchy--Schwarz and operator-norm inequalities. -/
lemma abs_matrixQuadratic_le
    (P : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ) :
    |matrixQuadratic P x| ≤
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P‖ * ‖x‖ ^ 2 := by
  rw [matrixQuadratic]
  calc
    |inner ℝ x (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P x)| ≤
        ‖x‖ * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P x‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ *
        (‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P‖ * ‖x‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P‖ * ‖x‖ ^ 2 := by ring

/-- A matrix quadratic form is additive in its representing matrix.

Original: linearity of `Matrix.toEuclideanCLM` and the inner product. -/
lemma matrixQuadratic_matrix_add
    (P Q : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ) :
    matrixQuadratic (P + Q) x = matrixQuadratic P x + matrixQuadratic Q x := by
  rw [matrixQuadratic, matrixQuadratic, matrixQuadratic]
  rw [map_add, ContinuousLinearMap.add_apply, inner_add_right]

/-- A matrix quadratic form is homogeneous in its representing matrix.

Original: linearity of `Matrix.toEuclideanCLM` and the inner product. -/
lemma matrixQuadratic_matrix_smul
    (c : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ) :
    matrixQuadratic (c • P) x = c * matrixQuadratic P x := by
  rw [matrixQuadratic, matrixQuadratic]
  rw [map_smul, ContinuousLinearMap.smul_apply, real_inner_smul_right]

/-- In positive dimension, a positive-definite matrix quadratic form uniformly dominates
the square of the Euclidean norm.

Reference: coercivity of positive-definite quadratic forms in finite dimensions. -/
lemma exists_pos_mul_norm_sq_le_matrixQuadratic [NeZero n]
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) :
    ∃ m > 0, ∀ x : ℝⁿ, m * ‖x‖ ^ 2 ≤ matrixQuadratic P x := by
  let S : Set ℝⁿ := sphere 0 1
  have hS_compact : IsCompact S := isCompact_sphere 0 1
  have hS_nonempty : S.Nonempty := by
    let e : ℝⁿ := PiLp.single 2 (0 : Fin n) 1
    refine ⟨e, ?_⟩
    simp [S, e, PiLp.norm_single]
  obtain ⟨u, huS, hu_min⟩ := hS_compact.exists_isMinOn hS_nonempty
    (matrixQuadratic_contDiff P).continuous.continuousOn
  have hu_ne : u ≠ 0 := by
    intro hu_zero
    subst u
    simp [S] at huS
  refine ⟨matrixQuadratic P u, matrixQuadratic_pos P hP hu_ne, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, matrixQuadratic]
  · let y : ℝⁿ := ‖x‖⁻¹ • x
    have hyS : y ∈ S := by
      simp [S, y, norm_smul, hx]
    have hmin_y : matrixQuadratic P u ≤ matrixQuadratic P y := hu_min hyS
    have hxy : ‖x‖ • y = x := by
      simp [y, smul_smul, hx]
    calc
      matrixQuadratic P u * ‖x‖ ^ 2 ≤ matrixQuadratic P y * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hmin_y (sq_nonneg ‖x‖)
      _ = ‖x‖ ^ 2 * matrixQuadratic P y := mul_comm _ _
      _ = matrixQuadratic P (‖x‖ • y) := (matrixQuadratic_smul P ‖x‖ y).symm
      _ = matrixQuadratic P x := by rw [hxy]

/-- A centered matrix quadratic form is smooth.

Original: analytic infrastructure for the standard quadratic Lyapunov construction. -/
lemma centeredMatrixQuadratic_contDiff
    (P : Matrix (Fin n) (Fin n) ℝ) (x_eq : ℝⁿ) :
    ContDiff ℝ ∞ (centeredMatrixQuadratic P x_eq) := by
  apply ContDiff.inner ℝ
  · exact contDiff_id.sub contDiff_const
  · exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P).contDiff.comp
      (contDiff_id.sub contDiff_const)

/-- The Fréchet derivative of a centered matrix quadratic form, evaluated at a direction.

Reference: the product rule for the standard quadratic Lyapunov function. -/
theorem fderiv_centeredMatrixQuadratic_apply
    (P : Matrix (Fin n) (Fin n) ℝ) (x_eq x v : ℝⁿ) :
    fderiv ℝ (centeredMatrixQuadratic P x_eq) x v =
      inner ℝ (x - x_eq) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P v) +
        inner ℝ v
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P (x - x_eq)) := by
  have hy : HasFDerivAt (fun z : ℝⁿ ↦ z - x_eq) (1 : ℝⁿ →L[ℝ] ℝⁿ) x :=
    (hasFDerivAt_id x).sub_const x_eq
  have hPy := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P).hasFDerivAt.comp x hy
  have hinner := hy.inner ℝ hPy
  have happ := congrArg (fun L : ℝⁿ →L[ℝ] ℝ ↦ L v) hinner.fderiv
  unfold centeredMatrixQuadratic matrixQuadratic
  simpa [Function.comp_def] using happ

/-- The derivative of a centered, possibly indefinite matrix quadratic form
along `y' = A y` is represented by `P A + Aᵀ P`.

Reference: the product rule for quadratic forms. -/
theorem fderiv_centeredMatrixQuadratic_apply_matrix
    (A P : Matrix (Fin n) (Fin n) ℝ) (x_eq x : ℝⁿ) :
    fderiv ℝ (centeredMatrixQuadratic P x_eq) x
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (x - x_eq)) =
      matrixQuadratic (P * A + Aᵀ * P) (x - x_eq) := by
  rw [fderiv_centeredMatrixQuadratic_apply]
  let y := x - x_eq
  let a := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A
  let p := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P
  have htranspose :
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Aᵀ = star a := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial A]
    exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).map_star' A
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [← inner_add_right]
  change inner ℝ y ((p * a + star a * p) y) = _
  rw [← htranspose]
  unfold matrixQuadratic
  congr 2
  simp [p, a]

/-- The absolute derivative of a centered matrix quadratic form is controlled
by twice the operator norm of its representing matrix.

Reference: the Cauchy--Schwarz and operator-norm inequalities. -/
theorem abs_fderiv_centeredMatrixQuadratic_le
    (P : Matrix (Fin n) (Fin n) ℝ) (x_eq x v : ℝⁿ) :
    |fderiv ℝ (centeredMatrixQuadratic P x_eq) x v| ≤
      2 * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P‖ *
        ‖x - x_eq‖ * ‖v‖ := by
  rw [fderiv_centeredMatrixQuadratic_apply]
  let p := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P
  let y := x - x_eq
  calc
    |inner ℝ y (p v) + inner ℝ v (p y)| ≤
        |inner ℝ y (p v)| + |inner ℝ v (p y)| := abs_add_le _ _
    _ ≤ ‖y‖ * ‖p v‖ + ‖v‖ * ‖p y‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ ‖y‖ * (‖p‖ * ‖v‖) + ‖v‖ * (‖p‖ * ‖y‖) := by
      gcongr <;> exact ContinuousLinearMap.le_opNorm _ _
    _ = 2 * ‖p‖ * ‖y‖ * ‖v‖ := by ring

/-- Near an equilibrium, the derivative of a centered matrix quadratic form applied to the
first-order remainder of `f` is dominated by any prescribed positive multiple of the
squared distance to the equilibrium.

This is the shared "remainder absorption" step of both branches of Lyapunov's indirect
method: the stable branch (`exists_centeredMatrixQuadratic_decay`) uses it to bound the
error term against the certificate's own decay rate, and the unstable branch
(`forwardUnstable_of_quadratic_certificate`) uses it to bound the error term against the
shifted certificate's growth rate.

Reference: adapted from the quadratic-Lyapunov proof of Lyapunov's indirect method;
Khalil, *Nonlinear Systems*. -/
theorem exists_abs_fderiv_centeredMatrixQuadratic_remainder_le
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (A M : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    {c : ℝ} (hc : 0 < c) :
    ∃ r > 0, ∀ x : ℝⁿ, ‖x - x_eq‖ < r →
      |fderiv ℝ (centeredMatrixQuadratic M x_eq) x
          (f x - f x_eq - Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (x - x_eq))| ≤
        c * ‖x - x_eq‖ ^ 2 := by
  let p : ℝⁿ →L[ℝ] ℝⁿ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M
  let η : ℝ := c / (4 * (‖p‖ + 1))
  have hp_nonneg : 0 ≤ ‖p‖ := norm_nonneg p
  have hp_one_pos : 0 < ‖p‖ + 1 := by positivity
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hderiv : HasFDerivAt f
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) x_eq := by
    simpa only [hJac] using (hf.differentiable (by norm_num) x_eq).hasFDerivAt
  obtain ⟨r, hr, hrem⟩ := hderiv.exists_centered_remainder_bound hη_pos
  refine ⟨r, hr, ?_⟩
  intro x hx
  let y : ℝⁿ := x - x_eq
  let e : ℝⁿ := f x - f x_eq - Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A y
  have he_norm : ‖e‖ ≤ η * ‖y‖ := hrem x (by simpa [y] using hx)
  have herror_abs :
      |fderiv ℝ (centeredMatrixQuadratic M x_eq) x e| ≤ 2 * ‖p‖ * ‖y‖ * ‖e‖ := by
    simpa [p, y] using abs_fderiv_centeredMatrixQuadratic_le M x_eq x e
  have hcoef : 2 * ‖p‖ * η ≤ c := by
    dsimp [η]
    rw [show 2 * ‖p‖ * (c / (4 * (‖p‖ + 1))) =
      (2 * ‖p‖ * c) / (4 * (‖p‖ + 1)) by ring]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc
    |fderiv ℝ (centeredMatrixQuadratic M x_eq) x e| ≤ 2 * ‖p‖ * ‖y‖ * ‖e‖ := herror_abs
    _ ≤ 2 * ‖p‖ * ‖y‖ * (η * ‖y‖) := by
      exact mul_le_mul_of_nonneg_left he_norm
        (mul_nonneg (mul_nonneg (by norm_num) hp_nonneg) (norm_nonneg y))
    _ = (2 * ‖p‖ * η) * ‖y‖ ^ 2 := by ring
    _ ≤ c * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖y‖)

/-- A solution of the Lyapunov equation makes the derivative of the `P`-quadratic form
along the linear vector field equal to minus the `Q`-quadratic form.

Reference: the continuous-time Lyapunov-equation identity. -/
theorem fderiv_centeredMatrixQuadratic_linear_general
    {A P Q : Matrix (Fin n) (Fin n) ℝ}
    (hEq : SolvesContinuousLyapunovEquation A P Q)
    (x_eq x : ℝⁿ) :
    fderiv ℝ (centeredMatrixQuadratic P x_eq) x
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (x - x_eq)) =
      -matrixQuadratic Q (x - x_eq) := by
  rw [fderiv_centeredMatrixQuadratic_apply]
  let y := x - x_eq
  let a := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A
  let p := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P
  let q := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q
  have htranspose :
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Aᵀ = star a := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial A]
    exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).map_star' A
  have hclm : p * a + star a * p = -q := by
    have hEq' : P * A + Aᵀ * P = -Q := hEq
    have h := congrArg (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) hEq'
    have h' :
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P *
              Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A +
            Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Aᵀ *
              Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P =
            -Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q := by
      simpa using h
    change p * a + Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Aᵀ * p = -q at h'
    rwa [htranspose] at h'
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [← inner_add_right]
  change inner ℝ y ((p * a + star a * p) y) = -matrixQuadratic Q y
  rw [hclm]
  simp [matrixQuadratic, q]

/-- For identity forcing, the quadratic derivative along the linear vector field is
`-‖x - x_eq‖²`.

Reference: the continuous-time Lyapunov-equation identity. -/
theorem fderiv_centeredMatrixQuadratic_linear
    {A P : Matrix (Fin n) (Fin n) ℝ}
    (hEq : SolvesContinuousLyapunovEquation A P 1)
    (x_eq x : ℝⁿ) :
    fderiv ℝ (centeredMatrixQuadratic P x_eq) x
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (x - x_eq)) =
      -‖x - x_eq‖ ^ 2 := by
  rw [fderiv_centeredMatrixQuadratic_linear_general hEq]
  simp [matrixQuadratic]

/-- A matrix quadratic form is bounded above by the operator norm of its representing
continuous linear map times the squared Euclidean norm.

Reference: the Cauchy--Schwarz and operator-norm bounds. -/
lemma matrixQuadratic_le_opNorm_mul_norm_sq
    (P : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ) :
    matrixQuadratic P x ≤
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P‖ * ‖x‖ ^ 2 :=
  (le_abs_self _).trans (abs_matrixQuadratic_le P x)

/-- The derivative of a centered matrix quadratic form is bounded by the product of
the state norm, direction norm, and twice the matrix operator norm.

Reference: the Cauchy--Schwarz and operator-norm bounds. -/
theorem fderiv_centeredMatrixQuadratic_le
    (P : Matrix (Fin n) (Fin n) ℝ) (x_eq x v : ℝⁿ) :
    fderiv ℝ (centeredMatrixQuadratic P x_eq) x v ≤
      2 * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P‖ *
        ‖x - x_eq‖ * ‖v‖ :=
  (le_abs_self _).trans (abs_fderiv_centeredMatrixQuadratic_le P x_eq x v)

/-- In positive dimension, every sublevel set of a centered positive-definite matrix
quadratic form is compact.

Reference: coercivity of positive-definite quadratic forms in finite dimensions. -/
lemma isCompact_centeredMatrixQuadratic_sublevel [NeZero n]
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) (x_eq : ℝⁿ) (c : ℝ) :
    IsCompact {x : ℝⁿ | centeredMatrixQuadratic P x_eq x ≤ c} := by
  obtain ⟨m, hm, hm_lower⟩ := exists_pos_mul_norm_sq_le_matrixQuadratic P hP
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_Iic.preimage (centeredMatrixQuadratic_contDiff P x_eq).continuous
  · rw [Metric.isBounded_iff_subset_closedBall x_eq]
    refine ⟨|c| / m + 1, ?_⟩
    intro x hx
    have hmc : m * ‖x - x_eq‖ ^ 2 ≤ |c| :=
      (hm_lower (x - x_eq)).trans (hx.trans (le_abs_self c))
    have hsq : ‖x - x_eq‖ ^ 2 ≤ |c| / m :=
      (le_div_iff₀ hm).2 (by simpa [mul_comm] using hmc)
    have hnorm : ‖x - x_eq‖ ≤ |c| / m + 1 := by
      nlinarith [sq_nonneg (‖x - x_eq‖ - 1)]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm

end LinearSystems

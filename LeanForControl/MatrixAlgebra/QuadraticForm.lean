import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.Order.Compact
import Architect

/-!
# Quadratic forms represented by a matrix

This file defines the real quadratic form `x ↦ xᵀPx` on Euclidean space and its analytic
properties (smoothness, Cauchy--Schwarz-style bounds, and the derivative of its centered
version). It has no system semantics: `P` is an arbitrary real square matrix, not
necessarily a state matrix, and none of these facts assume or need `P` to solve a Lyapunov
equation.

Positive-definiteness-dependent facts (`quadraticForm_pos`,
`exists_pos_mul_norm_sq_le_quadraticForm`) and the matrix-linearity facts
(`quadraticForm_matrix_add`, `quadraticForm_matrix_smul`) are bridged to Mathlib's
`Matrix.toQuadraticMap'`/`QuadraticMap` API via `quadraticForm_eq_toQuadraticMap'` rather
than reproved from scratch.

Reference: standard quadratic Lyapunov-function construction; Khalil, *Nonlinear Systems*.
-/

namespace MatrixAlgebra

open Matrix Set Metric
open scoped RealInnerProductSpace ContDiff

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The real quadratic form `x ↦ xᵀ P x` represented on Euclidean space.

Reference: standard quadratic Lyapunov-function construction. -/
@[blueprint "def:quadraticForm"
  (statement := /-- A real matrix $P$ represents the quadratic form
    $x \mapsto x^{\mathsf T}Px$ on Euclidean state space. -/)]
noncomputable def quadraticForm
    (P : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ) : ℝ :=
  inner ℝ x (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P x)

/-- The quadratic form associated to `P`, centered at an equilibrium `x_eq`.

Reference: standard quadratic Lyapunov-function construction. -/
noncomputable def centeredQuadraticForm
    (P : Matrix (Fin n) (Fin n) ℝ) (x_eq x : ℝⁿ) : ℝ :=
  quadraticForm P (x - x_eq)

/-- A matrix quadratic form is smooth.

Original: analytic infrastructure for the standard quadratic Lyapunov construction. -/
lemma quadraticForm_contDiff (P : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ ∞ (quadraticForm P) := by
  exact contDiff_id.inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) P).contDiff

/-- A matrix quadratic form is the same real number as Mathlib's `Matrix.toQuadraticMap'`,
evaluated on the underlying `Fin n → ℝ` data. This is the bridge that lets the
matrix-linearity and positive-definiteness lemmas below cite Mathlib's `QuadraticMap` API
instead of reproving it.

Reference: `Matrix.toQuadraticMap'` and `LinearMap.BilinMap.toQuadraticMap`. -/
lemma quadraticForm_eq_toQuadraticMap' (P : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ) :
    quadraticForm P x = P.toQuadraticMap' (WithLp.ofLp x) := by
  rw [quadraticForm, Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']
  simp only [Matrix.ofLp_toEuclideanCLM, PiLp.inner_apply, dotProduct]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- A positive-definite matrix has a positive quadratic form away from zero.

Reference: the defining property of a positive-definite matrix. -/
lemma quadraticForm_pos (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    {x : ℝⁿ} (hx : x ≠ 0) : 0 < quadraticForm P x := by
  rw [quadraticForm_eq_toQuadraticMap']
  exact hP.toQuadraticForm' _ (by simpa using hx)

/-- A matrix quadratic form is homogeneous of degree two.

Original: normalization infrastructure for positive-definite quadratic forms. -/
lemma quadraticForm_smul (P : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (x : ℝⁿ) :
    quadraticForm P (a • x) = a ^ 2 * quadraticForm P x := by
  simp only [quadraticForm, map_smul, real_inner_smul_left, real_inner_smul_right,
    pow_two]
  ring

/-- The absolute value of a real matrix quadratic form is bounded by the
operator norm times the squared vector norm; no definiteness is required.

Reference: the Cauchy--Schwarz and operator-norm inequalities. -/
lemma abs_quadraticForm_le
    (P : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ) :
    |quadraticForm P x| ≤
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P‖ * ‖x‖ ^ 2 := by
  rw [quadraticForm]
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

Reference: linearity of `Matrix.toQuadraticMap'` (via `Matrix.toLinearMap₂'`). -/
lemma quadraticForm_matrix_add
    (P Q : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ) :
    quadraticForm (P + Q) x = quadraticForm P x + quadraticForm Q x := by
  simp only [quadraticForm_eq_toQuadraticMap', Matrix.toQuadraticMap', map_add]
  rfl

/-- A matrix quadratic form is homogeneous in its representing matrix.

Reference: linearity of `Matrix.toQuadraticMap'` (via `Matrix.toLinearMap₂'`). -/
lemma quadraticForm_matrix_smul
    (c : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ) :
    quadraticForm (c • P) x = c * quadraticForm P x := by
  simp only [quadraticForm_eq_toQuadraticMap', Matrix.toQuadraticMap', map_smul]
  rfl

/-- In positive dimension, a positive-definite matrix quadratic form uniformly dominates
the square of the Euclidean norm.

Reference: coercivity of positive-definite quadratic forms in finite dimensions. -/
lemma exists_pos_mul_norm_sq_le_quadraticForm [NeZero n]
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) :
    ∃ m > 0, ∀ x : ℝⁿ, m * ‖x‖ ^ 2 ≤ quadraticForm P x := by
  let S : Set ℝⁿ := sphere 0 1
  have hS_compact : IsCompact S := isCompact_sphere 0 1
  have hS_nonempty : S.Nonempty := by
    let e : ℝⁿ := PiLp.single 2 (0 : Fin n) 1
    refine ⟨e, ?_⟩
    simp [S, e, PiLp.norm_single]
  obtain ⟨u, huS, hu_min⟩ := hS_compact.exists_isMinOn hS_nonempty
    (quadraticForm_contDiff P).continuous.continuousOn
  have hu_ne : u ≠ 0 := by
    intro hu_zero
    subst u
    simp [S] at huS
  refine ⟨quadraticForm P u, quadraticForm_pos P hP hu_ne, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, quadraticForm]
  · let y : ℝⁿ := ‖x‖⁻¹ • x
    have hyS : y ∈ S := by
      simp [S, y, norm_smul, hx]
    have hmin_y : quadraticForm P u ≤ quadraticForm P y := hu_min hyS
    have hxy : ‖x‖ • y = x := by
      simp [y, smul_smul, hx]
    calc
      quadraticForm P u * ‖x‖ ^ 2 ≤ quadraticForm P y * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hmin_y (sq_nonneg ‖x‖)
      _ = ‖x‖ ^ 2 * quadraticForm P y := mul_comm _ _
      _ = quadraticForm P (‖x‖ • y) := (quadraticForm_smul P ‖x‖ y).symm
      _ = quadraticForm P x := by rw [hxy]

/-- A centered matrix quadratic form is smooth.

Original: analytic infrastructure for the standard quadratic Lyapunov construction. -/
lemma centeredQuadraticForm_contDiff
    (P : Matrix (Fin n) (Fin n) ℝ) (x_eq : ℝⁿ) :
    ContDiff ℝ ∞ (centeredQuadraticForm P x_eq) := by
  apply ContDiff.inner ℝ
  · exact contDiff_id.sub contDiff_const
  · exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P).contDiff.comp
      (contDiff_id.sub contDiff_const)

/-- The Fréchet derivative of a centered matrix quadratic form, evaluated at a direction.

Reference: the product rule for the standard quadratic Lyapunov function. -/
theorem fderiv_centeredQuadraticForm_apply
    (P : Matrix (Fin n) (Fin n) ℝ) (x_eq x v : ℝⁿ) :
    fderiv ℝ (centeredQuadraticForm P x_eq) x v =
      inner ℝ (x - x_eq) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P v) +
        inner ℝ v
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P (x - x_eq)) := by
  have hy : HasFDerivAt (fun z : ℝⁿ ↦ z - x_eq) (1 : ℝⁿ →L[ℝ] ℝⁿ) x :=
    (hasFDerivAt_id x).sub_const x_eq
  have hPy := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P).hasFDerivAt.comp x hy
  have hinner := hy.inner ℝ hPy
  have happ := congrArg (fun L : ℝⁿ →L[ℝ] ℝ ↦ L v) hinner.fderiv
  unfold centeredQuadraticForm quadraticForm
  simpa [Function.comp_def] using happ

/-- The derivative of a centered, possibly indefinite matrix quadratic form
along `y' = A y` is represented by `P A + Aᵀ P`.

Reference: the product rule for quadratic forms. -/
theorem fderiv_centeredQuadraticForm_apply_matrix
    (A P : Matrix (Fin n) (Fin n) ℝ) (x_eq x : ℝⁿ) :
    fderiv ℝ (centeredQuadraticForm P x_eq) x
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (x - x_eq)) =
      quadraticForm (P * A + Aᵀ * P) (x - x_eq) := by
  rw [fderiv_centeredQuadraticForm_apply]
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
  unfold quadraticForm
  congr 2
  simp [p, a]

/-- The absolute derivative of a centered matrix quadratic form is controlled
by twice the operator norm of its representing matrix.

Reference: the Cauchy--Schwarz and operator-norm inequalities. -/
theorem abs_fderiv_centeredQuadraticForm_le
    (P : Matrix (Fin n) (Fin n) ℝ) (x_eq x v : ℝⁿ) :
    |fderiv ℝ (centeredQuadraticForm P x_eq) x v| ≤
      2 * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P‖ *
        ‖x - x_eq‖ * ‖v‖ := by
  rw [fderiv_centeredQuadraticForm_apply]
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

/-- A matrix quadratic form is bounded above by the operator norm of its representing
continuous linear map times the squared Euclidean norm.

Reference: the Cauchy--Schwarz and operator-norm bounds. -/
lemma quadraticForm_le_opNorm_mul_norm_sq
    (P : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ) :
    quadraticForm P x ≤
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P‖ * ‖x‖ ^ 2 :=
  (le_abs_self _).trans (abs_quadraticForm_le P x)

end MatrixAlgebra

import LeanForControl.Stability.LyapunovIndirect.DefsLyapunov
import LeanForControl.MatrixAlgebra.QuadraticForm
import LeanForControl.Analysis.FrechetRemainder
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Quadratic forms and the continuous-time Lyapunov equation

This file connects `MatrixAlgebra.QuadraticForm`'s generic quadratic-form machinery to
`SolvesContinuousLyapunovEquation`: the derivative identity that makes a Lyapunov-equation
solution's quadratic form decrease along a linear vector field, and the shared
remainder-absorption step used by both branches of Lyapunov's indirect method.

Reference: Khalil, *Nonlinear Systems*.
-/

namespace LinearSystems

open Matrix MatrixAlgebra
open scoped RealInnerProductSpace

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Near an equilibrium, the derivative of a centered matrix quadratic form applied to the
first-order remainder of `f` is dominated by any prescribed positive multiple of the
squared distance to the equilibrium.

This is the shared "remainder absorption" step of both branches of Lyapunov's indirect
method: the stable branch (`exists_centeredQuadraticForm_decay`) uses it to bound the
error term against the certificate's own decay rate, and the unstable branch
(`forwardUnstable_of_quadratic_certificate`) uses it to bound the error term against the
shifted certificate's growth rate.

Reference: adapted from the quadratic-Lyapunov proof of Lyapunov's indirect method;
Khalil, *Nonlinear Systems*. -/
theorem exists_abs_fderiv_centeredQuadraticForm_remainder_le
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (A M : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    {c : ℝ} (hc : 0 < c) :
    ∃ r > 0, ∀ x : ℝⁿ, ‖x - x_eq‖ < r →
      |fderiv ℝ (centeredQuadraticForm M x_eq) x
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
      |fderiv ℝ (centeredQuadraticForm M x_eq) x e| ≤ 2 * ‖p‖ * ‖y‖ * ‖e‖ := by
    simpa [p, y] using abs_fderiv_centeredQuadraticForm_le M x_eq x e
  have hcoef : 2 * ‖p‖ * η ≤ c := by
    dsimp [η]
    rw [show 2 * ‖p‖ * (c / (4 * (‖p‖ + 1))) =
      (2 * ‖p‖ * c) / (4 * (‖p‖ + 1)) by ring]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc
    |fderiv ℝ (centeredQuadraticForm M x_eq) x e| ≤ 2 * ‖p‖ * ‖y‖ * ‖e‖ := herror_abs
    _ ≤ 2 * ‖p‖ * ‖y‖ * (η * ‖y‖) := by
      exact mul_le_mul_of_nonneg_left he_norm
        (mul_nonneg (mul_nonneg (by norm_num) hp_nonneg) (norm_nonneg y))
    _ = (2 * ‖p‖ * η) * ‖y‖ ^ 2 := by ring
    _ ≤ c * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖y‖)

/-- A solution of the Lyapunov equation makes the derivative of the `P`-quadratic form
along the linear vector field equal to minus the `Q`-quadratic form.

Reference: the continuous-time Lyapunov-equation identity. -/
theorem fderiv_centeredQuadraticForm_linear_general
    {A P Q : Matrix (Fin n) (Fin n) ℝ}
    (hEq : SolvesContinuousLyapunovEquation A P Q)
    (x_eq x : ℝⁿ) :
    fderiv ℝ (centeredQuadraticForm P x_eq) x
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (x - x_eq)) =
      -quadraticForm Q (x - x_eq) := by
  rw [fderiv_centeredQuadraticForm_apply]
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
  change inner ℝ y ((p * a + star a * p) y) = -quadraticForm Q y
  rw [hclm]
  simp [quadraticForm, q]

/-- For identity forcing, the quadratic derivative along the linear vector field is
`-‖x - x_eq‖²`.

Reference: the continuous-time Lyapunov-equation identity. -/
theorem fderiv_centeredQuadraticForm_linear
    {A P : Matrix (Fin n) (Fin n) ℝ}
    (hEq : SolvesContinuousLyapunovEquation A P 1)
    (x_eq x : ℝⁿ) :
    fderiv ℝ (centeredQuadraticForm P x_eq) x
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (x - x_eq)) =
      -‖x - x_eq‖ ^ 2 := by
  rw [fderiv_centeredQuadraticForm_linear_general hEq]
  simp [quadraticForm]

end LinearSystems

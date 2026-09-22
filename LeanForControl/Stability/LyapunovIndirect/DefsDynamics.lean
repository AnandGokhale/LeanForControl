import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Linear-system vector fields

This file defines autonomous vector fields induced by finite-dimensional state
matrices on the repository's Euclidean state-space convention.

Reference: Khalil, *Nonlinear Systems*.
-/

namespace LinearSystems

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The affine-linear vector field with equilibrium `x_eq` and state matrix `A`.

Original: a typed bridge from `Matrix.toEuclideanCLM` to the repository's
`EuclideanSpace` state convention.
-/
noncomputable def affineLinearVectorField
    (A : Matrix (Fin n) (Fin n) ℝ) (x_eq : ℝⁿ) : ℝⁿ → ℝⁿ :=
  fun x => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (x - x_eq)

end LinearSystems

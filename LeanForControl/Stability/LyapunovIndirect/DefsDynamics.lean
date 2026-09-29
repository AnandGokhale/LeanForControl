import Mathlib.Analysis.CStarAlgebra.Matrix
import Architect

/-!
# Linear-system vector fields

This file defines autonomous vector fields induced by finite-dimensional state
matrices on the repository's Euclidean state-space convention.

Reference: Khalil, *Nonlinear Systems*.
-/

namespace LinearSystems

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The affine-linear vector field `x ↦ A (x - x_eq)`, whose equilibrium is `x_eq`.

A typed bridge from `Matrix.toEuclideanCLM` to the repository's `EuclideanSpace` state
convention: the linearization of a nonlinear field about `x_eq` is of this shape, which is what
lets the indirect method transfer a spectral condition on `A` to the nonlinear system. -/
@[blueprint "def:affineLinearVectorField"
  (title := "Affine-linear vector field")
  (statement := /-- For a matrix $A \in \mathbb{R}^{n \times n}$ and a point
    $x_{\mathrm{eq}} \in \mathbb{R}^{n}$, the \emph{affine-linear vector field} is
    \[
      f(x) = A\,(x - x_{\mathrm{eq}}),
    \]
    for which $x_{\mathrm{eq}}$ is an equilibrium. -/)]
noncomputable def affineLinearVectorField
    (A : Matrix (Fin n) (Fin n) ℝ) (x_eq : ℝⁿ) : ℝⁿ → ℝⁿ :=
  fun x => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (x - x_eq)

end LinearSystems

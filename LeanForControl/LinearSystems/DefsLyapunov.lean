import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Architect

/-!
# Definitions for matrix Lyapunov functions

This file defines the continuous-time Lyapunov equation and the real quadratic forms
used as Lyapunov certificates for finite-dimensional linear systems.

Reference: Khalil, *Nonlinear Systems*.
-/

namespace LinearSystems

open Matrix
open scoped RealInnerProductSpace

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- `P` solves the continuous-time Lyapunov equation for `A` and `Q` when
`P A + Aᵀ P = -Q`.

Reference: Khalil, *Nonlinear Systems*. -/
@[blueprint "def:solvesContinuousLyapunovEquation"
  (statement := /-- For real square matrices $A$, $P$, and $Q$, the matrix $P$
    solves the continuous-time Lyapunov equation with forcing $Q$ when
    \[
      PA+A^{\mathsf T}P=-Q.
    \] -/)]
def SolvesContinuousLyapunovEquation
    (A P Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P * A + Aᵀ * P = -Q

/-- The real quadratic form `x ↦ xᵀ P x` represented on Euclidean space.

Reference: standard quadratic Lyapunov-function construction. -/
@[blueprint "def:matrixQuadratic"
  (statement := /-- A real matrix $P$ represents the quadratic form
    $x \mapsto x^{\mathsf T}Px$ on Euclidean state space. -/)]
noncomputable def matrixQuadratic
    (P : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ) : ℝ :=
  inner ℝ x (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P x)

/-- The quadratic form associated to `P`, centered at an equilibrium `x_eq`.

Reference: standard quadratic Lyapunov-function construction. -/
noncomputable def centeredMatrixQuadratic
    (P : Matrix (Fin n) (Fin n) ℝ) (x_eq x : ℝⁿ) : ℝ :=
  matrixQuadratic P (x - x_eq)

end LinearSystems

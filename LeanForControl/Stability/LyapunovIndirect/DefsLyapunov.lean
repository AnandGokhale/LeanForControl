import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Architect

/-!
# Definitions for matrix Lyapunov functions

This file defines the continuous-time Lyapunov equation. See
`MatrixAlgebra.QuadraticForm` for the quadratic forms used as Lyapunov certificates —
they have no system semantics and live there instead.

Reference: Khalil, *Nonlinear Systems*.
-/

namespace LinearSystems

open Matrix

variable {n : ℕ}

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

end LinearSystems

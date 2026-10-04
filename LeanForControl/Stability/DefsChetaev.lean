import LeanForControl.Stability.DefsAutonomous
import Architect

/-!
# Geometric Chetaev certificates

The certificate is local to a closed ball.  Its positive region is an open set whose frontier
contains the base point; the certificate vanishes on the part of that frontier inside the ball,
and its Lie derivative is strictly positive in the region.

Reference: Hahn, *Stability of Motion*; Khalil, *Nonlinear Systems*.
-/

open Metric Set

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A bounded boundary-form Chetaev certificate for an autonomous vector field.

Global `C¹` regularity of `V` supports the chain rule and compactness argument.  The sign and
boundary conditions are required only in the closed ball of radius `rho`.  No equilibrium field
equation at `x_eq` is included: the resulting theorem concludes `Unstable`, the negation of the
repository's finite-forward Lyapunov-stability predicate, for this base point.

Reference: Hahn, *Stability of Motion*; Khalil, *Nonlinear Systems*. -/
@[blueprint "def:isChetaevFunction"
  (title := "Boundary-form Chetaev function")
  (statement := /-- A bounded boundary-form Chetaev certificate consists of an open region
    $D$, a base point $x_{\rm eq}\in\partial D$, a radius $\rho>0$, and a globally $C^1$
    function $V$. Inside $D$ and the closed $\rho$-ball, $V$ is positive and has strictly
    positive Lie derivative along the vector field; $V$ vanishes on the part of
    $\partial D$ inside that ball.

    Reference: Hahn, \emph{Stability of Motion}; Khalil, \emph{Nonlinear Systems}. -/)]
structure IsChetaevFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ)
    (x_eq : ℝⁿ) (D : Set ℝⁿ) (rho : ℝ) : Prop where
  hradius : 0 < rho
  hD_open : IsOpen D
  hfrontier : x_eq ∈ frontier D
  hV_c1 : ContDiff ℝ 1 V
  hpos : ∀ x ∈ D, ‖x - x_eq‖ ≤ rho → 0 < V x
  hboundary_zero : ∀ x ∈ frontier D, ‖x - x_eq‖ ≤ rho → V x = 0
  hLie_pos : ∀ x ∈ D, ‖x - x_eq‖ ≤ rho →
    0 < fderiv ℝ V x (f x)

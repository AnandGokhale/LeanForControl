import LeanForControl.Stability.DefsAutonomous
import Architect

/-!
# Geometric Chetaev certificates

The certificate is local to a closed ball. Its positive region is an open set whose topological
boundary contains the base point; the certificate vanishes on that boundary inside the ball,
and its Lie derivative is strictly positive in the region.
Mathlib calls the topological boundary `frontier`; throughout this file it means
`closure D \ interior D`, written $\partial D$ in control theory.

Reference: Khalil, *Nonlinear Systems*, 3rd ed. (Prentice Hall, 2002), Theorem 4.3,
p. 125 (Chetaev's instability theorem).  This is a boundary formulation of its escape
argument, not a literal transcription; "geometric" and "boundary-form" are descriptive
qualifiers for this formalization.
-/

open Metric Set

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A Chetaev certificate on a fixed closed ball for an autonomous vector field.

Global `C¹` regularity of `V` supports the chain rule and compactness argument.  The sign and
boundary conditions are required only in the closed ball of radius `rho`.  No equilibrium field
equation at `x_eq` is included: the resulting theorem concludes `Unstable`, the negation of the
repository's finite-forward Lyapunov-stability predicate, for this base point.

Reference: Khalil, *Nonlinear Systems*, 3rd ed. (Prentice Hall, 2002), Theorem 4.3,
p. 125.  Khalil uses the full positive set of `V` in a ball inside its differentiability
domain.  Here `D` is an independently supplied open positive region; no condition on other
positive components of `V` is imposed. Boundary vanishing and membership in the boundary
give `V x_eq = 0` and positive seeds near `x_eq`.  Neither `D` nor `V` is assumed globally
bounded, and `D` is not the differentiability domain from the textbook. -/
@[blueprint "def:isChetaevFunction"
  (title := "Boundary-form Chetaev function")
  (statement := /-- A Chetaev certificate on a fixed closed ball consists of an open region
    $D$, a base point $x_{\rm eq}\in\partial D$, a radius $\rho>0$, and a globally $C^1$
    function $V$. Inside $D$ and the closed $\rho$-ball, $V$ is positive and has strictly
    positive Lie derivative along the vector field; $V$ vanishes on the part of
    $\partial D$ inside that ball. Neither $D$ nor $V$ is assumed globally bounded,
    and no equation $f(x_{\rm eq})=0$ is required.

    Reference: Khalil, \emph{Nonlinear Systems}, 3rd ed. (Prentice Hall, 2002),
    Theorem 4.3, p. 125. This boundary formulation uses an independently supplied open
    positive region, rather than the full positive set in the textbook's ball;
    $D$ is not the textbook's differentiability domain. -/)]
structure IsChetaevFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ)
    (x_eq : ℝⁿ) (D : Set ℝⁿ) (rho : ℝ) : Prop where
  /-- The certificate ball has strictly positive radius. -/
  hradius : 0 < rho
  /-- The region on which certificate positivity is required is open. -/
  hD_open : IsOpen D
  /-- The base point belongs to the topological boundary `∂D`.
  Mathlib represents this boundary as `frontier D = closure D \ interior D`. -/
  hmem_boundary : x_eq ∈ frontier D
  /-- The certificate function is continuously differentiable on the entire state space. -/
  hV_c1 : ContDiff ℝ 1 V
  /-- The certificate is strictly positive in `D` within the closed certificate ball. -/
  hpos : ∀ x ∈ D, ‖x - x_eq‖ ≤ rho → 0 < V x
  /-- The certificate vanishes on `∂D` within the closed certificate ball.
  This is the boundary of `D`, not the whole sphere bounding the certificate ball. -/
  hboundary_zero : ∀ x ∈ frontier D, ‖x - x_eq‖ ≤ rho → V x = 0
  /-- The Lie derivative `DV(x) f(x)` is strictly positive in `D` within the closed ball. -/
  hLie_pos : ∀ x ∈ D, ‖x - x_eq‖ ≤ rho →
    0 < fderiv ℝ V x (f x)

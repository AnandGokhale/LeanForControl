import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Architect

/-!
# Finite forward solution segments

This file supplies stability predicates phrased in terms of every finite forward
solution segment.  Unlike `IsTrajectory`, these predicates do not silently discard
solutions that cease to exist after a finite escape time.

A finite forward solution segment is Mathlib's `IsIntegralCurveOn φ (fun _ x => f x) (Icc 0 T)`,
used directly rather than through a wrapper: `Icc 0 T` is empty for `T < 0`, so no separate
`0 ≤ T` hypothesis is needed to keep these predicates meaningful.

Reference: Khalil, *Nonlinear Systems*.
-/

open Set Filter Topology

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Forward Lyapunov stability, quantified over all finite forward solution segments.

Reference: Khalil, *Nonlinear Systems*.
-/
@[blueprint "def:forwardLyapunovStable"
  (statement := /-- An equilibrium is forward Lyapunov stable when every finite
    forward solution segment starting sufficiently close remains within any
    prescribed neighborhood for its entire interval of definition. -/)]
def ForwardLyapunovStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (T : ℝ) (φ : ℝ → ℝⁿ),
    IsIntegralCurveOn φ (fun _ x => f x) (Icc 0 T) → ‖φ 0 - x_eq‖ < δ →
      ∀ t ∈ Icc (0 : ℝ) T, ‖φ t - x_eq‖ < ε

/-- Local exponential stability on every finite forward solution segment.

The radius `r` selects the local basin; `C ≥ 1` is the overshoot constant and
`a > 0` is the exponential decay rate.

Reference: Khalil, *Nonlinear Systems*.
-/
@[blueprint "def:forwardLocallyExponentiallyStable"
  (statement := /-- An equilibrium is locally exponentially stable on finite
    forward segments when nearby solutions satisfy a uniform estimate
    $\|x(t)-x_{\rm eq}\|\leq C e^{-at}\|x(0)-x_{\rm eq}\|$. -/)]
def ForwardLocallyExponentiallyStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∃ r C a : ℝ, 0 < r ∧ 1 ≤ C ∧ 0 < a ∧
    ∀ (T : ℝ) (φ : ℝ → ℝⁿ), IsIntegralCurveOn φ (fun _ x => f x) (Icc 0 T) →
      ‖φ 0 - x_eq‖ < r → ∀ t ∈ Icc (0 : ℝ) T,
        ‖φ t - x_eq‖ ≤ C * Real.exp (-a * t) * ‖φ 0 - x_eq‖

/-- Forward instability is the negation of forward Lyapunov stability.

Reference: Khalil, *Nonlinear Systems*.
-/
@[blueprint "def:forwardUnstable"
  (statement := /-- Forward instability is the negation of stability quantified
    over all finite forward solution segments. -/)]
def ForwardUnstable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ¬ ForwardLyapunovStable f x_eq

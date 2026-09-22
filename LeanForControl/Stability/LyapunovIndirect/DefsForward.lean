import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Architect

/-!
# Finite forward solution segments

This file supplies stability predicates phrased in terms of every finite forward
solution segment.  Unlike `IsTrajectory`, these predicates do not silently discard
solutions that cease to exist after a finite escape time.

Reference: Khalil, *Nonlinear Systems*.
-/

open Set Filter Topology

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- `φ` solves `x' = f x` on the finite forward interval `[0, T]`.

Reference: Khalil, *Nonlinear Systems*.
-/
@[blueprint "def:isForwardTrajectoryOn"
  (statement := /-- A finite forward trajectory for $\dot x=f(x)$ on $[0,T]$
    is an integral curve on that interval, with $T\geq 0$. -/)]
def IsForwardTrajectoryOn (φ : ℝ → ℝⁿ) (f : ℝⁿ → ℝⁿ) (T : ℝ) : Prop :=
  0 ≤ T ∧ IsIntegralCurveOn φ (fun _ x => f x) (Icc 0 T)

/-- Forward Lyapunov stability, quantified over all finite forward solution segments.

Reference: Khalil, *Nonlinear Systems*.
-/
@[blueprint "def:forwardLyapunovStable"
  (statement := /-- An equilibrium is forward Lyapunov stable when every finite
    forward solution segment starting sufficiently close remains within any
    prescribed neighborhood for its entire interval of definition. -/)]
def ForwardLyapunovStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (T : ℝ) (φ : ℝ → ℝⁿ),
    IsForwardTrajectoryOn φ f T → ‖φ 0 - x_eq‖ < δ →
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
    ∀ (T : ℝ) (φ : ℝ → ℝⁿ), IsForwardTrajectoryOn φ f T →
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

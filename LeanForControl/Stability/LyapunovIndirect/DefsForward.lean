import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import LeanForControl.Stability.DefsAutonomous
import Architect

/-!
# Finite forward solution segments

This file supplies stability predicates phrased in terms of every finite forward
solution segment.  Unlike `IsTrajectory`, these predicates do not silently discard
solutions that cease to exist after a finite escape time.

A finite forward solution segment is Mathlib's
`IsTrajectoryOn φ f t₀ t₁`, used directly rather than through a
wrapper. No `t₀ ≤ t₁` hypothesis is needed: `Icc t₀ t₁` is empty when `t₁ < t₀`, so degenerate
segments are vacuous, and where a proof needs `t₀ ≤ t₁` it follows from the `t ∈ Icc t₀ t₁`
already in hand.

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
  ∀ ε > 0, ∃ δ > 0, ∀ (t₀ t₁ : ℝ) (φ : ℝ → ℝⁿ),
    IsTrajectoryOn φ f t₀ t₁ → ‖φ t₀ - x_eq‖ < δ →
      ∀ t ∈ Icc t₀ t₁, ‖φ t - x_eq‖ < ε

/-- Local exponential stability on every finite forward solution segment.

The radius `r` selects the local basin; `C ≥ 1` is the overshoot constant and
`a > 0` is the exponential decay rate. Decay is measured from `t₀`, not from the
time origin.

Reference: Khalil, *Nonlinear Systems*.
-/
@[blueprint "def:forwardLocallyExponentiallyStable"
  (statement := /-- An equilibrium is locally exponentially stable on finite
    forward segments when nearby solutions satisfy a uniform estimate
    $\|x(t)-x_{\rm eq}\|\leq C e^{-a(t-t_0)}\|x(t_0)-x_{\rm eq}\|$. -/)]
def ForwardLocallyExponentiallyStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∃ r C a : ℝ, 0 < r ∧ 1 ≤ C ∧ 0 < a ∧
    ∀ (t₀ t₁ : ℝ) (φ : ℝ → ℝⁿ), IsTrajectoryOn φ f t₀ t₁ →
      ‖φ t₀ - x_eq‖ < r → ∀ t ∈ Icc t₀ t₁,
        ‖φ t - x_eq‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x_eq‖

/-- Local asymptotic stability: forward Lyapunov stable, and forward-complete solutions
starting within `c` converge to the equilibrium.

Attractivity is per-solution and quantifies over forward-complete solutions, as convergence must.
The completeness restriction is harmless because the stability conjunct guards it: where
solutions escape in finite time `ForwardLyapunovStable` already fails. A `τ` uniform over
solutions is strictly stronger and is recorded separately, for the certificates that supply it.

Reference: Khalil, *Nonlinear Systems*.
-/
@[blueprint "def:forwardLocalAsymptoticStable"
  (statement := /-- An equilibrium is \emph{locally asymptotically stable} when it is forward
    Lyapunov stable and there is a radius $c>0$ such that every solution defined for all
    forward time with $\|\varphi(t_0)-x_{\rm eq}\|<c$ satisfies
    $\varphi(t)\to x_{\rm eq}$ as $t\to\infty$. -/)]
def ForwardLocalAsymptoticStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ForwardLyapunovStable f x_eq ∧
  ∃ c > 0, ∀ (t₀ : ℝ) (φ : ℝ → ℝⁿ), IsIntegralCurveOn φ (fun _ y => f y) (Ici t₀) →
    ‖φ t₀ - x_eq‖ < c → Tendsto φ atTop (𝓝 x_eq)

/-- Global asymptotic stability: forward Lyapunov stable, and *every* forward-complete solution
converges to the equilibrium.

As `ForwardLocalAsymptoticStable` but with no basin restriction.

Reference: Khalil, *Nonlinear Systems*.
-/
@[blueprint "def:forwardGlobalAsymptoticStable"
  (statement := /-- An equilibrium is \emph{globally asymptotically stable} when it is forward
    Lyapunov stable and every solution defined for all forward time satisfies
    $\varphi(t)\to x_{\rm eq}$ as $t\to\infty$. -/)]
def ForwardGlobalAsymptoticStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ForwardLyapunovStable f x_eq ∧
  ∀ (t₀ : ℝ) (φ : ℝ → ℝⁿ), IsIntegralCurveOn φ (fun _ y => f y) (Ici t₀) →
    Tendsto φ atTop (𝓝 x_eq)

/-- Forward instability is the negation of forward Lyapunov stability.

Reference: Khalil, *Nonlinear Systems*.
-/
@[blueprint "def:forwardUnstable"
  (statement := /-- Forward instability is the negation of stability quantified
    over all finite forward solution segments. -/)]
def ForwardUnstable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ¬ ForwardLyapunovStable f x_eq

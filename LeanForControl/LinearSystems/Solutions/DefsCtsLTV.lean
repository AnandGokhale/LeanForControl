import LeanForControl.LinearSystems.Continuous
import LeanForControl.ODEs.DefsPeanoBaker
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Architect

/-!
# Definitions for continuous-time solutions

Every `def` and `noncomputable def` for the `Solutions` directory's continuous-time track
lives here, apart from the theorems proved about them (`CtsLTV.lean`, `CtsLTI.lean`), per the
project convention: definitions live apart from theorems. The discrete-time definitions are in
`DefsDiscLTV.lean`.

The Peano-Baker series `stateTransitionMatrix` is defined for a coefficient in any real normed
algebra, apart from systems (`ODEs/DefsPeanoBaker.lean`, theory in `ODEs/PeanoBaker.lean`).  For
an LTV system the coefficient is the state operator `A(t)` itself, so `Φ` and the responses act on
the state space.  The time-invariant case is the constant map, specialized in `CtsLTI.lean`.

* `ContinuousLTV.stateTransition` — `Φ` for an LTV system, an operator on its state space.
* `ContinuousLTV.forcedResponse` — the variation-of-constants formula for
  `ẋ = A(t)x + B(t)u(t)`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5.
-/

namespace LinearSystems

open Matrix

namespace ContinuousLTV

variable {E U Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup U]
  [NormedSpace ℝ U] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The **state transition operator** of an LTV system: the Peano-Baker series `Φ(t, t₀)` of the
state operator `A`, in the Banach algebra of continuous linear operators on the state space.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "def:continuousLTV-stateTransition"
  (title := "State transition operator of an LTV system")
  (statement := /-- The state transition matrix $\Phi(t, t_0)$ (\cref{def:stateTransitionMatrix})
    of the state operator $A$, an operator on the state space. -/)]
noncomputable def stateTransition (s : ContinuousLTV E U Y) (t t₀ : ℝ) : E →L[ℝ] E :=
  stateTransitionMatrix s.A t t₀

/-- The **forced response** of `ẋ = A(t) x + B(t) u(t)` from the state `x₀` at time `t₀`, given
by the variation-of-constants formula
`x(t) = Φ(t, t₀) x₀ + ∫ τ in t₀..t, Φ(t, τ) B(τ) u(τ) dτ`.

With `u = 0` it is the homogeneous response `Φ(·, t₀) x₀`, the object Lyapunov stability is
stated about.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Theorem 5.2. -/
@[blueprint "def:forcedResponse"
  (title := "Forced response")
  (statement := /-- The \emph{forced response} of $\dot x = A(t)x + B(t)u(t)$ from the state
    $x_0$ at time $t_0$, given by the variation-of-constants formula
    \[
      x(t) = \Phi(t, t_0)\, x_0 + \int_{t_0}^{t} \Phi(t, \tau)\, B(\tau)\, u(\tau)\,
        \mathrm{d}\tau,
    \]
    with $\Phi$ the state transition operator (\cref{def:continuousLTV-stateTransition}).

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, Theorem 5.2.
  -/)]
noncomputable def forcedResponse (s : ContinuousLTV E U Y) (u : ℝ → U) (t₀ : ℝ) (x₀ : E)
    (t : ℝ) : E :=
  s.stateTransition t t₀ x₀ + ∫ τ in t₀..t, s.stateTransition t τ (s.B τ (u τ))

end ContinuousLTV

end LinearSystems

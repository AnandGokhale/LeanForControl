import LeanForControl.LinearSystems.Continuous
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Architect

/-!
# Definitions for continuous-time solutions

Every `def` and `noncomputable def` for the `Solutions` directory's continuous-time track
lives here, apart from the theorems proved about them (`CtsLTV.lean`, `CtsLTI.lean`), per the
project convention: definitions live apart from theorems. The discrete-time definitions are in
`DefsDiscLTV.lean`.

The Peano-Baker series is defined for a time-varying coefficient `A : ℝ → 𝔸` in any real
normed algebra `𝔸`; its theory (`PeanoBaker.lean`) uses only the algebra structure. The
time-invariant case is the constant map, specialized in `CtsLTI.lean` rather than given a
separate definition.

For a real LTV system the coefficient is the state matrix read as an operator on Euclidean
space, so `Φ` and the responses act on `EuclideanSpace ℝ X`.

* `peanoBakerTerm` — the `k`-th iterated-integral term of the Peano-Baker series.
* `stateTransitionMatrix` — the Peano-Baker series itself,
  `Φ(t, t₀) := ∑' k, peanoBakerTerm A k t t₀`.
* `ContinuousLTV.stateTransition` — `Φ` for a real LTV system, as an operator on Euclidean
  states.
* `ContinuousLTV.forcedResponse` — the variation-of-constants formula for
  `ẋ = A(t)x + B(t)u(t)`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5.
-/

namespace LinearSystems

open Matrix

section BanachAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- The `k`-th term of the Peano-Baker series for a time-varying coefficient `A`:
`peanoBakerTerm A 0 t t₀ = 1` and
`peanoBakerTerm A (k+1) t t₀ = ∫ s in t₀..t, A s * peanoBakerTerm A k s t₀`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5 (Peano-Baker series). -/
@[blueprint "def:peanoBakerTerm"
  (title := "Peano--Baker term")
  (statement := /-- The $k$-th term of the Peano--Baker series for a time-varying state
    coefficient $A(t)$:
    \[
      P_0(t,t_0) := 1, \qquad
      P_{k+1}(t,t_0) := \int_{t_0}^{t} A(s)\, P_k(s,t_0)\,\mathrm{d}s.
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5 (Peano-Baker series).
  -/)]
noncomputable def peanoBakerTerm (A : ℝ → 𝔸) : ℕ → ℝ → ℝ → 𝔸
  | 0,     _, _  => 1
  | k + 1, t, t₀ => ∫ s in t₀..t, A s * peanoBakerTerm A k s t₀

/-- The *state transition matrix* of a time-varying linear system `ẋ = A(t) x`, given by the
Peano-Baker series `Φ(t, t₀) := ∑' k, peanoBakerTerm A k t t₀`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Theorem 5.1
(Peano-Baker series). -/
@[blueprint "def:stateTransitionMatrix"
  (title := "State transition matrix")
  (statement := /-- The \emph{state transition matrix} $\Phi(t,t_0)$, given by the
    Peano--Baker series
    \[
      \Phi(t,t_0) := \sum_{k=0}^{\infty} P_k(t,t_0).
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, Theorem 5.1 (Peano-Baker
    series).
  -/)]
noncomputable def stateTransitionMatrix (A : ℝ → 𝔸) (t t₀ : ℝ) : 𝔸 :=
  ∑' k, peanoBakerTerm A k t t₀

end BanachAlgebra

namespace ContinuousLTV

variable {X U Y : Type*} [Fintype X] [DecidableEq X]

/-- The **state transition operator** of a real LTV system: the Peano-Baker series `Φ(t, t₀)`
of the state matrix read as an operator `A(t)` on the Euclidean state space, in the Banach
algebra of continuous linear operators on that space.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "def:continuousLTV-stateTransition"
  (title := "State transition operator of an LTV system")
  (statement := /-- The state transition matrix $\Phi(t, t_0)$ (\cref{def:stateTransitionMatrix})
    of $A$, acting on the Euclidean state space $\mathbb{R}^X$. -/)]
noncomputable def stateTransition (s : ContinuousLTV X U Y ℝ) (t t₀ : ℝ) :
    EuclideanSpace ℝ X →L[ℝ] EuclideanSpace ℝ X :=
  stateTransitionMatrix (fun t => toEuclideanCLM (n := X) (𝕜 := ℝ) (s.A t)) t t₀

variable [Fintype U] [DecidableEq U]

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
noncomputable def forcedResponse (s : ContinuousLTV X U Y ℝ) (u : ℝ → EuclideanSpace ℝ U)
    (t₀ : ℝ) (x₀ : EuclideanSpace ℝ X) (t : ℝ) : EuclideanSpace ℝ X :=
  s.stateTransition t t₀ x₀ + ∫ τ in t₀..t, s.stateTransition t τ (toEuclideanLin (s.B τ) (u τ))

end ContinuousLTV

end LinearSystems

import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Architect

/-!
# Definitions for continuous-time solutions

Every `def` and `noncomputable def` for the `Solutions` directory's continuous-time track
lives here, apart from the theorems proved about them (`CtsLTV.lean`, `CtsLTI.lean`), per the
project convention: definitions live apart from theorems. The discrete-time definitions are in
`DefsDiscLTV.lean`.

The state matrix is a genuinely *time-varying* `A : ℝ → Matrix X X ℝ`; the time-invariant case
is the constant map, specialized in `CtsLTI.lean` rather than given a separate definition.

`Matrix X X ℝ` carries no default norm instance in Mathlib (there are several
natural choices). We fix the `L∞`-operator norm, `Matrix.Norms.Operator`, throughout this
track: it is the one under which matrix multiplication is submultiplicative
(`‖A * B‖ ≤ ‖A‖ * ‖B‖`), which the Peano-Baker series' convergence proof needs.

* `peanoBakerTerm` — the `k`-th iterated-integral term of the Peano-Baker series.
* `stateTransitionMatrix` — the Peano-Baker series itself,
  `Φ(t, t₀) := ∑' k, peanoBakerTerm A k t t₀`.
* `forcedResponse` — the variation-of-constants formula for `ẋ = A(t)x + B(t)u(t)`.
* `homogeneousResponse` — the forced response with the input switched off, which is what the
  stability theory is stated about.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5.
-/

namespace LinearSystems

open Matrix
open scoped Matrix.Norms.Operator

variable {X U : Type*} [Fintype X] [DecidableEq X] [Fintype U]

/-- The `k`-th term of the Peano-Baker series for a time-varying state matrix `A`:
`peanoBakerTerm A 0 t t₀ = 1` and
`peanoBakerTerm A (k+1) t t₀ = ∫ s in t₀..t, A s * peanoBakerTerm A k s t₀`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5 (Peano-Baker series). -/
@[blueprint "def:peanoBakerTerm"
  (title := "Peano--Baker term")
  (statement := /-- The $k$-th term of the Peano--Baker series for a time-varying state
    matrix $A(t)$:
    \[
      P_0(t,t_0) := I, \qquad
      P_{k+1}(t,t_0) := \int_{t_0}^{t} A(s)\, P_k(s,t_0)\,\mathrm{d}s.
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5 (Peano-Baker series).
  -/)]
noncomputable def peanoBakerTerm (A : ℝ → Matrix X X ℝ) :
    ℕ → ℝ → ℝ → Matrix X X ℝ
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
noncomputable def stateTransitionMatrix (A : ℝ → Matrix X X ℝ) (t t₀ : ℝ) :
    Matrix X X ℝ :=
  ∑' k, peanoBakerTerm A k t t₀

/-- The *forced response* of `ẋ = A(t) x + B(t) u(t)` from the state `x₀` at time `t₀`, given
by the variation-of-constants formula
`x(t) = Φ(t, t₀) x₀ + ∫ τ in t₀..t, Φ(t, τ) B(τ) u(τ) dτ`.

The homogeneous response `Φ(·, t₀) x₀` is the special case `B = 0`; naming the forced one is
what lets it be quantified over, rather than retyped in every statement about it.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Theorem 5.2. -/
@[blueprint "def:forcedResponse"
  (title := "Forced response")
  (statement := /-- The \emph{forced response} of $\dot x = A(t)x + B(t)u(t)$ from the state
    $x_0$ at time $t_0$, given by the variation-of-constants formula
    \[
      x(t) = \Phi(t, t_0)\, x_0 + \int_{t_0}^{t} \Phi(t, \tau)\, B(\tau)\, u(\tau)\,
        \mathrm{d}\tau,
    \]
    with $\Phi$ the state transition matrix (\cref{def:stateTransitionMatrix}).

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, Theorem 5.2.
  -/)]
noncomputable def forcedResponse (A : ℝ → Matrix X X ℝ) (B : ℝ → Matrix X U ℝ)
    (u : ℝ → U → ℝ) (t₀ : ℝ) (x₀ : X → ℝ) : ℝ → X → ℝ :=
  fun t => stateTransitionMatrix A t t₀ *ᵥ x₀ +
    ∫ τ in t₀..t, stateTransitionMatrix A t τ *ᵥ (B τ *ᵥ u τ)

/-- The *homogeneous response* of `ẋ = A(t) x` from the state `x₀` at time `t₀`, namely
`x(t) = Φ(t, t₀) x₀`.

Hespanha's "homogeneous state response": the forced response (`forcedResponse`) with the input
switched off. It is named separately because the stability theory is stated about it — the
input matrix plays no part in Lyapunov stability.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Definition 8.1. -/
@[blueprint "def:homogeneousResponse"
  (title := "Homogeneous response")
  (statement := /-- The \emph{homogeneous response} of $\dot x = A(t)x$ from the state $x_0$ at
    time $t_0$,
    \[
      x(t) = \Phi(t, t_0)\, x_0,
    \]
    with $\Phi$ the state transition matrix (\cref{def:stateTransitionMatrix}).  This is the
    forced response (\cref{def:forcedResponse}) with the input switched off, and the object
    Lyapunov stability is stated about.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.1.
  -/)]
noncomputable def homogeneousResponse (A : ℝ → Matrix X X ℝ) (t₀ : ℝ) (x₀ : X → ℝ) :
    ℝ → X → ℝ :=
  fun t => stateTransitionMatrix A t t₀ *ᵥ x₀

end LinearSystems

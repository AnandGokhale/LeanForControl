import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Basic
import LeanForControl.MatrixAlgebra.Complexify
import LeanForControl.LinearSystems.Solutions.DefsCtsLTV
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Architect

/-!
# Stability definitions for linear systems

The spectral conditions that characterize stability of a linear system, stated over an
abstract index type `X` rather than `Fin n`, matching the convention everything downstream of
the `ContinuousLTV` object follows.

The continuous-time conditions (`IsHurwitz`, `IsHurwitzWithRate`, the Lyapunov equation
`PA + AᵀP = -Q` and its time-varying form `-Ṗ = PA + AᵀP + Q`) and their discrete-time
counterparts (`IsSchur`: every eigenvalue in the open unit disc; the discrete Lyapunov equation
`AᵀPA - P = -Q`).

Both predicates are stated through eigenpairs of the complexification rather than through an
enumeration of eigenvalues or through `spectrum`: that is the form in which they are produced
(`Matrix.exists_eigenpair_of_mem_spectrum_exp`) and consumed, and it avoids choosing an
ordering of the eigenvalues.

Zero-dimensional matrices satisfy both predicates vacuously, there being no nonzero
eigenvector.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.1.
-/

namespace LinearSystems

open Matrix

variable {X : Type*} [Fintype X]

/-- A real square matrix is **Hurwitz** when every complex eigenvalue has strictly negative
real part.

This is the spectral condition that Hespanha's Theorem 8.1 equates with asymptotic, and with
exponential, stability of `ẋ = A x`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.1. -/
@[blueprint "def:stability-isHurwitz"
  (title := "Hurwitz matrix")
  (statement := /-- A real square matrix $A$ is \emph{Hurwitz} when every eigenpair
    $(\mu, v)$ of its complexification, with $v \ne 0$, satisfies
    $\operatorname{Re}(\mu) < 0$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.1.
  -/)]
def IsHurwitz (A : Matrix X X ℝ) : Prop :=
  ∀ (μ : ℂ) (v : X → ℂ), v ≠ 0 →
    A.complexify *ᵥ v = μ • v → μ.re < 0

/-- A real square matrix is **Hurwitz with decay rate `α`** when every complex eigenvalue `μ`
satisfies `μ.re < -α`, so that the spectrum is bounded away from the imaginary axis by `α`.

`IsHurwitz` is the case `α = 0`, but it is stated separately rather than as `IsHurwitzWithRate
0` so that unfolding it gives `μ.re < 0` on the nose: `-0 = 0` is not definitional for the
reals, and the detour would be paid at every use site.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.1. -/
@[blueprint "def:stability-isHurwitzWithRate"
  (title := "Hurwitz with a prescribed decay rate")
  (statement := /-- A real square matrix $A$ is \emph{Hurwitz with decay rate} $\alpha$ when
    every eigenpair $(\mu, v)$ of its complexification, with $v \ne 0$, satisfies
    $\operatorname{Re}(\mu) < -\alpha$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.1.
  -/)]
def IsHurwitzWithRate (α : ℝ) (A : Matrix X X ℝ) : Prop :=
  ∀ (μ : ℂ) (v : X → ℂ), v ≠ 0 →
    A.complexify *ᵥ v = μ • v → μ.re < -α

/-- `P` satisfies the **continuous Lyapunov equation** for `A` with forcing `Q` when

    P A + Aᵀ P = -Q.

For `P` positive definite this is the statement that `x ↦ xᵀ P x` decreases along `ẋ = A x`
at the rate set by `Q`: Hespanha's Theorem 8.2 turns that into an equivalent of asymptotic
stability.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.2. -/
@[blueprint "def:continuousLyapunovEquation"
  (title := "Continuous Lyapunov equation")
  (statement := /-- For real square matrices $A$, $P$ and $Q$, the matrix $P$ satisfies the
    \emph{continuous Lyapunov equation} for $A$ with forcing $Q$ when
    \[
      PA + A^{\mathsf T}P = -Q.
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.2.
  -/)]
def ContinuousLyapunovEquation (A P Q : Matrix X X ℝ) : Prop :=
  P * A + Aᵀ * P = -Q

section Differential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `P` satisfies the **differential Lyapunov equation** for `A` with forcing `Q` when, at every
`t ≥ 0`,

    -Ṗ(t) = P(t) A(t) + A(t)* P(t) + Q(t),

with `A(t)*` the adjoint (the transpose, for matrices on Euclidean space).  The time-varying form
of `ContinuousLyapunovEquation`: for `P` positive definite, `x ↦ ⟪x, P(t) x⟫` decreases along
`ẋ = A(t) x` at the rate set by `Q(t)`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), equation (4.28). -/
@[blueprint "def:differentialLyapunovEquation"
  (title := "Differential Lyapunov equation")
  (statement := /-- For operator-valued functions $A$, $P$ and $Q$ of time on a real Hilbert
    space, $P$ satisfies the \emph{differential Lyapunov equation} for $A$ with forcing $Q$ when,
    for every $t \ge 0$, $P$ is differentiable at $t$ and
    \[
      -\dot P(t) = P(t)A(t) + A(t)^{*}P(t) + Q(t).
    \]
    For constant matrices it is the continuous Lyapunov equation
    (\cref{def:continuousLyapunovEquation}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), equation (4.28). -/)]
def DifferentialLyapunovEquation (A P Q : ℝ → E →L[ℝ] E) : Prop :=
  ∀ t : ℝ, 0 ≤ t → HasDerivAt P (-(P t * A t + star (A t) * P t + Q t)) t

namespace ContinuousLTV

variable {U Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- The integrand of Khalil's solution of the differential Lyapunov equation,
`Φ(τ, t)* Q(τ) Φ(τ, t)`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), proof of Theorem 4.12. -/
@[blueprint "def:continuousLTV-lyapunovIntegrand"
  (title := "Integrand of the Lyapunov integral")
  (statement := /-- For a linear time-varying system with state transition operator $\Phi$
    (\cref{def:continuousLTV-stateTransition}) and an operator function $Q$,
    \[
      \Phi(\tau, t)^{*} Q(\tau)\, \Phi(\tau, t).
    \]

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), proof of Theorem 4.12. -/)]
noncomputable def lyapunovIntegrand (s : ContinuousLTV E U Y) (Q : ℝ → E →L[ℝ] E) (t τ : ℝ) :
    E →L[ℝ] E :=
  star (s.stateTransition τ t) * Q τ * s.stateTransition τ t

/-- **Khalil's solution of the differential Lyapunov equation**,
`P(t) = ∫_t^∞ Φ(τ, t)* Q(τ) Φ(τ, t) dτ`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), proof of Theorem 4.12. -/
@[blueprint "def:continuousLTV-lyapunovIntegral"
  (title := "Lyapunov integral")
  (statement := /-- For a linear time-varying system and an operator function $Q$,
    \[
      P(t) = \int_t^\infty \Phi(\tau, t)^{*} Q(\tau)\, \Phi(\tau, t)\, d\tau
    \]
    (\cref{def:continuousLTV-lyapunovIntegrand}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), proof of Theorem 4.12. -/)]
noncomputable def lyapunovIntegral (s : ContinuousLTV E U Y) (Q : ℝ → E →L[ℝ] E) (t : ℝ) :
    E →L[ℝ] E :=
  ∫ τ in Set.Ioi t, s.lyapunovIntegrand Q t τ

end ContinuousLTV

end Differential

/-- A real square matrix is **Schur** when every complex eigenvalue lies in the open unit disc.

This is the spectral condition that Hespanha's Theorem 8.3 equates with asymptotic, and with
exponential, stability of `x(t+1) = A x(t)`: the discrete-time counterpart of `IsHurwitz`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.3. -/
@[blueprint "def:stability-isSchur"
  (title := "Schur matrix")
  (statement := /-- A real square matrix $A$ is \emph{Schur} when every eigenpair $(\mu, v)$ of
    its complexification, with $v \ne 0$, satisfies $|\mu| < 1$.  The discrete-time counterpart
    of \cref{def:stability-isHurwitz}.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.3.
  -/)]
def IsSchur (A : Matrix X X ℝ) : Prop :=
  ∀ (μ : ℂ) (v : X → ℂ), v ≠ 0 →
    A.complexify *ᵥ v = μ • v → ‖μ‖ < 1

/-- `P` solves the **discrete-time Lyapunov equation** for `A` with forcing `Q`:
`Aᵀ P A - P = -Q`.

Along `x(t+1) = A x(t)` the quadratic form `V(x) = xᵀ P x` then changes by
`V(A x) - V(x) = -xᵀ Q x`, the discrete counterpart of `V̇ = -xᵀ Q x`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.4. -/
@[blueprint "def:discreteLyapunovEquation"
  (title := "Discrete Lyapunov equation")
  (statement := /-- For real square matrices $A$, $P$ and $Q$, the matrix $P$ satisfies the
    \emph{discrete-time Lyapunov equation} for $A$ with forcing $Q$ when
    \[
      A^{\mathsf T} P A - P = -Q.
    \]
    Along $x(t+1) = Ax(t)$ the quadratic form $V(x) = x^{\mathsf T}Px$ then changes by
    $V(Ax) - V(x) = -x^{\mathsf T}Qx$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.4.
  -/)]
def DiscreteLyapunovEquation (A P Q : Matrix X X ℝ) : Prop :=
  Aᵀ * P * A - P = -Q

end LinearSystems

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import LeanForControl.MatrixAlgebra.Complex
import Architect

/-!
# Stability definitions for linear systems

The spectral conditions that characterize stability of a linear system, stated over an
abstract index type `X` rather than `Fin n`, matching the convention everything downstream of
the `ContinuousLinearSystem` object follows.

Only continuous-time conditions are here so far; the discrete-time counterpart (all
eigenvalues inside the open unit disc) belongs in this file when it is needed.

Both predicates are stated through eigenpairs of the complexification rather than through an
enumeration of eigenvalues or through `spectrum`: that is the form in which they are produced
(`MatrixAlgebra.exists_eigenpair_of_mem_spectrum_exp`) and consumed, and it avoids choosing an
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

end LinearSystems

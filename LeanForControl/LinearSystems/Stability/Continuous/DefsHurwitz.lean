import LeanForControl.LinearSystems.Basic
import Mathlib.Analysis.Complex.Basic
import Architect

/-!
# Definitions for Hurwitz matrices

This file defines continuous-time Hurwitz stability for real square matrices through
eigenpairs of their complexification. The eigenpair formulation matches the concrete
matrix-vector equations used by the Hautus development and avoids choosing an enumeration
of eigenvalues.

The definition intentionally allows zero-dimensional matrices. In dimension zero there
are no nonzero eigenvectors, so every matrix satisfies the predicate with every rate;
`LinearSystems.isHurwitzWithRate_fin_zero` records this convention explicitly.

Reference: João P. Hespanha, *Linear Systems Theory* (2nd ed.), continuous-time
stability. The rate-indexed predicate is the strict spectral-margin variant.
-/

namespace LinearSystems

open Matrix

variable {n : ℕ}

/-- A real matrix is Hurwitz with decay rate `α` when every complex eigenvalue `μ`
satisfies `μ.re < -α`.

This is stated using nonzero eigenvectors rather than an eigenvalue enumeration so it can
be used directly with PBH/Hautus arguments.

Reference: João P. Hespanha, *Linear Systems Theory* (2nd ed.), continuous-time
stability. The rate-indexed predicate is the strict spectral-margin variant. -/
@[blueprint "def:isHurwitzWithRate"
  (statement := /-- A real square matrix $A$ is \emph{Hurwitz with decay rate}
    $\alpha$ when every complex eigenpair $(\mu,v)$ with $v \ne 0$ satisfies
    $\operatorname{Re}(\mu) < -\alpha$. -/)]
def IsHurwitzWithRate (α : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (μ : ℂ) (v : Fin n → ℂ), v ≠ 0 →
    A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v → μ.re < -α

/-- A real matrix is Hurwitz when all of its complex eigenvalues have negative real part.

Reference: João P. Hespanha, *Linear Systems Theory* (2nd ed.), continuous-time
stability. The rate-indexed predicate is the strict spectral-margin variant. -/
@[blueprint "def:isHurwitz"
  (statement := /-- A real square matrix is \emph{Hurwitz} when every complex
    eigenvalue has strictly negative real part. -/)]
abbrev IsHurwitz (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsHurwitzWithRate 0 A

end LinearSystems

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

Reference: standard continuous-time linear systems terminology.
-/

namespace LinearSystems

open Matrix

variable {n : ℕ}

/-- The entrywise complexification of a real matrix. -/
noncomputable def complexification (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A.map (algebraMap ℝ ℂ)

/-- A real matrix is Hurwitz with decay rate `α` when every complex eigenvalue `μ`
satisfies `μ.re < -α`.

This is stated using nonzero eigenvectors rather than an eigenvalue enumeration so it can
be used directly with PBH/Hautus arguments.

Reference: standard continuous-time linear systems terminology. -/
@[blueprint "def:isHurwitzWithRate"
  (statement := /-- A real square matrix $A$ is \emph{Hurwitz with decay rate}
    $\alpha$ when every complex eigenpair $(\mu,v)$ with $v \ne 0$ satisfies
    $\operatorname{Re}(\mu) < -\alpha$. -/)]
def IsHurwitzWithRate (α : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (μ : ℂ) (v : Fin n → ℂ), v ≠ 0 →
    complexification A *ᵥ v = μ • v → μ.re < -α

/-- A real matrix is Hurwitz when all of its complex eigenvalues have negative real part.

Reference: standard continuous-time linear systems terminology. -/
@[blueprint "def:isHurwitz"
  (statement := /-- A real square matrix is \emph{Hurwitz} when every complex
    eigenvalue has strictly negative real part. -/)]
abbrev IsHurwitz (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsHurwitzWithRate 0 A

end LinearSystems

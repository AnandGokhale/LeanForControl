import Mathlib.Data.Matrix.Mul
import Architect

/-!
# Eigenpairs under elementary operations

An eigenpair is a pair `(μ, v)` with `A *ᵥ v = μ • v`. This file records what the elementary
operations on `A` do to it: shifting by a multiple of the identity shifts the eigenvalue,
scaling scales it, taking powers powers it, and the kernel spelling used by the
Hautus/PBH tests is the same statement rearranged.

All of it holds over an arbitrary commutative ring. None of it is about `ℂ`, about
complexification, or about stability — those uses live downstream.

The file sits below both `Exponential.lean` and `Spectrum.lean` because both need it:
`exp_mulVec_of_mulVec_eq_smul` is the exponential's member of this family, and its proof runs
through the power case.

Reference: standard linear algebra.
-/

namespace MatrixAlgebra

open Matrix

variable {R : Type*} [CommRing R] {X : Type*} [Fintype X]
variable {A : Matrix X X R} {μ : R} {v : X → R}

/-- Scaling a matrix scales its eigenvalues. -/
@[blueprint "lem:smul-mulVec-eigenpair"
  (title := "A scalar multiple scales the eigenvalues")
  (latexEnv := "lemma")
  (statement := /-- If $Av = \mu v$ then $(cA)v = (c\mu)v$. -/)]
lemma smul_mulVec_of_mulVec_eq_smul (h : A *ᵥ v = μ • v) (c : R) :
    (c • A) *ᵥ v = (c * μ) • v := by
  rw [Matrix.smul_mulVec, h, smul_smul]

variable [DecidableEq X]

/-- Powers of a matrix power its eigenvalues. -/
@[blueprint "lem:pow-mulVec-eigenpair"
  (title := "Powers power the eigenvalues")
  (latexEnv := "lemma")
  (statement := /-- If $Av = \mu v$ then $A^{k}v = \mu^{k}v$ for every $k$. -/)]
lemma pow_mulVec_of_mulVec_eq_smul (h : A *ᵥ v = μ • v) : ∀ k : ℕ, A ^ k *ᵥ v = μ ^ k • v
  | 0 => by simp
  | k + 1 => by
      calc A ^ (k + 1) *ᵥ v = A ^ k *ᵥ (A *ᵥ v) := by rw [pow_succ, Matrix.mulVec_mulVec]
        _ = μ ^ (k + 1) • v := by
            rw [h, Matrix.mulVec_smul, pow_mulVec_of_mulVec_eq_smul h k, smul_smul, pow_succ,
              mul_comm]

/-- A scalar shift shifts the eigenvalues, leaving the eigenvectors alone. -/
@[blueprint "lem:mulVec-add-smul-one"
  (title := "A scalar shift shifts the eigenvalues")
  (latexEnv := "lemma")
  (statement := /-- For a square matrix $A$ over a commutative ring and scalars
    $\alpha, \mu$, a vector $v$ satisfies $(A + \alpha I)v = (\mu + \alpha)v$ if and only if
    $Av = \mu v$. -/)]
lemma mulVec_add_smul_one_eq_smul_iff (A : Matrix X X R) (α μ : R) (v : X → R) :
    (A + α • (1 : Matrix X X R)) *ᵥ v = (μ + α) • v ↔ A *ᵥ v = μ • v := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, add_smul]
  exact add_left_inj _

/-- The kernel spelling of an eigenpair, as the Hautus and PBH tests write it. -/
@[blueprint "lem:mulVec-sub-smul-one-eq-zero"
  (title := "The kernel form of an eigenpair")
  (latexEnv := "lemma")
  (statement := /-- $(\mu I - A)v = 0$ if and only if $Av = \mu v$. -/)]
lemma mulVec_sub_smul_one_eq_zero_iff (A : Matrix X X R) (μ : R) (v : X → R) :
    (μ • (1 : Matrix X X R) - A) *ᵥ v = 0 ↔ A *ᵥ v = μ • v := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  exact eq_comm

end MatrixAlgebra

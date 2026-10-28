import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Architect

/-!
# Eigenpairs, the spectrum and `λ_max`

An eigenpair is a pair `(μ, v)` with `A *ᵥ v = μ • v`.  The first part records what the elementary
operations on `A` do to it: shifting by a multiple of the identity shifts the eigenvalue, scaling
scales it, taking powers powers it, and the kernel spelling used by the Hautus/PBH tests is the
same statement rearranged.  All of it holds over an arbitrary commutative ring, except
`mem_spectrum_iff_exists_eigenpair`, which identifies the spectrum of a matrix over a field with
its eigenvalues.

The second part is about real spectra.  A real matrix `S` is *symmetrizable* when `S P` is
symmetric for some `P ≻ 0`.  Such an `S` is similar to the symmetric matrix `P^{-½} (S P) P^{-½}`,
so its spectrum is real; symmetric matrices are the case `P = I`.  These are the matrices on which
the largest eigenvalue `λ_max` means what it says, and `Matrix.lambdaMax` asks for a proof that its
argument is one of them.

Reference: standard linear algebra.
-/

namespace Matrix

section Eigenpair

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
            rw [h, mulVec_smul, pow_mulVec_of_mulVec_eq_smul h k, smul_smul, pow_succ,
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

/-- Over a field, membership in the spectrum of a matrix is exactly having an eigenvector. -/
@[blueprint "lem:mem-spectrum-iff-exists-eigenpair"
  (title := "The spectrum of a matrix is its set of eigenvalues")
  (latexEnv := "lemma")
  (statement := /-- For a square matrix $M$ over a field $K$, $\mu \in \sigma(M)$ if and only if
    $Mv = \mu v$ for some $v \ne 0$. -/)]
lemma mem_spectrum_iff_exists_eigenpair {K : Type*} [Field K]
    (M : Matrix X X K) (μ : K) :
    μ ∈ spectrum K M ↔ ∃ v : X → K, v ≠ 0 ∧ M *ᵥ v = μ • v := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact ⟨v, hv.2, by simpa [Matrix.toLin'_apply'] using hv.apply_eq_smul⟩
  · rintro ⟨v, hv0, hv⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hv0⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa [Matrix.toLin'_apply'] using hv

end Eigenpair

section RealSpectrum

variable {n : Type*} [Fintype n]

/-- `S` is *symmetrizable*: `S P` is symmetric for some `P ≻ 0`.  Then `S` is similar to a symmetric
matrix, so its spectrum is real. -/
@[blueprint "def:isSymmetrizable"
  (title := "Symmetrizable matrix")
  (statement := /-- A matrix $S \in \mathbb{R}^{n \times n}$ is \emph{symmetrizable} if $S P$ is
    symmetric for some $P \succ 0$.  Then $S$ is similar to the symmetric matrix
    $P^{-1/2} (S P) P^{-1/2}$, so its eigenvalues are real.  Symmetric matrices are the case
    $P = I$. -/)]
def IsSymmetrizable (S : Matrix n n ℝ) : Prop :=
  ∃ P : Matrix n n ℝ, P.PosDef ∧ (S * P).IsHermitian

/-- A symmetric matrix is symmetrizable, with `P = I`. -/
theorem IsHermitian.isSymmetrizable {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    S.IsSymmetrizable := by
  classical
  exact ⟨1, PosDef.one, by rwa [Matrix.mul_one]⟩

variable [DecidableEq n]

/-- `λ_max(S)`: the largest eigenvalue of a symmetrizable `S`, the supremum of its spectrum. -/
@[blueprint "def:lambdaMax"
  (title := "Largest eigenvalue")
  (statement := /-- For a symmetrizable $S$ (\cref{def:isSymmetrizable}), $\lambda_{\max}(S)$ is its
    largest eigenvalue. -/)]
noncomputable def lambdaMax (S : Matrix n n ℝ) (_hS : S.IsSymmetrizable) : ℝ :=
  sSup (spectrum ℝ S)

end RealSpectrum

end Matrix

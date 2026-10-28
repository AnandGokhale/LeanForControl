import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Architect

/-!
# Symmetrizable matrices and `λ_max`

A real matrix `S` is *symmetrizable* when `S P` is symmetric for some `P ≻ 0`.  Such an `S` is
similar to the symmetric matrix `P^{-½} (S P) P^{-½}`, so its spectrum is real; symmetric matrices
are the case `P = I`.  These are the matrices on which the largest eigenvalue `λ_max` means what it
says, and `Matrix.lambdaMax` asks for a proof that its argument is one of them.

Reference: standard linear algebra.
-/

namespace Matrix

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

end Matrix

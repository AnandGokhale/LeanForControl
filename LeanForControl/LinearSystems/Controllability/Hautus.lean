import LeanForControl.LinearSystems.Controllability.Controllability
import LeanForControl.LinearSystems.Observability.Hautus
import LeanForControl.MatrixAlgebra.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Architect

/-!
# Hautus controllability via duality

Controllability Hautus is the dual of observability Hautus. Rather than
mirror the entire eigenvector argument from
`LinearSystems.Observability.Hautus`, we route through the bridge
`IsControllable A B ↔ IsObservable Aᵀ Bᵀ` and reuse the observability
results from there. The key matrix identity is
`(controllabilityMatrix A B)ᵀ = observabilityMatrix Aᵀ Bᵀ`, which makes
the rank-form characterizations match across the duality.
-/

namespace LinearSystems

open Matrix

variable {n m : ℕ}

/-- The transpose of the controllability matrix is the observability matrix
of the transposed system: `𝒞(A, B)ᵀ = 𝒪(Aᵀ, Bᵀ)`. -/
lemma controllabilityMatrix_transpose
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    (controllabilityMatrix A B)ᵀ = observabilityMatrix Aᵀ Bᵀ := by
  ext ki j
  obtain ⟨k, i⟩ := ki
  rw [Matrix.transpose_apply, controllabilityMatrix_apply,
      observabilityMatrix_apply,
      ← Matrix.transpose_pow,
      ← Matrix.transpose_mul,
      Matrix.transpose_apply]

/-- **Duality bridge.** A linear system `(A, B)` is controllable iff the
transposed system `(Aᵀ, Bᵀ)` is observable. -/
theorem isControllable_iff_isObservable_transpose
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    IsControllable A B ↔ IsObservable Aᵀ Bᵀ := by
  rw [isControllable_iff_controllabilityMatrix_rank_eq,
      isObservable_iff_observabilityMatrix_rank_eq Aᵀ Bᵀ,
      ← controllabilityMatrix_transpose,
      Matrix.rank_transpose]

/-- The Hautus controllability matrix at `μ`, `[μI - A | B]`. -/
@[blueprint "def:hautusControllabilityMatrix"
  (statement := /-- The \emph{Hautus controllability matrix} of $(A, B)$
    at a complex number $\mu$ is the block-column matrix
    \[
      H^{\mathrm{ctrl}}_{A, B}(\mu)
        \;=\; \begin{bmatrix} \mu I - A & B \end{bmatrix}
        \in \mathbb{C}^{n \times (n + m)} .
    \] -/)]
noncomputable def hautusControllabilityMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ) :
    Matrix (Fin n) (Fin n ⊕ Fin m) ℂ :=
  Matrix.fromCols (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A) B

/-- The transpose of the Hautus controllability matrix is the Hautus
observability matrix of the transposed system. -/
lemma hautusControllabilityMatrix_transpose
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ) :
    (hautusControllabilityMatrix A B μ)ᵀ = hautusObservabilityMatrix Aᵀ Bᵀ μ := by
  unfold hautusControllabilityMatrix hautusObservabilityMatrix
  rw [Matrix.transpose_fromCols, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one]

/-- **Controllability Hautus lemma.** A finite-dimensional linear system
`(A, B)` over `ℂ` is controllable if and only if for every `μ ∈ ℂ`, the
Hautus block `[μI - A | B]` has full row rank. -/
@[blueprint "thm:isControllable-iff-hautus"
  (statement := /-- A finite-dimensional system $(A, B)$ over $\mathbb{C}$
    is controllable if and only if for every $\mu \in \mathbb{C}$ the Hautus
    matrix $H^{\mathrm{ctrl}}_{A, B}(\mu)$ has full row rank:
    \[
      \mathrm{IsControllable}(A, B)
      \iff
      \forall \mu \in \mathbb{C},\
        \operatorname{rank} H^{\mathrm{ctrl}}_{A, B}(\mu) = n.
    \] -/)
  (proof := /-- Combine the duality bridge
    \texttt{isControllable\_iff\_isObservable\_transpose} with the
    observability Hautus iff \cref{thm:isObservable-iff-hautus}, then
    convert the kernel-form RHS to the rank form via the matrix bridge
    \texttt{mulVec\_kernel\_trivial\_iff\_rank\_eq\_card\_cols} from
    `MatrixAlgebra.Rank`, and finally identify the transposed Hautus matrices. -/)]
theorem isControllable_iff_hautus
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    IsControllable A B
      ↔ ∀ μ : ℂ, Matrix.rank (hautusControllabilityMatrix A B μ) = n := by
  rw [isControllable_iff_isObservable_transpose, isObservable_iff_hautus]
  refine forall_congr' fun μ => ?_
  rw [Matrix.ker_mulVecLin_eq_bot_iff,
      MatrixAlgebra.mulVec_kernel_trivial_iff_rank_eq_card_cols,
      Fintype.card_fin,
      ← hautusControllabilityMatrix_transpose,
      Matrix.rank_transpose]

end LinearSystems

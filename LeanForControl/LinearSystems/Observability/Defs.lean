import LeanForControl.LinearSystems.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.Complex.Basic
import Architect

/-!
# Definitions for observability

Every `def`, `noncomputable def`, and predicate for the `Observability` directory lives
here, apart from the theorems proved about them (`Observability.lean`, `Hautus.lean`), per
the project convention: definitions live apart from theorems.

* `observabilityMatrix`, `IsObservable` — the textbook observability matrix and predicate,
  generic over a `Semiring 𝕜`.
* `unobservableSubspace`, `hautusObservabilityMatrix` — the unobservable subspace and the
  Hautus/PBH matrix `[μI - A; C]`, `ℂ`-only since the Hautus development needs eigenvalues.
-/

namespace LinearSystems

open Matrix

section Semiring

variable {𝕜 : Type*} [Semiring 𝕜]
variable {n p : ℕ}

/-- The observability matrix of `(A, C)`.

The `(k, i)`-th row is the `i`-th row of `C · Aᵏ`, where `k : Fin n`
ranges over `0, 1, …, n-1`. We index rows by `Fin n × Fin p` so that
`A ^ (k : ℕ)` is available without first casting `k` through `Fin.val`. -/
@[blueprint "def:observabilityMatrix"
  (statement := /-- The \emph{observability matrix} of a pair $(A, C)$
    with $A \in \mathbb{F}^{n \times n}$ and $C \in \mathbb{F}^{p \times n}$
    is the block-row matrix
    \[
      \mathcal{O}(A, C) =
      \begin{bmatrix} C \\ C\, A \\ C\, A^{2} \\ \vdots \\ C\, A^{n-1} \end{bmatrix}
      \in \mathbb{F}^{(n p) \times n}.
    \]
    Rows are indexed by $\mathrm{Fin}\, n \times \mathrm{Fin}\, p$, so that
    $A^{k}$ is available without casting $k : \mathrm{Fin}\, n$ through
    $\mathrm{Fin.val}$. -/)]
def observabilityMatrix
    (A : Matrix (Fin n) (Fin n) 𝕜) (C : Matrix (Fin p) (Fin n) 𝕜) :
    Matrix (Fin n × Fin p) (Fin n) 𝕜 :=
  Matrix.of fun ki j => (C * A ^ (ki.1 : ℕ)) ki.2 j

/-- The textbook observability predicate: the only state for which
`C · Aᵏ` annihilates the state for every power `k = 0, …, n-1` is the zero
state. This phrasing does not mention `observabilityMatrix`, so the milestone
theorem `isObservable_iff_observabilityMatrix_ker_trivial` has real content. -/
@[blueprint "def:isObservable"
  (statement := /-- A linear system $(A, C)$ is \emph{observable} when the only
    state $x \in \mathbb{F}^{n}$ for which
    \[
      C\, A^{k}\, x = 0 \qquad \text{for every } k = 0, 1, \dots, n-1
    \]
    is the zero state. This phrasing does not mention $\mathcal{O}(A, C)$,
    so the bridge \cref{thm:isObservable-iff-ker-trivial} has real content. -/)]
def IsObservable
    (A : Matrix (Fin n) (Fin n) 𝕜) (C : Matrix (Fin p) (Fin n) 𝕜) : Prop :=
  ∀ x : Fin n → 𝕜, (∀ k : Fin n, (C * A ^ (k : ℕ)) *ᵥ x = 0) → x = 0

end Semiring

section Hautus

variable {n p : ℕ}

/-- The unobservable subspace of `(A, C)`: states that the output `C · A^k`
fails to distinguish from zero for every `k = 0, …, n-1`.

Defined as the intersection of the kernels of the linear maps
`(C · A^k).mulVecLin` for `k : Fin n`. By Cayley–Hamilton (see
`A_mulVec_mem_unobservableSubspace_of_mem`) this submodule is `A`-invariant. -/
@[blueprint "def:unobservableSubspace"
  (statement := /-- The \emph{unobservable subspace} of $(A, C)$ is the
    $A$-invariant subspace
    \[
      \mathcal{N}(A, C) \;=\;
        \{\, v \in \mathbb{C}^{n} \;:\;
            C\, A^{k}\, v = 0 \text{ for every } k = 0, 1, \dots, n - 1 \,\}.
    \]
    Equivalently, $\mathcal{N}(A, C) = \ker \mathcal{O}(A, C)$, but here it
    is phrased without naming $\mathcal{O}$ so the bridge
    \cref{thm:unobservable-eq-bot-iff-observable} reads as content. -/)]
noncomputable def unobservableSubspace
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    Submodule ℂ (Fin n → ℂ) :=
  ⨅ k : Fin n, LinearMap.ker (C * A ^ (k : ℕ)).mulVecLin

/-- The Hautus observability matrix at `μ`,
`[μ • 1 - A; C] : Matrix (Fin n ⊕ Fin p) (Fin n) ℂ`. -/
@[blueprint "def:hautusObservabilityMatrix"
  (statement := /-- The \emph{Hautus observability matrix} of $(A, C)$ at
    a complex number $\mu$ is the block-row matrix
    \[
      H_{A, C}(\mu) \;=\; \begin{bmatrix} \mu I - A \\ C \end{bmatrix}
        \in \mathbb{C}^{(n + p) \times n} .
    \] -/)]
noncomputable def hautusObservabilityMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ) :
    Matrix (Fin n ⊕ Fin p) (Fin n) ℂ :=
  Matrix.fromRows (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A) C

end Hautus

end LinearSystems

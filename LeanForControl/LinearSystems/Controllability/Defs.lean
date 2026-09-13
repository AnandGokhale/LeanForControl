import LeanForControl.LinearSystems.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.Complex.Basic
import Architect

/-!
# Definitions for controllability

Every `def`, `noncomputable def`, and predicate for the `Controllability` directory lives
here, apart from the theorems proved about them (`Controllability.lean`, `Reachability.lean`,
`Hautus.lean`), per the project convention: definitions live apart from theorems.

* `controllabilityMatrix`, `IsControllable` — the textbook controllability matrix and
  predicate, generic over a `Semiring 𝕜`.
* `reachableSubspace` — the reachable subspace as the range of the controllability matrix,
  `Field`-scoped since it needs `LinearMap.range`.
* `hautusControllabilityMatrix` — the Hautus/PBH matrix `[μI - A | B]`, `ℂ`-only since the
  Hautus development needs eigenvalues.
-/

namespace LinearSystems

open Matrix

section Semiring

variable {𝕜 : Type*} [Semiring 𝕜]
variable {n m : ℕ}

/-- The controllability matrix of `(A, B)`.

The `(k, j)`-th column is the `j`-th column of `Aᵏ · B`, where `k : Fin n`
ranges over `0, 1, …, n-1`. -/
@[blueprint "def:controllabilityMatrix"
  (statement := /-- The \emph{controllability matrix} of a pair $(A, B)$
    with $A \in \mathbb{F}^{n \times n}$ and $B \in \mathbb{F}^{n \times m}$
    is the block-column matrix
    \[
      \mathcal{C}(A, B) =
      \begin{bmatrix} B & A\, B & A^{2}\, B & \cdots & A^{n-1}\, B \end{bmatrix}
      \in \mathbb{F}^{n \times (n m)}.
    \]
    Columns are indexed by $\mathrm{Fin}\, n \times \mathrm{Fin}\, m$, so that
    $A^{k}$ is available without casting $k : \mathrm{Fin}\, n$ through
    $\mathrm{Fin.val}$. -/)]
def controllabilityMatrix
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    Matrix (Fin n) (Fin n × Fin m) 𝕜 :=
  Matrix.of fun i kj => (A ^ (kj.1 : ℕ) * B) i kj.2

/-- The textbook controllability predicate (existential reachability):
every state can be reached from the origin in `n` steps via some sequence
of inputs. Phrased in matrix-power language so the bridge theorem
`isControllable_iff_controllabilityMatrix_rank_eq` has real content. -/
@[blueprint "def:isControllable"
  (statement := /-- A linear system $(A, B)$ is \emph{controllable} when
    every target state $x \in \mathbb{F}^{n}$ is reachable from the origin
    in $n$ steps: there exist input vectors
    $u_{0}, u_{1}, \dots, u_{n-1} \in \mathbb{F}^{m}$ such that
    \[
      x = \sum_{k = 0}^{n-1} A^{k}\, B\, u_{k}.
    \]
    This phrasing does not name the controllability matrix, so the bridge
    \cref{thm:isControllable-iff-rank} has real content. -/)]
def IsControllable
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) : Prop :=
  ∀ x : Fin n → 𝕜, ∃ u : Fin n → (Fin m → 𝕜),
    x = ∑ k : Fin n, (A ^ (k : ℕ) * B) *ᵥ u k

end Semiring

section Field

variable {𝕜 : Type*} [Field 𝕜]
variable {n m : ℕ}

/-- The reachable subspace of `(A, B)`, defined as the range of the
finite-horizon controllability matrix.

Reference: Hespanha, *Linear Systems Theory*. -/
@[blueprint "def:reachableSubspace"
  (statement := /-- The reachable subspace of a pair $(A,B)$ is the column
    span of its controllability matrix:
    \[
      \mathcal R(A,B)=\operatorname{range}\mathcal C(A,B).
    \]
    Thus it is exactly the span of $B,AB,\ldots,A^{n-1}B$. -/)]
noncomputable def reachableSubspace
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    Submodule 𝕜 (Fin n → 𝕜) :=
  LinearMap.range (controllabilityMatrix A B).mulVecLin

end Field

section Hautus

variable {n m : ℕ}

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

end Hautus

end LinearSystems

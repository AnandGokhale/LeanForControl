import LeanForControl.LinearSystems.Basic
import LeanForControl.LinearSystems.MatrixLemmas
import Architect

/-!
# Observability of a finite-dimensional linear system

For a discrete- or continuous-time linear system

  ẋ = A x ,  y = C x

with `A : Matrix (Fin n) (Fin n) 𝕜` and `C : Matrix (Fin p) (Fin n) 𝕜`,
this file defines:

* `LinearSystems.observabilityMatrix A C`, the stacked block-row matrix
      [ C ; C·A ; C·A² ; ⋯ ; C·Aⁿ⁻¹ ]
  with row index `Fin n × Fin p` and column index `Fin n`;
* `LinearSystems.IsObservable A C`, the textbook condition that the only state
  annihilating `C·Aᵏ` for every `k = 0, …, n-1` is the zero state.

The milestone theorem is
`LinearSystems.isObservable_iff_observabilityMatrix_ker_trivial`, the bridge
between the two formulations: observability is exactly the triviality of the
kernel of the observability matrix acting by `*ᵥ`.
-/

namespace LinearSystems

open Matrix

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

/-- Block-row shape lemma: row `(k, i)` of the observability matrix at
column `j` is the `(i, j)` entry of `C · Aᵏ`. Holds definitionally. -/
@[simp, blueprint "lem:observabilityMatrix-apply"
  (statement := /-- Block-row entry shape: at row $(k, i)$ and column $j$,
    the observability matrix coincides with the $(i, j)$ entry of $C\, A^{k}$:
    \[
      \mathcal{O}(A, C)_{(k,i),\, j} = (C\, A^{k})_{i,\, j}.
    \] -/)
  (proof := /-- Holds definitionally by the encoding chosen for
    \cref{def:observabilityMatrix}. -/)]
lemma observabilityMatrix_apply
    (A : Matrix (Fin n) (Fin n) 𝕜) (C : Matrix (Fin p) (Fin n) 𝕜)
    (k : Fin n) (i : Fin p) (j : Fin n) :
    observabilityMatrix A C (k, i) j = (C * A ^ (k : ℕ)) i j :=
  rfl

/-- `mulVec` of the observability matrix at row `(k, i)` equals the `i`-th
coordinate of `(C · Aᵏ) *ᵥ x`. Holds definitionally and is the workhorse
behind the milestone theorem. -/
@[blueprint "lem:observabilityMatrix-mulVec-apply"
  (statement := /-- For every state $x \in \mathbb{F}^{n}$ and every
    $(k, i) \in \mathrm{Fin}\, n \times \mathrm{Fin}\, p$,
    \[
      \bigl(\mathcal{O}(A, C) \cdot x\bigr)_{(k, i)}
        = \bigl(C\, A^{k} \cdot x\bigr)_{i}.
    \]
    This is the definitional bridge that powers
    \cref{thm:isObservable-iff-ker-trivial}. -/)
  (proof := /-- Holds by definitional unfolding of $\mathcal{O}(A, C)$
    (see \cref{def:observabilityMatrix}). -/)]
lemma observabilityMatrix_mulVec_apply
    (A : Matrix (Fin n) (Fin n) 𝕜) (C : Matrix (Fin p) (Fin n) 𝕜)
    (x : Fin n → 𝕜) (k : Fin n) (i : Fin p) :
    (observabilityMatrix A C *ᵥ x) (k, i) = ((C * A ^ (k : ℕ)) *ᵥ x) i :=
  rfl

/-- **Milestone theorem.**

A finite-dimensional linear system `(A, C)` is observable in the textbook
sense (`IsObservable`) iff the observability matrix has trivial kernel under
`*ᵥ`. -/
@[blueprint "thm:isObservable-iff-ker-trivial"
  (statement := /-- A finite-dimensional linear system $(A, C)$ is observable
    in the sense of \cref{def:isObservable} if and only if the observability
    matrix $\mathcal{O}(A, C)$ has trivial kernel under matrix-vector
    multiplication:
    \[
      \mathrm{IsObservable}(A, C)
      \iff
      \bigl(\forall x,\ \mathcal{O}(A, C) \cdot x = 0 \Rightarrow x = 0\bigr).
    \] -/)
  (proof := /-- Both directions follow from the bridge
    \cref{lem:observabilityMatrix-mulVec-apply}, which identifies the
    $(k, i)$-coordinate of $\mathcal{O}(A, C) \cdot x$ with the
    $i$-coordinate of $(C\, A^{k}) \cdot x$. The forward direction reads
    the per-power kernel out of the assembled kernel coordinatewise; the
    reverse direction packs them back. -/)]
theorem isObservable_iff_observabilityMatrix_ker_trivial
    (A : Matrix (Fin n) (Fin n) 𝕜) (C : Matrix (Fin p) (Fin n) 𝕜) :
    IsObservable A C ↔
      ∀ x : Fin n → 𝕜, observabilityMatrix A C *ᵥ x = 0 → x = 0 := by
  constructor
  · -- (→) Observability implies trivial kernel of `observabilityMatrix`.
    intro hObs x hx
    refine hObs x ?_
    intro k
    funext i
    have hki : (observabilityMatrix A C *ᵥ x) (k, i) = 0 := congrFun hx (k, i)
    -- The bridge lemma identifies this coordinate with `((C · Aᵏ) *ᵥ x) i`.
    rw [observabilityMatrix_mulVec_apply] at hki
    simpa using hki
  · -- (←) Trivial kernel of `observabilityMatrix` implies observability.
    intro hKer x hx
    refine hKer x ?_
    funext ki
    obtain ⟨k, i⟩ := ki
    rw [observabilityMatrix_mulVec_apply]
    have hk : (C * A ^ (k : ℕ)) *ᵥ x = 0 := hx k
    -- Read off the `i`-th coordinate of the vanishing vector.
    have := congrFun hk i
    simpa using this

/-!
## Follow-ups for the Hautus track

The following helpers were not needed to prove
`isObservable_iff_observabilityMatrix_ker_trivial`, but will be needed before
attacking either Hautus or the rank-based reformulations:

* a rank-vs-trivial-kernel bridge for matrices of shape `Matrix (m × p) n 𝕜`,
  most naturally phrased through `Matrix.toLin'` and `LinearMap.ker`;
* block-matrix rank lemmas for stacked rows
  `[A₁ ; A₂ ; … ; Aₖ]`, lifting per-block kernels to the stack and back;
* a transition from `(C · Aᵏ) *ᵥ x = 0 ∀ k < n` to invariance of the
  unobservable subspace under `A` (Cayley–Hamilton style argument), needed
  to extract eigenvectors for the Hautus direction;
* coercion lemmas between `(C * A^k) *ᵥ x` and `C *ᵥ (A^k *ᵥ x)`, which
  are useful when restating observability in terms of trajectories rather
  than matrix powers.

These belong in `LinearSystems.MatrixLemmas` (matrix-level facts) and a future
`LinearSystems.Hautus` (control-level facts) once needed.
-/

end LinearSystems

/-!
## Rank-form characterization

We reopen `namespace LinearSystems` in a fresh section over `[Field 𝕜]` so
the typeclass diamond between the outer `[Semiring 𝕜]` (used for the
existing definitions and the kernel-form milestone) and the rank-side
`[Field 𝕜]` is broken: in the section below, the only scalar-typeclass on
`𝕜` is `Field`, and the `Semiring` derived from it is the canonical one,
matching the instance picked by `MatrixLemmas`.
-/

namespace LinearSystems

open Matrix

variable {𝕜 : Type*} [Field 𝕜] {n p : ℕ}

/-- Rank-form characterization: observability is equivalent to the
observability matrix having full column rank. Chains the kernel-form
milestone with the matrix bridge from `MatrixLemmas`. -/
@[blueprint "thm:isObservable-iff-rank"
  (statement := /-- A finite-dimensional system $(A, C)$ is observable if
    and only if the observability matrix $\mathcal{O}(A, C)$ has full column
    rank, i.e.
    \[
      \operatorname{rank} \mathcal{O}(A, C) = n,
    \]
    where $n$ is the state dimension. -/)
  (proof := /-- Chain the kernel-form milestone
    \cref{thm:isObservable-iff-ker-trivial} with the matrix-level bridge
    $\bigl(\forall x,\ M \cdot x = 0 \Rightarrow x = 0\bigr) \iff
     \operatorname{rank} M = n$ from `MatrixLemmas`, applied with
    $M = \mathcal{O}(A, C)$. -/)]
theorem isObservable_iff_observabilityMatrix_rank_eq
    (A : Matrix (Fin n) (Fin n) 𝕜) (C : Matrix (Fin p) (Fin n) 𝕜) :
    IsObservable A C ↔ Matrix.rank (observabilityMatrix A C) = n := by
  refine (isObservable_iff_observabilityMatrix_ker_trivial A C).trans ?_
  refine (LinearSystems.MatrixLemmas.mulVec_kernel_trivial_iff_rank_eq_card_cols
    (observabilityMatrix A C)).trans ?_
  rw [Fintype.card_fin]

end LinearSystems

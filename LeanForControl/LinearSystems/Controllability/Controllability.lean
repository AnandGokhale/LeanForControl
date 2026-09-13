import LeanForControl.LinearSystems.Controllability.Defs
import LeanForControl.MatrixAlgebra.Rank
import Architect

/-!
# Controllability of a finite-dimensional linear system

Theorems about the controllability matrix and predicate defined in
`LinearSystems.Controllability.Defs`: the block-column shape lemma, and the milestone
rank-form characterization of controllability.

This file deliberately stays at the *shape lemma + rank characterization* level: the
reachable-subspace theory lives in `Reachability.lean`, and the eigenvector/PBH
characterization lives in `Hautus.lean`. -/

namespace LinearSystems

open Matrix

variable {𝕜 : Type*} [Semiring 𝕜]
variable {n m : ℕ}

/-- Block-column shape lemma: the entry at row `i`, column `(k, j)` of the
controllability matrix is the `(i, j)` entry of `Aᵏ · B`. Holds
definitionally. -/
@[simp, blueprint "lem:controllabilityMatrix-apply"
  (statement := /-- Block-column entry shape: at row $i$ and column $(k, j)$,
    the controllability matrix coincides with the $(i, j)$ entry of $A^{k}\, B$:
    \[
      \mathcal{C}(A, B)_{i,\, (k, j)} = (A^{k}\, B)_{i,\, j}.
    \] -/)
  (proof := /-- Holds definitionally by the encoding chosen for
    \cref{def:controllabilityMatrix}. -/)]
lemma controllabilityMatrix_apply
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (i : Fin n) (k : Fin n) (j : Fin m) :
    controllabilityMatrix A B i (k, j) = (A ^ (k : ℕ) * B) i j :=
  rfl

end LinearSystems

/-!
## Rank-form characterization

Reopened namespace over `[Field 𝕜]` only, breaking the typeclass diamond
between the outer `[Semiring 𝕜]` and the rank-side `[Field 𝕜]`. -/

namespace LinearSystems

open Matrix

variable {𝕜 : Type*} [Field 𝕜] {n m : ℕ}

/-- The matrix-vector product of the controllability matrix with a vector
indexed by `Fin n × Fin m` rewrites as a sum of per-power matrix-vector
products with curried inputs. Bridge between the assembled-matrix form and
the matrix-power-sum form of `IsControllable`, and reused by the reachable-
subspace development in `LinearSystems.Controllability.Reachability`. -/
lemma controllabilityMatrix_mulVec_eq_sum
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (u : Fin n × Fin m → 𝕜) :
    controllabilityMatrix A B *ᵥ u
      = ∑ k : Fin n, (A ^ (k : ℕ) * B) *ᵥ (fun j => u (k, j)) := by
  funext i
  rw [Finset.sum_apply]
  change ∑ kj : Fin n × Fin m, controllabilityMatrix A B i kj * u kj
        = ∑ k : Fin n, ((A ^ (k : ℕ) * B) *ᵥ (fun j => u (k, j))) i
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [controllabilityMatrix_apply, Matrix.mulVec, dotProduct]

/-- `IsControllable` reformulated in the assembled-matrix form: the
controllability matrix's `*ᵥ` action is surjective onto the state space. -/
private lemma isControllable_iff_controllabilityMatrix_mulVec_surjective
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    IsControllable A B
      ↔ ∀ x : Fin n → 𝕜, ∃ u : Fin n × Fin m → 𝕜,
          controllabilityMatrix A B *ᵥ u = x := by
  unfold IsControllable
  constructor
  · intro h x
    obtain ⟨u', hu'⟩ := h x
    refine ⟨fun kj => u' kj.1 kj.2, ?_⟩
    rw [controllabilityMatrix_mulVec_eq_sum]
    exact hu'.symm
  · intro h x
    obtain ⟨u, hu⟩ := h x
    refine ⟨fun k j => u (k, j), ?_⟩
    rw [← hu, controllabilityMatrix_mulVec_eq_sum]

/-- Rank-form characterization: controllability is equivalent to the
controllability matrix having full row rank. -/
@[blueprint "thm:isControllable-iff-rank"
  (statement := /-- A linear system $(A, B)$ is controllable if and only
    if the controllability matrix has full row rank,
    \[
      \operatorname{rank} \mathcal{C}(A, B) = n,
    \]
    where $n$ is the state dimension. -/)
  (proof := /-- Combine the reindexing identity
    $\mathcal{C}(A, B) \cdot u
       = \sum_{k} A^{k} B \cdot u_{k}$
    (with $u_{k}(j) = u(k, j)$) with the matrix-level bridge
    $\bigl(\forall y,\ \exists x,\ M\, x = y\bigr) \iff
     \operatorname{rank} M = n$ from `MatrixAlgebra.Rank`, applied with
    $M = \mathcal{C}(A, B)$. -/)]
theorem isControllable_iff_controllabilityMatrix_rank_eq
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    IsControllable A B ↔ Matrix.rank (controllabilityMatrix A B) = n := by
  refine (isControllable_iff_controllabilityMatrix_mulVec_surjective A B).trans ?_
  refine (MatrixAlgebra.mulVec_range_top_iff_rank_eq_card_rows
    (controllabilityMatrix A B)).trans ?_
  rw [Fintype.card_fin]

end LinearSystems

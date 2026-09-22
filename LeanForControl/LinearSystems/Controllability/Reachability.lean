import LeanForControl.LinearSystems.Controllability.Defs
import LeanForControl.LinearSystems.Controllability.Controllability
import LeanForControl.MatrixAlgebra.Rank
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Architect

/-!
# Reachable subspaces of finite-dimensional linear systems

This file characterizes the reachable subspace through the finite-horizon
controllability matrix and proves its invariance under the state matrix. The
`A ^ n` boundary term in the invariance proof is closed by Cayley--Hamilton.

References:
* João P. Hespanha, *Linear Systems Theory*.
* R. E. Kalman, “Mathematical Description of Linear Dynamical Systems,”
  *Journal of the Society for Industrial and Applied Mathematics, Series A:
  Control* 1(2), 152–192, 1963. DOI: 10.1137/0301010.
* Kailath, *Linear Systems*.
-/

namespace LinearSystems

open Matrix

variable {𝕜 : Type*} [Field 𝕜]
variable {n m : ℕ}

/-- A state vector `x` belongs to `reachableSubspace A B` exactly when it is
the product of `controllabilityMatrix A B` with a vector indexed by
`Fin n × Fin m`.

Original: formalization infrastructure for LeanForControl. -/
@[blueprint "lem:mem-reachableSubspace-iff"
  (statement := /-- Let $A\in\mathbb{F}^{n\times n}$ and
    $B\in\mathbb{F}^{n\times m}$, and let
    $\mathcal C(A,B)\in\mathbb{F}^{n\times(nm)}$ be their controllability
    matrix. For $x\in\mathbb{F}^n$,
    \[
      x\in\mathcal R(A,B)
      \quad\Longleftrightarrow\quad
      \exists u:\operatorname{Fin}(n)\times\operatorname{Fin}(m)
        \to\mathbb{F},\qquad \mathcal C(A,B)u=x.
    \]
    Here $\mathcal R(A,B)=\operatorname{range}\mathcal C(A,B)$ is the
    reachable subspace. -/)]
lemma mem_reachableSubspace_iff
    {A : Matrix (Fin n) (Fin n) 𝕜} {B : Matrix (Fin n) (Fin m) 𝕜}
    (x : Fin n → 𝕜) :
    x ∈ reachableSubspace A B ↔
      ∃ u : Fin n × Fin m → 𝕜, controllabilityMatrix A B *ᵥ u = x := by
  simp [reachableSubspace, LinearMap.mem_range]

/-- Every individual finite-horizon input response belongs to the reachable
subspace.

Original: formalization infrastructure for LeanForControl. -/
lemma finiteHorizonResponse_mem_reachableSubspace
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (k : Fin n) (u : Fin m → 𝕜) :
    (A ^ (k : ℕ) * B) *ᵥ u ∈ reachableSubspace A B := by
  rw [mem_reachableSubspace_iff]
  classical
  refine ⟨fun kj => if kj.1 = k then u kj.2 else 0, ?_⟩
  rw [controllabilityMatrix_mulVec_eq_sum]
  rw [Fintype.sum_eq_single k]
  · simp
  · intro k' hk'
    simp only [hk', if_false]
    change (A ^ (k' : ℕ) * B) *ᵥ (0 : Fin m → 𝕜) = 0
    exact Matrix.mulVec_zero _

/-- The reachable subspace is exactly the supremum of the ranges of the
finite-horizon maps `A^k B`.

Original: formalization infrastructure for LeanForControl. -/
theorem reachableSubspace_eq_iSup_range
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    reachableSubspace A B =
      ⨆ k : Fin n, LinearMap.range (A ^ (k : ℕ) * B).mulVecLin := by
  apply le_antisymm
  · rintro x hx
    rw [mem_reachableSubspace_iff] at hx
    obtain ⟨u, rfl⟩ := hx
    rw [controllabilityMatrix_mulVec_eq_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    apply Submodule.mem_iSup_of_mem k
    exact ⟨fun j => u (k, j), rfl⟩
  · refine iSup_le fun k => ?_
    rintro x ⟨u, rfl⟩
    exact finiteHorizonResponse_mem_reachableSubspace A B k u

/-- The image of the input matrix is contained in the reachable subspace.

Reference: Hespanha, *Linear Systems Theory*. -/
theorem range_B_le_reachableSubspace
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    LinearMap.range B.mulVecLin ≤ reachableSubspace A B := by
  rintro x ⟨u, rfl⟩
  by_cases hn : n = 0
  · subst n
    have : B *ᵥ u = 0 := Subsingleton.elim _ _
    change B *ᵥ u ∈ reachableSubspace A B
    rw [this]
    exact Submodule.zero_mem _
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    simpa using
      finiteHorizonResponse_mem_reachableSubspace A B (⟨0, hnpos⟩ : Fin n) u

/-- The system is controllable exactly when its reachable subspace is the
whole state space.

Reference: Hespanha, *Linear Systems Theory*. -/
@[blueprint "thm:reachableSubspace-eq-top-iff-controllable"
  (statement := /-- A pair $(A,B)$ is controllable if and only if its
    reachable subspace is the whole state space. -/)]
theorem reachableSubspace_eq_top_iff_isControllable
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    reachableSubspace A B = ⊤ ↔ IsControllable A B := by
  rw [isControllable_iff_controllabilityMatrix_rank_eq]
  unfold reachableSubspace
  rw [LinearMap.range_eq_top]
  simpa using
    (MatrixAlgebra.mulVec_range_top_iff_rank_eq_card_rows
      (controllabilityMatrix A B))

/-- Cayley--Hamilton closes the single boundary term needed for reachable
subspace invariance. -/
private lemma cayleyHamilton_boundary_mem_reachableSubspace
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (u : Fin m → 𝕜) :
    (A ^ n * B) *ᵥ u ∈ reachableSubspace A B := by
  have hCH := Matrix.aeval_self_charpoly A
  have h_apply : (Polynomial.aeval A A.charpoly * B) *ᵥ u = 0 := by
    rw [hCH, Matrix.zero_mul, Matrix.zero_mulVec]
  have hdeg : A.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [Polynomial.aeval_eq_sum_range, hdeg, Finset.sum_range_succ] at h_apply
  have hmonic : A.charpoly.coeff n = 1 := by
    have hL := A.charpoly_monic
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg] at hL
    exact hL
  rw [hmonic, one_smul, Matrix.add_mul, Matrix.add_mulVec] at h_apply
  have hsum :
      ((∑ i ∈ Finset.range n, A.charpoly.coeff i • A ^ i) * B) *ᵥ u ∈
        reachableSubspace A B := by
    rw [Matrix.sum_mul, Matrix.sum_mulVec]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Matrix.smul_mul, Matrix.smul_mulVec]
    exact Submodule.smul_mem _ _
      (finiteHorizonResponse_mem_reachableSubspace A B ⟨i, hi⟩ u)
  have htarget :
      (A ^ n * B) *ᵥ u =
        -(((∑ i ∈ Finset.range n, A.charpoly.coeff i • A ^ i) * B) *ᵥ u) := by
    exact eq_neg_of_add_eq_zero_right h_apply
  rw [htarget]
  exact Submodule.neg_mem _ hsum

/-- The finite-horizon reachable subspace is invariant under the state
matrix.  The highest-power case is discharged by Cayley--Hamilton.

Reference: Hespanha, *Linear Systems Theory*. -/
@[blueprint "lem:reachableSubspace-invariant"
  (statement := /-- The reachable subspace is $A$-invariant:
    $A\mathcal R(A,B)\subseteq\mathcal R(A,B)$. -/)]
theorem reachableSubspace_invariant
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    reachableSubspace A B ∈ Module.End.invtSubmodule A.mulVecLin := by
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  intro x hx
  rw [mem_reachableSubspace_iff] at hx
  obtain ⟨u, rfl⟩ := hx
  rw [controllabilityMatrix_mulVec_eq_sum, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ']
  by_cases hk : k.val + 1 < n
  · exact finiteHorizonResponse_mem_reachableSubspace A B ⟨k.val + 1, hk⟩
      (fun j => u (k, j))
  · push Not at hk
    have heq : k.val + 1 = n := by omega
    rw [heq]
    exact cayleyHamilton_boundary_mem_reachableSubspace A B (fun j => u (k, j))

end LinearSystems

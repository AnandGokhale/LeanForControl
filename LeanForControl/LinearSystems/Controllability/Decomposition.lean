import LeanForControl.LinearSystems.Controllability.DefsDecomposition

/-!
# The standalone controllable decomposition

The reachable subspace is invariant under the state map and contains the
input range.  This file proves that the induced pair on that canonical
subspace is genuinely controllable, first by its invariant-subspace
universal property and then in terms of the library's `IsControllable`
predicate after choosing a finite basis.

Reference: Hespanha, *Linear Systems Theory*.
-/

namespace LinearSystems

open Matrix

variable {n m : ℕ}

/-- Coercing the restricted state map back to the ambient state space
recovers multiplication by `A`.

Original: coordinate infrastructure for LeanForControl. -/
@[simp] lemma reachableStateMap_coe
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (x : reachableSubspace A B) :
    (reachableStateMap A B x : Fin n → ℂ) = A *ᵥ (x : Fin n → ℂ) := rfl

/-- Coercing the restricted input map back to the ambient state space
recovers multiplication by `B`.

Original: coordinate infrastructure for LeanForControl. -/
@[simp] lemma reachableInputMap_coe
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (u : Fin m → ℂ) :
    (reachableInputMap A B u : Fin n → ℂ) = B *ᵥ u := rfl

/-- Powers of the restricted state map agree with ambient powers of `A`.

Original: coordinate infrastructure for LeanForControl. -/
lemma reachableStateMap_pow_coe
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (k : ℕ) (x : reachableSubspace A B) :
    (((reachableStateMap A B) ^ k) x : Fin n → ℂ) =
      A ^ k *ᵥ (x : Fin n → ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, reachableStateMap_coe, ih]
      calc
        A *ᵥ (A ^ k *ᵥ (x : Fin n → ℂ)) =
            (A * A ^ k) *ᵥ (x : Fin n → ℂ) :=
          Matrix.mulVec_mulVec (x : Fin n → ℂ) A (A ^ k)
        _ = A ^ (k + 1) *ᵥ (x : Fin n → ℂ) := by rw [← pow_succ']

/-- Universal-property form of controllability for the restricted reachable
pair: every invariant subspace containing its input range is the whole
reachable state space.

Reference: Hespanha, *Linear Systems Theory*. -/
@[blueprint "thm:reachable-restriction-controllable-invariant"
  (statement := /-- The state and input maps restricted to the reachable
    subspace form a controllable pair: no proper invariant subspace contains
    the restricted input range. -/)]
theorem reachableStateMap_controllable
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    ∀ S : Submodule ℂ (reachableSubspace A B),
      LinearMap.range (reachableInputMap A B) ≤ S →
      S ∈ Module.End.invtSubmodule (reachableStateMap A B) → S = ⊤ := by
  intro S hB hA
  rw [eq_top_iff]
  intro x _
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hA
  have hpow : ∀ k : ℕ, ∀ u : Fin m → ℂ,
      ((reachableStateMap A B) ^ k) (reachableInputMap A B u) ∈ S := by
    intro k u
    induction k with
    | zero => simpa using hB ⟨u, rfl⟩
    | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact hA _ ih
  obtain ⟨u, hu⟩ := (mem_reachableSubspace_iff (x : Fin n → ℂ)).mp x.2
  have hx : x = ∑ k : Fin n,
      ((reachableStateMap A B) ^ (k : ℕ))
        (reachableInputMap A B (fun j => u (k, j))) := by
    apply Subtype.ext
    rw [← hu, controllabilityMatrix_mulVec_eq_sum]
    simp only [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [reachableStateMap_pow_coe, reachableInputMap_coe,
      ← Matrix.mulVec_mulVec]
  rw [hx]
  exact Submodule.sum_mem S fun k _ => hpow k _

/-- The restricted state matrix acts on basis coordinates exactly as the
restricted state map.

Original: coordinate infrastructure for LeanForControl. -/
lemma reachableStateMatrix_mulVec_coordinates
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (x : reachableSubspace A B) :
    reachableStateMatrix A B *ᵥ (reachableStateBasis A B).equivFun x =
      (reachableStateBasis A B).equivFun (reachableStateMap A B x) := by
  simpa [reachableStateMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (reachableStateBasis A B)
      (reachableStateBasis A B) (reachableStateMap A B) x

/-- The restricted input matrix acts on standard input coordinates exactly
as the restricted input map.

Original: coordinate infrastructure for LeanForControl. -/
lemma reachableInputMatrix_mulVec_coordinates
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (u : Fin m → ℂ) :
    reachableInputMatrix A B *ᵥ u =
      (reachableStateBasis A B).equivFun (reachableInputMap A B u) := by
  simpa [reachableInputMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℂ (Fin m))
      (reachableStateBasis A B) (reachableInputMap A B) u

/-- The finite matrix pair representing the canonical reachable restriction
is controllable in the library's textbook sense.

Reference: Hespanha, *Linear Systems Theory*. -/
@[blueprint "thm:reachable-matrices-controllable"
  (statement := /-- In any finite basis of the reachable subspace, the
    restricted state and input matrices form a controllable pair. -/)]
theorem reachableMatrices_isControllable
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    IsControllable (reachableStateMatrix A B) (reachableInputMatrix A B) := by
  rw [← reachableSubspace_eq_top_iff_isControllable]
  let S := reachableSubspace (reachableStateMatrix A B) (reachableInputMatrix A B)
  let T := S.comap (reachableStateBasis A B).equivFun.toLinearMap
  have hB : LinearMap.range (reachableInputMap A B) ≤ T := by
    rintro x ⟨u, rfl⟩
    change (reachableStateBasis A B).equivFun (reachableInputMap A B u) ∈ S
    rw [← reachableInputMatrix_mulVec_coordinates]
    exact range_B_le_reachableSubspace _ _ ⟨u, rfl⟩
  have hA : T ∈ Module.End.invtSubmodule (reachableStateMap A B) := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    change (reachableStateBasis A B).equivFun (reachableStateMap A B x) ∈ S
    rw [← reachableStateMatrix_mulVec_coordinates]
    exact reachableSubspace_invariant _ _ hx
  have hT : T = ⊤ := reachableStateMap_controllable A B T hB hA
  rw [eq_top_iff]
  intro z hz
  let x := (reachableStateBasis A B).equivFun.symm z
  have hx : x ∈ T := by rw [hT]; trivial
  change (reachableStateBasis A B).equivFun x ∈ S at hx
  change (reachableStateBasis A B).equivFun
      ((reachableStateBasis A B).equivFun.symm z) ∈ S at hx
  simpa only [LinearEquiv.apply_symm_apply] using hx

end LinearSystems

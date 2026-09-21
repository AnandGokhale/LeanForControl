import LeanForControl.LinearSystems.Observability.DefsDecomposition

/-!
# The standalone observable decomposition

The unobservable subspace is the largest invariant subspace contained in the
kernel of the output map.  Quotienting by it therefore gives a genuinely
observable pair.  This file proves that semantic universal property and its
matrix formulation through the existing `IsObservable` predicate.

Reference: Hespanha, *Linear Systems Theory*.
-/

namespace LinearSystems

open Matrix

variable {n p : ℕ}

/-- The unobservable subspace lies in the kernel of the output map, including
when the state dimension is zero.

Reference: Hespanha, *Linear Systems Theory*. -/
lemma unobservableSubspace_le_ker_C
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    unobservableSubspace A C ≤ LinearMap.ker C.mulVecLin := by
  intro x hx
  rw [LinearMap.mem_ker]
  by_cases hn : n = 0
  · subst n
    have hx0 : x = 0 := Subsingleton.elim _ _
    rw [hx0, map_zero]
  · have h0 :=
      (mem_unobservableSubspace_iff x).mp hx ⟨0, Nat.pos_of_ne_zero hn⟩
    simpa using h0

/-- The unobservable subspace is the largest `A`-invariant subspace contained
in the kernel of `C`.

Reference: Hespanha, *Linear Systems Theory*. -/
@[blueprint "thm:unobservableSubspace-greatest-invariant"
  (statement := /-- Every $A$-invariant subspace contained in $\ker C$ is
    contained in the unobservable subspace. -/)]
theorem le_unobservableSubspace_of_invariant_of_le_ker
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    (S : Submodule ℂ (Fin n → ℂ))
    (hA : S ∈ Module.End.invtSubmodule A.mulVecLin)
    (hC : S ≤ LinearMap.ker C.mulVecLin) :
    S ≤ unobservableSubspace A C := by
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hA
  intro x hx
  rw [mem_unobservableSubspace_iff]
  intro k
  have hpow : ∀ j : ℕ, A ^ j *ᵥ x ∈ S := by
    intro j
    induction j with
    | zero => simpa using hx
    | succ j ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec]
        exact hA _ ih
  have hzero := hC (hpow k)
  rw [LinearMap.mem_ker] at hzero
  rw [← Matrix.mulVec_mulVec]
  exact hzero

/-- Universal-property form of observability for the quotient pair: its only
invariant subspace contained in the induced output kernel is zero.

Reference: Hespanha, *Linear Systems Theory*. -/
@[blueprint "thm:observable-quotient-observable-invariant"
  (statement := /-- The state and output maps induced on the quotient by the
    unobservable subspace form an observable pair. -/)]
theorem observableStateMap_observable
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    ∀ S : Submodule ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C),
      S ∈ Module.End.invtSubmodule (observableStateMap A C) →
      S ≤ LinearMap.ker (observableOutputMap A C) → S = ⊥ := by
  intro S hA hC
  let T := S.comap (unobservableSubspace A C).mkQ
  have hTA : T ∈ Module.End.invtSubmodule A.mulVecLin := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hA ⊢
    intro x hx
    change observableStateMap A C ((unobservableSubspace A C).mkQ x) ∈ S
    exact hA _ hx
  have hTC : T ≤ LinearMap.ker C.mulVecLin := by
    intro x hx
    rw [LinearMap.mem_ker]
    have hout := hC hx
    rw [LinearMap.mem_ker] at hout
    simpa [observableOutputMap, Submodule.liftQ_apply] using hout
  have hT := le_unobservableSubspace_of_invariant_of_le_ker A C T hTA hTC
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := (unobservableSubspace A C).mkQ_surjective q
  have hxT : x ∈ T := hq
  have hxN := hT hxT
  exact (Submodule.Quotient.mk_eq_zero _).mpr hxN

/-- The observable quotient state matrix acts on basis coordinates exactly
as the induced quotient state map.

Original: coordinate infrastructure for LeanForControl. -/
lemma observableStateMatrix_mulVec_coordinates
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    (x : (Fin n → ℂ) ⧸ unobservableSubspace A C) :
    observableStateMatrix A C *ᵥ (observableStateBasis A C).equivFun x =
      (observableStateBasis A C).equivFun (observableStateMap A C x) := by
  simpa [observableStateMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (observableStateBasis A C)
      (observableStateBasis A C) (observableStateMap A C) x

/-- The observable quotient output matrix acts on basis coordinates exactly
as the induced quotient output map.

Original: coordinate infrastructure for LeanForControl. -/
lemma observableOutputMatrix_mulVec_coordinates
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    (x : (Fin n → ℂ) ⧸ unobservableSubspace A C) :
    observableOutputMatrix A C *ᵥ (observableStateBasis A C).equivFun x =
      observableOutputMap A C x := by
  simpa [observableOutputMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (observableStateBasis A C)
      (Pi.basisFun ℂ (Fin p)) (observableOutputMap A C) x

/-- The finite matrix pair representing the quotient by the unobservable
subspace is observable in the library's textbook sense.

Reference: Hespanha, *Linear Systems Theory*. -/
@[blueprint "thm:observable-matrices-observable"
  (statement := /-- In any finite basis of the quotient by the unobservable
    subspace, the induced state and output matrices form an observable pair. -/)]
theorem observableMatrices_isObservable
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    IsObservable (observableStateMatrix A C) (observableOutputMatrix A C) := by
  rw [← unobservableSubspace_eq_bot_iff_isObservable]
  let U := unobservableSubspace (observableStateMatrix A C) (observableOutputMatrix A C)
  let S := U.comap (observableStateBasis A C).equivFun.toLinearMap
  have hA : S ∈ Module.End.invtSubmodule (observableStateMap A C) := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    change (observableStateBasis A C).equivFun (observableStateMap A C x) ∈ U
    rw [← observableStateMatrix_mulVec_coordinates]
    exact A_mulVec_mem_unobservableSubspace_of_mem hx
  have hC : S ≤ LinearMap.ker (observableOutputMap A C) := by
    intro x hx
    rw [LinearMap.mem_ker]
    rw [← observableOutputMatrix_mulVec_coordinates]
    by_cases hq :
        Module.finrank ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C) = 0
    · have hz : (observableStateBasis A C).equivFun x = 0 := by
        ext i
        exact Fin.elim0 (hq ▸ i)
      rw [hz, Matrix.mulVec_zero]
    · have hzero := (mem_unobservableSubspace_iff
        ((observableStateBasis A C).equivFun x)).mp hx
        (⟨0, Nat.pos_of_ne_zero hq⟩ :
          Fin (Module.finrank ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C)))
      simpa using hzero
  have hS : S = ⊥ := observableStateMap_observable A C S hA hC
  rw [eq_bot_iff]
  intro z hz
  let x := (observableStateBasis A C).equivFun.symm z
  have hx : x ∈ S := by
    change (observableStateBasis A C).equivFun x ∈ U
    change (observableStateBasis A C).equivFun
      ((observableStateBasis A C).equivFun.symm z) ∈ U
    simpa only [LinearEquiv.apply_symm_apply] using hz
  rw [hS] at hx
  have hx0 : x = 0 := hx
  calc
    z = (observableStateBasis A C).equivFun x := by
      exact ((observableStateBasis A C).equivFun.apply_symm_apply z).symm
    _ = 0 := by rw [hx0, map_zero]

end LinearSystems

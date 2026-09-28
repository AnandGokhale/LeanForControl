import LeanForControl.LinearSystems.Observability.DefsDecomposition

/-!
# Observability of the observable component

The state and output maps induced on the quotient by the unobservable
subspace give an observable matrix pair. The quotient represents the
observable component of Hespanha's observable decomposition; it does not
choose a complementary subspace in the original state space.

The scalar field is `ℂ` because the upstream `unobservableSubspace` and
its invariance theorem are currently defined over `ℂ`.

Reference: Hespanha, *Linear Systems Theory*, observable decomposition.
-/

namespace LinearSystems

open Matrix

variable {n p : ℕ}

/-- An invariant subspace of the quotient contained in the induced
output kernel is zero.

Original: quotient form of the largest-invariant-subspace characterization. -/
private theorem observable_invariant_eq_bot
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
private lemma observableStateMatrix_mulVec_coordinates
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    (x : (Fin n → ℂ) ⧸ unobservableSubspace A C) :
    observableStateMatrix A C *ᵥ
        (Module.finBasis ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C)).equivFun x =
      (Module.finBasis ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C)).equivFun
        (observableStateMap A C x) := by
  simpa [observableStateMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (Module.finBasis ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C))
      (Module.finBasis ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C)) (observableStateMap A C) x

/-- The observable quotient output matrix acts on basis coordinates exactly
as the induced quotient output map.

Original: coordinate infrastructure for LeanForControl. -/
private lemma observableOutputMatrix_mulVec_coordinates
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    (x : (Fin n → ℂ) ⧸ unobservableSubspace A C) :
    observableOutputMatrix A C *ᵥ
        (Module.finBasis ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C)).equivFun x =
      observableOutputMap A C x := by
  simpa [observableOutputMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (Module.finBasis ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C))
      (Pi.basisFun ℂ (Fin p)) (observableOutputMap A C) x

/-- The matrices of the observable component form an observable pair.

Equivalent formulation of the observable-component conclusion in Hespanha,
*Linear Systems Theory*, observable decomposition. The quotient matrices
use the chosen basis `Module.finBasis`. -/
@[blueprint "thm:observable-matrices-observable"
  (statement := /-- Let $A_o,C_o$ be the matrices of the induced maps
    (\cref{def:observable-state-map,def:observable-output-map}) in the chosen
    finite basis of $\mathbb C^n/\mathcal N(A,C)$. Then $(A_o,C_o)$ is observable
    in the sense of \cref{def:isObservable}. -/)]
theorem observableMatrices_isObservable
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    IsObservable (observableStateMatrix A C) (observableOutputMatrix A C) := by
  let b := Module.finBasis ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C)
  rw [← unobservableSubspace_eq_bot_iff_isObservable]
  let U := unobservableSubspace (observableStateMatrix A C) (observableOutputMatrix A C)
  let S := U.comap b.equivFun.toLinearMap
  have hA : S ∈ Module.End.invtSubmodule (observableStateMap A C) := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    change b.equivFun (observableStateMap A C x) ∈ U
    rw [← observableStateMatrix_mulVec_coordinates]
    exact A_mulVec_mem_unobservableSubspace_of_mem hx
  have hC : S ≤ LinearMap.ker (observableOutputMap A C) := by
    intro x hx
    rw [LinearMap.mem_ker]
    rw [← observableOutputMatrix_mulVec_coordinates]
    exact unobservableSubspace_le_ker_C _ _ hx
  have hS : S = ⊥ := observable_invariant_eq_bot A C S hA hC
  rw [eq_bot_iff]
  intro z hz
  let x := b.equivFun.symm z
  have hx : x ∈ S := by
    change b.equivFun x ∈ U
    change b.equivFun
      (b.equivFun.symm z) ∈ U
    simpa only [LinearEquiv.apply_symm_apply] using hz
  rw [hS] at hx
  have hx0 : x = 0 := hx
  calc
    z = b.equivFun x := by
      exact (b.equivFun.apply_symm_apply z).symm
    _ = 0 := by rw [hx0, map_zero]

end LinearSystems

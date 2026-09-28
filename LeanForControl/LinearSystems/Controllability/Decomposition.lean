import LeanForControl.LinearSystems.Controllability.DefsDecomposition

/-!
# Controllability of the controllable component

The state and input maps restricted to the reachable subspace give a
controllable matrix pair. This is the controllable-component conclusion
of Hespanha's controllable decomposition, expressed without choosing a
complement in the original state space.

`IsControllable` uses finite input responses from the origin. The argument
is algebraic over a field and does not require the state matrix to be invertible.

Reference: Hespanha, *Linear Systems Theory*, controllable decomposition.
-/

namespace LinearSystems

open Matrix

variable {𝕜 : Type*} [Field 𝕜] {n m : ℕ}

/-- An invariant subspace of the restricted state space containing the
restricted input range is the whole space.

Original: restriction of the ambient smallest-invariant-subspace characterization. -/
private theorem reachable_invariant_eq_top
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    ∀ S : Submodule 𝕜 (reachableSubspace A B),
      LinearMap.range (reachableInputMap A B) ≤ S →
      S ∈ Module.End.invtSubmodule (reachableStateMap A B) → S = ⊤ := by
  intro S hB hA
  let T := S.map (reachableSubspace A B).subtype
  have hTA : T ∈ Module.End.invtSubmodule A.mulVecLin := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hA ⊢
    rintro x ⟨y, hy, rfl⟩
    exact ⟨reachableStateMap A B y, hA _ hy, rfl⟩
  have hTB : LinearMap.range B.mulVecLin ≤ T := by
    rintro x ⟨u, rfl⟩
    exact ⟨reachableInputMap A B u, hB ⟨u, rfl⟩, rfl⟩
  have hR := reachableSubspace_le_of_invariant_of_range_le A B T hTA hTB
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hxy⟩ := hR x.property
  have hyx : y = x := Subtype.ext hxy
  simpa only [hyx] using hy

/-- The restricted state matrix acts on basis coordinates exactly as the
restricted state map.

Original: coordinate infrastructure for LeanForControl. -/
private lemma reachableStateMatrix_mulVec_coordinates
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (x : reachableSubspace A B) :
    reachableStateMatrix A B *ᵥ (Module.finBasis 𝕜 (reachableSubspace A B)).equivFun x =
      (Module.finBasis 𝕜 (reachableSubspace A B)).equivFun (reachableStateMap A B x) := by
  simpa [reachableStateMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (Module.finBasis 𝕜 (reachableSubspace A B))
      (Module.finBasis 𝕜 (reachableSubspace A B)) (reachableStateMap A B) x

/-- The restricted input matrix acts on standard input coordinates exactly
as the restricted input map.

Original: coordinate infrastructure for LeanForControl. -/
private lemma reachableInputMatrix_mulVec_coordinates
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (u : Fin m → 𝕜) :
    reachableInputMatrix A B *ᵥ u =
      (Module.finBasis 𝕜 (reachableSubspace A B)).equivFun (reachableInputMap A B u) := by
  simpa [reachableInputMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (Pi.basisFun 𝕜 (Fin m))
      (Module.finBasis 𝕜 (reachableSubspace A B)) (reachableInputMap A B) u

/-- The matrices of the controllable component form a controllable pair.

Reference: Hespanha, *Linear Systems Theory*, controllable decomposition.
This is the component conclusion in the chosen basis `Module.finBasis`,
not a statement constructing an ambient similarity transformation. -/
@[blueprint "thm:reachable-matrices-controllable"
  (statement := /-- Let $A_c,B_c$ be the matrices of the restricted maps
    (\cref{def:reachable-state-map,def:reachable-input-map}) in the chosen
    finite basis of $\mathcal R(A,B)$. Then $(A_c,B_c)$ is controllable
    in the sense of \cref{def:isControllable}. -/)]
theorem reachableMatrices_isControllable
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    IsControllable (reachableStateMatrix A B) (reachableInputMatrix A B) := by
  let b := Module.finBasis 𝕜 (reachableSubspace A B)
  rw [← reachableSubspace_eq_top_iff_isControllable]
  let S := reachableSubspace (reachableStateMatrix A B) (reachableInputMatrix A B)
  let T := S.comap b.equivFun.toLinearMap
  have hB : LinearMap.range (reachableInputMap A B) ≤ T := by
    rintro x ⟨u, rfl⟩
    change b.equivFun (reachableInputMap A B u) ∈ S
    rw [← reachableInputMatrix_mulVec_coordinates]
    exact range_B_le_reachableSubspace _ _ ⟨u, rfl⟩
  have hA : T ∈ Module.End.invtSubmodule (reachableStateMap A B) := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    change b.equivFun (reachableStateMap A B x) ∈ S
    rw [← reachableStateMatrix_mulVec_coordinates]
    exact reachableSubspace_invariant _ _ hx
  have hT : T = ⊤ := reachable_invariant_eq_top A B T hB hA
  rw [eq_top_iff]
  intro z hz
  let x := b.equivFun.symm z
  have hx : x ∈ T := by rw [hT]; trivial
  change b.equivFun x ∈ S at hx
  change b.equivFun
      (b.equivFun.symm z) ∈ S at hx
  simpa only [LinearEquiv.apply_symm_apply] using hx

end LinearSystems

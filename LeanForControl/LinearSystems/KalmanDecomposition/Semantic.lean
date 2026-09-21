import LeanForControl.LinearSystems.KalmanDecomposition.DefsSemantic
import LeanForControl.LinearSystems.KalmanDecomposition.Dimensions
import LeanForControl.LinearSystems.Controllability.Decomposition
import LeanForControl.LinearSystems.Observability.Decomposition
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Architect

/-!
# Semantic Kalman decomposition

This file connects the existing four-sector coordinate decomposition to
canonical systems carrying the expected semantics:

* the reachable restriction is controllable;
* the quotient by the unobservable subspace is observable;
* the quotient of the reachable subspace by its unobservable intersection is
  simultaneously controllable and observable.

The last space is the mathematically correct meaning of the chosen `co`
coordinate sector.  The complement itself is not assumed invariant.

References: Hespanha, *Linear Systems Theory*; Kailath, *Linear Systems*;
Kalman, “Mathematical Description of Linear Dynamical Systems” (1963).
-/

namespace LinearSystems

open Matrix

variable {n m p : ℕ}

/-- The canonical controllable-observable state map has no proper invariant
subspace containing its input range.

Reference: Kailath, *Linear Systems*. -/
theorem controllableObservableStateMap_controllable
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    ∀ S : Submodule ℂ (ControllableObservableSpace A B C),
      LinearMap.range (controllableObservableInputMap A B C) ≤ S →
      S ∈ Module.End.invtSubmodule (controllableObservableStateMap A B C) →
      S = ⊤ := by
  intro S hB hA
  let T := S.comap (controllableObservableKernel A B C).mkQ
  have hTB : LinearMap.range (reachableInputMap A B) ≤ T := by
    rintro x ⟨u, rfl⟩
    exact hB ⟨u, rfl⟩
  have hTA : T ∈ Module.End.invtSubmodule (reachableStateMap A B) := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hA ⊢
    intro x hx
    change controllableObservableStateMap A B C
      ((controllableObservableKernel A B C).mkQ x) ∈ S
    exact hA _ hx
  have hT : T = ⊤ := reachableStateMap_controllable A B T hTB hTA
  rw [eq_top_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := (controllableObservableKernel A B C).mkQ_surjective q
  have hx : x ∈ T := by rw [hT]; trivial
  exact hx

/-- The canonical controllable-observable state map has no nonzero invariant
subspace contained in its output kernel.

Reference: Kailath, *Linear Systems*. -/
theorem controllableObservableStateMap_observable
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    ∀ S : Submodule ℂ (ControllableObservableSpace A B C),
      S ∈ Module.End.invtSubmodule (controllableObservableStateMap A B C) →
      S ≤ LinearMap.ker (controllableObservableOutputMap A B C) →
      S = ⊥ := by
  intro S hA hC
  let T := S.comap (controllableObservableKernel A B C).mkQ
  let U := T.map (reachableSubspace A B).subtype
  have hUA : U ∈ Module.End.invtSubmodule A.mulVecLin := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hA ⊢
    rintro x ⟨y, hy, rfl⟩
    refine ⟨reachableStateMap A B y, ?_, rfl⟩
    change controllableObservableStateMap A B C
      ((controllableObservableKernel A B C).mkQ y) ∈ S
    exact hA _ hy
  have hUC : U ≤ LinearMap.ker C.mulVecLin := by
    rintro x ⟨y, hy, rfl⟩
    rw [LinearMap.mem_ker]
    have hout := hC hy
    rw [LinearMap.mem_ker] at hout
    simpa [controllableObservableOutputMap, Submodule.liftQ_apply] using hout
  have hUN := le_unobservableSubspace_of_invariant_of_le_ker A C U hUA hUC
  have hTI : T ≤ controllableObservableKernel A B C := by
    intro x hx
    exact hUN ⟨x, hx, rfl⟩
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := (controllableObservableKernel A B C).mkQ_surjective q
  have hxT : x ∈ T := hq
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hTI hxT)

/-- The canonical-core state matrix acts on basis coordinates exactly as the
induced quotient state map.

Original: coordinate infrastructure for LeanForControl. -/
lemma controllableObservableStateMatrix_mulVec_coordinates
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) (x : ControllableObservableSpace A B C) :
    controllableObservableStateMatrix A B C *ᵥ
        (controllableObservableBasis A B C).equivFun x =
      (controllableObservableBasis A B C).equivFun
        (controllableObservableStateMap A B C x) := by
  simpa [controllableObservableStateMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (controllableObservableBasis A B C)
      (controllableObservableBasis A B C)
      (controllableObservableStateMap A B C) x

/-- The canonical-core input matrix acts on standard coordinates exactly as
the induced quotient input map.

Original: coordinate infrastructure for LeanForControl. -/
lemma controllableObservableInputMatrix_mulVec_coordinates
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) (u : Fin m → ℂ) :
    controllableObservableInputMatrix A B C *ᵥ u =
      (controllableObservableBasis A B C).equivFun
        (controllableObservableInputMap A B C u) := by
  simpa [controllableObservableInputMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℂ (Fin m))
      (controllableObservableBasis A B C)
      (controllableObservableInputMap A B C) u

/-- The canonical-core output matrix acts on basis coordinates exactly as
the induced quotient output map.

Original: coordinate infrastructure for LeanForControl. -/
lemma controllableObservableOutputMatrix_mulVec_coordinates
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) (x : ControllableObservableSpace A B C) :
    controllableObservableOutputMatrix A B C *ᵥ
        (controllableObservableBasis A B C).equivFun x =
      controllableObservableOutputMap A B C x := by
  simpa [controllableObservableOutputMatrix, Module.Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (controllableObservableBasis A B C)
      (Pi.basisFun ℂ (Fin p)) (controllableObservableOutputMap A B C) x

/-- The matrix pair of the canonical controllable-observable core is
controllable in the library's textbook sense.

Reference: Kailath, *Linear Systems*. -/
theorem controllableObservableMatrices_isControllable
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    IsControllable (controllableObservableStateMatrix A B C)
      (controllableObservableInputMatrix A B C) := by
  rw [← reachableSubspace_eq_top_iff_isControllable]
  let R := reachableSubspace (controllableObservableStateMatrix A B C)
    (controllableObservableInputMatrix A B C)
  let S := R.comap (controllableObservableBasis A B C).equivFun.toLinearMap
  have hB : LinearMap.range (controllableObservableInputMap A B C) ≤ S := by
    rintro x ⟨u, rfl⟩
    change (controllableObservableBasis A B C).equivFun
      (controllableObservableInputMap A B C u) ∈ R
    rw [← controllableObservableInputMatrix_mulVec_coordinates]
    exact range_B_le_reachableSubspace _ _ ⟨u, rfl⟩
  have hA : S ∈ Module.End.invtSubmodule
      (controllableObservableStateMap A B C) := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    change (controllableObservableBasis A B C).equivFun
      (controllableObservableStateMap A B C x) ∈ R
    rw [← controllableObservableStateMatrix_mulVec_coordinates]
    exact reachableSubspace_invariant _ _ hx
  have hS : S = ⊤ :=
    controllableObservableStateMap_controllable A B C S hB hA
  rw [eq_top_iff]
  intro z hz
  let x := (controllableObservableBasis A B C).equivFun.symm z
  have hx : x ∈ S := by rw [hS]; trivial
  change (controllableObservableBasis A B C).equivFun x ∈ R at hx
  change (controllableObservableBasis A B C).equivFun
      ((controllableObservableBasis A B C).equivFun.symm z) ∈ R at hx
  simpa only [LinearEquiv.apply_symm_apply] using hx

/-- The matrix pair of the canonical controllable-observable core is
observable in the library's textbook sense.

Reference: Kailath, *Linear Systems*. -/
theorem controllableObservableMatrices_isObservable
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    IsObservable (controllableObservableStateMatrix A B C)
      (controllableObservableOutputMatrix A B C) := by
  rw [← unobservableSubspace_eq_bot_iff_isObservable]
  let N := unobservableSubspace (controllableObservableStateMatrix A B C)
    (controllableObservableOutputMatrix A B C)
  let S := N.comap (controllableObservableBasis A B C).equivFun.toLinearMap
  have hA : S ∈ Module.End.invtSubmodule
      (controllableObservableStateMap A B C) := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    change (controllableObservableBasis A B C).equivFun
      (controllableObservableStateMap A B C x) ∈ N
    rw [← controllableObservableStateMatrix_mulVec_coordinates]
    exact A_mulVec_mem_unobservableSubspace_of_mem hx
  have hC : S ≤ LinearMap.ker (controllableObservableOutputMap A B C) := by
    intro x hx
    rw [LinearMap.mem_ker]
    rw [← controllableObservableOutputMatrix_mulVec_coordinates]
    by_cases hq : Module.finrank ℂ (ControllableObservableSpace A B C) = 0
    · have hz : (controllableObservableBasis A B C).equivFun x = 0 := by
        ext i
        exact Fin.elim0 (hq ▸ i)
      rw [hz, Matrix.mulVec_zero]
    · have hzero := (mem_unobservableSubspace_iff
        ((controllableObservableBasis A B C).equivFun x)).mp hx
        (⟨0, Nat.pos_of_ne_zero hq⟩ :
          Fin (Module.finrank ℂ (ControllableObservableSpace A B C)))
      simpa using hzero
  have hS : S = ⊥ := controllableObservableStateMap_observable A B C S hA hC
  rw [eq_bot_iff]
  intro z hz
  let x := (controllableObservableBasis A B C).equivFun.symm z
  have hx : x ∈ S := by
    change (controllableObservableBasis A B C).equivFun x ∈ N
    change (controllableObservableBasis A B C).equivFun
      ((controllableObservableBasis A B C).equivFun.symm z) ∈ N
    simpa only [LinearEquiv.apply_symm_apply] using hz
  rw [hS] at hx
  have hx0 : x = 0 := hx
  calc
    z = (controllableObservableBasis A B C).equivFun x := by
      exact ((controllableObservableBasis A B C).equivFun.apply_symm_apply z).symm
    _ = 0 := by rw [hx0, map_zero]

/-- The canonical core is simultaneously controllable and observable.

References: Hespanha, *Linear Systems Theory*; Kailath, *Linear Systems*. -/
@[blueprint "thm:kalman-controllable-observable-core"
  (statement := /-- The dynamics on
    $\mathcal R/(\mathcal R\cap\mathcal N)$ is both controllable and
    observable. -/)]
theorem controllableObservableMatrices_isControllable_and_isObservable
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    IsControllable (controllableObservableStateMatrix A B C)
        (controllableObservableInputMatrix A B C) ∧
      IsObservable (controllableObservableStateMatrix A B C)
        (controllableObservableOutputMatrix A B C) :=
  ⟨controllableObservableMatrices_isControllable A B C,
    controllableObservableMatrices_isObservable A B C⟩

/-- Mapping the unobservable part of the reachable subtype back to the
ambient state space gives the canonical intersection `R ⊓ N`.

Original: subtype/ambient bridge for LeanForControl. -/
theorem map_controllableObservableKernel_eq_inf
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    (controllableObservableKernel A B C).map
        (reachableSubspace A B).subtype =
      reachableSubspace A B ⊓ unobservableSubspace A C := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hxR, hxN⟩
    exact ⟨⟨x, hxR⟩, hxN, rfl⟩

/-- The kernel removed from the reachable subtype has the dimension of the
canonical intersection `R ⊓ N`.

Reference: Kailath, *Linear Systems*. -/
theorem finrank_controllableObservableKernel_eq_inf
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    Module.finrank ℂ (controllableObservableKernel A B C) =
      Module.finrank ℂ
        ↥(reachableSubspace A B ⊓ unobservableSubspace A C) := by
  have h := Submodule.finrank_map_subtype_eq (reachableSubspace A B)
    (controllableObservableKernel A B C)
  rw [map_controllableObservableKernel_eq_inf] at h
  exact h.symm

/-- Rank-nullity for the canonical controllable-observable quotient.

Reference: Kailath, *Linear Systems*. -/
theorem finrank_controllableObservableSpace_add_kernel
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    Module.finrank ℂ (ControllableObservableSpace A B C) +
        Module.finrank ℂ (controllableObservableKernel A B C) =
      Module.finrank ℂ (reachableSubspace A B) := by
  exact Submodule.finrank_quotient_add_finrank
    (controllableObservableKernel A B C)

namespace KalmanDecomposition

variable {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin m) ℂ}
  {C : Matrix (Fin p) (Fin n) ℂ}

/-- The controllable portion represented by `cuo ⊕ co` is the canonical
reachable restriction, whose matrix pair is controllable.

Reference: Kailath, *Linear Systems*. -/
theorem controllablePart_isControllable (_d : KalmanDecomposition A B C) :
    IsControllable (reachableStateMatrix A B) (reachableInputMatrix A B) :=
  reachableMatrices_isControllable A B

/-- The observable portion is canonically the quotient by the unobservable
subspace, whose matrix pair is observable.

Reference: Kailath, *Linear Systems*. -/
theorem observablePart_isObservable (_d : KalmanDecomposition A B C) :
    IsObservable (observableStateMatrix A C) (observableOutputMatrix A C) :=
  observableMatrices_isObservable A C

/-- The controllable-observable semantics associated with a Kalman
decomposition is carried by the canonical core, independently of the chosen
noncanonical complements.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "thm:kalman-semantic-core"
  (statement := /-- Every Kalman decomposition represents the same canonical
    controllable-observable quotient, and that quotient is both controllable
    and observable. -/)]
theorem controllableObservableCore_isControllable_and_isObservable
    (_d : KalmanDecomposition A B C) :
    IsControllable (controllableObservableStateMatrix A B C)
        (controllableObservableInputMatrix A B C) ∧
      IsObservable (controllableObservableStateMatrix A B C)
        (controllableObservableOutputMatrix A B C) :=
  controllableObservableMatrices_isControllable_and_isObservable A B C

/-- The dimension of the canonical controllable-observable quotient equals
the dimension of the chosen `co` coordinate sector.  This is an identification
of dimensions, not an equality of the noncanonical complement with the
quotient.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "thm:kalman-co-finrank-eq-core"
  (statement := /-- Every chosen controllable-observable sector has the same
    dimension as the canonical quotient
    $\mathcal R/(\mathcal R\cap\mathcal N)$. -/)]
theorem finrank_co_eq_controllableObservableSpace
    (d : KalmanDecomposition A B C) :
    Module.finrank ℂ d.co =
      Module.finrank ℂ (ControllableObservableSpace A B C) := by
  have hq := finrank_controllableObservableSpace_add_kernel A B C
  have hk := finrank_controllableObservableKernel_eq_inf A B C
  have hi := d.finrank_cuo_eq_inf
  have hr := d.finrank_cuo_add_finrank_co
  omega

end KalmanDecomposition

/-- Existence-level structural Kalman theorem: one decomposition witnesses
the four-sector lattice structure, while its canonical controllable and
observable systems have the expected semantics and its `co` sector has the
dimension of the canonical controllable-observable quotient.

The existing `kalman_block_matrix_zero_pattern` theorem supplies the adapted
matrix zero pattern for any bases chosen on these sectors.

References: Hespanha, *Linear Systems Theory*; Kailath, *Linear Systems*;
Kalman, “Mathematical Description of Linear Dynamical Systems” (1963). -/
@[blueprint "thm:kalman-structural-decomposition"
  (statement := /-- Every finite-dimensional complex system admits a Kalman
    decomposition whose reachable restriction is controllable, whose
    observable quotient is observable, and whose canonical
    controllable-observable quotient is both. -/)]
theorem exists_kalmanDecomposition_with_semantics
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    ∃ d : KalmanDecomposition A B C,
      IsControllable (reachableStateMatrix A B) (reachableInputMatrix A B) ∧
      IsObservable (observableStateMatrix A C) (observableOutputMatrix A C) ∧
      IsControllable (controllableObservableStateMatrix A B C)
        (controllableObservableInputMatrix A B C) ∧
      IsObservable (controllableObservableStateMatrix A B C)
        (controllableObservableOutputMatrix A B C) ∧
      Module.finrank ℂ d.co =
        Module.finrank ℂ (ControllableObservableSpace A B C) := by
  obtain ⟨d⟩ := exists_kalmanDecomposition A B C
  exact ⟨d, d.controllablePart_isControllable, d.observablePart_isObservable,
    d.controllableObservableCore_isControllable_and_isObservable.1,
    d.controllableObservableCore_isControllable_and_isObservable.2,
    d.finrank_co_eq_controllableObservableSpace⟩

end LinearSystems

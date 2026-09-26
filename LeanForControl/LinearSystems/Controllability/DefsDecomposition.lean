import LeanForControl.LinearSystems.Controllability.Reachability
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Architect

/-!
# Definitions for the controllable decomposition

The canonical controllable part of `(A,B)` is the restriction to
`reachableSubspace A B`.  A finite basis turns that restricted pair into
ordinary `Fin`-indexed matrices, so the public `IsControllable` predicate can
be applied without introducing a parallel notion of matrix controllability.

Original: semantic decomposition infrastructure for LeanForControl.
-/

namespace LinearSystems

open Matrix

variable {n m : ℕ}

/-- The state endomorphism restricted to the canonical reachable subspace.

Reference: Hespanha, *Linear Systems Theory*, §13.2. -/
noncomputable def reachableStateMap
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    Module.End ℂ (reachableSubspace A B) :=
  A.mulVecLin.restrict (fun _ hx => reachableSubspace_invariant A B hx)

/-- The input map with codomain restricted to the canonical reachable
subspace.

Reference: Hespanha, *Linear Systems Theory*, §13.2. -/
noncomputable def reachableInputMap
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    (Fin m → ℂ) →ₗ[ℂ] reachableSubspace A B :=
  B.mulVecLin.codRestrict (reachableSubspace A B) fun u =>
    range_B_le_reachableSubspace A B ⟨u, rfl⟩

/-- A finite basis of the reachable subspace used for the standalone
controllable matrix decomposition.

Original: coordinate infrastructure for LeanForControl. -/
noncomputable def reachableStateBasis
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :=
  Module.finBasis ℂ (reachableSubspace A B)

/-- The state matrix of the restricted reachable dynamics.

Reference: Hespanha, *Linear Systems Theory*, §13.2. -/
noncomputable def reachableStateMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    Matrix (Fin (Module.finrank ℂ (reachableSubspace A B)))
      (Fin (Module.finrank ℂ (reachableSubspace A B))) ℂ :=
  LinearMap.toMatrix (reachableStateBasis A B) (reachableStateBasis A B)
    (reachableStateMap A B)

/-- The input matrix of the restricted reachable dynamics.

Reference: Hespanha, *Linear Systems Theory*, §13.2. -/
noncomputable def reachableInputMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    Matrix (Fin (Module.finrank ℂ (reachableSubspace A B))) (Fin m) ℂ :=
  LinearMap.toMatrix (Pi.basisFun ℂ (Fin m)) (reachableStateBasis A B)
    (reachableInputMap A B)

end LinearSystems

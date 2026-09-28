import LeanForControl.LinearSystems.Controllability.Reachability
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Architect

/-!
# The controllable component

Restrict the state and input maps to the reachable subspace. Their matrices
represent the controllable component in a chosen finite basis, as in the
controllable decomposition of Hespanha, *Linear Systems Theory*.
The basis choice is Lean coordinate infrastructure.
-/

namespace LinearSystems

open Matrix

variable {𝕜 : Type*} [Field 𝕜] {n m : ℕ}

/-- The restriction of `A` to the reachable subspace.

Reference: Hespanha, *Linear Systems Theory*, controllable decomposition. -/
@[blueprint "def:reachable-state-map"
  (statement := /-- Let $\mathcal R(A,B)$ be the reachable subspace
    (\cref{def:reachableSubspace}). Its invariance under $A$ defines the
    restricted state map $A_c:\mathcal R(A,B)\to\mathcal R(A,B)$,
    $A_c x=Ax$. -/)]
noncomputable def reachableStateMap
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    Module.End 𝕜 (reachableSubspace A B) :=
  A.mulVecLin.restrict (fun _ hx => reachableSubspace_invariant A B hx)

/-- The input map `B` with values in the reachable subspace.

Reference: Hespanha, *Linear Systems Theory*, controllable decomposition. -/
@[blueprint "def:reachable-input-map"
  (statement := /-- Since $\operatorname{im}B\subseteq\mathcal R(A,B)$,
    the input map takes values in the reachable subspace:
    $B_c:\mathbb F^m\to\mathcal R(A,B)$, $B_c u=Bu$. -/)]
noncomputable def reachableInputMap
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    (Fin m → 𝕜) →ₗ[𝕜] reachableSubspace A B :=
  B.mulVecLin.codRestrict (reachableSubspace A B) fun u =>
    range_B_le_reachableSubspace A B ⟨u, rfl⟩

/-- The matrix of the restricted state map in `Module.finBasis`.

Original: Lean coordinate representation of the controllable component.
The basis is chosen, so the matrix is not canonical. -/
noncomputable def reachableStateMatrix
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    Matrix (Fin (Module.finrank 𝕜 (reachableSubspace A B)))
      (Fin (Module.finrank 𝕜 (reachableSubspace A B))) 𝕜 :=
  LinearMap.toMatrix (Module.finBasis 𝕜 (reachableSubspace A B))
    (Module.finBasis 𝕜 (reachableSubspace A B))
    (reachableStateMap A B)

/-- The matrix of the restricted input map in `Module.finBasis`,
with standard input coordinates.

Original: Lean coordinate representation of the controllable component.
The basis is chosen, so the matrix is not canonical. -/
noncomputable def reachableInputMatrix
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    Matrix (Fin (Module.finrank 𝕜 (reachableSubspace A B))) (Fin m) 𝕜 :=
  LinearMap.toMatrix (Pi.basisFun 𝕜 (Fin m)) (Module.finBasis 𝕜 (reachableSubspace A B))
    (reachableInputMap A B)

end LinearSystems

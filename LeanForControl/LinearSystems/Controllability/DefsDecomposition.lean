import LeanForControl.LinearSystems.Controllability.Reachability
import Mathlib.LinearAlgebra.Basis.Defs
import Architect

/-!
# The controllable component

Restrict the state and input maps to the reachable subspace. Their matrices
represent the controllable component in a supplied finite basis, as in the
controllable decomposition in Hespanha, *Linear Systems Theory* (2nd ed.), Theorem 13.2.
These restriction maps give a coordinate-free formulation of its component.
The matrix definitions take the state basis as an explicit argument.
-/

namespace LinearSystems

open Matrix

variable {𝕜 : Type*} [Field 𝕜] {n m : ℕ}

/-- The restriction of `A` to the reachable subspace.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Theorem 13.2;
coordinate-free construction of the controllable component. -/
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

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Theorem 13.2;
coordinate-free construction of the controllable component. -/
@[blueprint "def:reachable-input-map"
  (statement := /-- Since $\operatorname{im}B\subseteq\mathcal R(A,B)$,
    the input map takes values in the reachable subspace:
    $B_c:\mathbb F^m\to\mathcal R(A,B)$, $B_c u=Bu$. -/)]
noncomputable def reachableInputMap
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    (Fin m → 𝕜) →ₗ[𝕜] reachableSubspace A B :=
  B.mulVecLin.codRestrict (reachableSubspace A B) fun u =>
    range_B_le_reachableSubspace A B ⟨u, rfl⟩

/-- The matrix of the restricted state map in the supplied basis. -/
@[blueprint "def:reachable-state-matrix"
  (statement := /-- Given a basis $b$ of $\mathcal R(A,B)$ indexed by
    $\operatorname{Fin}(r)$, let $A_c$ be the matrix of the restricted state
    map (\cref{def:reachable-state-map}) in $b$. -/)]
noncomputable def reachableStateMatrix
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    {r : ℕ} (b : Module.Basis (Fin r) 𝕜 (reachableSubspace A B)) :
    Matrix (Fin r) (Fin r) 𝕜 :=
  LinearMap.toMatrix b b (reachableStateMap A B)

/-- The matrix of the restricted input map in the supplied state basis,
with standard input coordinates. -/
@[blueprint "def:reachable-input-matrix"
  (statement := /-- Given the same basis $b$ as in
    \cref{def:reachable-state-matrix}, let $B_c$ be the matrix of the
    restricted input map (\cref{def:reachable-input-map}) in $b$ and the
    standard input basis. -/)]
noncomputable def reachableInputMatrix
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    {r : ℕ} (b : Module.Basis (Fin r) 𝕜 (reachableSubspace A B)) :
    Matrix (Fin r) (Fin m) 𝕜 :=
  LinearMap.toMatrix (Pi.basisFun 𝕜 (Fin m)) b (reachableInputMap A B)

end LinearSystems

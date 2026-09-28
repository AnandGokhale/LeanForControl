import LeanForControl.LinearSystems.Observability.Hautus
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Architect

/-!
# The observable component

The state and output maps descend to the quotient by the unobservable
subspace. In a finite basis their matrices represent the observable component
in Hespanha, *Linear Systems Theory*, observable decomposition.
The quotient construction is an equivalent formulation of that component;
the basis choice is Lean coordinate infrastructure.
-/

namespace LinearSystems

open Matrix

variable {n p : ℕ}

/-- The state map induced on the quotient by the unobservable subspace.

Equivalent quotient formulation of the observable component in Hespanha,
*Linear Systems Theory*, observable decomposition. -/
@[blueprint "def:observable-state-map"
  (statement := /-- The invariance of $\mathcal N(A,C)$
    (\cref{lem:unobservableSubspace-invariant}) defines a state map on
    $\mathbb C^n/\mathcal N(A,C)$ by $A_o[x]=[Ax]$. -/)]
noncomputable def observableStateMap
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    Module.End ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C) :=
  (unobservableSubspace A C).mapQ (unobservableSubspace A C) A.mulVecLin
    (by intro x hx; exact A_mulVec_mem_unobservableSubspace_of_mem hx)

/-- The output map induced on the quotient by the unobservable subspace.

Equivalent quotient formulation of the observable component in Hespanha,
*Linear Systems Theory*, observable decomposition. -/
@[blueprint "def:observable-output-map"
  (statement := /-- Since $\mathcal N(A,C)\subseteq\ker C$, the output map
    descends to $\mathbb C^n/\mathcal N(A,C)$: $C_o[x]=Cx$. -/)]
noncomputable def observableOutputMap
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    ((Fin n → ℂ) ⧸ unobservableSubspace A C) →ₗ[ℂ] (Fin p → ℂ) :=
  (unobservableSubspace A C).liftQ C.mulVecLin (unobservableSubspace_le_ker_C A C)

/-- The matrix of the induced state map in `Module.finBasis`.

Original: Lean coordinate representation of the observable component.
The basis is chosen, so the matrix is not canonical. -/
noncomputable def observableStateMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    Matrix (Fin (Module.finrank ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C)))
      (Fin (Module.finrank ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C))) ℂ :=
  LinearMap.toMatrix (Module.finBasis ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C))
    (Module.finBasis ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C))
    (observableStateMap A C)

/-- The matrix of the induced output map in `Module.finBasis`,
with standard output coordinates.

Original: Lean coordinate representation of the observable component.
The basis is chosen, so the matrix is not canonical. -/
noncomputable def observableOutputMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    Matrix (Fin p)
      (Fin (Module.finrank ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C))) ℂ :=
  LinearMap.toMatrix (Module.finBasis ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C))
    (Pi.basisFun ℂ (Fin p))
    (observableOutputMap A C)

end LinearSystems

import LeanForControl.LinearSystems.Observability.Observability
import Mathlib.LinearAlgebra.Basis.Defs
import Architect

/-!
# The observable component

The state and output maps descend to the quotient by the unobservable
subspace. This quotient-space construction corresponds to the observable
component. The matrix definitions take the quotient basis as an explicit argument.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Theorem 16.2;
coordinate-free quotient construction corresponding to its observable component.
-/

namespace LinearSystems

open Matrix

variable {n p : ℕ}

/-- The state map induced on the quotient by the unobservable subspace.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Theorem 16.2;
coordinate-free quotient construction corresponding to its observable component.
This is the quotient-space construction corresponding to the observable component. -/
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

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Theorem 16.2;
coordinate-free quotient construction corresponding to its observable component.
This is the quotient-space construction corresponding to the observable component. -/
@[blueprint "def:observable-output-map"
  (statement := /-- Since $\mathcal N(A,C)\subseteq\ker C$
    (\cref{lem:unobservableSubspace-le-ker-C}), the output map
    descends to $\mathbb C^n/\mathcal N(A,C)$: $C_o[x]=Cx$. -/)]
noncomputable def observableOutputMap
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    ((Fin n → ℂ) ⧸ unobservableSubspace A C) →ₗ[ℂ] (Fin p → ℂ) :=
  (unobservableSubspace A C).liftQ C.mulVecLin (unobservableSubspace_le_ker_C A C)

/-- The matrix of the induced state map in the supplied quotient basis. -/
@[blueprint "def:observable-state-matrix"
  (statement := /-- Given a basis $b$ of $\mathbb C^n/\mathcal N(A,C)$
    indexed by $\operatorname{Fin}(r)$, let $A_o$ be the matrix of the
    induced state map (\cref{def:observable-state-map}) in $b$. -/)]
noncomputable def observableStateMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    {r : ℕ} (b : Module.Basis (Fin r) ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C)) :
    Matrix (Fin r) (Fin r) ℂ :=
  LinearMap.toMatrix b b (observableStateMap A C)

/-- The matrix of the induced output map in the supplied quotient basis,
with standard output coordinates. -/
@[blueprint "def:observable-output-matrix"
  (statement := /-- Given the same basis $b$ as in
    \cref{def:observable-state-matrix}, let $C_o$ be the matrix of the
    induced output map (\cref{def:observable-output-map}) in $b$ and the
    standard output basis. -/)]
noncomputable def observableOutputMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    {r : ℕ} (b : Module.Basis (Fin r) ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C)) :
    Matrix (Fin p) (Fin r) ℂ :=
  LinearMap.toMatrix b (Pi.basisFun ℂ (Fin p)) (observableOutputMap A C)

end LinearSystems

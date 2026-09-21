import LeanForControl.LinearSystems.Controllability.DefsDecomposition
import LeanForControl.LinearSystems.Observability.DefsDecomposition
import Mathlib.LinearAlgebra.Dimension.Free
import Architect

/-!
# Definitions for the canonical controllable-observable core

The chosen `co` complement in a `KalmanDecomposition` need not be invariant.
The canonical dynamics it represents therefore lives on

`reachableSubspace A B / (reachableSubspace A B ∩ unobservableSubspace A C)`.

The intersection is expressed below as a submodule of the reachable subtype.
State, input, and output maps descend to the quotient, and finite bases give
ordinary matrices for the existing controllability and observability APIs.

References: Hespanha, *Linear Systems Theory*; Kailath, *Linear Systems*.
-/

namespace LinearSystems

open Matrix

variable {n m p : ℕ}

/-- The unobservable part inside the reachable-state subtype.

Reference: Kailath, *Linear Systems*. -/
noncomputable def controllableObservableKernel
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    Submodule ℂ (reachableSubspace A B) :=
  (unobservableSubspace A C).comap (reachableSubspace A B).subtype

/-- The canonical controllable-observable state space.

Reference: Kailath, *Linear Systems*. -/
abbrev ControllableObservableSpace
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :=
  reachableSubspace A B ⧸ controllableObservableKernel A B C

/-- The state map induced on the controllable-observable quotient.

Reference: Kailath, *Linear Systems*. -/
noncomputable def controllableObservableStateMap
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    Module.End ℂ (ControllableObservableSpace A B C) :=
  (controllableObservableKernel A B C).mapQ
    (controllableObservableKernel A B C) (reachableStateMap A B) (by
      intro x hx
      exact A_mulVec_mem_unobservableSubspace_of_mem hx)

/-- The input map induced on the controllable-observable quotient.

Reference: Kailath, *Linear Systems*. -/
noncomputable def controllableObservableInputMap
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    (Fin m → ℂ) →ₗ[ℂ] ControllableObservableSpace A B C :=
  (controllableObservableKernel A B C).mkQ.comp (reachableInputMap A B)

/-- The output map induced on the controllable-observable quotient.

Reference: Kailath, *Linear Systems*. -/
noncomputable def controllableObservableOutputMap
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    ControllableObservableSpace A B C →ₗ[ℂ] (Fin p → ℂ) :=
  (controllableObservableKernel A B C).liftQ
    (C.mulVecLin.comp (reachableSubspace A B).subtype) (by
      intro x hx
      rw [LinearMap.mem_ker]
      change C *ᵥ (x : Fin n → ℂ) = 0
      by_cases hn : n = 0
      · subst n
        have hx0 : (x : Fin 0 → ℂ) = 0 := Subsingleton.elim _ _
        rw [hx0, Matrix.mulVec_zero]
      · have h0 := (mem_unobservableSubspace_iff (x : Fin n → ℂ)).mp hx
          ⟨0, Nat.pos_of_ne_zero hn⟩
        simpa using h0)

/-- A finite basis of the canonical controllable-observable state space.

Original: coordinate infrastructure for LeanForControl. -/
noncomputable def controllableObservableBasis
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :=
  Module.finBasis ℂ (ControllableObservableSpace A B C)

/-- The state matrix of the canonical controllable-observable dynamics.

Reference: Kailath, *Linear Systems*. -/
noncomputable def controllableObservableStateMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    Matrix (Fin (Module.finrank ℂ (ControllableObservableSpace A B C)))
      (Fin (Module.finrank ℂ (ControllableObservableSpace A B C))) ℂ :=
  LinearMap.toMatrix (controllableObservableBasis A B C)
    (controllableObservableBasis A B C)
    (controllableObservableStateMap A B C)

/-- The input matrix of the canonical controllable-observable dynamics.

Reference: Kailath, *Linear Systems*. -/
noncomputable def controllableObservableInputMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    Matrix (Fin (Module.finrank ℂ (ControllableObservableSpace A B C)))
      (Fin m) ℂ :=
  LinearMap.toMatrix (Pi.basisFun ℂ (Fin m))
    (controllableObservableBasis A B C)
    (controllableObservableInputMap A B C)

/-- The output matrix of the canonical controllable-observable dynamics.

Reference: Kailath, *Linear Systems*. -/
noncomputable def controllableObservableOutputMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    Matrix (Fin p)
      (Fin (Module.finrank ℂ (ControllableObservableSpace A B C))) ℂ :=
  LinearMap.toMatrix (controllableObservableBasis A B C)
    (Pi.basisFun ℂ (Fin p)) (controllableObservableOutputMap A B C)

end LinearSystems

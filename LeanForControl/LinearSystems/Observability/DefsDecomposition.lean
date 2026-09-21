import LeanForControl.LinearSystems.Observability.Hautus
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Architect

/-!
# Definitions for the observable decomposition

The canonical observable part of `(A,C)` is the quotient of the state space
by `unobservableSubspace A C`.  Invariance makes the state map descend to the
quotient, while the output map descends because it kills every unobservable
state.  A finite quotient basis then supplies ordinary `Fin`-indexed matrices.

Original: semantic decomposition infrastructure for LeanForControl.
-/

namespace LinearSystems

open Matrix

variable {n p : ℕ}

/-- The state endomorphism induced on the quotient by the unobservable
subspace.

Reference: Hespanha, *Linear Systems Theory*. -/
noncomputable def observableStateMap
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    Module.End ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C) :=
  (unobservableSubspace A C).mapQ (unobservableSubspace A C) A.mulVecLin
    (by intro x hx; exact A_mulVec_mem_unobservableSubspace_of_mem hx)

/-- The output map induced on the quotient by the unobservable subspace.

Reference: Hespanha, *Linear Systems Theory*. -/
noncomputable def observableOutputMap
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    ((Fin n → ℂ) ⧸ unobservableSubspace A C) →ₗ[ℂ] (Fin p → ℂ) :=
  (unobservableSubspace A C).liftQ C.mulVecLin (by
    intro x hx
    rw [LinearMap.mem_ker]
    by_cases hn : n = 0
    · subst n
      have hx0 : x = 0 := Subsingleton.elim _ _
      rw [hx0, map_zero]
    · have h0 :=
        (mem_unobservableSubspace_iff x).mp hx ⟨0, Nat.pos_of_ne_zero hn⟩
      simpa using h0)

/-- A finite basis of the quotient by the unobservable subspace.

Original: coordinate infrastructure for LeanForControl. -/
noncomputable def observableStateBasis
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :=
  Module.finBasis ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C)

/-- The state matrix of the observable quotient dynamics.

Reference: Hespanha, *Linear Systems Theory*. -/
noncomputable def observableStateMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    Matrix (Fin (Module.finrank ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C)))
      (Fin (Module.finrank ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C))) ℂ :=
  LinearMap.toMatrix (observableStateBasis A C) (observableStateBasis A C)
    (observableStateMap A C)

/-- The output matrix of the observable quotient dynamics.

Reference: Hespanha, *Linear Systems Theory*. -/
noncomputable def observableOutputMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    Matrix (Fin p)
      (Fin (Module.finrank ℂ ((Fin n → ℂ) ⧸ unobservableSubspace A C))) ℂ :=
  LinearMap.toMatrix (observableStateBasis A C) (Pi.basisFun ℂ (Fin p))
    (observableOutputMap A C)

end LinearSystems

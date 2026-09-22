import LeanForControl.LinearSystems.Realization.FiniteDetermination
import Mathlib.LinearAlgebra.Isomorphisms
import Architect

/-!
# Finite Ho–Kalman range/shift construction

This file establishes the canonical state-space and induced-shift core of a
finite Ho–Kalman construction.  The state space is the range of the unshifted
finite Hankel map.  Explicit kernel and range compatibility hypotheses make
the one-step shifted Hankel map descend to an endomorphism of that range.

Turning this core into a bundled realization and proving recovery of every
supplied block requires an additional finite shift-consistency theorem across
successive block columns; that work is deliberately kept separate from the
well-definedness result proved here.

Reference: Ho and Kalman, “Effective construction of linear state-variable
models from input/output functions” (1966).
-/

namespace LinearSystems

open Matrix

namespace Realization

variable {𝕜 : Type*} [Field 𝕜]
variable {m p r s : ℕ}

/-- The finite block Hankel matrix built from supplied Markov blocks, with an
explicit shift in the sequence index.

Reference: Ho and Kalman (1966). -/
def shiftedHankel (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s shift : ℕ) :
    Matrix (Fin r × Fin p) (Fin s × Fin m) 𝕜 :=
  Matrix.of fun ia jb => M (shift + (ia.1 : ℕ) + (jb.1 : ℕ)) ia.2 jb.2

/-- Compatibility conditions ensuring that the shifted Hankel map induces a
well-defined endomorphism of the unshifted Hankel range.

The kernel inclusion gives independence from the chosen input-history
representative.  The range inclusion makes the shifted image a state again.

Reference: Ho and Kalman (1966). -/
structure HankelShiftCompatible
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ) : Prop where
  /-- Null histories for the unshifted Hankel matrix remain null after one
  shift. -/
  ker_le :
    LinearMap.ker (shiftedHankel M r s 0).mulVecLin ≤
      LinearMap.ker (shiftedHankel M r s 1).mulVecLin
  /-- Every shifted output history belongs to the unshifted Hankel range. -/
  range_le :
    LinearMap.range (shiftedHankel M r s 1).mulVecLin ≤
      LinearMap.range (shiftedHankel M r s 0).mulVecLin

/-- The canonical finite Ho–Kalman state space: the range of the unshifted
Hankel map.

Reference: Ho and Kalman (1966). -/
def hankelStateSpace (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) :=
  LinearMap.range (shiftedHankel M r s 0).mulVecLin

/-- The shifted Hankel map, with codomain restricted to the canonical state
space using range compatibility.

Original: finite Ho–Kalman infrastructure for LeanForControl. -/
def hankelShiftToState (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s) :
    (Fin s × Fin m → 𝕜) →ₗ[𝕜] hankelStateSpace M r s :=
  (shiftedHankel M r s 1).mulVecLin.codRestrict
    (hankelStateSpace M r s) fun u =>
      h.range_le ⟨u, rfl⟩

/-- The shifted Hankel map descends through the quotient by the unshifted
Hankel kernel.

This is the central well-definedness step of the finite Ho–Kalman
construction.

Reference: Ho and Kalman (1966). -/
def hankelShiftQuotientMap (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s) :
    ((Fin s × Fin m → 𝕜) ⧸
        LinearMap.ker (shiftedHankel M r s 0).mulVecLin) →ₗ[𝕜]
      hankelStateSpace M r s :=
  (LinearMap.ker (shiftedHankel M r s 0).mulVecLin).liftQ
    (hankelShiftToState M r s h) (by
      intro u hu
      rw [LinearMap.mem_ker] at hu ⊢
      apply Subtype.ext
      exact LinearMap.mem_ker.mp
        (h.ker_le (LinearMap.mem_ker.mpr hu)))

/-- The canonical state transition on the finite Hankel range.

Reference: Ho and Kalman (1966). -/
noncomputable def hankelStateMap
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s) :
    hankelStateSpace M r s →ₗ[𝕜] hankelStateSpace M r s :=
  (hankelShiftQuotientMap M r s h).comp
    (shiftedHankel M r s 0).mulVecLin.quotKerEquivRange.symm.toLinearMap

/-- On a state represented by an input history, the canonical state map is
exactly one Hankel shift.

Reference: Ho and Kalman (1966). -/
theorem hankelStateMap_apply_image
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s)
    (u : Fin s × Fin m → 𝕜) :
    hankelStateMap M r s h
        ⟨(shiftedHankel M r s 0).mulVecLin u, ⟨u, rfl⟩⟩ =
      ⟨(shiftedHankel M r s 1).mulVecLin u, h.range_le ⟨u, rfl⟩⟩ := by
  let y : LinearMap.range (shiftedHankel M r s 0).mulVecLin :=
    ⟨(shiftedHankel M r s 0).mulVecLin u, ⟨u, rfl⟩⟩
  change hankelStateMap M r s h y = _
  rw [hankelStateMap, LinearMap.comp_apply]
  have hrepr :
      (shiftedHankel M r s 0).mulVecLin.quotKerEquivRange.symm.toLinearMap
          y =
        (LinearMap.ker (shiftedHankel M r s 0).mulVecLin).mkQ u :=
    by
      dsimp [y]
      exact
        LinearMap.quotKerEquivRange_symm_apply_image
          (shiftedHankel M r s 0).mulVecLin u ⟨u, rfl⟩
  calc
    (hankelShiftQuotientMap M r s h)
        ((shiftedHankel M r s 0).mulVecLin.quotKerEquivRange.symm.toLinearMap
          y) =
        (hankelShiftQuotientMap M r s h)
          ((LinearMap.ker
            (shiftedHankel M r s 0).mulVecLin).mkQ u) :=
      congrArg (hankelShiftQuotientMap M r s h) hrepr
    _ = _ := rfl

/-- A finite basis of the canonical Hankel state space.

Original: coordinate infrastructure for LeanForControl. -/
noncomputable def hankelStateBasis
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ) :=
  Module.finBasis 𝕜 (hankelStateSpace M r s)

/-- The matrix of the canonical finite Hankel shift in range coordinates.

Reference: Ho and Kalman (1966). -/
noncomputable def hankelStateMatrix
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜)
    (r s : ℕ) (h : HankelShiftCompatible M r s) :
    Matrix (Fin (Module.finrank 𝕜 (hankelStateSpace M r s)))
      (Fin (Module.finrank 𝕜 (hankelStateSpace M r s))) 𝕜 :=
  LinearMap.toMatrix (hankelStateBasis M r s) (hankelStateBasis M r s)
    (hankelStateMap M r s h)

/-- The dimension of the canonical finite Ho–Kalman state space is the rank
of the unshifted Hankel matrix.

Reference: Ho and Kalman (1966). -/
theorem hankelStateSpace_finrank_eq_rank
    (M : ℕ → Matrix (Fin p) (Fin m) 𝕜) (r s : ℕ) :
    Module.finrank 𝕜 (hankelStateSpace M r s) =
      Matrix.rank (shiftedHankel M r s 0) :=
  rfl

end Realization

end LinearSystems

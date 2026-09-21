import LeanForControl.LinearSystems.KalmanDecomposition.Semantic
import LeanForControl.LinearSystems.Realization.Minimal
import Architect

/-!
# Canonical realization reduction

The structural controllable-observable quotient constructed by the Kalman
development is packaged here as a realization. Its Markov parameters agree
with the original realization, so it is a behavior-preserving reduction.

References: Kailath, *Linear Systems*; Kalman, “Mathematical Description of
Linear Dynamical Systems” (1963).
-/

namespace LinearSystems

open Matrix

namespace Realization

variable {n m p : ℕ}

/-- The realization carried by the canonical quotient
`R/(R ∩ N)`, with the original feedthrough matrix.

Reference: Kailath, *Linear Systems*. -/
noncomputable def core (R : Realization ℂ n m p) :
    Realization ℂ
      (Module.finrank ℂ (ControllableObservableSpace R.A R.B R.C)) m p where
  A := controllableObservableStateMatrix R.A R.B R.C
  B := controllableObservableInputMatrix R.A R.B R.C
  C := controllableObservableOutputMatrix R.A R.B R.C
  D := R.D

/-- Powers of the canonical-core state matrix act on quotient coordinates as
powers of the induced state map.

Original: coordinate infrastructure for LeanForControl. -/
lemma core_state_pow_mulVec_coordinates (R : Realization ℂ n m p) (k : ℕ)
    (x : ControllableObservableSpace R.A R.B R.C) :
    (controllableObservableStateMatrix R.A R.B R.C ^ k) *ᵥ
        (controllableObservableBasis R.A R.B R.C).equivFun x =
      (controllableObservableBasis R.A R.B R.C).equivFun
        (((controllableObservableStateMap R.A R.B R.C) ^ k) x) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec,
        ih, controllableObservableStateMatrix_mulVec_coordinates,
        pow_succ', Module.End.mul_apply]

/-- The induced quotient state map commutes with the quotient projection on
every power of the reachable-state map.

Original: quotient infrastructure for LeanForControl. -/
lemma core_stateMap_pow_mkQ (R : Realization ℂ n m p) (k : ℕ)
    (x : reachableSubspace R.A R.B) :
    ((controllableObservableStateMap R.A R.B R.C) ^ k)
        ((controllableObservableKernel R.A R.B R.C).mkQ x) =
      (controllableObservableKernel R.A R.B R.C).mkQ
        (((reachableStateMap R.A R.B) ^ k) x) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl

/-- Each Markov parameter of the canonical core equals the corresponding
Markov parameter of the original realization.

Reference: Kailath, *Linear Systems*. -/
theorem core_markovParameter_eq (R : Realization ℂ n m p) (k : ℕ) :
    R.core.markovParameter k = R.markovParameter k := by
  rw [Matrix.ext_iff_mulVec]
  intro u
  change
    (controllableObservableOutputMatrix R.A R.B R.C *
          controllableObservableStateMatrix R.A R.B R.C ^ k *
        controllableObservableInputMatrix R.A R.B R.C) *ᵥ u =
      (R.C * R.A ^ k * R.B) *ᵥ u
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [controllableObservableInputMatrix_mulVec_coordinates,
    core_state_pow_mulVec_coordinates]
  change
    controllableObservableOutputMatrix R.A R.B R.C *ᵥ
        (controllableObservableBasis R.A R.B R.C).equivFun
          (((controllableObservableStateMap R.A R.B R.C) ^ k)
            ((controllableObservableKernel R.A R.B R.C).mkQ
              (reachableInputMap R.A R.B u))) =
      R.C *ᵥ (R.A ^ k *ᵥ (R.B *ᵥ u))
  rw [core_stateMap_pow_mkQ,
    controllableObservableOutputMatrix_mulVec_coordinates]
  change
    R.C *ᵥ
        ((((reachableStateMap R.A R.B) ^ k)
          (reachableInputMap R.A R.B u) : reachableSubspace R.A R.B) :
            Fin n → ℂ) =
      R.C *ᵥ (R.A ^ k *ᵥ (R.B *ᵥ u))
  rw [reachableStateMap_pow_coe, reachableInputMap_coe]

/-- The canonical controllable-observable core preserves the full external
behavior of a realization.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "thm:canonical-core-preserves-behavior"
  (statement := /-- Passing to the canonical quotient
    $mathcal R/(mathcal Rcapmathcal N)$ preserves the feedthrough matrix
    and every Markov parameter. -/)]
theorem behaviorallyEquivalent_core (R : Realization ℂ n m p) :
    R.BehaviorallyEquivalent R.core :=
  ⟨rfl, fun k => (R.core_markovParameter_eq k).symm⟩

/-- The canonical core realization is controllable.

Reference: Kailath, *Linear Systems*. -/
theorem core_isControllable (R : Realization ℂ n m p) :
    R.core.IsControllable :=
  controllableObservableMatrices_isControllable R.A R.B R.C

/-- The canonical core realization is observable.

Reference: Kailath, *Linear Systems*. -/
theorem core_isObservable (R : Realization ℂ n m p) :
    R.core.IsObservable :=
  controllableObservableMatrices_isObservable R.A R.B R.C

end Realization

end LinearSystems

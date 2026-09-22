import LeanForControl.LinearSystems.Realization.HoKalman

/-!
# Realization-theory regression examples

These examples exercise the public realization API at degenerate dimensions,
two explicit minimal two-state systems related by a nontrivial shear, finite
Markov determinacy, and a redundant-state counterexample to uniqueness
without minimality.

Original: regression examples for LeanForControl.
-/

namespace LinearSystems

namespace RealizationExamples

open Realization
open Matrix

variable {m p : ℕ}

/-- The zero-state realization with prescribed feedthrough matrix.

Original: degenerate-dimension regression example for LeanForControl. -/
def stateless (D : Matrix (Fin p) (Fin m) ℂ) : Realization ℂ 0 m p where
  A := 0
  B := 0
  C := 0
  D := D

/-- A zero-state realization is controllable.

Original: degenerate-dimension regression example for LeanForControl. -/
theorem stateless_isControllable (D : Matrix (Fin p) (Fin m) ℂ) :
    (stateless D).IsControllable := by
  intro x
  refine ⟨fun _ _ => 0, ?_⟩
  ext i
  exact Fin.elim0 i

/-- A zero-state realization is observable.

Original: degenerate-dimension regression example for LeanForControl. -/
theorem stateless_isObservable (D : Matrix (Fin p) (Fin m) ℂ) :
    (stateless D).IsObservable := by
  intro x _
  ext i
  exact Fin.elim0 i

/-- A zero-state realization is minimal.

Original: degenerate-dimension regression example for LeanForControl. -/
theorem stateless_isMinimal (D : Matrix (Fin p) (Fin m) ℂ) :
    (stateless D).IsMinimal :=
  (stateless D).isMinimal_of_isControllable_of_isObservable
    (stateless_isControllable D) (stateless_isObservable D)

/-- The canonical core theorem produces a minimal realization for an
arbitrary realization through the public API.

Original: API regression example for LeanForControl. -/
example {n : ℕ} (R : Realization ℂ n m p) :
    ∃ (q : ℕ) (S : Realization ℂ q m p),
      R.BehaviorallyEquivalent S ∧ S.IsMinimal :=
  R.exists_behaviorallyEquivalent_isMinimal

/-! ## A nontrivial two-state change of coordinates -/

/-- A nontrivial shear used as a two-state coordinate change.

Original: numerical regression example for LeanForControl. -/
def shear : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![1, 1], ![0, 1]]

/-- The inverse shear.

Original: numerical regression example for LeanForControl. -/
def shearInv : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![1, -1], ![0, 1]]

/-- A two-state realization whose input and output maps expose every state.

Original: numerical regression example for LeanForControl. -/
def diagonalTwoState : Realization ℂ 2 2 2 where
  A := ![![1, 0], ![0, 2]]
  B := 1
  C := 1
  D := 0

/-- The preceding realization after the nontrivial state change `shear`.

Original: numerical regression example for LeanForControl. -/
def shearedTwoState : Realization ℂ 2 2 2 where
  A := ![![1, 1], ![0, 2]]
  B := shear
  C := shearInv
  D := 0

/-- The two explicit two-state systems are related by the nonidentity shear.

Original: numerical regression example for LeanForControl. -/
def diagonalSimilarSheared : Similar diagonalTwoState shearedTwoState where
  T := shear
  Tinv := shearInv
  Tinv_mul_T := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [shear, shearInv, Matrix.mul_apply, Fin.sum_univ_two]
  T_mul_Tinv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [shear, shearInv, Matrix.mul_apply, Fin.sum_univ_two]
  state := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [diagonalTwoState, shearedTwoState, shear, Matrix.mul_apply,
        Fin.sum_univ_two]
  input := by simp [diagonalTwoState, shearedTwoState]
  output := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [diagonalTwoState, shearedTwoState, shear, shearInv,
        Matrix.mul_apply, Fin.sum_univ_two]
  feedthrough := rfl

/-- The diagonal two-state realization is controllable because `B = I`.

Original: numerical regression example for LeanForControl. -/
theorem diagonalTwoState_isControllable :
    diagonalTwoState.IsControllable := by
  intro x
  refine ⟨fun k => if k = 0 then x else 0, ?_⟩
  rw [Fin.sum_univ_two]
  simp [diagonalTwoState]

/-- The diagonal two-state realization is observable because `C = I`.

Original: numerical regression example for LeanForControl. -/
theorem diagonalTwoState_isObservable :
    diagonalTwoState.IsObservable := by
  intro x hx
  simpa [diagonalTwoState] using hx (0 : Fin 2)

/-- The diagonal numerical example is minimal.

Original: numerical regression example for LeanForControl. -/
theorem diagonalTwoState_isMinimal : diagonalTwoState.IsMinimal :=
  diagonalTwoState.isMinimal_of_isControllable_of_isObservable
    diagonalTwoState_isControllable diagonalTwoState_isObservable

/-- The sheared numerical example is also minimal.

Original: numerical regression example for LeanForControl. -/
theorem shearedTwoState_isMinimal : shearedTwoState.IsMinimal :=
  diagonalSimilarSheared.isMinimal_iff.mp diagonalTwoState_isMinimal

/-- The explicit shear preserves the complete external behavior.

Original: numerical regression example for LeanForControl. -/
theorem diagonalTwoState_behaviorallyEquivalent_sheared :
    diagonalTwoState.BehaviorallyEquivalent shearedTwoState :=
  diagonalSimilarSheared.behaviorallyEquivalent _ _

/-- The R2 uniqueness theorem recovers the existence of a similarity witness
from minimality and behavior, without being given the explicit shear.

Original: uniqueness API regression example for LeanForControl. -/
example : Nonempty (Similar diagonalTwoState shearedTwoState) :=
  similar_of_isMinimal_of_behaviorallyEquivalent
    diagonalTwoState shearedTwoState diagonalTwoState_isMinimal
    shearedTwoState_isMinimal diagonalTwoState_behaviorallyEquivalent_sheared

/-- Direct calculation verifies the four Markov parameters required by the
two-state finite-determinacy bound.

Original: finite-determinacy numerical regression for LeanForControl. -/
theorem diagonalTwoState_markov_eq_sheared_of_lt_four
    (k : ℕ) (hk : k < 4) :
    diagonalTwoState.markovParameter k =
      shearedTwoState.markovParameter k := by
  interval_cases k <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [markovParameter, diagonalTwoState, shearedTwoState, shear,
      shearInv, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

/-- For the two two-state systems, the directly checked four-term window is
enough to recover agreement of the entire Markov sequence.

Original: finite-determinacy API regression example for LeanForControl. -/
example : diagonalTwoState.BehaviorallyEquivalent shearedTwoState := by
  apply behaviorallyEquivalent_of_markovParameter_eq_lt_add
  · rfl
  · intro k hk
    exact diagonalTwoState_markov_eq_sheared_of_lt_four k hk

/-! ## Why minimality is necessary -/

/-- A one-state realization whose state is completely unreachable and
unobservable, with prescribed feedthrough behavior.

Original: nonminimal regression example for LeanForControl. -/
def redundantZero (D : Matrix (Fin p) (Fin m) ℂ) : Realization ℂ 1 m p where
  A := 0
  B := 0
  C := 0
  D := D

/-- The redundant one-state realization has the same behavior as the
zero-state realization.

Original: nonminimal regression example for LeanForControl. -/
theorem redundantZero_behaviorallyEquivalent_stateless
    (D : Matrix (Fin p) (Fin m) ℂ) :
    (redundantZero D).BehaviorallyEquivalent (stateless D) := by
  constructor
  · rfl
  · intro k
    simp [redundantZero, stateless, markovParameter]

/-- The redundant one-state realization is not minimal: the same behavior
has a zero-state realization.  Thus behavior alone cannot force similarity
without the minimality hypothesis.

Original: nonminimal regression example for LeanForControl. -/
theorem redundantZero_not_isMinimal (D : Matrix (Fin p) (Fin m) ℂ) :
    ¬(redundantZero D).IsMinimal := by
  intro hmin
  have hdim := hmin 0 (stateless D)
    (redundantZero_behaviorallyEquivalent_stateless D)
  omega

/-! ## Finite Ho–Kalman synthesis -/

/-- The canonical finite Ho–Kalman realization of the explicit minimal
two-state example.

Original: finite Ho–Kalman regression example for LeanForControl. -/
noncomputable def diagonalTwoStateHoKalman :=
  minimalHoKalmanRealization diagonalTwoState
    diagonalTwoState_isMinimal (by omega)

/-- The synthesized two-state system recovers each block in its directly
supplied four-block determination window.

Original: finite Ho–Kalman regression example for LeanForControl. -/
theorem diagonalTwoStateHoKalman_markovParameter_eq
    (k : ℕ) (hk : k < 4) :
    diagonalTwoStateHoKalman.markovParameter k =
      diagonalTwoState.markovParameter k := by
  simpa [diagonalTwoStateHoKalman, minimalHoKalmanRealization] using
    hoKalmanRealization_markovParameter_eq
      diagonalTwoState.markovParameter diagonalTwoState.D 2 4
      (minimalHoKalmanShiftCompatible
        diagonalTwoState diagonalTwoState_isMinimal)
      (by omega) (by omega) k hk

/-- The synthesized two-state system has the complete behavior of the source.

Original: finite Ho–Kalman regression example for LeanForControl. -/
theorem diagonalTwoState_behaviorallyEquivalent_hoKalman :
    diagonalTwoState.BehaviorallyEquivalent diagonalTwoStateHoKalman :=
  behaviorallyEquivalent_minimalHoKalmanRealization
    diagonalTwoState diagonalTwoState_isMinimal (by omega)

/-- The synthesized two-state system is minimal.

Original: finite Ho–Kalman regression example for LeanForControl. -/
theorem diagonalTwoStateHoKalman_isMinimal :
    diagonalTwoStateHoKalman.IsMinimal :=
  minimalHoKalmanRealization_isMinimal
    diagonalTwoState diagonalTwoState_isMinimal (by omega)

/-- Its canonical Hankel-range state dimension is exactly two.

Original: finite Ho–Kalman regression example for LeanForControl. -/
theorem diagonalTwoStateHoKalman_stateDim_eq :
    Module.finrank ℂ
        (hankelStateSpace diagonalTwoState.markovParameter 2 4) = 2 :=
  minimalHoKalmanRealization_stateDim_eq
    diagonalTwoState diagonalTwoState_isMinimal (by omega)

/-- A second Ho–Kalman construction of the same behavior using five block
columns instead of four.

Original: horizon-independence regression example for LeanForControl. -/
noncomputable def diagonalTwoStateHoKalmanFive :=
  hoKalmanRealization diagonalTwoState.markovParameter diagonalTwoState.D 2 5
    (hankelShiftCompatible_markovParameter_of_isControllable_of_isObservable
      diagonalTwoState diagonalTwoState_isControllable
      diagonalTwoState_isObservable 5 (by omega)) (by omega) (by omega)

/-- The four-column and five-column constructions are similar after transport
along their canonical equality of state dimensions.

Original: horizon-independence regression example for LeanForControl. -/
theorem diagonalTwoStateHoKalman_horizons_similar :
    ∃ e : Module.finrank ℂ
          (hankelStateSpace diagonalTwoState.markovParameter 2 4) =
        Module.finrank ℂ
          (hankelStateSpace diagonalTwoState.markovParameter 2 5),
      Nonempty
        (Similar (e ▸ diagonalTwoStateHoKalman)
          diagonalTwoStateHoKalmanFive) := by
  let h₄ := minimalHoKalmanShiftCompatible
    diagonalTwoState diagonalTwoState_isMinimal
  let h₅ :=
    hankelShiftCompatible_markovParameter_of_isControllable_of_isObservable
      diagonalTwoState diagonalTwoState_isControllable
      diagonalTwoState_isObservable 5 (by omega)
  have hw₄ := minimalHoKalman_window diagonalTwoState
  have hrank₅ :
      Matrix.rank
          (shiftedHankel diagonalTwoState.markovParameter 2 5 0) ≤ 2 := by
    rw [shiftedHankel_markovParameter_zero_eq_hankelMatrix]
    exact diagonalTwoState.hankelMatrix_rank_le_stateDim 2 5
  have hw₅ :
      2 + Matrix.rank
          (shiftedHankel diagonalTwoState.markovParameter 2 5 0) ≤ 5 := by
    omega
  simpa [diagonalTwoStateHoKalman, diagonalTwoStateHoKalmanFive,
    minimalHoKalmanRealization, h₄, h₅] using
    exists_stateDim_eq_and_similar_hoKalmanRealizations
      diagonalTwoState diagonalTwoState_isMinimal 2 4 2 5 h₄ h₅
      (by omega) (by omega) (by omega) (by omega) hw₄ hw₅

/-- The rank-zero finite Ho–Kalman construction with prescribed feedthrough.

Original: pure-feedthrough Ho–Kalman regression example for LeanForControl. -/
noncomputable def zeroHoKalman
    (D : Matrix (Fin p) (Fin m) ℂ) :=
  hoKalmanRealization (fun _ => (0 : Matrix (Fin p) (Fin m) ℂ)) D 1 1
    (zeroHankelShiftCompatible 1 1) (by omega) (by omega)

/-- The rank-zero construction really has zero state dimension.

Original: pure-feedthrough Ho–Kalman regression example for LeanForControl. -/
theorem zeroHoKalman_stateDim_eq_zero
    (_D : Matrix (Fin p) (Fin m) ℂ) :
    Module.finrank ℂ
        (hankelStateSpace
          (fun _ => (0 : Matrix (Fin p) (Fin m) ℂ)) 1 1) = 0 := by
  rw [hankelStateSpace_finrank_eq_rank]
  rw [show shiftedHankel
        (fun _ => (0 : Matrix (Fin p) (Fin m) ℂ)) 1 1 0 =
        (0 : Matrix (Fin 1 × Fin p) (Fin 1 × Fin m) ℂ) by
      ext
      rfl]
  exact Matrix.rank_zero

/-- The rank-zero construction has exactly the prescribed pure feedthrough
behavior.

Original: pure-feedthrough Ho–Kalman regression example for LeanForControl. -/
theorem stateless_behaviorallyEquivalent_zeroHoKalman
    (D : Matrix (Fin p) (Fin m) ℂ) :
    (stateless D).BehaviorallyEquivalent (zeroHoKalman D) := by
  apply behaviorallyEquivalent_of_markovParameter_eq_lt_add
  · rfl
  · intro k hk
    have hdim := zeroHoKalman_stateDim_eq_zero D
    omega

/-- The rank-zero Ho–Kalman construction is minimal.

Original: pure-feedthrough Ho–Kalman regression example for LeanForControl. -/
theorem zeroHoKalman_isMinimal (D : Matrix (Fin p) (Fin m) ℂ) :
    (zeroHoKalman D).IsMinimal := by
  intro n' S _
  have hdim := zeroHoKalman_stateDim_eq_zero D
  omega

/-- Ho–Kalman removes the unreachable and unobservable state from the
redundant one-state realization, returning a behaviorally equivalent
zero-dimensional realization.

Original: redundant-state Ho–Kalman regression example for LeanForControl. -/
theorem redundantZero_behaviorallyEquivalent_zeroHoKalman
    (D : Matrix (Fin p) (Fin m) ℂ) :
    (redundantZero D).BehaviorallyEquivalent (zeroHoKalman D) :=
  (redundantZero_behaviorallyEquivalent_stateless D).trans
    (stateless_behaviorallyEquivalent_zeroHoKalman D)

end RealizationExamples

end LinearSystems

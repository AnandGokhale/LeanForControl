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

end RealizationExamples

end LinearSystems

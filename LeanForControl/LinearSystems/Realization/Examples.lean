import LeanForControl.LinearSystems.Realization.Minimality

/-!
# Realization-theory regression examples

These examples exercise the public realization API at degenerate dimensions
and ensure the minimal-realization existence theorem is usable without
opening implementation namespaces.

Original: regression examples for LeanForControl.
-/

namespace LinearSystems

namespace RealizationExamples

open Realization

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

end RealizationExamples

end LinearSystems

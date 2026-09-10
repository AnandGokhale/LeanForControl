import LeanForControl.LinearSystems.Reachability.KalmanDecomposition

/-!
# Regression examples for the Kalman decomposition

These small systems exercise both degenerate edges of the dimension-generic
development and a concrete two-state decomposition.  They intentionally use
the public API rather than unfolding implementation details of the chosen
complements.

Original: regression examples for LeanForControl.
-/

namespace LinearSystems.KalmanDecompositionExamples

open Matrix

/-- A concrete two-state system with no actuated directions. -/
def zeroA2 : Matrix (Fin 2) (Fin 2) ℂ := 0

/-- One input channel which acts as the zero map. -/
def zeroB2 : Matrix (Fin 2) (Fin 1) ℂ := 0

/-- One output channel which measures no state direction. -/
def zeroC2 : Matrix (Fin 1) (Fin 2) ℂ := 0

/-- The concrete two-state zero-input system has trivial reachable subspace. -/
example : reachableSubspace zeroA2 zeroB2 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨u, rfl⟩ := hx
  ext i
  simp [zeroA2, zeroB2, controllabilityMatrix, Matrix.mulVec]

/-- The concrete two-state zero-output system has full unobservable subspace. -/
example : unobservableSubspace zeroA2 zeroC2 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [mem_unobservableSubspace_iff]
  intro k
  simp [zeroA2, zeroC2]

/-- The general theorem specializes to the concrete two-state edge system. -/
example : Nonempty (KalmanDecomposition zeroA2 zeroB2 zeroC2) :=
  exists_kalmanDecomposition zeroA2 zeroB2 zeroC2

/-- Zero state dimension is covered uniformly, with arbitrary input and
output dimensions. -/
example (m p : ℕ) (A : Matrix (Fin 0) (Fin 0) ℂ)
    (B : Matrix (Fin 0) (Fin m) ℂ) (C : Matrix (Fin p) (Fin 0) ℂ) :
    Nonempty (KalmanDecomposition A B C) :=
  exists_kalmanDecomposition A B C

end LinearSystems.KalmanDecompositionExamples

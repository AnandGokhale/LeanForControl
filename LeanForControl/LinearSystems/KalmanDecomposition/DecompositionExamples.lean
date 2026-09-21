import LeanForControl.LinearSystems.KalmanDecomposition.Decomposition
import LeanForControl.LinearSystems.KalmanDecomposition.Semantic
import Mathlib.Tactic.FinCases

/-!
# Regression examples for the Kalman decomposition

These small systems exercise both degenerate edges of the dimension-generic
development and a concrete two-state decomposition.  They intentionally use
the public API rather than unfolding implementation details of the chosen
complements.

Original: regression examples for LeanForControl.
-/

namespace LinearSystems.DecompositionExamples

open Matrix

/-- The zero state map on a one-dimensional state space. -/
def zeroA1 : Matrix (Fin 1) (Fin 1) ℂ := 0

/-- A one-dimensional input map with unit gain. -/
def oneB1 : Matrix (Fin 1) (Fin 1) ℂ := 1

/-- A one-dimensional output map with unit gain. -/
def oneC1 : Matrix (Fin 1) (Fin 1) ℂ := 1

/-- The one-state unit-input system is completely controllable. -/
example : IsControllable zeroA1 oneB1 := by
  intro x
  refine ⟨fun _ _ => x 0, ?_⟩
  funext i
  fin_cases i
  simp [zeroA1, oneB1]

/-- The one-state unit-output system is completely observable. -/
example : IsObservable zeroA1 oneC1 := by
  intro x hx
  funext i
  fin_cases i
  have h := hx (0 : Fin 1)
  have h0 := congrFun h (0 : Fin 1)
  simpa [zeroA1, oneC1, Matrix.mulVec, dotProduct] using h0

/-- A two-state input map actuating only the first coordinate. -/
def splitB2 : Matrix (Fin 2) (Fin 1) ℂ :=
  fun i _ => if i = 0 then 1 else 0

/-- A two-state output map measuring only the second coordinate. -/
def splitC2 : Matrix (Fin 1) (Fin 2) ℂ :=
  fun _ j => if j = 1 then 1 else 0

/-- The first standard coordinate vector in the concrete two-state example. -/
def e0 : Fin 2 → ℂ := fun i => if i = 0 then 1 else 0

/-- The second standard coordinate vector in the concrete two-state example. -/
def e1 : Fin 2 → ℂ := fun i => if i = 1 then 1 else 0

/-- A concrete two-state system with no actuated directions. -/
def zeroA2 : Matrix (Fin 2) (Fin 2) ℂ := 0

/-- One input channel which acts as the zero map. -/
def zeroB2 : Matrix (Fin 2) (Fin 1) ℂ := 0

/-- One output channel which measures no state direction. -/
def zeroC2 : Matrix (Fin 1) (Fin 2) ℂ := 0

/-- The first coordinate is reachable in the split two-state example. -/
lemma e0_mem_reachable_split :
    e0 ∈ reachableSubspace zeroA2 splitB2 := by
  apply range_B_le_reachableSubspace zeroA2 splitB2
  refine ⟨fun _ => 1, ?_⟩
  funext i
  fin_cases i <;> simp [splitB2, e0, Matrix.mulVec, dotProduct]

/-- The first coordinate is unobservable in the split two-state example. -/
lemma e0_mem_unobservable_split :
    e0 ∈ unobservableSubspace zeroA2 splitC2 := by
  rw [mem_unobservableSubspace_iff]
  intro k
  fin_cases k <;> funext i <;> fin_cases i <;>
    simp [zeroA2, splitC2, e0, Matrix.mulVec, dotProduct]

/-- Every reachable vector in the split example has zero second coordinate. -/
lemma reachable_split_apply_one_eq_zero {x : Fin 2 → ℂ}
    (hx : x ∈ reachableSubspace zeroA2 splitB2) : x 1 = 0 := by
  obtain ⟨u, rfl⟩ := (mem_reachableSubspace_iff x).mp hx
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro kj hkj
  obtain ⟨k, j⟩ := kj
  fin_cases k <;> fin_cases j <;>
    simp [controllabilityMatrix, zeroA2, splitB2]

/-- Every unobservable vector in the split example has zero second
coordinate. -/
lemma unobservable_split_apply_one_eq_zero {x : Fin 2 → ℂ}
    (hx : x ∈ unobservableSubspace zeroA2 splitC2) : x 1 = 0 := by
  have h := (mem_unobservableSubspace_iff x).mp hx (0 : Fin 2)
  have h0 := congrFun h (0 : Fin 1)
  simpa [zeroA2, splitC2, Matrix.mulVec, dotProduct] using h0

/-- The second coordinate is outside the sum of the reachable and
unobservable subspaces in the split example. -/
lemma e1_not_mem_reachable_sup_unobservable_split :
    e1 ∉ reachableSubspace zeroA2 splitB2 ⊔
      unobservableSubspace zeroA2 splitC2 := by
  intro h
  obtain ⟨r, u, hru⟩ := Submodule.mem_sup'.mp h
  have hr := reachable_split_apply_one_eq_zero r.2
  have hu := unobservable_split_apply_one_eq_zero u.2
  have hcoord := congrFun hru (1 : Fin 2)
  simp [e1, hr, hu] at hcoord

/-- A concrete decomposition with two nonzero Kalman sectors: the first
coordinate lies in `cuo`, while the complementary second coordinate forces a
nonzero `uo` sector. -/
example : ∃ d : KalmanDecomposition zeroA2 splitB2 splitC2,
    d.cuo ≠ ⊥ ∧ d.uo ≠ ⊥ := by
  obtain ⟨d⟩ := exists_kalmanDecomposition zeroA2 splitB2 splitC2
  refine ⟨d, ?_, ?_⟩
  · intro hbot
    have he0 : e0 ∈ d.cuo := by
      rw [d.cuo_eq]
      exact ⟨e0_mem_reachable_split, e0_mem_unobservable_split⟩
    rw [hbot] at he0
    have heq : e0 = 0 := he0
    have h := congrFun heq (0 : Fin 2)
    simp [e0] at h
  · intro hbot
    have htop := d.isCompl_uo.codisjoint.eq_top
    rw [hbot, sup_bot_eq] at htop
    apply e1_not_mem_reachable_sup_unobservable_split
    rw [htop]
    trivial

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

/-- The standalone reachable restriction is genuinely controllable for every
system, not merely equipped with a block-zero pattern. -/
example (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin m) ℂ) :
    IsControllable (reachableStateMatrix A B) (reachableInputMatrix A B) :=
  reachableMatrices_isControllable A B

/-- The quotient by the unobservable subspace is genuinely observable for
every system. -/
example (n p : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) :
    IsObservable (observableStateMatrix A C) (observableOutputMatrix A C) :=
  observableMatrices_isObservable A C

/-- The canonical core used to interpret the `co` block is simultaneously
controllable and observable, including all degenerate dimensions. -/
example (n m p : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin m) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    IsControllable (controllableObservableStateMatrix A B C)
        (controllableObservableInputMatrix A B C) ∧
      IsObservable (controllableObservableStateMatrix A B C)
        (controllableObservableOutputMatrix A B C) :=
  controllableObservableMatrices_isControllable_and_isObservable A B C

/-- The zero-dimensional system satisfies the complete structural theorem,
including semantic controllability and observability conclusions. -/
example (m p : ℕ) (A : Matrix (Fin 0) (Fin 0) ℂ)
    (B : Matrix (Fin 0) (Fin m) ℂ) (C : Matrix (Fin p) (Fin 0) ℂ) :
    ∃ d : KalmanDecomposition A B C,
      IsControllable (reachableStateMatrix A B) (reachableInputMatrix A B) ∧
      IsObservable (observableStateMatrix A C) (observableOutputMatrix A C) ∧
      IsControllable (controllableObservableStateMatrix A B C)
        (controllableObservableInputMatrix A B C) ∧
      IsObservable (controllableObservableStateMatrix A B C)
        (controllableObservableOutputMatrix A B C) ∧
      Module.finrank ℂ d.co =
        Module.finrank ℂ (ControllableObservableSpace A B C) :=
  exists_kalmanDecomposition_with_semantics A B C

end LinearSystems.DecompositionExamples

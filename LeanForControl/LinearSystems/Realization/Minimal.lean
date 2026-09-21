import LeanForControl.LinearSystems.Controllability.Controllability
import LeanForControl.LinearSystems.Observability.Observability
import LeanForControl.LinearSystems.Realization.Hankel
import Architect

/-!
# Minimal realizations

Minimality is stated semantically: no behaviorally equivalent realization
with the same input and output dimensions has fewer states. The principal
rank argument in this file proves that every controllable and observable
realization is minimal.

References: Kailath, *Linear Systems*; Kalman, “Mathematical Description of
Linear Dynamical Systems” (1963).
-/

namespace LinearSystems

open Matrix

namespace Realization

variable {𝕜 : Type*} [Field 𝕜]
variable {n n' m p : ℕ}

/-- A realization is minimal when every behaviorally equivalent realization
has at least as many states.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "def:minimal-realization"
  (statement := /-- A realization of state dimension $n$ is minimal when
    every realization with the same feedthrough matrix and Markov parameters
    has state dimension at least $n$. -/)]
def IsMinimal (R : Realization 𝕜 n m p) : Prop :=
  ∀ (n' : ℕ) (S : Realization 𝕜 n' m p),
    R.BehaviorallyEquivalent S → n ≤ n'

/-- Every finite Hankel matrix has rank at most the state dimension of a
realization through which it factors.

Reference: Kailath, *Linear Systems*. -/
theorem hankelMatrix_rank_le_stateDim (R : Realization 𝕜 n m p) (r s : ℕ) :
    Matrix.rank (R.hankelMatrix r s) ≤ n := by
  rw [hankelMatrix_eq_observability_mul_controllability]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  simpa using Matrix.rank_le_card_width (R.observabilityHorizon r)

/-- For a controllable and observable realization, the square finite Hankel
matrix at the state horizon has rank equal to the state dimension.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "thm:hankel-full-rank-controllable-observable"
  (statement := /-- If $(A,B)$ is controllable and $(A,C)$ is observable,
    then the $n$-by-$n$ block Hankel matrix has rank $n$. -/)]
theorem hankelMatrix_rank_eq_stateDim_of_controllable_of_observable
    (R : Realization 𝕜 n m p) (hctrl : R.IsControllable)
    (hobs : R.IsObservable) :
    Matrix.rank (R.hankelMatrix n n) = n := by
  rw [hankelMatrix_eq_observability_mul_controllability]
  have hsurj :
      LinearMap.range (R.controllabilityHorizon n).mulVecLin = ⊤ := by
    rw [controllabilityHorizon_stateDim]
    rw [LinearMap.range_eq_top]
    exact
      (MatrixAlgebra.mulVec_range_top_iff_rank_eq_card_rows
        (controllabilityMatrix R.A R.B)).mpr (by
          simpa using
            (isControllable_iff_controllabilityMatrix_rank_eq R.A R.B).mp
              hctrl)
  rw [Matrix.rank, Matrix.mulVecLin_mul,
    LinearMap.range_comp_of_range_eq_top _ hsurj, ← Matrix.rank]
  exact
    (isObservable_iff_observabilityMatrix_rank_eq R.A R.C).mp hobs

/-- A controllable and observable realization is minimal.

The proof compares a common finite Hankel matrix across an arbitrary
behaviorally equivalent competitor. The first realization gives that Hankel
matrix rank n; factorization through the competitor bounds the same rank by
the competitor's state dimension.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "thm:controllable-observable-implies-minimal"
  (statement := /-- Every finite-dimensional realization that is both
    controllable and observable is minimal. -/)]
theorem isMinimal_of_isControllable_of_isObservable
    (R : Realization 𝕜 n m p) (hctrl : R.IsControllable)
    (hobs : R.IsObservable) : R.IsMinimal := by
  intro n' S hbehavior
  calc
    n = Matrix.rank (R.hankelMatrix n n) :=
      (R.hankelMatrix_rank_eq_stateDim_of_controllable_of_observable
        hctrl hobs).symm
    _ = Matrix.rank (S.hankelMatrix n n) := by
      rw [hbehavior.hankelMatrix_eq n n]
    _ ≤ n' := S.hankelMatrix_rank_le_stateDim n n

end Realization

end LinearSystems

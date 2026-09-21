import LeanForControl.LinearSystems.Realization.Reduction
import Architect

/-!
# Characterization and existence of minimal realizations

The canonical core reduction supplies the converse to the Hankel-rank
minimality theorem: a semantically minimal complex realization cannot lose
dimension when reduced to its reachable and observable core. Dimension
equalities then force the original system itself to be controllable and
observable.

References: Kailath, *Linear Systems*; Kalman, “Mathematical Description of
Linear Dynamical Systems” (1963).
-/

namespace LinearSystems

namespace Realization

variable {n m p : ℕ}

/-- A minimal complex realization is controllable and observable.

The proof compares the realization with its behaviorally equivalent canonical
core. Minimality forces the core to have at least n states, while its
construction as a quotient of the reachable subspace bounds it by n.
Equality forces the reachable subspace to be all states and the quotient
kernel to vanish.

Reference: Kailath, *Linear Systems*. -/
theorem isControllable_and_isObservable_of_isMinimal
    (R : Realization ℂ n m p) (hmin : R.IsMinimal) :
    R.IsControllable ∧ R.IsObservable := by
  let q := Module.finrank ℂ (ControllableObservableSpace R.A R.B R.C)
  have hnq : n ≤ q := hmin q R.core R.behaviorallyEquivalent_core
  have hsum :=
    finrank_controllableObservableSpace_add_kernel R.A R.B R.C
  have hreach_le : Module.finrank ℂ (reachableSubspace R.A R.B) ≤ n := by
    calc
      Module.finrank ℂ (reachableSubspace R.A R.B) ≤
          Module.finrank ℂ (Fin n → ℂ) :=
        Submodule.finrank_le _
      _ = n := by simp
  have hq : q = n := by
    dsimp [q]
    omega
  have hreach :
      Module.finrank ℂ (reachableSubspace R.A R.B) = n := by
    dsimp [q] at hq
    omega
  have hkernel :
      Module.finrank ℂ (controllableObservableKernel R.A R.B R.C) = 0 := by
    dsimp [q] at hq
    omega
  have hreachable_top : reachableSubspace R.A R.B = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa using hreach
  have hkernel_bot :
      controllableObservableKernel R.A R.B R.C = ⊥ :=
    Submodule.finrank_eq_zero.mp hkernel
  constructor
  · change LinearSystems.IsControllable R.A R.B
    exact
      (reachableSubspace_eq_top_iff_isControllable R.A R.B).mp
        hreachable_top
  · change LinearSystems.IsObservable R.A R.C
    rw [← unobservableSubspace_eq_bot_iff_isObservable R.A R.C]
    rw [eq_bot_iff]
    intro x hx
    have hxR : x ∈ reachableSubspace R.A R.B := by
      rw [hreachable_top]
      trivial
    let y : reachableSubspace R.A R.B := ⟨x, hxR⟩
    have hyK : y ∈ controllableObservableKernel R.A R.B R.C := hx
    rw [hkernel_bot] at hyK
    have hy0 : y = 0 := hyK
    exact congrArg Subtype.val hy0

/-- A complex realization is minimal exactly when it is both controllable
and observable.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "thm:minimal-iff-controllable-observable"
  (statement := /-- A finite-dimensional complex realization is minimal if
    and only if it is controllable and observable. -/)]
theorem isMinimal_iff_isControllable_and_isObservable
    (R : Realization ℂ n m p) :
    R.IsMinimal ↔ R.IsControllable ∧ R.IsObservable := by
  constructor
  · exact R.isControllable_and_isObservable_of_isMinimal
  · rintro ⟨hctrl, hobs⟩
    exact R.isMinimal_of_isControllable_of_isObservable hctrl hobs

/-- Every complex realization has a behaviorally equivalent minimal
realization, namely its canonical controllable-observable core.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "thm:minimal-realization-exists"
  (statement := /-- Every finite-dimensional realization admits a
    behaviorally equivalent minimal realization. -/)]
theorem exists_behaviorallyEquivalent_isMinimal (R : Realization ℂ n m p) :
    ∃ (q : ℕ) (S : Realization ℂ q m p),
      R.BehaviorallyEquivalent S ∧ S.IsMinimal := by
  refine ⟨Module.finrank ℂ (ControllableObservableSpace R.A R.B R.C),
    R.core, R.behaviorallyEquivalent_core, ?_⟩
  exact R.core.isMinimal_of_isControllable_of_isObservable
    R.core_isControllable R.core_isObservable

/-- The state dimension of a minimal complex realization is the rank of its
square state-horizon Hankel matrix.

Reference: Kailath, *Linear Systems*. -/
theorem hankelMatrix_rank_eq_stateDim_of_isMinimal
    (R : Realization ℂ n m p) (hmin : R.IsMinimal) :
    Matrix.rank (R.hankelMatrix n n) = n := by
  obtain ⟨hctrl, hobs⟩ :=
    R.isControllable_and_isObservable_of_isMinimal hmin
  exact R.hankelMatrix_rank_eq_stateDim_of_controllable_of_observable
    hctrl hobs

/-- Behaviorally equivalent minimal realizations have the same state
dimension.

This dimension-uniqueness statement is field-generic and follows directly
from the quantified semantic definition of minimality.

Reference: Kailath, *Linear Systems*. -/
theorem IsMinimal.stateDim_eq_of_behaviorallyEquivalent
    {𝕜 : Type*} [Field 𝕜] {n₁ n₂ : ℕ}
    {R₁ : Realization 𝕜 n₁ m p} {R₂ : Realization 𝕜 n₂ m p}
    (hmin₁ : R₁.IsMinimal) (hmin₂ : R₂.IsMinimal)
    (hbehavior : R₁.BehaviorallyEquivalent R₂) :
    n₁ = n₂ :=
  Nat.le_antisymm (hmin₁ n₂ R₂ hbehavior)
    (hmin₂ n₁ R₁ hbehavior.symm)

end Realization

end LinearSystems

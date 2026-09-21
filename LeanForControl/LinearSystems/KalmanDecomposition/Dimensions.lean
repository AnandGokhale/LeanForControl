import LeanForControl.LinearSystems.KalmanDecomposition.Decomposition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Architect

/-!
# Dimensions of the Kalman sectors

The reachable and unobservable subspaces are canonical, whereas the
complements chosen by a `KalmanDecomposition` are not.  This file records the
additive dimension identities that distinguish those two facts and proves
that every choice of Kalman sectors has the same four dimensions.

References: Hespanha, *Linear Systems Theory*; Kailath, *Linear Systems*.
-/

namespace LinearSystems.KalmanDecomposition

variable {n m p : ℕ}
variable {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin m) ℂ}
  {C : Matrix (Fin p) (Fin n) ℂ}

/-- The controllable-unobservable sector has the dimension of the canonical
intersection of the reachable and unobservable subspaces.

Reference: Kailath, *Linear Systems*. -/
theorem finrank_cuo_eq_inf (d : KalmanDecomposition A B C) :
    Module.finrank ℂ d.cuo = Module.finrank ℂ
      ↥(reachableSubspace A B ⊓ unobservableSubspace A C) := by
  rw [d.cuo_eq]

/-- The controllable sectors have total dimension equal to the reachable
subspace.

Reference: Kailath, *Linear Systems*. -/
theorem finrank_cuo_add_finrank_co (d : KalmanDecomposition A B C) :
    Module.finrank ℂ d.cuo + Module.finrank ℂ d.co =
      Module.finrank ℂ (reachableSubspace A B) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq d.cuo d.co
  rw [d.cuo_sup_co, d.disjoint_cuo_co.eq_bot, finrank_bot,
    add_zero] at h
  exact h.symm

/-- The unobservable sectors have total dimension equal to the unobservable
subspace.

Reference: Kailath, *Linear Systems*. -/
theorem finrank_cuo_add_finrank_uuo (d : KalmanDecomposition A B C) :
    Module.finrank ℂ d.cuo + Module.finrank ℂ d.uuo =
      Module.finrank ℂ (unobservableSubspace A C) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq d.cuo d.uuo
  have hdisj : Disjoint d.cuo d.uuo := by
    rw [disjoint_iff_inf_le]
    intro x hx
    have hxR : (x : Fin n → ℂ) ∈ reachableSubspace A B := by
      rw [← d.cuo_sup_co]
      exact Submodule.mem_sup_left hx.1
    have hxbot : (x : Fin n → ℂ) ∈ reachableSubspace A B ⊓ d.uuo :=
      ⟨hxR, hx.2⟩
    rw [d.disjoint_reachable_uuo.eq_bot] at hxbot
    exact hxbot
  rw [d.cuo_sup_uuo, hdisj.eq_bot, finrank_bot, add_zero] at h
  exact h.symm

/-- The four Kalman sectors have total dimension equal to the state
dimension.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "thm:kalman-sector-finranks"
  (statement := /-- The four Kalman sectors form a direct decomposition of
    the state space, so their dimensions add to the state dimension. -/)]
theorem finrank_cuo_add_co_add_uuo_add_uo (d : KalmanDecomposition A B C) :
    Module.finrank ℂ d.cuo + Module.finrank ℂ d.co +
        Module.finrank ℂ d.uuo + Module.finrank ℂ d.uo = n := by
  have hRuuo : Module.finrank ℂ (reachableSubspace A B) +
      Module.finrank ℂ d.uuo =
      Module.finrank ℂ
        ↥(reachableSubspace A B ⊔ unobservableSubspace A C) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (reachableSubspace A B) d.uuo
    rw [d.reachable_sup_uuo, d.disjoint_reachable_uuo.eq_bot,
      finrank_bot, add_zero] at h
    exact h.symm
  have hTop := Submodule.finrank_add_eq_of_isCompl d.isCompl_uo
  rw [Module.finrank_pi, Fintype.card_fin] at hTop
  calc
    Module.finrank ℂ d.cuo + Module.finrank ℂ d.co +
          Module.finrank ℂ d.uuo + Module.finrank ℂ d.uo =
        (Module.finrank ℂ (reachableSubspace A B) +
          Module.finrank ℂ d.uuo) + Module.finrank ℂ d.uo := by
      rw [d.finrank_cuo_add_finrank_co]
    _ = Module.finrank ℂ
          ↥(reachableSubspace A B ⊔ unobservableSubspace A C) +
          Module.finrank ℂ d.uo := by rw [hRuuo]
    _ = n := hTop

/-- Two Kalman decompositions have controllable-unobservable sectors of the
same dimension, although the chosen submodules need not be equal.

Original: canonicality bookkeeping for LeanForControl. -/
theorem finrank_cuo_eq_finrank_cuo (d₁ d₂ : KalmanDecomposition A B C) :
    Module.finrank ℂ d₁.cuo = Module.finrank ℂ d₂.cuo := by
  rw [d₁.cuo_eq, d₂.cuo_eq]

/-- Two Kalman decompositions have controllable-observable sectors of the
same dimension, although the chosen submodules need not be equal.

Original: canonicality bookkeeping for LeanForControl. -/
theorem finrank_co_eq_finrank_co (d₁ d₂ : KalmanDecomposition A B C) :
    Module.finrank ℂ d₁.co = Module.finrank ℂ d₂.co := by
  have h₁ := d₁.finrank_cuo_add_finrank_co
  have h₂ := d₂.finrank_cuo_add_finrank_co
  rw [d₁.finrank_cuo_eq_finrank_cuo d₂] at h₁
  omega

/-- Two Kalman decompositions have uncontrollable-unobservable sectors of
the same dimension, although the chosen submodules need not be equal.

Original: canonicality bookkeeping for LeanForControl. -/
theorem finrank_uuo_eq_finrank_uuo (d₁ d₂ : KalmanDecomposition A B C) :
    Module.finrank ℂ d₁.uuo = Module.finrank ℂ d₂.uuo := by
  have h₁ := d₁.finrank_cuo_add_finrank_uuo
  have h₂ := d₂.finrank_cuo_add_finrank_uuo
  rw [d₁.finrank_cuo_eq_finrank_cuo d₂] at h₁
  omega

/-- Two Kalman decompositions have uncontrollable-observable sectors of the
same dimension, although the chosen submodules need not be equal.

Original: canonicality bookkeeping for LeanForControl. -/
theorem finrank_uo_eq_finrank_uo (d₁ d₂ : KalmanDecomposition A B C) :
    Module.finrank ℂ d₁.uo = Module.finrank ℂ d₂.uo := by
  have h₁ := d₁.finrank_cuo_add_co_add_uuo_add_uo
  have h₂ := d₂.finrank_cuo_add_co_add_uuo_add_uo
  rw [d₁.finrank_cuo_eq_finrank_cuo d₂, d₁.finrank_co_eq_finrank_co d₂,
    d₁.finrank_uuo_eq_finrank_uuo d₂] at h₁
  omega

end LinearSystems.KalmanDecomposition

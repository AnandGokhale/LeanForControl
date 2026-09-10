import LeanForControl.LinearSystems.Hautus
import LeanForControl.LinearSystems.Reachability
import Architect

/-!
# Data for the finite-dimensional Kalman decomposition

This file bundles four coordinate sectors adapted to the reachable and
unobservable subspaces of a complex finite-dimensional state-space system.
The chosen complements are noncanonical vector-space complements and are not
individually claimed to be invariant under the state matrix.

Reference: Kailath, *Linear Systems*.

Original: the bundled API is formalization infrastructure for LeanForControl.
-/

namespace LinearSystems

variable {n m p : ℕ}

/-- A noncanonical choice of four coordinate sectors adapted to the reachable
and unobservable subspaces.

The fields record the exact lattice relationships used later; in particular,
`cuo ⊔ co` is reachable, `cuo ⊔ uuo` is unobservable, and the four spaces
together form the whole state space. No chosen complement is asserted to be
individually invariant under the state matrix.

Reference: Kailath, *Linear Systems*.

Original: this structure packages the data for the LeanForControl API. -/
@[blueprint "def:kalman-decomposition"
  (statement := /-- A Kalman decomposition of $(A,B,C)$ records four
    coordinate sectors adapted to the reachable and unobservable subspaces.
    Their direct sums recover those subspaces and the full state space. The
    chosen complements are noncanonical and are not individually asserted to
    be invariant under $A$. -/)]
structure KalmanDecomposition
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) where
  /-- The controllable-unobservable sector. -/
  cuo : Submodule ℂ (Fin n → ℂ)
  /-- A complement of `cuo` inside the reachable subspace. -/
  co : Submodule ℂ (Fin n → ℂ)
  /-- A complement of `cuo` inside the unobservable subspace. -/
  uuo : Submodule ℂ (Fin n → ℂ)
  /-- A complement of the sum of the reachable and unobservable subspaces. -/
  uo : Submodule ℂ (Fin n → ℂ)
  /-- The `cuo` sector is the intersection of the reachable and unobservable
  subspaces. -/
  cuo_eq : cuo = reachableSubspace A B ⊓ unobservableSubspace A C
  /-- The `cuo` and `co` sectors are disjoint. -/
  disjoint_cuo_co : Disjoint cuo co
  /-- The `cuo` and `co` sectors span the reachable subspace. -/
  cuo_sup_co : cuo ⊔ co = reachableSubspace A B
  /-- The reachable subspace and the `uuo` sector are disjoint. -/
  disjoint_reachable_uuo : Disjoint (reachableSubspace A B) uuo
  /-- Adding `uuo` to the reachable subspace gives the sum of the reachable
  and unobservable subspaces. -/
  reachable_sup_uuo : reachableSubspace A B ⊔ uuo =
    reachableSubspace A B ⊔ unobservableSubspace A C
  /-- The `uuo` sector lies in the unobservable subspace. -/
  uuo_le_unobservable : uuo ≤ unobservableSubspace A C
  /-- The `cuo` and `uuo` sectors span the unobservable subspace. -/
  cuo_sup_uuo : cuo ⊔ uuo = unobservableSubspace A C
  /-- The `uo` sector complements the sum of the reachable and unobservable
  subspaces. -/
  isCompl_uo : IsCompl
    (reachableSubspace A B ⊔ unobservableSubspace A C) uo

end LinearSystems

import LeanForControl.LinearSystems.Controllability.Defs
import LeanForControl.LinearSystems.Observability.Defs
import Architect

/-!
# State-space realizations

This file bundles the four matrices of a finite-dimensional linear realization.
The state dimension remains an explicit natural-number index, so realizations
with different state dimensions can be compared without hiding dimensions in
existentially quantified types.

Reference: Kailath, *Linear Systems*.
-/

namespace LinearSystems

/-- A finite-dimensional state-space realization with `n` states, `m` inputs,
and `p` outputs over `𝕜`.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "def:state-space-realization"
  (statement := /-- A state-space realization is a quadruple $(A,B,C,D)$ of
    compatible matrices, with the state dimension recorded explicitly. -/)]
structure Realization (𝕜 : Type*) [Semiring 𝕜] (n m p : ℕ) where
  /-- State-transition matrix. -/
  A : Matrix (Fin n) (Fin n) 𝕜
  /-- Input matrix. -/
  B : Matrix (Fin n) (Fin m) 𝕜
  /-- Output matrix. -/
  C : Matrix (Fin p) (Fin n) 𝕜
  /-- Feedthrough matrix. -/
  D : Matrix (Fin p) (Fin m) 𝕜

namespace Realization

variable {𝕜 : Type*} [Semiring 𝕜]
variable {n m p : ℕ}

/-- A realization is controllable when its state/input pair is controllable.

Reference: Kailath, *Linear Systems*. -/
def IsControllable (r : Realization 𝕜 n m p) : Prop :=
  LinearSystems.IsControllable r.A r.B

/-- A realization is observable when its state/output pair is observable.

Reference: Kailath, *Linear Systems*. -/
def IsObservable (r : Realization 𝕜 n m p) : Prop :=
  LinearSystems.IsObservable r.A r.C

end Realization

end LinearSystems

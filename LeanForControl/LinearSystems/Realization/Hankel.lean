import LeanForControl.LinearSystems.Realization.MarkovParameters
import Mathlib.LinearAlgebra.Matrix.Rank
import Architect

/-!
# Finite Hankel matrices of a realization

Arbitrary row and column horizons are retained explicitly. This lets a single
finite Hankel matrix be compared across behaviorally equivalent realizations
whose state dimensions differ.

Reference: Kailath, *Linear Systems*.
-/

namespace LinearSystems

open Matrix

namespace Realization

variable {𝕜 : Type*} [CommSemiring 𝕜]
variable {n n₁ n₂ m p r s : ℕ}

/-- The finite-horizon controllability block matrix
`[B, A B, ..., A^(s-1) B]`.

Reference: Kailath, *Linear Systems*. -/
def controllabilityHorizon (R : Realization 𝕜 n m p) (s : ℕ) :
    Matrix (Fin n) (Fin s × Fin m) 𝕜 :=
  Matrix.of fun i kj => (R.A ^ (kj.1 : ℕ) * R.B) i kj.2

/-- The finite-horizon observability block matrix with block rows
`C, C A, ..., C A^(r-1)`.

Reference: Kailath, *Linear Systems*. -/
def observabilityHorizon (R : Realization 𝕜 n m p) (r : ℕ) :
    Matrix (Fin r × Fin p) (Fin n) 𝕜 :=
  Matrix.of fun ki j => (R.C * R.A ^ (ki.1 : ℕ)) ki.2 j

/-- The finite block Hankel matrix whose `(i,j)` block is the Markov
parameter `C A^(i+j) B`.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "def:finite-hankel-matrix"
  (statement := /-- For row horizon $r$ and column horizon $s$, the finite
    Hankel matrix has block $(i,j)$ equal to $CA^{i+j}B$. -/)]
def hankelMatrix (R : Realization 𝕜 n m p) (r s : ℕ) :
    Matrix (Fin r × Fin p) (Fin s × Fin m) 𝕜 :=
  Matrix.of fun ia jb => (R.markovParameter ((ia.1 : ℕ) + (jb.1 : ℕ))) ia.2 jb.2

/-- A finite Hankel matrix depends only on external behavior.

Original: semantic bridge for LeanForControl. -/
theorem BehaviorallyEquivalent.hankelMatrix_eq
    {R₁ : Realization 𝕜 n₁ m p} {R₂ : Realization 𝕜 n₂ m p}
    (h : R₁.BehaviorallyEquivalent R₂) (r s : ℕ) :
    R₁.hankelMatrix r s = R₂.hankelMatrix r s := by
  ext ia jb
  exact congrFun (congrFun (h.2 ((ia.1 : ℕ) + (jb.1 : ℕ))) ia.2) jb.2

/-- The finite Hankel matrix factors through the state space as the product
of the finite observability and controllability matrices.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "thm:hankel-factorization"
  (statement := /-- Every finite Hankel matrix factors as the finite
    observability matrix times the finite controllability matrix. -/)]
theorem hankelMatrix_eq_observability_mul_controllability
    (R : Realization 𝕜 n m p) (r s : ℕ) :
    R.hankelMatrix r s = R.observabilityHorizon r * R.controllabilityHorizon s := by
  ext ia jb
  simp only [hankelMatrix, markovParameter, observabilityHorizon,
    controllabilityHorizon, Matrix.of_apply, Matrix.mul_apply]
  rw [pow_add, ← Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.mul_assoc]

/-- At the state dimension, the finite controllability horizon is the
library's controllability matrix.

Original: compatibility lemma for LeanForControl. -/
theorem controllabilityHorizon_stateDim (R : Realization 𝕜 n m p) :
    R.controllabilityHorizon n = LinearSystems.controllabilityMatrix R.A R.B :=
  rfl

/-- At the state dimension, the finite observability horizon is the
library's observability matrix.

Original: compatibility lemma for LeanForControl. -/
theorem observabilityHorizon_stateDim (R : Realization 𝕜 n m p) :
    R.observabilityHorizon n = LinearSystems.observabilityMatrix R.A R.C :=
  rfl

end Realization

end LinearSystems

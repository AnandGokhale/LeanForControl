import LeanForControl.LinearSystems.Basic

/-!
# Controllability of a finite-dimensional linear system

For a linear system

  ẋ = A x + B u

with `A : Matrix (Fin n) (Fin n) 𝕜` and `B : Matrix (Fin n) (Fin m) 𝕜`, this
file defines the (finite-horizon) controllability matrix

  𝒞(A, B) = [ B   A·B   A²·B   ⋯   Aⁿ⁻¹·B ] .

We index columns by `Fin n × Fin m` so that `A ^ (k : ℕ)` is available without
casting `k : Fin n` through `Fin.val`.

This file deliberately stays at the *definition + shape lemma* level: the
controllability characterizations (reachable subspace = span of columns,
controllable iff full column rank) are second-milestone work. -/

namespace LinearSystems

open Matrix

variable {𝕜 : Type*} [Semiring 𝕜]
variable {n m : ℕ}

/-- The controllability matrix of `(A, B)`.

The `(k, j)`-th column is the `j`-th column of `Aᵏ · B`, where `k : Fin n`
ranges over `0, 1, …, n-1`. -/
def controllabilityMatrix
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    Matrix (Fin n) (Fin n × Fin m) 𝕜 :=
  Matrix.of fun i kj => (A ^ (kj.1 : ℕ) * B) i kj.2

/-- Block-column shape lemma: the entry at row `i`, column `(k, j)` of the
controllability matrix is the `(i, j)` entry of `Aᵏ · B`. Holds
definitionally. -/
@[simp]
lemma controllabilityMatrix_apply
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (i : Fin n) (k : Fin n) (j : Fin m) :
    controllabilityMatrix A B i (k, j) = (A ^ (k : ℕ) * B) i j :=
  rfl

end LinearSystems

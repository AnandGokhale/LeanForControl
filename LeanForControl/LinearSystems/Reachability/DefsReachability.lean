import LeanForControl.LinearSystems.Controllability
import Architect

/-!
# Definition of the reachable subspace

This file defines the reachable subspace of a finite-dimensional linear
system as the range of its finite-horizon controllability matrix.

References:
* João P. Hespanha, *Linear Systems Theory*.
* R. E. Kalman, “Mathematical Description of Linear Dynamical Systems,”
  *Journal of the Society for Industrial and Applied Mathematics, Series A:
  Control* 1(2), 152–192, 1963. DOI: 10.1137/0301010.
* Kailath, *Linear Systems*.
-/

namespace LinearSystems

variable {𝕜 : Type*} [Field 𝕜]
variable {n m : ℕ}

/-- The reachable subspace of `(A, B)`, defined as the range of the
finite-horizon controllability matrix.

Reference: Hespanha, *Linear Systems Theory*. -/
@[blueprint "def:reachableSubspace"
  (statement := /-- The reachable subspace of a pair $(A,B)$ is the column
    span of its controllability matrix:
    \[
      \mathcal R(A,B)=\operatorname{range}\mathcal C(A,B).
    \]
    Thus it is exactly the span of $B,AB,\ldots,A^{n-1}B$. -/)]
noncomputable def reachableSubspace
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    Submodule 𝕜 (Fin n → 𝕜) :=
  LinearMap.range (controllabilityMatrix A B).mulVecLin

end LinearSystems

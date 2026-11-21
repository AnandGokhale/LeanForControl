import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed
import Architect

/-!
# Matrices as operators on Euclidean space

`Matrix.toEuclideanCLM` reads a square matrix as a bounded operator on `EuclideanSpace ℝ X`.  It is
continuous and bounded by the matrix norm, being linear on a finite-dimensional space, and it
takes the transpose to the adjoint.

After `open Matrix`, a matrix acts on a Euclidean vector by `A • x`, so statements read as on paper:
`x(t) = e^{A(t-t₀)} x(t₀)` is `x t = exp ((t - t₀) • A) • x t₀`.  The action is a module structure,
so `(A * B) • x = A • B • x` and linearity come for free; `smul_euclidean_def` unfolds it to
`toEuclideanCLM`.  Where the operator itself is the object (a Jacobian, an operator norm) it is
still written `toEuclideanCLM A`.

Reference: standard linear algebra.
-/

namespace Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `toEuclideanCLM`, which reads a matrix as an operator on Euclidean space, is continuous: it is
linear on a finite-dimensional space. -/
theorem continuous_toEuclideanCLM : Continuous (toEuclideanCLM (n := X) (𝕜 := ℝ)) :=
  LinearMap.continuous_of_finiteDimensional
    (toEuclideanCLM (n := X) (𝕜 := ℝ)).toAlgEquiv.toLinearMap

open scoped Matrix.Norms.Operator in
/-- The matrices' Euclidean operators are bounded by their `L∞` norms, up to a constant: a linear
map between finite-dimensional spaces is continuous.  No explicit constant is needed. -/
theorem exists_norm_toEuclideanCLM_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : Matrix X X ℝ, ‖toEuclideanCLM (n := X) (𝕜 := ℝ) M‖ ≤ C * ‖M‖ := by
  let T : Matrix X X ℝ →L[ℝ] (EuclideanSpace ℝ X →L[ℝ] EuclideanSpace ℝ X) :=
    LinearMap.toContinuousLinearMap
      (toEuclideanCLM (n := X) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap
  exact ⟨‖T‖, norm_nonneg _, fun M => T.le_opNorm M⟩

/-- The transpose of a matrix is the adjoint of the operator it defines on Euclidean space. -/
@[blueprint "lem:toEuclideanCLM-transpose"
  (title := "The transpose is the adjoint")
  (latexEnv := "lemma")
  (statement := /-- For a real square matrix $M$, the operator of $M^{\mathsf T}$ on Euclidean
    space is the adjoint of the operator of $M$. -/)]
theorem toEuclideanCLM_transpose (M : Matrix X X ℝ) :
    toEuclideanCLM (n := X) (𝕜 := ℝ) Mᵀ = star (toEuclideanCLM (n := X) (𝕜 := ℝ) M) := by
  rw [← conjTranspose_eq_transpose_of_trivial, ← Matrix.star_eq_conjTranspose]
  exact (toEuclideanCLM (n := X) (𝕜 := ℝ)).map_star' M

/-- A real matrix acts on `ℝⁿ` with the Euclidean norm: `A • x` is `A x`. -/
noncomputable scoped instance : Module (Matrix X X ℝ) (EuclideanSpace ℝ X) :=
  Module.compHom _ (toEuclideanCLM (n := X) (𝕜 := ℝ)).toRingEquiv.toRingHom

theorem smul_euclidean_def (A : Matrix X X ℝ) (x : EuclideanSpace ℝ X) :
    A • x = toEuclideanCLM (n := X) (𝕜 := ℝ) A x := rfl

/-- A matrix commutes with real scalars: `A • (c • x) = c • A • x`. -/
scoped instance : SMulCommClass (Matrix X X ℝ) ℝ (EuclideanSpace ℝ X) :=
  ⟨fun A c x => by simp [smul_euclidean_def]⟩

end Matrix

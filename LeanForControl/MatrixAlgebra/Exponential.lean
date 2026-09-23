import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# The matrix exponential as an algebraic object

This file collects facts relating the matrix exponential to entrywise complexification —
algebraic and norm-compatibility bridges between the real and complex matrix exponential,
with no system semantics (no Hurwitz hypothesis, no spectral conclusion).

Reference: standard properties of the matrix exponential.
-/

namespace MatrixAlgebra

open Matrix NormedSpace
open scoped Matrix.Norms.Frobenius

variable {n : ℕ}

/-- Entrywise complexification commutes with the matrix exponential.

Original: compatibility bridge for the real and complex matrix exponential. -/
lemma complexification_exp (A : Matrix (Fin n) (Fin n) ℝ) :
    (exp A).map (algebraMap ℝ ℂ) = exp (A.map (algebraMap ℝ ℂ)) := by
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℝ) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  let φ : Matrix (Fin n) (Fin n) ℝ →+* Matrix (Fin n) (Fin n) ℂ :=
    (algebraMap ℝ ℂ).mapMatrix
  have hφ : Continuous φ := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact Complex.continuous_ofReal.comp
      ((continuous_apply j).comp (continuous_apply i))
  simpa [φ] using NormedSpace.map_exp φ hφ A

end MatrixAlgebra

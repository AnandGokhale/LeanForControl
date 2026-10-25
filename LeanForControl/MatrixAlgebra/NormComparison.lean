import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed

/-!
# Sup norm against Euclidean norm

Linear time-varying systems carry the sup norm on `X → ℝ` and the `L∞` operator norm on
matrices (`Matrix.Norms.Operator`); nonlinear systems carry the Euclidean norm on
`EuclideanSpace ℝ X`.  This file compares the two, so that results pass between them.

## Main results

* `norm_ofLp_le`, `norm_le_sqrt_card_mul_norm_ofLp` — `‖y‖∞ ≤ ‖y‖₂ ≤ √|X| ‖y‖∞`.
* `sq_norm_le_dotProduct_self` — `‖v‖∞² ≤ v ⬝ᵥ v`.
* `norm_le_of_mulVec_le` — a bound `‖M v‖∞ ≤ C ‖v‖∞` bounds the `L∞` operator norm.
* `norm_toEuclideanCLM_le`, `norm_toEuclideanCLM_symm_le` — the Euclidean and `L∞` operator
  norms of a matrix agree up to the factor `√|X|`.
-/

namespace MatrixAlgebra

open Matrix WithLp
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X]

/-- The sup norm is at most the Euclidean norm. -/
lemma norm_ofLp_le (y : EuclideanSpace ℝ X) : ‖ofLp y‖ ≤ ‖y‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr fun i => PiLp.norm_apply_le y i

/-- The Euclidean norm is at most `√|X|` times the sup norm. -/
lemma norm_le_sqrt_card_mul_norm_ofLp (y : EuclideanSpace ℝ X) :
    ‖y‖ ≤ √(Fintype.card X) * ‖ofLp y‖ := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg (ofLp y)),
    ← Real.sqrt_mul (Nat.cast_nonneg _)]
  gcongr
  calc ∑ i, ‖y i‖ ^ 2
      ≤ ∑ _i : X, ‖ofLp y‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        gcongr
        exact norm_le_pi_norm (ofLp y) i
    _ = Fintype.card X * ‖ofLp y‖ ^ 2 := by simp

/-- The square of the sup norm is at most the sum of squares. -/
lemma sq_norm_le_dotProduct_self (v : X → ℝ) : ‖v‖ ^ 2 ≤ v ⬝ᵥ v :=
  calc ‖v‖ ^ 2
      ≤ ‖toLp 2 v‖ ^ 2 := by
        gcongr
        simpa using norm_ofLp_le (toLp 2 v)
    _ = v ⬝ᵥ v := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [dotProduct, sq]

/-- A bound `‖M x‖ ≤ C ‖x‖` on every vector is a bound on the `L∞` operator norm. -/
lemma norm_le_of_mulVec_le {M : Matrix X X ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖M *ᵥ x‖ ≤ C * ‖x‖) : ‖M‖ ≤ C := by
  rw [linfty_opNorm_eq_opNorm]
  exact ContinuousLinearMap.opNorm_le_bound _ hC h

/-! ## Quadratic forms under the sup norm -/

/-- `|x ⬝ᵥ y| ≤ |X| ‖x‖ ‖y‖` for the sup norm. -/
theorem abs_dotProduct_le (x y : X → ℝ) :
    |x ⬝ᵥ y| ≤ Fintype.card X * (‖x‖ * ‖y‖) :=
  calc |x ⬝ᵥ y|
      ≤ ∑ i, |x i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : X, ‖x‖ * ‖y‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
        exact mul_le_mul (norm_le_pi_norm x i) (norm_le_pi_norm y i) (norm_nonneg _)
          (norm_nonneg _)
    _ = Fintype.card X * (‖x‖ * ‖y‖) := by simp

/-- `xᵀ M x ≤ |X| ‖M‖ ‖x‖²` for the sup norm and the `L∞` operator norm. -/
theorem dotProduct_mulVec_le (M : Matrix X X ℝ) (x : X → ℝ) :
    x ⬝ᵥ (M *ᵥ x) ≤ Fintype.card X * ‖M‖ * ‖x‖ ^ 2 :=
  calc x ⬝ᵥ (M *ᵥ x)
      ≤ Fintype.card X * (‖x‖ * ‖M *ᵥ x‖) := (le_abs_self _).trans (abs_dotProduct_le _ _)
    _ ≤ Fintype.card X * (‖x‖ * (‖M‖ * ‖x‖)) := by gcongr; exact linfty_opNorm_mulVec M x
    _ = Fintype.card X * ‖M‖ * ‖x‖ ^ 2 := by ring

/-- `xᵀ (Mᵀ N M) x = (M x)ᵀ N (M x)`. -/
theorem dotProduct_transpose_mul_mulVec (M N : Matrix X X ℝ) (x : X → ℝ) :
    x ⬝ᵥ ((Mᵀ * N * M) *ᵥ x) = (M *ᵥ x) ⬝ᵥ (N *ᵥ (M *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

variable [DecidableEq X]

/-- The Euclidean operator norm of a matrix is at most `√|X|` times its `L∞` operator norm. -/
lemma norm_toEuclideanCLM_le (M : Matrix X X ℝ) :
    ‖Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ) M‖ ≤ √(Fintype.card X) * ‖M‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y =>
    calc ‖Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ) M y‖
        ≤ √(Fintype.card X) * ‖M *ᵥ ofLp y‖ := by
          simpa using norm_le_sqrt_card_mul_norm_ofLp (Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ) M y)
      _ ≤ √(Fintype.card X) * (‖M‖ * ‖y‖) := by
          gcongr
          exact (linfty_opNorm_mulVec M _).trans (by gcongr; exact norm_ofLp_le y)
      _ = √(Fintype.card X) * ‖M‖ * ‖y‖ := by ring

/-- The `L∞` operator norm of the matrix of a Euclidean operator is at most `√|X|` times its
operator norm. -/
lemma norm_toEuclideanCLM_symm_le (J : EuclideanSpace ℝ X →L[ℝ] EuclideanSpace ℝ X) :
    ‖(Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ)).symm J‖ ≤ √(Fintype.card X) * ‖J‖ :=
  norm_le_of_mulVec_le (by positivity) fun v =>
    calc ‖(Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ)).symm J *ᵥ v‖
        = ‖ofLp (J (toLp 2 v))‖ := by
          conv_rhs =>
            rw [← StarAlgEquiv.apply_symm_apply (Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ)) J]
          rw [ofLp_toEuclideanCLM, ofLp_toLp]
      _ ≤ ‖J‖ * ‖toLp 2 v‖ := (norm_ofLp_le _).trans (J.le_opNorm _)
      _ ≤ ‖J‖ * (√(Fintype.card X) * ‖v‖) := by
          gcongr
          simpa using norm_le_sqrt_card_mul_norm_ofLp (toLp 2 v)
      _ = √(Fintype.card X) * ‖J‖ * ‖v‖ := by ring

end MatrixAlgebra

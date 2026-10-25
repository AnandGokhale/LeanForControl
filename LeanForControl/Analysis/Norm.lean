import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Architect

/-!
# Norm inequalities

Elementary inequalities for norms that the stability proofs use repeatedly.
-/

/-- **Squared norms differ by at most `(‖a‖ + ‖b‖) ‖a - b‖`**: a difference of squares and the
reverse triangle inequality. -/
@[blueprint "lem:abs-norm-sq-sub-norm-sq-le"
  (title := "Difference of squared norms")
  (latexEnv := "lemma")
  (statement := /-- In a seminormed group,
    $\bigl|\|a\|^2 - \|b\|^2\bigr| \le (\|a\| + \|b\|)\,\|a - b\|$. -/)
  (proof := /-- $\|a\|^2 - \|b\|^2 = (\|a\| + \|b\|)(\|a\| - \|b\|)$, and
    $\bigl|\|a\| - \|b\|\bigr| \le \|a - b\|$. -/)]
theorem abs_norm_sq_sub_norm_sq_le {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le a b) (by positivity)

/-- **The norm of a pair is at most the sum of the norms of its components**: the product norm is
the maximum, which is at most the sum. -/
@[blueprint "lem:prod-norm-le-norm-fst-add-norm-snd"
  (title := "Norm of a pair")
  (latexEnv := "lemma")
  (statement := /-- For $p = (p_1, p_2)$ in a product of seminormed groups, with the max norm,
    $\|p\| \le \|p_1\| + \|p_2\|$. -/)
  (proof := /-- $\|p\| = \max\{\|p_1\|, \|p_2\|\}$, and the maximum of two nonnegative numbers
    is at most their sum. -/)]
theorem Prod.norm_le_norm_fst_add_norm_snd {E₁ E₂ : Type*} [SeminormedAddGroup E₁]
    [SeminormedAddGroup E₂] (p : E₁ × E₂) : ‖p‖ ≤ ‖p.1‖ + ‖p.2‖ := by
  rw [Prod.norm_def]
  exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)

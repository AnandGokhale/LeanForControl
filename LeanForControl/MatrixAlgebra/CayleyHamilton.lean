import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Cayley--Hamilton, solved for the top power

`A ^ n` is a linear combination of `A ^ 0, …, A ^ (n - 1)`
(`pow_card_eq_neg_sum_charpoly_coeff`).  Both the reachable and the unobservable subspace use it
for `A`-invariance.  It holds over any nontrivial commutative ring.

Reference: standard linear algebra.
-/

namespace Matrix

variable {R : Type*} [CommRing R] [Nontrivial R]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Cayley--Hamilton, solved for the top power: an `n × n` matrix satisfies
`A ^ n = -∑_{i < n} cᵢ • A ^ i`, where `cᵢ` are the coefficients of its characteristic
polynomial. So any property closed under linear combinations that holds for
`A ^ 0, …, A ^ (n - 1)` also holds for `A ^ n`. -/
lemma pow_card_eq_neg_sum_charpoly_coeff (A : Matrix n n R) :
    A ^ Fintype.card n =
      -∑ i ∈ Finset.range (Fintype.card n), A.charpoly.coeff i • A ^ i := by
  -- Expand `aeval A A.charpoly = 0` as a sum of `card n + 1` terms and split off the top
  -- one, whose coefficient is `1` because the characteristic polynomial is monic.
  have hCH : Polynomial.aeval A A.charpoly = 0 := Matrix.aeval_self_charpoly A
  have hdeg : A.charpoly.natDegree = Fintype.card n := Matrix.charpoly_natDegree_eq_dim A
  have hmonic : A.charpoly.coeff (Fintype.card n) = 1 := by
    rw [← hdeg]
    exact A.charpoly_monic.leadingCoeff
  rw [Polynomial.aeval_eq_sum_range, hdeg, Finset.sum_range_succ, hmonic, one_smul] at hCH
  exact eq_neg_of_add_eq_zero_right hCH

end Matrix

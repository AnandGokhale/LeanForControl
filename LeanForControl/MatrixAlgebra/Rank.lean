import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# `MatrixAlgebra.Rank`

Reusable matrix-level facts that bridge

* the kernel-of-`*ᵥ` formulation,
* the linear-map-`ker = ⊥` formulation,
* and the `Matrix.rank` / full-column-rank formulation,

together with the one Cayley--Hamilton consequence that both the reachable and the
unobservable subspace need for `A`-invariance: `A ^ n` is a linear combination of
`A ^ 0, …, A ^ (n - 1)` (`pow_card_eq_neg_sum_charpoly_coeff`).

This file has no system semantics — it is generic matrix-algebra
infrastructure, consumed by `LinearSystems.Observability.Observability` and
`LinearSystems.Controllability.Controllability`. It carries no `@[blueprint]`
annotations and intentionally exposes no LaTeX nodes — control-level
statements belong in those two files.

The rank bridges are `Field`-scoped: `Matrix.rank` requires `[CommRing 𝕜]`, and the
column or row independence bridges to `rank = card ...` need `[Field 𝕜]`. The
Cayley--Hamilton expansion holds over any nontrivial commutative ring.
-/

namespace MatrixAlgebra

open Matrix

section Field

variable {𝕜 : Type*} [Field 𝕜]
variable {m n : Type*}

/-- Bridge between the kernel-of-`*ᵥ` form and the rank-equals-card-of-columns
form: a matrix `M : Matrix m n 𝕜` over a field has full column rank iff the
only `x` with `M *ᵥ x = 0` is the zero vector.

Proof chains `Matrix.ker_mulVecLin_eq_bot_iff` with rank-nullity. -/
lemma mulVec_kernel_trivial_iff_rank_eq_card_cols [Fintype n] (M : Matrix m n 𝕜) :
    (∀ x : n → 𝕜, M *ᵥ x = 0 → x = 0) ↔ Matrix.rank M = Fintype.card n := by
  rw [← Matrix.ker_mulVecLin_eq_bot_iff]
  have hsum := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_pi] at hsum
  unfold Matrix.rank
  constructor
  · intro hker
    rw [hker, finrank_bot] at hsum
    omega
  · intro hrank
    have h0 : Module.finrank 𝕜 (LinearMap.ker M.mulVecLin) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp h0

/-- Bridge between the surjectivity-of-`*ᵥ` form and the rank-equals-card-of-rows
form: a matrix `M : Matrix m n 𝕜` over a field has full row rank iff every `y`
in the codomain is in the range of `M *ᵥ ·`. -/
lemma mulVec_range_top_iff_rank_eq_card_rows
    [Fintype m] [Fintype n] (M : Matrix m n 𝕜) :
    (∀ y : m → 𝕜, ∃ x : n → 𝕜, M *ᵥ x = y) ↔ Matrix.rank M = Fintype.card m := by
  have hsurj_iff :
      (∀ y : m → 𝕜, ∃ x : n → 𝕜, M *ᵥ x = y)
        ↔ LinearMap.range M.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    rfl
  rw [hsurj_iff]
  unfold Matrix.rank
  constructor
  · intro h
    rw [h, finrank_top, Module.finrank_pi]
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    rw [h, Module.finrank_pi]

end Field

section CayleyHamilton

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

end CayleyHamilton

end MatrixAlgebra

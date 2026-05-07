import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# `LinearSystems.MatrixLemmas`

Reusable matrix-level facts that bridge

* the kernel-of-`*ᵥ` formulation,
* the linear-map-`ker = ⊥` formulation,
* and the `Matrix.rank` / full-column-rank formulation.

This file is project-internal plumbing for `LinearSystems.Observability` and
`LinearSystems.Controllability`. It carries no `@[blueprint]` annotations and
intentionally exposes no LaTeX nodes — control-level statements belong in the
two `Observability` / `Controllability` files.

The file is `Field`-scoped: `Matrix.rank` requires `[CommRing 𝕜]`, and the
column or row independence bridges to `rank = card ...` need `[Field 𝕜]`.
-/

namespace LinearSystems.MatrixLemmas

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

end LinearSystems.MatrixLemmas

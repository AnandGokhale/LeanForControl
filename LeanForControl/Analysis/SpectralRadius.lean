import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# A contractive power from a spectral radius bound

This file has no matrices in it: it is a general Banach-algebra consequence of Gelfand's
spectral-radius formula, used by `MatrixAlgebra`/`LinearSystems` to bound the matrix
exponential but stated for an arbitrary complete normed algebra over `ℂ`.

Reference: Rudin, *Functional Analysis* (Gelfand's spectral-radius formula).
-/

open Filter Set
open scoped Topology

/-- An element with spectral radius strictly below one has a positive power whose norm is
strictly below one.

Reference: Rudin, *Functional Analysis* (Gelfand's spectral-radius formula). -/
lemma exists_pow_norm_lt_one_of_spectralRadius_lt_one
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    [Nontrivial 𝔸] (a : 𝔸) (ha : spectralRadius ℂ a < 1) :
    ∃ m : ℕ, 0 < m ∧ ‖a ^ m‖ < 1 := by
  have heventually : ∀ᶠ m : ℕ in atTop,
      ((↑‖a ^ m‖₊ : ENNReal) ^ (1 / (m : ℝ))) < 1 :=
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a)
      (Iio_mem_nhds ha)
  have hnonzero : ∀ᶠ m : ℕ in atTop, m ≠ 0 := eventually_ne_atTop 0
  obtain ⟨m, hmroot, hm0⟩ := (heventually.and hnonzero).exists
  refine ⟨m, Nat.pos_of_ne_zero hm0, ?_⟩
  by_contra hnot
  have hbase : (1 : ENNReal) ≤ (↑‖a ^ m‖₊ : ENNReal) := by
    apply ENNReal.coe_le_coe.mpr
    change (1 : ℝ) ≤ ‖a ^ m‖
    exact not_lt.mp hnot
  have hexponent : 0 < (1 / (m : ℝ)) :=
    one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0))
  exact (not_le_of_gt hmroot) (ENNReal.one_le_rpow hbase hexponent)

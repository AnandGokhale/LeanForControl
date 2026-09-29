import Mathlib.Analysis.Normed.Algebra.GelfandFormula

import Architect

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
@[blueprint "lem:exists-pow-norm-lt-one"
  (title := "A contractive power from a spectral radius below one")
  (latexEnv := "lemma")
  (statement := /-- Let $\mathbb{A}$ be a nontrivial complete normed algebra over $\mathbb{C}$
    and let $a \in \mathbb{A}$ have spectral radius $r(a) < 1$.  Then there is an $m > 0$ with
    $\|a^m\| < 1$. -/)
  (proof := /-- Gelfand's formula gives $\|a^m\|^{1/m} \to r(a)$, so $\|a^m\|^{1/m} < 1$ for all
    large $m$; pick any such $m$ with $m \neq 0$.  Were $\|a^m\| \ge 1$, raising to the positive
    power $1/m$ would give $\|a^m\|^{1/m} \ge 1$, a contradiction. -/)]
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

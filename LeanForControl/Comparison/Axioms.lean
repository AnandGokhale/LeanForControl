import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKInfty
import LeanForControl.Comparison.ClassKL


/-- Given `φ : ℝ≥0 × ℝ≥0 → ℝ` satisfying uniform convergence to zero in the first argument
    and uniform stability near zero, there exists a global class KL function `β` with
    `φ r s ≤ β r s` for all `r s ≥ 0`.

    This is the global analogue of Lemma 9 in Kellett, *A compendium of comparison function
    results* (2014), stated on `ℝ≥0 × ℝ≥0` with the paper's exact hypotheses. -/
axiom exists_classKLGlobal_of_stability_properties
    (φ : ℝ → ℝ → ℝ)
    (h_convergence : ∀ r > 0, ∀ ε > 0, ∃ T > 0,
        ∀ s, 0 ≤ s → s ≤ r → ∀ t ≥ T, φ s t < ε)
    (h_uniform_stability : ∀ ε > 0, ∃ δ > 0,
        ∀ s, 0 ≤ s → s ≤ δ → ∀ t ≥ 0, φ s t ≤ ε) :
    ∃ β : ClassKLGlobal, ∀ r ≥ 0, ∀ s ≥ 0, φ r s ≤ β.toFun r s


/-- Any class K function `α` on `[0, a)` has a class K minorant `β ≤ α` that is globally
Lipschitz on a neighbourhood of `0`. The Lipschitz extension `β_ext` agrees with `β` on `[0, a)`
and satisfies `β(x) ≤ L·x` near the base point. -/
axiom exists_classK_minorant_lipschitz {a b : ℝ} (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a) :
    ∃ (β : ClassK a b) (β_ext : ℝ → ℝ) (L : ℝ) (hL_pos : 0 < L),
      (∀ x ∈ Set.Ico 0 a, β.toFun x ≤ α.toFun x) ∧
      (∀ x ∈ Set.Ico 0 a, β_ext x = β.toFun x) ∧
      (∀ x ∈ Set.Ioc 0 base, β.toFun x ≤ L * x) ∧
      Continuous β_ext ∧
      LipschitzWith ⟨L, hL_pos.le⟩ β_ext

/-- Every class K function `α` on `[0, a)` extends to a continuous, monotone function on all
of `ℝ` that agrees with `α` on `[0, a)`. -/
axiom ClassK.exists_global_extension {a b : ℝ} (α : ClassK a b) :
    ∃ (α_ext : ℝ → ℝ),
      Continuous α_ext ∧
      (∀ x ∈ Set.Ico 0 a, α_ext x = α.toFun x) ∧
      (∀ x y, x ≤ y → α_ext x ≤ α_ext y)

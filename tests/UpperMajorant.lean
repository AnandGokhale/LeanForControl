import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! A regression proof for the endpoint hypothesis of continuous upper majorants.
Run `lake env lean tests/UpperMajorant.lean` from the repository root.
-/

open Set Filter
open scoped Topology

namespace UpperMajorantRegression

/-- The monotone step function that witnesses the missing right-continuity-at-zero
hypothesis in `exists_strictMono_upper_bound_global`. -/
noncomputable def zeroOneStep (s : ℝ) : ℝ := if s ≤ 0 then 0 else 1

/-- The step counterexample vanishes at zero. -/
theorem zeroOneStep_zero : zeroOneStep 0 = 0 := by
  simp [zeroOneStep]

/-- The step counterexample is monotone on the nonnegative reals. -/
theorem zeroOneStep_monotoneOn : MonotoneOn zeroOneStep (Ici 0) := by
  intro a ha b hb hab
  unfold zeroOneStep
  split_ifs <;> linarith

/-- No continuous majorant vanishing at zero can dominate `zeroOneStep` on the
nonnegative reals.  This refutes the former upper-majorant assumptions without using
the conclusion's strict-monotonicity or unboundedness clauses. -/
theorem zeroOneStep_has_no_continuous_majorant_at_zero :
    ¬ ∃ f : ℝ → ℝ,
      f 0 = 0 ∧
      ContinuousOn f (Ici 0) ∧
      ∀ s ≥ 0, zeroOneStep s ≤ f s := by
  rintro ⟨f, hf_zero, hf_cont, hf_bound⟩
  have hseq_mem : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1 : ℝ) := by
    intro n
    positivity
  have hseq_tendsto : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hf_tendsto : Tendsto (fun n : ℕ => f (1 / (n + 1 : ℝ))) atTop (𝓝 (f 0)) :=
    (hf_cont.continuousWithinAt (mem_Ici.mpr le_rfl)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hseq_tendsto, Eventually.of_forall fun n =>
        mem_Ici.mpr (hseq_mem n).le⟩)
  have h_lower : ∀ n : ℕ, (1 : ℝ) ≤ f (1 / (n + 1 : ℝ)) := by
    intro n
    have h := hf_bound (1 / (n + 1 : ℝ)) (hseq_mem n).le
    rw [zeroOneStep, if_neg (not_le.mpr (hseq_mem n))] at h
    exact h
  have : (1 : ℝ) ≤ f 0 :=
    ge_of_tendsto' hf_tendsto h_lower
  linarith

end UpperMajorantRegression

#print axioms UpperMajorantRegression.zeroOneStep_has_no_continuous_majorant_at_zero

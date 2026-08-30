import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue

open MeasureTheory intervalIntegral Real Set Filter

lemma sSup_mem_of_isClosed {S : Set ℝ}
    (hS : S.Nonempty) (hBdd : BddAbove S) (hCl : IsClosed S) : sSup S ∈ S :=
  hCl.csSup_mem hS hBdd

/-- If a continuous function starts ≤ 0 and ends > 0, it has a last root `a` in `[t₀, t₁)`,
    after which it is strictly positive on `(a, t₁]`. -/
lemma ContinuousOn.exists_greatest_zero_of_nonpos_of_pos {g : ℝ → ℝ} {t₀ t₁ : ℝ}
    (hg_cont : ContinuousOn g (Icc t₀ t₁))
    (ht : t₀ < t₁) (hg_start : g t₀ ≤ 0) (hg_end : 0 < g t₁) :
    ∃ a ∈ Ico t₀ t₁, g a = 0 ∧ ∀ t ∈ Ioc a t₁, 0 < g t := by
  haveI : CompactSpace ↥(Icc t₀ t₁) := isCompact_iff_compactSpace.mp isCompact_Icc
  let f : Icc t₀ t₁ → ℝ := fun x => g x.val
  have h_pre_closed : IsClosed (f ⁻¹' {0}) := isClosed_singleton.preimage hg_cont.restrict
  -- 2. Prove the preimage is nonempty via IVT
  obtain ⟨c, hc_mem, hc_eq⟩ := intermediate_value_Icc ht.le hg_cont ⟨hg_start, hg_end.le⟩
  have h_pre_nonempty : (f ⁻¹' {0}).Nonempty := ⟨⟨c, hc_mem⟩, hc_eq⟩
  -- 3. A closed subset of a compact space is compact, so it attains its maximum!
  -- This completely replaces `sSup`, `BddAbove`, and the `Subtype.val ''` mapping.
  obtain ⟨m, hm_mem, hm_max⟩ :=
    h_pre_closed.isCompact.exists_isMaxOn h_pre_nonempty continuous_subtype_val.continuousOn
  let a := m.val
  use a
  have ha_mem_Icc : a ∈ Icc t₀ t₁ := m.property
  have ha_eq_zero : g a = 0 := hm_mem
  -- 4. Prove `a < t₁`
  have ha_lt_t1 : a < t₁ := by
    by_contra h_not
    have ha_eq_t1 : a = t₁ := le_antisymm ha_mem_Icc.2 (not_lt.mp h_not)
    rw [ha_eq_t1] at ha_eq_zero
    linarith
  refine ⟨⟨ha_mem_Icc.1, ha_lt_t1⟩, ha_eq_zero, ?_⟩
  -- 5. Strict positivity on (a, t₁] via IVT contradiction
  intro t ht_mem
  by_contra h_not
  push Not at h_not
  have h_cont_sub : ContinuousOn g (Icc t t₁) :=
    hg_cont.mono (Icc_subset_Icc (ha_mem_Icc.1.trans ht_mem.1.le) le_rfl)
  obtain ⟨r, hr_mem, hr_eq⟩ := intermediate_value_Icc ht_mem.2 h_cont_sub ⟨h_not, hg_end.le⟩
  -- Package `r` back into our subtype to contradict the maximum `m`
  let r_sub : Icc t₀ t₁ := ⟨r, ⟨ha_mem_Icc.1.trans (ht_mem.1.le.trans hr_mem.1), hr_mem.2⟩⟩
  have hr_in_pre : r_sub ∈ f ⁻¹' {0} := hr_eq
  -- By the definition of `exists_isMaxOn`, `m` is an upper bound for the set.
  have h_contra : a < a := ht_mem.1.trans_le (hr_mem.1.trans (hm_max hr_in_pre))
  linarith

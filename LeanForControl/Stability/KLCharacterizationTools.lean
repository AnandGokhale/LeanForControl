import LeanForControl.Stability.DefsNonAutonomous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKInfty
import LeanForControl.Comparison.ClassKL

import LeanForControl.Analysis.Integrals
import LeanForControl.Analysis.MonotoneFunctions

import Architect

/-!
# `Stability.KLCharacterizationTools`

Uniform decay envelopes: a single function of elapsed time that bounds *every* trajectory
starting in a given ball, extracted from a uniform convergence-time hypothesis.

Reference: Sontag, *Comments on integral variants of ISS* (1998), the smoothing construction
behind Khalil's Lemma 4.5.

## Main results

* `exists_classLSingular_decayBound` — the local envelope, a single `ClassLSingular`.
* `exists_decayBound_family` — the global envelope, a family indexed by the radius.

Only these two are public; both are consumed by `Stability/KLCharacterization.lean`. Everything
else here is the construction behind them.

## The construction (private)

`Tbar_fn f x_eq η r` is the least delay `T` after which *every* trajectory starting within `r`
of `x_eq` is inside the `η`-ball — the infimum of the `T`s that `LocallyHasUniformConvergenceTime`
asserts to exist. It is antitone in `η` but need not be continuous, so it cannot itself serve as
an envelope. Averaging it over a sliding window,

  `W_fn f x_eq r η = (2/η) ∫_{η/2}^{η} [T̄(s,r) + r/η] ds`,

smooths it: `W_fn f x_eq r` is continuous and *strictly* antitone on `(0,∞)`, blows up as
`η → 0⁺` and vanishes as `η → ∞`. Inverting it (`Analysis/MonotoneFunctions`) exchanges those
two boundary behaviours, giving a decay envelope in elapsed time. The `r/η` term is what makes
the average strictly antitone rather than merely antitone, and forces the blow-up at `0⁺`.

Neither `Tbar_fn` nor `W_fn` appears in the statements above: a caller receives an envelope with
the properties it needs, not this particular one.
-/

open MeasureTheory intervalIntegral Set Filter Topology

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## T̄ — optimal uniform convergence time -/

private noncomputable def validTSet (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (η r : ℝ) : Set ℝ :=
  {T | 0 ≤ T ∧ ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
    IsTrajectoryNA φ f t₀ → ‖φ t₀ - x_eq‖ < r → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η}

/-- `Tbar_fn f x_eq η r` is the infimum of valid convergence times from the `r`-ball to the
    `η`-ball: the smallest `T` that works for all trajectories simultaneously. -/
private noncomputable def Tbar_fn (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (η r : ℝ) : ℝ :=
  sInf (validTSet f x_eq η r)

private lemma validTSet_bddBelow (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (η r : ℝ) :
    BddBelow (validTSet f x_eq η r) :=
  ⟨0, fun _ hT => hT.1⟩

private lemma validTSet_nonempty {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {η : ℝ} (hη : 0 < η) {r : ℝ} (hr : r ∈ Set.Ioc 0 c) :
    (validTSet f x_eq η r).Nonempty := by
  obtain ⟨T, hT_pos, hT_prop⟩ := hconv η hη
  exact ⟨T, hT_pos.le, fun t₀ ht₀ φ hφ h_init t ht =>
    hT_prop t₀ ht₀ φ hφ (h_init.trans_le hr.2) t ht⟩

private lemma Tbar_nonneg_of {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {η : ℝ} (hη : 0 < η) {r : ℝ} (hr : r ∈ Set.Ioc 0 c) :
    0 ≤ Tbar_fn f x_eq η r :=
  le_csInf (validTSet_nonempty hconv hη hr) (fun _ hT => hT.1)

private lemma Tbar_antitone {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) :
    AntitoneOn (fun η => Tbar_fn f x_eq η r) (Set.Ioi 0) := by
  intro η₁ hη₁ η₂ hη₂ h_le
  exact csInf_le_csInf (validTSet_bddBelow f x_eq η₂ r) (validTSet_nonempty hconv hη₁ hr)
    fun T ⟨hT_nn, hT_prop⟩ => ⟨hT_nn,
      fun t₀ ht₀ φ hφ h_init t ht => (hT_prop t₀ ht₀ φ hφ h_init t ht).trans_le h_le⟩

private lemma Tbar_intervalIntegrable {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) :
    IntervalIntegrable (fun s => Tbar_fn f x_eq s r) MeasureTheory.volume a b := by
  apply AntitoneOn.intervalIntegrable
  exact (Tbar_antitone hconv hr).mono fun s hs => by
    rw [Set.uIcc_of_le hab] at hs; exact Set.mem_Ioi.mpr (ha.trans_le hs.1)

private lemma Tbar_intervalIntegrable_of_pos {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun s => Tbar_fn f x_eq s r) MeasureTheory.volume a b := by
  rcases le_total a b with hab | hab
  · exact Tbar_intervalIntegrable hconv hr hab ha
  · exact (Tbar_intervalIntegrable hconv hr hab hb).symm

private lemma Tbar_zero_of_classK_bound {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : HasUniformClassKBound f x_eq α)
    {a : ℝ} (ha_lt_aα : a < a_α) (ha_le_c : a ≤ c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 a) {η : ℝ} (h_le : α.toFun r ≤ η) :
    Tbar_fn f x_eq η r = 0 := by
  have hr_lt_aα : r < a_α := hr.2.trans_lt ha_lt_aα
  have hr_Ico : r ∈ Set.Ico 0 a_α := ⟨hr.1.le, hr_lt_aα⟩
  have h_alpha_pos : 0 < α.toFun r := (α.pos_iff hr_Ico).mpr hr.1
  have hη_pos : 0 < η := h_alpha_pos.trans_le h_le
  refine le_antisymm (csInf_le (validTSet_bddBelow f x_eq η r) ⟨le_refl 0, ?_⟩)
    (le_csInf (validTSet_nonempty hconv hη_pos ⟨hr.1, hr.2.trans ha_le_c⟩) (fun _ hT => hT.1))
  intro t₀ ht₀ φ hφ h_init t ht
  have h_stab := hα_bound t₀ ht₀ φ hφ (h_init.trans hr_lt_aα) t (by linarith)
  have h_strict := (α.strict_mono_iff ⟨norm_nonneg _, h_init.trans hr_lt_aα⟩ hr_Ico).mpr h_init
  exact (h_stab.trans_lt h_strict).trans_le h_le

private lemma Tbar_mono_r {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {r₁ r₂ : ℝ} (hr₂ : r₂ ∈ Set.Ioc 0 c) (h_le : r₁ ≤ r₂) {η : ℝ} (hη : 0 < η) :
    Tbar_fn f x_eq η r₁ ≤ Tbar_fn f x_eq η r₂ :=
  csInf_le_csInf (validTSet_bddBelow f x_eq η r₁) (validTSet_nonempty hconv hη hr₂)
    fun _T hT => ⟨hT.1, fun t₀ ht₀ φ hφ h_init t ht =>
      hT.2 t₀ ht₀ φ hφ (h_init.trans_le h_le) t ht⟩

/-- Unpacking the infimum: if `s > T̄(η, r)` then the trajectory has already reached the
    `η`-ball by elapsed time `s`. -/
private lemma norm_le_of_Tbar_lt {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {η r s t₀ t : ℝ} {φ : ℝ → ℝⁿ}
    (hne : (validTSet f x_eq η r).Nonempty)
    (hlt : Tbar_fn f x_eq η r < s) (ht₀ : 0 ≤ t₀)
    (hφ : IsTrajectoryNA φ f t₀) (h_init : ‖φ t₀ - x_eq‖ < r)
    (ht : t₀ + s ≤ t) :
    ‖φ t - x_eq‖ ≤ η := by
  -- sInf(validTSet) < s and validTSet nonempty ⇒ ∃ T ∈ validTSet, T < s ⇒ t₀ + T ≤ t
  obtain ⟨_T, ⟨_, hT_prop⟩, hT_lt⟩ := exists_lt_of_csInf_lt hne hlt
  exact (hT_prop t₀ ht₀ φ hφ h_init t (by linarith)).le

/-! ## W — sliding average of T̄ -/

/-- `W_fn f x_eq r η = (2/η) ∫_{η/2}^{η} [T̄(s,r) + r/η] ds`
    (Sontag 1998). Strictly decreasing in `η`, strictly increasing in `r`. -/
private noncomputable def W_fn (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (r η : ℝ) : ℝ :=
  (2 / η) * ∫ s in (η / 2)..η, (Tbar_fn f x_eq s r + r / η)

private lemma W_ge_Tbar {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) {η : ℝ} (hη : 0 < η) :
    Tbar_fn f x_eq η r + r / η ≤ W_fn f x_eq r η := by
  have h_int_sum : IntervalIntegrable (fun s => Tbar_fn f x_eq s r + r / η) volume (η / 2) η :=
    (Tbar_intervalIntegrable hconv hr (by linarith : η / 2 ≤ η) (half_pos hη)).add
      intervalIntegral.intervalIntegrable_const
  have h_anti := Tbar_antitone hconv hr
  have h_integral_bound :
      ∫ s in (η / 2)..η, Tbar_fn f x_eq η r + r / η ≤
      ∫ s in (η / 2)..η, Tbar_fn f x_eq s r + r / η := by
    refine intervalIntegral.integral_mono_on (by linarith)
      intervalIntegral.intervalIntegrable_const h_int_sum (fun s hs => ?_)
    have hs_pos : 0 < s := by linarith [hs.1]
    linarith [h_anti (Set.mem_Ioi.mpr hs_pos) (Set.mem_Ioi.mpr hη) hs.2]
  have h_const_int :
      ∫ s in (η / 2)..η, Tbar_fn f x_eq η r + r / η =
      (η / 2) * (Tbar_fn f x_eq η r + r / η) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  dsimp [W_fn]
  calc Tbar_fn f x_eq η r + r / η
      = (2 / η) * ((η / 2) * (Tbar_fn f x_eq η r + r / η)) := by
        rw [← mul_assoc, show (2 / η) * (η / 2) = 1 from by field_simp, one_mul]
    _ ≤ (2 / η) * ∫ s in (η / 2)..η, Tbar_fn f x_eq s r + r / η := by
        rw [← h_const_int]; gcongr

/-- Splitting the constant out of the average: the `r/η` term integrates to `r/2`, so
    `W = (2/η)∫T̄ + r/η`. Every property of `W` is read off this form. -/
private lemma W_fn_eq {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) {η : ℝ} (hη : 0 < η) :
    W_fn f x_eq r η = (2 / η) * (∫ s in (η / 2)..η, Tbar_fn f x_eq s r) + r / η := by
  simp only [W_fn]
  rw [intervalIntegral.integral_add
    (Tbar_intervalIntegrable hconv hr (le_of_lt (half_lt_self hη)) (half_pos hη))
    intervalIntegral.intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul]
  have h_const : (η - η / 2) * (r / η) = r / 2 := by field_simp; ring
  rw [h_const]; field_simp [hη.ne']

private lemma W_fn_continuousOn {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) : ContinuousOn (W_fn f x_eq r) (Set.Ioi 0) := by
  have h_int_cont : ContinuousOn (fun η => ∫ s in (η / 2)..η, Tbar_fn f x_eq s r) (Set.Ioi 0) :=
    continuousOn_integral_endpoints (Tbar_intervalIntegrable_of_pos hconv hr)
      (continuousOn_id.div_const 2) continuousOn_id
      (fun η hη => by have : (0 : ℝ) < η := hη; linarith) (fun η hη => hη)
  have h_rhs_cont : ContinuousOn
      (fun η => (2 / η) * (∫ s in (η / 2)..η, Tbar_fn f x_eq s r) + r / η) (Set.Ioi 0) := by
    refine ContinuousOn.add (ContinuousOn.mul ?_ h_int_cont) ?_ <;>
      exact fun η hη =>
        (continuousAt_const.div continuousAt_id (Set.mem_Ioi.mp hη).ne').continuousWithinAt
  exact h_rhs_cont.congr (fun η hη => W_fn_eq hconv hr hη)

private lemma W_fn_strictAntiOn {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) : StrictAntiOn (W_fn f x_eq r) (Set.Ioi 0) := by
  -- The average of an antitone function is antitone; the `r/η` term is what makes it strict.
  have h_avg_anti : AntitoneOn (fun η => (2 / η) * ∫ s in (η / 2)..η, Tbar_fn f x_eq s r)
      (Set.Ioi 0) := by
    refine AntitoneOn.congr (antitoneOn_integral_average
      (f := fun s => Tbar_fn f x_eq s r) (a := fun η => η / 2) (b := fun η => η)
      (Tbar_antitone hconv hr) (Tbar_intervalIntegrable_of_pos hconv hr)
      (fun η hη => by have h : (0 : ℝ) < η := hη; linarith)
      (fun η hη => by have h : (0 : ℝ) < η := hη; linarith)
      (fun _ _ _ _ hxy => by linarith) (fun _ _ _ _ hxy => hxy)) ?_
    intro η hη
    have h : (0 : ℝ) < η := hη
    field_simp
    ring
  have h_r_div_strict : StrictAntiOn (fun η => r / η) (Set.Ioi 0) := fun η₁ hη₁ η₂ hη₂ h_lt =>
    (div_lt_div_iff₀ hη₂ hη₁).mpr (mul_lt_mul_of_pos_left h_lt hr.1)
  intro η₁ hη₁ η₂ hη₂ h_lt
  rw [W_fn_eq hconv hr hη₁, W_fn_eq hconv hr hη₂]
  linarith [h_avg_anti hη₁ hη₂ h_lt.le, h_r_div_strict hη₁ hη₂ h_lt]

private lemma W_fn_tendsto_nhdsGT {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) :
    Filter.Tendsto (W_fn f x_eq r) (𝓝[>] 0) Filter.atTop := by
  -- `W ≥ r/η`, which already blows up at `0⁺`.
  have h_lower_bound : ∀ᶠ η in 𝓝[>] (0 : ℝ), r / η ≤ W_fn f x_eq r η := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    linarith [W_ge_Tbar hconv hr hη, Tbar_nonneg_of hconv hη hr]
  have h_r_div : Filter.Tendsto (fun η : ℝ => r / η) (𝓝[>] 0) Filter.atTop := by
    simpa [div_eq_mul_inv] using Filter.Tendsto.const_mul_atTop hr.1 tendsto_inv_nhdsGT_zero
  exact tendsto_atTop_mono' (𝓝[>] 0) h_lower_bound h_r_div

private lemma W_fn_tendsto_atTop {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : HasUniformClassKBound f x_eq α)
    {a : ℝ} (ha_le_c : a ≤ c) (ha_lt_aα : a < a_α)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 a) :
    Filter.Tendsto (W_fn f x_eq r) Filter.atTop (nhds 0) := by
  have hr_c : r ∈ Set.Ioc 0 c := ⟨hr.1, hr.2.trans ha_le_c⟩
  have h_avg : Filter.Tendsto (fun η => (2 / η) * ∫ s in (η / 2)..η, Tbar_fn f x_eq s r)
      Filter.atTop (nhds 0) := by
    have h := tendsto_integral_average_atTop_zero
      (f := fun s => Tbar_fn f x_eq s r) (a := fun η => η / 2) (b := fun η => η)
      (fun s hs => Tbar_nonneg_of hconv hs hr_c)
      (Tbar_antitone hconv hr_c)
      (Tbar_intervalIntegrable_of_pos hconv hr_c)
      (by -- For large enough η the class K bound α(r) is a finite ceiling, so T̄ = 0 eventually.
        have h_eventually_zero : ∀ᶠ η in Filter.atTop, Tbar_fn f x_eq η r = 0 := by
          filter_upwards [Filter.eventually_ge_atTop (α.toFun r)] with η hη
          exact Tbar_zero_of_classK_bound hconv α hα_bound ha_lt_aα ha_le_c hr hη
        exact tendsto_const_nhds.congr' (h_eventually_zero.mono (fun _ h => h.symm)))
      (by filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with η hη; linarith)
      (tendsto_id.atTop_div_const zero_lt_two)
    refine h.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with η hη
    field_simp
    ring
  have h_rdiv : Filter.Tendsto (fun η => r / η) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using Filter.Tendsto.const_mul r tendsto_inv_atTop_zero
  have h_sum := h_avg.add h_rdiv
  simp only [add_zero] at h_sum
  refine h_sum.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with η hη
  exact (W_fn_eq hconv hr_c hη).symm

private lemma W_fn_mono_r {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {r₁ r₂ : ℝ} (hr₁ : r₁ ∈ Set.Ioc 0 c) (hr₂ : r₂ ∈ Set.Ioc 0 c) (h_le : r₁ ≤ r₂)
    {η : ℝ} (hη : 0 < η) :
    W_fn f x_eq r₁ η ≤ W_fn f x_eq r₂ η := by
  rw [W_fn_eq hconv hr₁ hη, W_fn_eq hconv hr₂ hη]
  refine add_le_add ?_ (div_le_div_of_nonneg_right h_le hη.le)
  gcongr
  exact intervalIntegral.integral_mono_on (half_le_self hη.le)
    (Tbar_intervalIntegrable_of_pos hconv hr₁ (η / 2) η (half_pos hη) hη)
    (Tbar_intervalIntegrable_of_pos hconv hr₂ (η / 2) η (half_pos hη) hη)
    fun x hx => Tbar_mono_r hconv hr₂ h_le (by linarith [hx.1])

/-! ## The inverse of `W` — the decay envelope -/

/-- The four facts about `W_fn f x_eq r` that `Analysis/MonotoneFunctions` needs in order to
    invert it: continuous, strictly antitone, blowing up at `0⁺` and vanishing at `+∞`. -/
private lemma W_fn_invertible {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : HasUniformClassKBound f x_eq α)
    {a : ℝ} (ha_le_c : a ≤ c) (ha_lt_aα : a < a_α)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 a) :
    ContinuousOn (W_fn f x_eq r) (Set.Ioi 0) ∧ StrictAntiOn (W_fn f x_eq r) (Set.Ioi 0) ∧
      Filter.Tendsto (W_fn f x_eq r) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (W_fn f x_eq r) (𝓝[>] 0) Filter.atTop :=
  have hr_c : r ∈ Set.Ioc 0 c := ⟨hr.1, hr.2.trans ha_le_c⟩
  ⟨W_fn_continuousOn hconv hr_c, W_fn_strictAntiOn hconv hr_c,
    W_fn_tendsto_atTop hconv α hα_bound ha_le_c ha_lt_aα hr, W_fn_tendsto_nhdsGT hconv hr_c⟩

private lemma invFunOn_mono_r {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : HasUniformClassKBound f x_eq α)
    {a : ℝ} (ha_le_c : a ≤ c) (ha_lt_aα : a < a_α)
    {r₁ r₂ : ℝ} (hr₁ : r₁ ∈ Set.Ioc 0 a) (hr₂ : r₂ ∈ Set.Ioc 0 a) (h_le : r₁ ≤ r₂)
    {s : ℝ} (hs : 0 < s) :
    Function.invFunOn (W_fn f x_eq r₁) (Set.Ioi 0) s ≤
      Function.invFunOn (W_fn f x_eq r₂) (Set.Ioi 0) s := by
  obtain ⟨hc₁, ha₁, hz₁, ht₁⟩ := W_fn_invertible hconv α hα_bound ha_le_c ha_lt_aα hr₁
  obtain ⟨hc₂, ha₂, hz₂, ht₂⟩ := W_fn_invertible hconv α hα_bound ha_le_c ha_lt_aα hr₂
  -- By contradiction: if the inverses were out of order, `W r₁` would exceed itself at `U₂`.
  by_contra h_contra
  have h_strict := ha₁ (invFunOn_pos hc₂ hz₂ ht₂ hs) (invFunOn_pos hc₁ hz₁ ht₁ hs)
    (not_le.mp h_contra)
  rw [apply_invFunOn_eq hc₁ hz₁ ht₁ hs] at h_strict
  linarith [h_strict, W_fn_mono_r hconv ⟨hr₁.1, hr₁.2.trans ha_le_c⟩
    ⟨hr₂.1, hr₂.2.trans ha_le_c⟩ h_le (invFunOn_pos hc₂ hz₂ ht₂ hs),
    apply_invFunOn_eq hc₂ hz₂ ht₂ hs]

/-- The inverse of `W` bounds the decay: a trajectory starting strictly inside the `r`-ball is
    within `invFunOn (W_fn f x_eq r) (Ioi 0) (t - t₀)` of `x_eq` at every later time. -/
private lemma U_decay_bound {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : HasUniformClassKBound f x_eq α)
    {a : ℝ} (ha_le_c : a ≤ c) (ha_lt_aα : a < a_α)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 a)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {φ : ℝ → ℝⁿ} (hφ : IsTrajectoryNA φ f t₀)
    (h_init : ‖φ t₀ - x_eq‖ < r) {t : ℝ} (ht : t₀ < t) :
    ‖φ t - x_eq‖ ≤ Function.invFunOn (W_fn f x_eq r) (Set.Ioi 0) (t - t₀) := by
  obtain ⟨hc, hanti, hz, htop⟩ := W_fn_invertible hconv α hα_bound ha_le_c ha_lt_aα hr
  have hr_c : r ∈ Set.Ioc 0 c := ⟨hr.1, hr.2.trans ha_le_c⟩
  have hs : 0 < t - t₀ := sub_pos.mpr ht
  set U := Function.invFunOn (W_fn f x_eq r) (Set.Ioi 0) (t - t₀) with hU_def
  have hU_pos : 0 < U := invFunOn_pos hc hz htop hs
  -- `U` is the radius whose *optimal* convergence time the elapsed time `t - t₀` exceeds …
  have h_Tbar_lt : Tbar_fn f x_eq U r < t - t₀ := by
    calc Tbar_fn f x_eq U r
        < Tbar_fn f x_eq U r + r / U := lt_add_of_pos_right _ (div_pos hr.1 hU_pos)
      _ ≤ W_fn f x_eq r U            := W_ge_Tbar hconv hr_c hU_pos
      _ = t - t₀                     := apply_invFunOn_eq hc hz htop hs
  -- … so `t - t₀` is itself a valid convergence time to the `U`-ball.
  exact norm_le_of_Tbar_lt (validTSet_nonempty hconv hU_pos hr_c) h_Tbar_lt ht₀ hφ h_init
    (by linarith)

/-! ## The local envelope -/

/-- **Local uniform decay envelope.** Uniform convergence times on the `c`-ball together with a
    uniform class `K` bound `α` produce a *single* singular class `L` function `U` — one
    function of elapsed time alone — bounding every trajectory that starts within `a` of `x_eq`.

    This is the time-decay half of the class `KL` characterization: `α` carries the dependence
    on the initial deviation and `U` the decay in elapsed time.

    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.5. -/
@[blueprint "lem:exists-classLSingular-decayBound"
  (title := "Local uniform decay envelope")
  (latexEnv := "lemma")
  (statement := /-- Suppose the trajectories of $\dot{x} = f(t,x)$ have local uniform
    convergence times on the ball of radius $c$ (\cref{def:locallyHasUniformConvergenceTime})
    and admit a uniform class $\mathcal{K}$ bound $\alpha$ defined on $[0, a_\alpha)$
    (\cref{def:hasUniformClassKBound}).  Let $0 < a \le c$ with $a < a_\alpha$.  Then there is a
    singular class $\mathcal{L}$ function $U$ (\cref{def:isClassLSingular}) such that
    \[
      \|\varphi(t) - x_{\mathrm{eq}}\| \le U(t - t_{0})
    \]
    for every $t_{0} \ge 0$, every trajectory $\varphi$ on $[t_{0},\infty)$ with
    $\|\varphi(t_{0}) - x_{\mathrm{eq}}\| < a$, and every $t > t_{0}$.

    The bound depends on the elapsed time alone: neither on $t_{0}$, nor on the trajectory, nor
    on where in the $a$-ball it started.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.5.
  -/)
  (proof := /-- Let $\bar{T}(\eta, r)$ be the least delay after which every trajectory starting
    within $r$ of $x_{\mathrm{eq}}$ lies inside the $\eta$-ball; it is finite by hypothesis and
    antitone in $\eta$, but possibly discontinuous.  Smooth it by the sliding average
    \[
      W(r, \eta) = \frac{2}{\eta}\int_{\eta/2}^{\eta}
        \Bigl[\bar{T}(s, r) + \frac{r}{\eta}\Bigr]\,ds,
    \]
    which equals $\frac{2}{\eta}\int_{\eta/2}^{\eta}\bar{T}(s,r)\,ds + r/\eta$.  The averaged
    term is antitone in $\eta$ and the $r/\eta$ term is strictly antitone, so $W(r, \cdot)$ is
    continuous and strictly antitone on $(0,\infty)$; it dominates $r/\eta$, hence tends to
    $+\infty$ as $\eta \to 0^{+}$, and $\bar{T}(\cdot, r)$ vanishes beyond $\alpha(r)$, hence
    $W(r, \eta) \to 0$ as $\eta \to \infty$.  Inverting it (\cref{lem:invFunOnPos},
    \cref{lem:strictAntiOnInvFunOn}, \cref{lem:invFunOnTendstoZero},
    \cref{lem:invFunOnContinuousOn}, \cref{lem:invFunOnTendstoAtTop}) gives
    $U = \mathrm{invFunOn}\,W(r,\cdot)\,(0,\infty)$, singular class $\mathcal{L}$.  Finally
    $W(r, U(s)) = s$ and $W \ge \bar{T} + r/\eta$ give $\bar{T}(U(s), r) < s$, so $s$ is itself
    a valid convergence time to the $U(s)$-ball, which is the claimed bound. -/)]
theorem exists_classLSingular_decayBound {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {c : ℝ}
    (hconv : LocallyHasUniformConvergenceTime f x_eq c)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : HasUniformClassKBound f x_eq α)
    {a : ℝ} (ha : 0 < a) (ha_le_c : a ≤ c) (ha_lt_aα : a < a_α) :
    ∃ U : ClassLSingular,
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f t₀ → ‖φ t₀ - x_eq‖ < a →
        ∀ t : ℝ, t₀ < t → ‖φ t - x_eq‖ ≤ U.toFun (t - t₀) := by
  obtain ⟨hc, hanti, hz, htop⟩ :=
    W_fn_invertible hconv α hα_bound ha_le_c ha_lt_aα (⟨ha, le_rfl⟩ : a ∈ Set.Ioc 0 a)
  exact ⟨{ toFun        := Function.invFunOn (W_fn f x_eq a) (Set.Ioi 0)
           continuous   := invFunOn_continuousOn hc hanti hz htop
           pos          := fun _ hs => invFunOn_pos hc hz htop hs
           anti         := (strictAntiOn_invFunOn hc hanti hz htop).antitoneOn
           tendsto_zero := invFunOn_tendsto_zero hc hanti hz htop
           tendsto_top  := invFunOn_tendsto_atTop hc hanti hz htop },
    fun _ ht₀ _ hφ h_init _ ht =>
      U_decay_bound hconv α hα_bound ha_le_c ha_lt_aα ⟨ha, le_rfl⟩ ht₀ hφ h_init ht⟩

/-! ## The global envelope -/

/-- Construct a `ClassK b (α b)` from a `ClassKInfty` by restriction to `[0, b]`. -/
private noncomputable def mk_ClassK_from_KInfty (α : ClassKInfty) {b : ℝ} (hb : 0 < b) :
    ClassK b (α.toFun b) :=
  ClassK.of_strictMono hb
    ((α.pos_iff (Set.mem_Ici.mpr hb.le)).mpr hb)
    α.toFun α.map_zero rfl
    (α.continuous.mono Set.Icc_subset_Ici_self)
    (α.strict_mono.mono Set.Icc_subset_Ici_self)

/-- A uniform class `K∞` bound restricts to a uniform class `K` bound at any finite radius.

This is the only place the global and local bound notions differ, so it is stated once here
rather than rebuilt inside each global lemma. -/
private lemma HasUniformClassKInftyBound.toClassK
    {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {α : ClassKInfty}
    (h : HasUniformClassKInftyBound f x_eq α) {b : ℝ} (hb : 0 < b) :
    HasUniformClassKBound f x_eq (mk_ClassK_from_KInfty α hb) :=
  fun t₀ ht₀ φ hφ _ t ht => h t₀ ht₀ φ hφ t ht

/-- **Global uniform decay envelope.** Global uniform convergence times together with a uniform
    class `K∞` bound produce a family `U` of decay envelopes, indexed by the radius of the ball
    the trajectory starts in: `U r` is positive, antitone and vanishing at `+∞`, the family is
    monotone in `r`, and `U r (t - t₀)` bounds every trajectory starting within `r` of `x_eq`.

    The four shape conditions are exactly the hypotheses of
    `ClassKLGlobal.of_KInfty_LSingular_family`, which is what consumes this result.

    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.5 (global case). -/
@[blueprint "lem:exists-decayBound-family"
  (title := "Global uniform decay envelope")
  (latexEnv := "lemma")
  (statement := /-- Suppose the trajectories of $\dot{x} = f(t,x)$ have global uniform
    convergence times (\cref{def:globallyHasUniformConvergenceTime}) and admit a uniform class
    $\mathcal{K}_{\infty}$ bound (\cref{def:hasUniformClassKInftyBound}).  Then there is a
    family $U : (0,\infty) \times (0,\infty) \to \mathbb{R}$ with
    \begin{enumerate}
      \item $U(r, s) > 0$ for all $r > 0$ and $s > 0$;
      \item $U(r, \cdot)$ antitone on $(0,\infty)$ for each $r > 0$;
      \item $U(r, s) \to 0$ as $s \to \infty$, for each $r > 0$;
      \item $r \mapsto U(r+1, s)$ monotone on $[0,\infty)$ for each $s > 0$;
      \item $\|\varphi(t) - x_{\mathrm{eq}}\| \le U(r, t - t_{0})$ for every $r > 0$, every
        $t_{0} \ge 0$, every trajectory $\varphi$ on $[t_{0},\infty)$ with
        $\|\varphi(t_{0}) - x_{\mathrm{eq}}\| < r$, and every $t > t_{0}$.
    \end{enumerate}
    Conditions (1)--(4) are exactly the hypotheses of
    \cref{lem:classKLGlobal-of-KInfty-LSingular-family}; (5) is the decay bound.  Unlike the
    local case (\cref{lem:exists-classLSingular-decayBound}) no single envelope can serve every
    initial state, so the radius remains a parameter.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.5 (global case).
  -/)
  (proof := /-- Every radius is finite, so at radius $r$ the global hypotheses restrict to the
    local ones (uniform convergence times on the $r$-ball, and the class $\mathcal{K}_{\infty}$
    bound read as a class $\mathcal{K}$ bound on $[0, r+1)$).  Take $U(r, \cdot)$ to be the
    envelope of \cref{lem:exists-classLSingular-decayBound} at that radius, namely the inverse
    of $W(r, \cdot)$.  Conditions (1)--(3) and (5) are then that lemma's conclusions, and (4)
    holds because $W$ is monotone in $r$ — a larger ball has larger optimal convergence times —
    so inverting reverses nothing. -/)]
theorem exists_decayBound_family {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (α : ClassKInfty)
    (hGUC : GloballyHasUniformConvergenceTime f x_eq)
    (h_bound : HasUniformClassKInftyBound f x_eq α) :
    ∃ U : ℝ → ℝ → ℝ,
      (∀ r > 0, ∀ s > 0, 0 < U r s) ∧
      (∀ r > 0, AntitoneOn (U r) (Set.Ioi 0)) ∧
      (∀ r > 0, Filter.Tendsto (U r) Filter.atTop (nhds 0)) ∧
      (∀ s > 0, MonotoneOn (fun r => U (r + 1) s) (Set.Ici 0)) ∧
      (∀ r > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f t₀ →
        ‖φ t₀ - x_eq‖ < r → ∀ t : ℝ, t₀ < t → ‖φ t - x_eq‖ ≤ U r (t - t₀)) := by
  -- At radius `r` the global hypotheses restrict to the local ones, with `c = r` and the class
  -- `K∞` bound read as a class `K` bound on `[0, r+1)`.
  have shape : ∀ r : ℝ, 0 < r →
      ContinuousOn (W_fn f x_eq r) (Set.Ioi 0) ∧ StrictAntiOn (W_fn f x_eq r) (Set.Ioi 0) ∧
        Filter.Tendsto (W_fn f x_eq r) Filter.atTop (nhds 0) ∧
        Filter.Tendsto (W_fn f x_eq r) (𝓝[>] 0) Filter.atTop := fun r hr =>
    W_fn_invertible (hGUC r hr) (mk_ClassK_from_KInfty α (by linarith : (0:ℝ) < r + 1))
      (h_bound.toClassK _) le_rfl (by linarith) ⟨hr, le_rfl⟩
  refine ⟨fun r => Function.invFunOn (W_fn f x_eq r) (Set.Ioi 0), ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr s hs
    obtain ⟨hc, _, hz, htop⟩ := shape r hr
    exact invFunOn_pos hc hz htop hs
  · intro r hr
    obtain ⟨hc, hanti, hz, htop⟩ := shape r hr
    exact (strictAntiOn_invFunOn hc hanti hz htop).antitoneOn
  · intro r hr
    obtain ⟨hc, hanti, hz, htop⟩ := shape r hr
    exact invFunOn_tendsto_zero hc hanti hz htop
  · -- Monotone in the radius: localize at the larger radius `r₂ + 1`, which contains both.
    intro s hs r₁ hr₁ r₂ hr₂ h_le
    have hr1_nn : (0 : ℝ) ≤ r₁ := hr₁
    have hr2_nn : (0 : ℝ) ≤ r₂ := hr₂
    exact invFunOn_mono_r (hGUC (r₂ + 1) (by linarith))
      (mk_ClassK_from_KInfty α (by linarith : (0:ℝ) < r₂ + 2)) (h_bound.toClassK _)
      le_rfl (by linarith) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      (by linarith) hs
  · intro r hr t₀ ht₀ φ hφ h_init t ht
    exact U_decay_bound (hGUC r hr) (mk_ClassK_from_KInfty α (by linarith : (0:ℝ) < r + 1))
      (h_bound.toClassK _) le_rfl (by linarith) ⟨hr, le_rfl⟩ ht₀ hφ h_init ht

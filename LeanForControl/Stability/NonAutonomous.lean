import LeanForControl.Stability.DefsNonAutonomous
import LeanForControl.Stability.NA_axioms
import LeanForControl.Stability.classK
import LeanForControl.axioms

import Architect


open MeasureTheory



variable {n : ℕ}

/-!
# `Stability.NonAutonomous`

Comparison-function characterisations of stability for non-autonomous ODEs `ẋ = f(t, x)`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.5.

## Main results

* **Lemma 4.5 (i)** (`uniformlyStableNA_iff_classK`): `UniformlyStableNA` iff there exist
  a class K function `α` and `c > 0` (independent of `t₀`) such that
  `‖x(t) - x_eq‖ ≤ α(‖x(t₀) - x_eq‖)` for all `t ≥ t₀ ≥ 0`, `‖x(t₀) - x_eq‖ < c`. (4.19)

* **Lemma 4.5 (ii)** (`uniformlyAsymptoticStableNA_iff_classKL`): `UniformlyAsymptoticStableNA`
  iff there exist a class KL function `β` and `c > 0` (independent of `t₀`) such that
  `‖x(t) - x_eq‖ ≤ β(‖x(t₀) - x_eq‖, t − t₀)` for all `t ≥ t₀ ≥ 0`, `‖x(t₀) - x_eq‖ < c`.
  (4.20)

* **Lemma 4.5 (iii)** (`globallyUniformlyAsymptoticStableNA_iff_classKL`):
  `GloballyUniformlyAsymptoticStableNA` iff the class KL bound (4.20) holds for every
  initial state (no restriction on `‖x(t₀) - x_eq‖`).
-/

open Set Filter Topology

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)



lemma uniformlyStable_implies_classK (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    (hUS : UniformlyStableNA f x_eq) :
    ∃ (a b : ℝ) (_ : 0 < a) (_ : 0 < b) (α : ClassK a b),
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
        IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < a →
        ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ α.toFun (‖φ t₀ - x_eq‖) := by
  obtain ⟨δ₀, hδ₀, hUS_1⟩ := hUS 1 one_pos
  let a := δ₀ / 2
  have ha       : 0 < a   := half_pos hδ₀
  have ha_lt_δ₀ : a < δ₀  := half_lt_self hδ₀
  let reachable (r : ℝ) : Set ℝ :=
    {d | ∃ (φ : ℝ → ℝⁿ) (t₀ t : ℝ), 0 ≤ t₀ ∧ t₀ ≤ t ∧ IsTrajectoryNA φ f ∧
         ‖φ t₀ - x_eq‖ ≤ r ∧ d = ‖φ t - x_eq‖}
  let ω (r : ℝ) : ℝ := sSup (reachable r)
  -- Common bound: any reachable d ≤ 1 when the initial radius is ≤ a
  have hbdd_of_le : ∀ r ≤ a, BddAbove (reachable r) := fun r hr =>
    ⟨1, fun d ⟨φ, t₀, t, ht₀, ht, hφ, h_init, heq⟩ =>
      heq ▸ le_of_lt (hUS_1 t₀ ht₀ φ hφ (h_init.trans_lt (hr.trans_lt ha_lt_δ₀)) t ht)⟩
  -- ω(0) = 0: stability at ε forces any ‖φ t₀ - x_eq‖ = 0 trajectory to stay at 0
  have hω_zero : ω 0 = 0 := by
    apply le_antisymm
    · refine Real.sSup_le ?_ le_rfl
      rintro d ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩
      have h0 : ‖φ t₀ - x_eq‖ = 0 := le_antisymm h_init (norm_nonneg _)
      refine le_of_forall_pos_lt_add (fun ε hε => ?_)
      obtain ⟨δ, hδ, hUS_ε⟩ := hUS ε hε
      linarith [hUS_ε t₀ ht₀ φ hφ (h0 ▸ hδ) t ht]
    · rcases (reachable 0).eq_empty_or_nonempty with h | ⟨d, hd⟩
      · change 0 ≤ sSup (reachable 0); rw [h]; simp
      · obtain ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩ := hd
        exact (norm_nonneg _).trans
          (le_csSup (hbdd_of_le 0 ha.le) ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩)
  -- ω non-decreasing on [0, a]: reachable r₁ ⊆ reachable r₂ when r₁ ≤ r₂ ≤ a
  have hω_mono : ∀ s₁ s₂, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ a → ω s₁ ≤ ω s₂ := by
    intro s₁ s₂ hs₁ hs₁₂ hs₂
    have hbdd₂ := hbdd_of_le s₂ hs₂
    rcases (reachable s₁).eq_empty_or_nonempty with h | hne
    · have hω₁ : ω s₁ = 0 := by change sSup (reachable s₁) = 0; rw [h]; simp
      rw [hω₁]; change 0 ≤ sSup (reachable s₂)
      rcases (reachable s₂).eq_empty_or_nonempty with h2 | ⟨d, hd⟩
      · rw [h2]; simp
      · obtain ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩ := hd
        exact (norm_nonneg _).trans (le_csSup hbdd₂ ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩)
    · refine csSup_le_csSup hbdd₂ hne ?_
      rintro d ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩
      exact ⟨φ, t₀, t, ht₀, ht, hφ, h_init.trans hs₁₂, rfl⟩
  -- Class K majorant: exists_strictMono_upper_bound lifts ω to a strictly increasing bound
  obtain ⟨b, hb, α, hα_bound⟩ : ∃ (b : ℝ) (_ : 0 < b) (α : ClassK a b),
      ∀ r ∈ Set.Ico 0 a, ω r ≤ α.toFun r := by
    obtain ⟨g, b, hb, hg_zero, hg_a, hg_cont, hg_mono, hg_bound⟩ :=
      exists_strictMono_upper_bound a ha ω hω_zero hω_mono
    exact ⟨b, hb, ClassK.of_strictMono ha hb g hg_zero hg_a hg_cont hg_mono,
      fun r hr => hg_bound r hr.1 hr.2.le⟩
  -- Chain: ‖φ t - x_eq‖ ≤ ω(‖φ t₀ - x_eq‖) ≤ α(‖φ t₀ - x_eq‖)
  refine ⟨a, b, ha, hb, α, fun t₀ ht₀ φ hφ h_init t ht => ?_⟩
  have hr : ‖φ t₀ - x_eq‖ ∈ Set.Ico 0 a := ⟨norm_nonneg _, h_init⟩
  exact (le_csSup (s := reachable (‖φ t₀ - x_eq‖)) (hbdd_of_le _ hr.2.le)
      ⟨φ, t₀, t, ht₀, ht, hφ, le_rfl, rfl⟩).trans (hα_bound _ hr)


/-- **Lemma 4.5 (i)**: The equilibrium `x_eq` is uniformly stable if and only if there exist
    a class K function `α` on `[0, c)` and a constant `c > 0` (independent of `t₀`) such that
    every trajectory with `‖φ t₀ - x_eq‖ < c` satisfies
    `‖φ t - x_eq‖ ≤ α(‖φ t₀ - x_eq‖)` for all `t ≥ t₀ ≥ 0`. -/
@[blueprint "lem:uniformlyStableNA-iff-classK"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ of $\dot{x} = f(t,x)$ is
    \emph{uniformly stable} (\cref{def:uniformlyStableNA}) if and only if there exist a
    class $\mathcal{K}$ function $\alpha$ and a positive constant $c$, independent of
    $t_{0}$, such that
    \[
      \|\varphi(t) - x_{\mathrm{eq}}\| \le \alpha(\|\varphi(t_{0}) - x_{\mathrm{eq}}\|)
      \quad \forall\, t \ge t_{0} \ge 0,\; \forall\, \|\varphi(t_{0}) - x_{\mathrm{eq}}\| < c.
    \] -/)]
theorem uniformlyStableNA_iff_classK (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) :
    UniformlyStableNA f x_eq ↔
    ∃ (a b : ℝ) (_ : 0 < a) (_ : 0 < b) (α : ClassK a b),
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
        IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < a →
        ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ α (‖φ t₀ - x_eq‖) := by
  refine ⟨uniformlyStable_implies_classK f x_eq, ?_⟩
  · rintro ⟨a, b, ha, hb, α, hα⟩ ε hε
    have h_cont := α.continuous 0 ⟨le_refl 0, α.ha⟩
    rw [Metric.continuousWithinAt_iff] at h_cont
    rcases h_cont ε hε with ⟨δ_c, hδ_c_pos, hδ_c⟩
    let δ := min (δ_c / 2) (a / 2)
    have hδ_pos : 0 < δ  := lt_min (half_pos hδ_c_pos) (half_pos ha)
    have hδ_a   : δ < a  := (min_le_right ..).trans_lt (half_lt_self ha)
    have hδ_lt  : δ < δ_c := (min_le_left ..).trans_lt (half_lt_self hδ_c_pos)
    refine ⟨δ, hδ_pos, fun t₀ ht₀ φ hφ h_init t ht => ?_⟩
    have h_mono := α.strict_mono ⟨norm_nonneg _, h_init.trans hδ_a⟩ ⟨hδ_pos.le, hδ_a⟩ h_init
    have h_alpha := hδ_c ⟨hδ_pos.le, hδ_a⟩
      (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ_pos]; exact hδ_lt)
    rw [α.map_zero, Real.dist_eq, sub_zero] at h_alpha
    linarith [hα t₀ ht₀ φ hφ (h_init.trans hδ_a) t ht, h_mono, (abs_lt.mp h_alpha).2]


/-! ### T̄ — optimal convergence-time function -/

/-- `validTSet f x_eq η r` is the set of times `T ≥ 0` such that every trajectory starting
    within `r` of `x_eq` reaches within `η` of `x_eq` after time `T`. -/
private noncomputable def validTSet (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (η r : ℝ) : Set ℝ :=
  {T | 0 ≤ T ∧ ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
    IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < r → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η}

/-- `Tbar_fn f x_eq η r` is the infimum of valid convergence times from the `r`-ball to the
    `η`-ball: the smallest `T` that works for all trajectories simultaneously. -/
private noncomputable def Tbar_fn (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (η r : ℝ) : ℝ :=
  sInf (validTSet f x_eq η r)

private lemma validTSet_bddBelow (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (η r : ℝ) :
    BddBelow (validTSet f x_eq η r) :=
  ⟨0, fun _ hT => hT.1⟩

private lemma validTSet_nonempty (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {η : ℝ} (hη : 0 < η) {r : ℝ} (hr : r ∈ Set.Ioc 0 c) :
    (validTSet f x_eq η r).Nonempty := by
  obtain ⟨T, hT_pos, hT_prop⟩ := hconv η hη
  exact ⟨T, hT_pos.le, fun t₀ ht₀ φ hφ h_init t ht =>
    hT_prop t₀ ht₀ φ hφ (h_init.trans_le hr.2) t ht⟩

private lemma Tbar_nonneg_of (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {η : ℝ} (hη : 0 < η) {r : ℝ} (hr : r ∈ Set.Ioc 0 c) :
    0 ≤ Tbar_fn f x_eq η r :=
  le_csInf (validTSet_nonempty f x_eq hconv hη hr) (fun _ hT => hT.1)

private lemma Tbar_antitone (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) :
    AntitoneOn (fun η => Tbar_fn f x_eq η r) (Set.Ioi 0) := by
  intro η₁ hη₁ η₂ hη₂ h_le
  apply csInf_le_csInf (validTSet_bddBelow f x_eq η₂ r)
    (validTSet_nonempty f x_eq hconv hη₁ hr)
  rintro T ⟨hT_nn, hT_prop⟩
  exact ⟨hT_nn, fun t₀ ht₀ φ hφ h_init t ht => (hT_prop t₀ ht₀ φ hφ h_init t ht).trans_le h_le⟩

private lemma Tbar_monotone (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {η : ℝ} (hη : 0 < η) :
    MonotoneOn (fun r => Tbar_fn f x_eq η r) (Set.Ioc 0 c) := by
  intro r₁ hr₁ r₂ hr₂ h_le
  apply csInf_le_csInf (validTSet_bddBelow f x_eq η r₁)
    (validTSet_nonempty f x_eq hconv hη hr₂)
  rintro T ⟨hT_nn, hT_prop⟩
  exact ⟨hT_nn, fun t₀ ht₀ φ hφ h_init t ht =>
    hT_prop t₀ ht₀ φ hφ (h_init.trans_le h_le) t ht⟩

/-! ### W — Sontag averaging function -/

/-- `W_fn f x_eq r η = (2/η) ∫_{η/2}^{η} [T̄(s,r) + r/η] ds`
    (Sontag 1998). Strictly decreasing in `η`, strictly increasing in `r`. -/
private noncomputable def W_fn (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (r η : ℝ) : ℝ :=
  (2 / η) * ∫ s in (η / 2)..η, (Tbar_fn f x_eq s r + r / η)

/-- Integrability of `s ↦ T̄(s, r)` on `[a, b]` (antitone → measurable → integrable).
    TODO: prove using `AntitoneOn.integrableOn` or a Lebesgue measurability argument. -/
private lemma Tbar_intervalIntegrable (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) :
    IntervalIntegrable (fun s => Tbar_fn f x_eq s r) MeasureTheory.volume a b := by
  apply AntitoneOn.intervalIntegrable
  apply (Tbar_antitone f x_eq hconv hr).mono
  intro s hs
  rw [Set.uIcc_of_le hab] at hs
  exact Set.mem_Ioi.mpr (ha.trans_le hs.1)

private lemma W_pos (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) {η : ℝ} (hη : 0 < η) :
    0 < W_fn f x_eq r η := by
  have h_int_Tbar := Tbar_intervalIntegrable f x_eq hconv hr (by linarith : η / 2 ≤ η) (half_pos hη)
  have h_int_sum : IntervalIntegrable (fun s => Tbar_fn f x_eq s r + r / η) volume (η / 2) η :=
    h_int_Tbar.add intervalIntegrable_const
  have h_bound : ∫ s in (η / 2)..η, r / η ≤ ∫ s in (η / 2)..η, Tbar_fn f x_eq s r + r / η := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const h_int_sum
      (fun s hs => ?_)
    linarith [Tbar_nonneg_of f x_eq hconv (by linarith [hs.1] : 0 < s) hr]
  have h_const_int : ∫ s in (η / 2)..η, r / η = r / 2 := by
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    rw [show η - η / 2 = η / 2 from by ring]; field_simp
  calc (0 : ℝ) < r / η := div_pos hr.1 hη
    _ = (2 / η) * (r / 2) := by ring
    _ ≤ (2 / η) * ∫ s in (η / 2)..η, Tbar_fn f x_eq s r + r / η :=
        mul_le_mul_of_nonneg_left (by linarith [h_bound, h_const_int]) (by positivity)

private lemma W_ge_Tbar (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) {η : ℝ} (hη : 0 < η) :
    Tbar_fn f x_eq η r + r / η ≤ W_fn f x_eq r η := by
  have h_int_Tbar := Tbar_intervalIntegrable f x_eq hconv hr (by linarith : η / 2 ≤ η) (half_pos hη)
  have h_int_sum : IntervalIntegrable (fun s => Tbar_fn f x_eq s r + r / η) volume (η / 2) η :=
    h_int_Tbar.add intervalIntegrable_const
  have h_anti := Tbar_antitone f x_eq hconv hr
  have h_integral_bound :
      ∫ s in (η / 2)..η, Tbar_fn f x_eq η r + r / η ≤
      ∫ s in (η / 2)..η, Tbar_fn f x_eq s r + r / η := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const h_int_sum
      (fun s hs => ?_)
    have hs_pos : 0 < s := by linarith [hs.1]
    linarith [h_anti (Set.mem_Ioi.mpr hs_pos) (Set.mem_Ioi.mpr hη) hs.2]
  have h_const_int :
      ∫ s in (η / 2)..η, Tbar_fn f x_eq η r + r / η =
      (η / 2) * (Tbar_fn f x_eq η r + r / η) := by
    rw [intervalIntegral.integral_const]
    change (η - η / 2) * _ = (η / 2) * _; ring
  dsimp [W_fn]
  calc Tbar_fn f x_eq η r + r / η
      = (2 / η) * ((η / 2) * (Tbar_fn f x_eq η r + r / η)) := by
        rw [← mul_assoc, show (2 / η) * (η / 2) = 1 from by field_simp, one_mul]
    _ ≤ (2 / η) * ∫ s in (η / 2)..η, Tbar_fn f x_eq s r + r / η := by
        rw [← h_const_int]
        exact mul_le_mul_of_nonneg_left h_integral_bound (by positivity)

/-- Unpacking the infimum: If s > Tbar(η, r), then the trajectory has already reached the η-ball. -/
private lemma norm_le_of_Tbar_lt {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {η r s t₀ t : ℝ} {φ : ℝ → ℝⁿ}
  (hne : (validTSet f x_eq η r).Nonempty)
  (hlt : Tbar_fn f x_eq η r < s) (ht₀ : 0 ≤ t₀)
  (hφ : IsTrajectoryNA φ f) (h_init : ‖φ t₀ - x_eq‖ < r)
  (ht : t₀ + s ≤ t) :
  ‖φ t - x_eq‖ ≤ η := by
  -- sInf(validTSet) < s and validTSet nonempty ⇒ ∃ T ∈ validTSet, T < s ⇒ t₀ + T ≤ t
  obtain ⟨T, ⟨_, hT_prop⟩, hT_lt⟩ := exists_lt_of_csInf_lt hne hlt
  exact (hT_prop t₀ ht₀ φ hφ h_init t (by linarith)).le


/-! ### UAS → ClassKL (forward direction, Sontag 1998) -/
lemma uniformlyAsymptoticStableNA_implies_classKL (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    (hUAS : UniformlyAsymptoticStableNA f x_eq) :
    ∃ (a : ℝ) (_ : 0 < a) (β : ClassKL a),
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
        IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < a →
        ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ β.toFun (‖φ t₀ - x_eq‖) (t - t₀) := by
  obtain ⟨hUS, c, hc_pos, hconv⟩ := hUAS
  obtain ⟨a_α, b_α, ha_α, hb_α, α, hα_bound⟩ := (uniformlyStableNA_iff_classK f x_eq).mp hUS
  let a := min (a_α / 2) c
  have ha : 0 < a := lt_min (by linarith) hc_pos
  have ha_le_aα2 : a ≤ a_α / 2 := min_le_left _ _
  have ha_le_c   : a ≤ c        := min_le_right _ _
  have ha_lt_aα  : a < a_α      := ha_le_aα2.trans_lt (half_lt_self ha_α)
  -- T̄(η, r) = 0 when the ClassK bound α already puts us inside B_η
  have hTbar_zero : ∀ r ∈ Set.Ioc 0 a, ∀ η, α.toFun r ≤ η → Tbar_fn f x_eq η r = 0 := by
    intro r hr η h_le
    have hr_lt_aα : r < a_α := hr.2.trans_lt ha_lt_aα
    have hr_Ico : r ∈ Set.Ico 0 a_α := ⟨hr.1.le, hr_lt_aα⟩
    have h_alpha_pos : 0 < α.toFun r :=
      α.map_zero ▸ α.strict_mono ⟨le_refl 0, ha_α⟩ hr_Ico hr.1
    have hη_pos : 0 < η := h_alpha_pos.trans_le h_le
    refine le_antisymm (csInf_le (validTSet_bddBelow f x_eq η r) ⟨le_refl 0, ?_⟩)
      (le_csInf (validTSet_nonempty f x_eq hconv hη_pos ⟨hr.1, hr.2.trans ha_le_c⟩)
        (fun _ hT => hT.1))
    intro t₀ ht₀ φ hφ h_init t ht
    have h_stab := hα_bound t₀ ht₀ φ hφ (h_init.trans hr_lt_aα) t (by linarith)
    have h_strict := α.strict_mono ⟨norm_nonneg _, h_init.trans hr_lt_aα⟩ hr_Ico h_init
    exact (h_stab.trans_lt h_strict).trans_le h_le
  -- W and its properties
  have hW_pos : ∀ r ∈ Set.Ioc 0 c, ∀ η > 0, 0 < W_fn f x_eq r η :=
    fun r hr η hη => W_pos f x_eq hconv hr hη
  have hW_ge_Tbar : ∀ r ∈ Set.Ioc 0 c, ∀ η > 0, Tbar_fn f x_eq η r + r / η ≤ W_fn f x_eq r η :=
    fun r hr η hη => W_ge_Tbar f x_eq hconv hr hη
  have hTbar_II : ∀ r ∈ Set.Ioc 0 c, ∀ a b : ℝ, 0 < a → 0 < b →
      IntervalIntegrable (fun s => Tbar_fn f x_eq s r) volume a b := by
    intro r hr a b ha hb
    rcases le_total a b with hab | hab
    · exact Tbar_intervalIntegrable f x_eq hconv hr hab ha
    · exact (Tbar_intervalIntegrable f x_eq hconv hr hab hb).symm
  have hW_eq : ∀ r ∈ Set.Ioc 0 c, ∀ η ∈ Set.Ioi 0,
      W_fn f x_eq r η = (2 / η) * (∫ s in (η / 2)..η, Tbar_fn f x_eq s r) + r / η := by
    intro r hr η hη
    have hη_ne : η ≠ 0 := ne_of_gt hη
    simp only [W_fn]
    rw [intervalIntegral.integral_add
      (Tbar_intervalIntegrable f x_eq hconv hr (le_of_lt (half_lt_self hη)) (half_pos hη))
      intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    have h_const : (η - η / 2) * (r / η) = r / 2 := by field_simp; ring
    rw [h_const]; field_simp [hη_ne]
  have hW_cont : ∀ r ∈ Set.Ioc 0 c, ContinuousOn (W_fn f x_eq r) (Set.Ioi 0) := by
    intro r hr
    have h_int_cont : ContinuousOn (fun η => ∫ s in (η / 2)..η, Tbar_fn f x_eq s r)
      (Set.Ioi 0) := continuousOn_halfWindow_integral (hTbar_II r hr)
    apply ContinuousOn.congr
      (f := fun η => (2 / η) * (∫ s in (η / 2)..η, Tbar_fn f x_eq s r) + r / η)
    · refine ContinuousOn.add (ContinuousOn.mul ?_ h_int_cont) ?_ <;>
        exact fun η hη =>
          (continuousAt_const.div continuousAt_id (Set.mem_Ioi.mp hη).ne').continuousWithinAt
    · exact hW_eq r hr
  have hW_strict_anti : ∀ r ∈ Set.Ioc 0 c, StrictAntiOn (W_fn f x_eq r) (Set.Ioi 0) := by
    intro r hr
    have h_avg_anti : AntitoneOn (fun η => (2 / η) * ∫ s in (η / 2)..η, Tbar_fn f x_eq s r)
      (Set.Ioi 0) :=
      antitoneOn_halfWindow_average (Tbar_antitone f x_eq hconv hr) (hTbar_II r hr)
    have h_r_div_strict : StrictAntiOn (fun η => r / η) (Set.Ioi 0) := fun η₁ hη₁ η₂ hη₂ h_lt =>
      (div_lt_div_iff₀ hη₂ hη₁).mpr (mul_lt_mul_of_pos_left h_lt hr.1)
    intro η₁ hη₁ η₂ hη₂ h_lt
    rw [hW_eq r hr η₁ hη₁, hW_eq r hr η₂ hη₂]
    linarith [h_avg_anti hη₁ hη₂ h_lt.le, h_r_div_strict hη₁ hη₂ h_lt]
  have hW_tendsto : ∀ r ∈ Set.Ioc 0 a, Filter.Tendsto (W_fn f x_eq r) Filter.atTop (nhds 0) := by
    intro r hr
    have hr_c : r ∈ Set.Ioc 0 c := ⟨hr.1, hr.2.trans ha_le_c⟩
    have h_avg : Filter.Tendsto (fun η => (2 / η) * ∫ s in (η / 2)..η, Tbar_fn f x_eq s r)
      Filter.atTop (nhds 0) := by
      apply tendsto_halfWindow_average_zero
      · exact fun s hs => Tbar_nonneg_of f x_eq hconv hs hr_c
      · exact Tbar_antitone f x_eq hconv hr_c
      · exact hTbar_II r hr_c
      · -- For large enough η, every trajectory starting within r is already within η
        -- (the class K bound α(r) is a finite ceiling), so Tbar = 0 eventually.
        have h_eventually_zero : ∀ᶠ η in Filter.atTop, Tbar_fn f x_eq η r = 0 := by
          filter_upwards [Filter.eventually_ge_atTop (α.toFun r)] with η hη
          exact hTbar_zero r hr η hη
        exact tendsto_const_nhds.congr' (h_eventually_zero.mono (fun _ h => h.symm))
    have h_rdiv : Filter.Tendsto (fun η => r / η) Filter.atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using Filter.Tendsto.const_mul r tendsto_inv_atTop_zero
    have h_sum := h_avg.add h_rdiv
    simp only [add_zero] at h_sum
    refine h_sum.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with η hη
    exact (hW_eq r hr_c η hη).symm
  -- U = W⁻¹ (functional inverse on (0,∞))
  have hW_tendsto_top : ∀ r ∈ Set.Ioc 0 c, Filter.Tendsto (W_fn f x_eq r) (𝓝[>] 0)
    Filter.atTop := by
    intro r hr
    have h_r_pos : 0 < r := hr.1
    -- W(η) is bounded below by r / η
    have h_lower_bound : ∀ᶠ η in 𝓝[>] (0 : ℝ), r / η ≤ W_fn f x_eq r η := by
      filter_upwards [self_mem_nhdsWithin] with η hη
      have h_ge := hW_ge_Tbar r hr η hη
      linarith [Tbar_nonneg_of f x_eq hconv hη ⟨hr.1, hr.2⟩]
    -- The limit of r * (1/η) as η → 0⁺ is ∞; squeeze theorem pushes W(η) to ∞
    have h_r_div : Filter.Tendsto (fun η : ℝ => r / η) (𝓝[>] 0) Filter.atTop := by
      simpa [div_eq_mul_inv] using Filter.Tendsto.const_mul_atTop h_r_pos tendsto_inv_nhdsGT_zero
    exact tendsto_atTop_mono' (𝓝[>] 0) h_lower_bound h_r_div
  let U (r s : ℝ) : ℝ := Function.invFunOn (W_fn f x_eq r) (Set.Ioi 0) s
  have hU_bound : ∀ r ∈ Set.Ioc 0 a,
      ∀ t₀ ≥ 0, ∀ φ, IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < r →
      ∀ t > t₀, ‖φ t - x_eq‖ ≤ U r (t - t₀) := by
    intro r hr t₀ ht₀ φ hφ h_init t ht
    let s := t - t₀
    have hs_nonneg : 0 ≤ s := sub_nonneg.mpr ht.le
    have hr_c : r ∈ Set.Ioc 0 c := ⟨hr.1, hr.2.trans ha_le_c⟩
    -- Fact 1: U maps into (0, ∞), so the radius is strictly positive
    have hU_pos : 0 < U r s :=
      invFunOn_pos (hW_cont r hr_c) (hW_tendsto r hr) (hW_tendsto_top r hr_c) (sub_pos.mpr ht)
    -- Fact 2: U is the right-inverse of W, so W(U(s)) = s
    have h_WU : W_fn f x_eq r (U r s) = s :=
      apply_invFunOn_eq (hW_cont r hr_c) (hW_tendsto r hr) (hW_tendsto_top r hr_c) (sub_pos.mpr ht)
    -- Use hW_ge_Tbar to show s > Tbar
    have h_W_ge := hW_ge_Tbar r hr_c (U r s) hU_pos
    have h_Tbar_lt_s : Tbar_fn f x_eq (U r s) r < s := by
      calc Tbar_fn f x_eq (U r s) r
        _ < Tbar_fn f x_eq (U r s) r + r / (U r s) := lt_add_of_pos_right _ (div_pos hr.1 hU_pos)
        _ ≤ W_fn f x_eq r (U r s)                  := h_W_ge
        _ = s                                      := h_WU
    -- Because s > Tbar (the infimum of valid times), s is a valid time!
    have ht_eq : t₀ + s ≤ t := by change t₀ + (t - t₀) ≤ t; linarith
    have hne : (validTSet f x_eq (U r s) r).Nonempty :=
      validTSet_nonempty f x_eq hconv hU_pos hr_c
    exact norm_le_of_Tbar_lt hne h_Tbar_lt_s ht₀ hφ h_init ht_eq
  have ha_c : a ∈ Set.Ioc 0 c := ⟨ha, ha_le_c⟩
  have ha_a : a ∈ Set.Ioc 0 a := ⟨ha, le_refl a⟩
  have hU_strict_anti : StrictAntiOn (U a) (Set.Ioi 0) :=
    strictAntiOn_invFunOn (hW_cont a ha_c) (hW_strict_anti a ha_c) (hW_tendsto a ha_a)
      (hW_tendsto_top a ha_c)
  -- Old axiom had `s ≥ 0`; new lemma requires `s > 0` (s = 0 is a junk value case)
  have hU_pos : ∀ s > 0, 0 < U a s := fun _ hs =>
    invFunOn_pos (hW_cont a ha_c) (hW_tendsto a ha_a) (hW_tendsto_top a ha_c) hs
  have hU_tendsto : Filter.Tendsto (U a) Filter.atTop (nhds 0) :=
    invFunOn_tendsto_zero (hW_cont a ha_c) (hW_strict_anti a ha_c) (hW_tendsto a ha_a)
      (hW_tendsto_top a ha_c)
  let β_fun (r s : ℝ) : ℝ :=
    if h : s = 0 then α.toFun r
    else min (α.toFun r) (Real.sqrt (α.toFun r * U a s))
  -- let β_fun (r s : ℝ) : ℝ :=
  --   if h : s = 0 then α.toFun r
  --   else min (α.toFun r) (Real.sqrt (α.toFun r * U a s)) * (1 / (1 + s))
  refine ⟨a, ha, {
    ha       := ha
    toFun    := β_fun
    map_zero := by
      intro s hs; simp [β_fun, α.map_zero]
    nonneg := by
      intro r hr s hs
      dsimp [β_fun]
      have h_α : 0 ≤ α.toFun r := (α.maps_to ⟨hr.1, hr.2.trans ha_lt_aα⟩).1
      split_ifs with h_zero
      · exact h_α
      · exact le_min h_α (Real.sqrt_nonneg _)
    strict_mono_r := by
      intro s hs r₁ hr₁ r₂ hr₂ h_lt
      dsimp [β_fun]
      have hr₁_aα : r₁ ∈ Set.Ico 0 a_α := ⟨hr₁.1, hr₁.2.trans ha_lt_aα⟩
      have hr₂_aα : r₂ ∈ Set.Ico 0 a_α := ⟨hr₂.1, hr₂.2.trans ha_lt_aα⟩
      have h_α_lt : α.toFun r₁ < α.toFun r₂ := α.strict_mono hr₁_aα hr₂_aα h_lt
      by_cases h_zero : s = 0
      · simp [if_pos h_zero, h_α_lt]
      · simp only [if_neg h_zero]
        have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm h_zero)
        refine min_lt_min h_α_lt (Real.sqrt_lt_sqrt
          (mul_nonneg (α.maps_to hr₁_aα).1 (hU_pos s hs_pos).le)
          (mul_lt_mul_of_pos_right h_α_lt (hU_pos s hs_pos)))
    continuous_r  := by
      intro s hs
      dsimp [β_fun]
      -- Continuity: use Continuous.if for piecewise continuity
      split_ifs with h_zero
      · exact α.continuous.mono (Set.Ico_subset_Ico_right ha_lt_aα.le)
      · have h_cont_α := α.continuous.mono (Set.Ico_subset_Ico_right ha_lt_aα.le)
        fun_prop
    anti_s := by
      intro r hr s₁ hs₁ s₂ hs₂ h_le
      dsimp [β_fun]
      have h_α_nonneg : 0 ≤ α.toFun r := (α.maps_to ⟨hr.1, hr.2.trans ha_lt_aα⟩).1
      rcases (Set.mem_Ici.mp hs₁).eq_or_lt with rfl | hs₁_pos
      · rcases (Set.mem_Ici.mp hs₂).eq_or_lt with rfl | hs₂_pos
        · exact le_refl _
        · simp [if_neg (ne_of_gt hs₂_pos)]
      · rcases (Set.mem_Ici.mp hs₂).eq_or_lt with rfl | hs₂_pos
        · linarith
        · simp only [if_neg (ne_of_gt hs₁_pos), if_neg (ne_of_gt hs₂_pos)]
          gcongr
          exact hU_strict_anti.antitoneOn hs₁_pos hs₂_pos h_le
    tendsto_zero  := by
      intro r hr
      dsimp [β_fun]
      have h_α : 0 ≤ α.toFun r := (α.maps_to ⟨hr.1, hr.2.trans ha_lt_aα⟩).1
      have h_eq : (fun s ↦ if s = 0 then α.toFun r
        else min (α.toFun r) √(α.toFun r * U a s)) =ᶠ[atTop]
        (fun s ↦ min (α.toFun r) √(α.toFun r * U a s)) := by
        filter_upwards [Filter.eventually_ne_atTop 0] with s hs
        exact if_neg hs
      apply Filter.Tendsto.congr' h_eq.symm
      refine squeeze_zero (fun s => le_min h_α (Real.sqrt_nonneg _))
        (fun s => min_le_right _ _) ?_
      have h_inner : Tendsto (fun s ↦ α.toFun r * U a s) atTop (𝓝 0) := by
        simpa using Filter.Tendsto.const_mul (α.toFun r) hU_tendsto
      have h_sqrt : Tendsto (fun x : ℝ ↦ Real.sqrt x) (𝓝 0) (𝓝 0) := by
        simpa [Real.sqrt_zero] using Real.continuous_sqrt.tendsto 0
      exact h_sqrt.comp h_inner
  }, ?_⟩
  intro t₀ ht₀ φ hφ h_init t ht
  have h_α : ‖φ t - x_eq‖ ≤ α.toFun (‖φ t₀ - x_eq‖) :=
    hα_bound t₀ ht₀ φ hφ (h_init.trans_le ha_lt_aα.le) t ht
  rcases ht.eq_or_lt with rfl | ht_strict
  · simp [β_fun, h_α]
  · have h_sub_ne : t - t₀ ≠ 0 := ne_of_gt (sub_pos.mpr ht_strict)
    dsimp [β_fun]
    simp only [if_neg h_sub_ne]
    have h_U : ‖φ t - x_eq‖ ≤ U a (t - t₀) :=
      hU_bound a ⟨ha, le_refl a⟩ t₀ ht₀ φ hφ h_init t ht_strict
    refine le_min h_α ?_
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (φ t - x_eq), h_α, h_U])


/-- **Lemma 4.5 (ii)**: The equilibrium `x_eq` is uniformly asymptotically stable if and only
    if there exist a class KL function `β` on `[0, c)` and a constant `c > 0` (independent of
    `t₀`) such that every trajectory with `‖φ t₀ - x_eq‖ < c` satisfies
    `‖φ t - x_eq‖ ≤ β(‖φ t₀ - x_eq‖, t − t₀)` for all `t ≥ t₀ ≥ 0`. -/
@[blueprint "lem:uniformlyAsymptoticStableNA-iff-classKL"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{uniformly asymptotically
    stable} (\cref{def:uniformlyAsymptoticStableNA}) if and only if there exist a class
    $\mathcal{KL}$ function $\beta$ and a positive constant $c$, independent of $t_{0}$,
    such that
    \[
      \|\varphi(t) - x_{\mathrm{eq}}\| \le \beta(\|\varphi(t_{0}) - x_{\mathrm{eq}}\|,\, t - t_{0})
      \quad \forall\, t \ge t_{0} \ge 0,\; \forall\, \|\varphi(t_{0}) - x_{\mathrm{eq}}\| < c.
    \] -/)]
theorem uniformlyAsymptoticStableNA_iff_classKL_iff_classKL (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) :
    UniformlyAsymptoticStableNA f x_eq ↔
    ∃ (a : ℝ) (_ : 0 < a) (β : ClassKL a),
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
        IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < a →
        ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ β.toFun (‖φ t₀ - x_eq‖) (t - t₀) := by
  refine ⟨uniformlyAsymptoticStableNA_implies_classKL f x_eq, ?_⟩
  -- Backward: ∃ ClassKL bound → UAS
  rintro ⟨a, ha, β, hβ⟩
  have ha2 : (a / 2 : ℝ) ∈ Set.Ico 0 a := ⟨by positivity, half_lt_self ha⟩
  refine ⟨?_, a / 2, half_pos ha, ?_⟩
  · -- Uniform stability: continuity of β(·, 0) at 0 gives δ(ε)
    intro ε hε
    have h_cont := β.continuous_r 0 le_rfl 0 ⟨le_refl 0, ha⟩
    rw [Metric.continuousWithinAt_iff] at h_cont
    obtain ⟨δ, hδ_pos, hδ⟩ := h_cont ε hε
    refine ⟨min δ (a / 2), lt_min hδ_pos (half_pos ha),
            fun t₀ ht₀ φ hφ h_init t ht => ?_⟩
    have hr : ‖φ t₀ - x_eq‖ ∈ Set.Ico 0 a :=
      ⟨norm_nonneg _, h_init.trans ((min_le_right ..).trans_lt (half_lt_self ha))⟩
    have ht_sub : 0 ≤ t - t₀ := sub_nonneg.mpr ht
    have h2 := β.anti_s _ hr (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht_sub) ht_sub
    have hd : dist (‖φ t₀ - x_eq‖) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
      exact h_init.trans_le (min_le_left ..)
    have h3 := hδ hr hd
    rw [β.map_zero 0 le_rfl, Real.dist_eq, sub_zero,
        abs_of_nonneg (β.nonneg _ hr 0 le_rfl)] at h3
    linarith [hβ t₀ ht₀ φ hφ hr.2 t ht]
  · -- Convergence: β(a/2, s) → 0 as s → ∞ bounds all β(r, s) for r < a/2
    intro η hη
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
      (β.tendsto_zero (a / 2) ha2 (Iio_mem_nhds hη))
    refine ⟨max T 0 + 1, by linarith [le_max_right T (0:ℝ)], ?_⟩
    intro t₀ ht₀ φ hφ h_init t ht
    have ht_sub : 0 ≤ t - t₀ := by linarith [le_max_right T (0:ℝ)]
    have hr : ‖φ t₀ - x_eq‖ ∈ Set.Ico 0 a :=
      ⟨norm_nonneg _, h_init.trans (half_lt_self ha)⟩
    have h1 := hβ t₀ ht₀ φ hφ hr.2 t (by linarith)
    have h2 : β.toFun ‖φ t₀ - x_eq‖ (t - t₀) < β.toFun (a / 2) (t - t₀) :=
      β.strict_mono_r _ ht_sub hr ha2 h_init
    have h3 : β.toFun (a / 2) (t - t₀) ≤ β.toFun (a / 2) (max T 0) :=
      β.anti_s (a / 2) ha2 (Set.mem_Ici.mpr (le_max_right T 0))
        (Set.mem_Ici.mpr ht_sub) (by linarith [le_max_right T (0:ℝ)])
    have h4 : β.toFun (a / 2) (max T 0) < η := hT (max T 0) (le_max_left T 0)
    linarith




-- /-- **Lemma 4.5 (iii)**: The equilibrium `x_eq` is globally uniformly asymptotically stable
--     if and only if there exists a function `β : ℝ≥0 × ℝ≥0 → ℝ≥0` that is class K in the
--     first argument and decays to zero in the second (a global class KL bound), such that
--     `‖φ t - x_eq‖ ≤ β(‖φ t₀ - x_eq‖, t − t₀)` holds for **every** trajectory and every
--     `t ≥ t₀ ≥ 0`, with no restriction on the initial size `‖φ t₀ - x_eq‖`. -/
-- @[blueprint "lem:globallyUniformlyAsymptoticStableNA-iff-classKL"
--   (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{globally uniformly
--     asymptotically stable} (\cref{def:globallyUniformlyAsymptoticStableNA}) if and only
--     if there exists $\beta : [0,\infty) \times [0,\infty) \to [0,\infty)$ that is class
--     $\mathcal{K}$ in the first argument and, for each fixed $r \ge 0$, is decreasing to
--     $0$ as $s \to \infty$, such that
--     \[
--       \|\varphi(t) - x_{\mathrm{eq}}\| \le \beta(\|\varphi(t_{0}) - x_{\mathrm{eq}}\|,
--              \, t - t_{0})
--       \quad \forall\, t \ge t_{0} \ge 0,
--     \]
--     with no restriction on the initial state $\varphi(t_{0})$. -/)]
-- theorem globallyUniformlyAsymptoticStableNA_iff_classKL (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) :
--     GloballyUniformlyAsymptoticStableNA f x_eq ↔
--     ∃ β : ℝ → ℝ → ℝ,
--       (∀ s ≥ 0, β 0 s = 0) ∧
--       (∀ s ≥ 0, StrictMonoOn (fun r => β r s) (Set.Ici 0)) ∧
--       (∀ r ≥ 0, AntitoneOn (fun s => β r s) (Set.Ici 0)) ∧
--       (∀ r ≥ 0, Filter.Tendsto (fun s => β r s) Filter.atTop (nhds 0)) ∧
--       ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
--         IsTrajectoryNA φ f →
--         ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ β (‖φ t₀ - x_eq‖) (t - t₀) := by
--   constructor
--   · sorry
--   · sorry

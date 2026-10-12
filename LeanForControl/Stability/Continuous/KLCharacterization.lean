import LeanForControl.Stability.Continuous.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue
import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKInfty
import LeanForControl.Comparison.ClassKL
import LeanForControl.Comparison.ComparisonFunctions
import LeanForControl.Analysis.Integrals
import LeanForControl.Analysis.MonotoneFunctions
import Architect

/-!
# `Stability.Continuous.KLCharacterization` — comparison-function characterizations

The uniform stability notions of `Stability.Continuous.Defs` are equivalent to comparison-function
bounds on the trajectories of the system: uniform stability to a class `K` bound, uniform
asymptotic stability to a class `KL` bound.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.5.

## Main declarations

* `HasUniformClassKBound`, `HasUniformClassKInftyBound` — the comparison-function estimates
  `‖x(t) - x_eq‖ ≤ α(‖x(t₀) - x_eq‖)` on every trajectory segment.
* `exists_classLSingular_decayBound` — a uniform convergence time and a class `K` bound give a
  single decay envelope, a function of elapsed time alone bounding every trajectory from a ball.
* `exists_decayBound_family` — the global version, a family of envelopes indexed by the radius.
* `stable_iff_classK`, `uniformlyStable_iff_classK` — stability is a class `K` bound for each
  initial time; uniform stability is one class `K` bound for all of them.
* `uniformlyAsymptoticallyStable_iff_classKL`, `globallyUniformlyAsymptoticallyStable_iff_classKL`
  — uniform asymptotic stability is a class `KL` bound, locally and globally.
* `hasUniformConvergenceTime_of_classKL` — the easy half: a class `KL` bound gives a uniform
  convergence time.
* `UniformlyStable.exists_classK_Ici` and its `KL` analogues — the same bounds on solutions over
  `[t₀, ∞)`, with no completeness hypothesis.
* `uniformlyStable_iff_classK_of_isForwardCompleteOn` and its `KL` analogues — the converse too,
  for a system forward complete from some ball about `x_eq` (from every state, globally).

The decay envelope is the time-decay half of a class `KL` bound, and the hard direction of the
characterization; Sontag's smoothing construction below builds it.

Reference for the construction: Sontag, *Comments on integral variants of ISS* (1998).

## The construction (private)

`Tbar_fn sys x_eq η r` is the least delay `T` after which *every* trajectory starting within `r`
of `x_eq` is inside the `η`-ball, as far as it is defined — the infimum of the `T`s that
`HasUniformConvergenceTime` asserts to exist.  It is antitone in `η` but need not be continuous,
so it cannot itself serve as an envelope.  Averaging it over a sliding window,

  `W_fn sys x_eq r η = (2/η) ∫_{η/2}^{η} [T̄(s,r) + r/η] ds`,

smooths it: `W_fn sys x_eq r` is continuous and *strictly* antitone on `(0,∞)`, blows up as
`η → 0⁺` and vanishes as `η → ∞`.  Inverting it (`Analysis/MonotoneFunctions`) exchanges those
two boundary behaviours, giving a decay envelope in elapsed time.  The `r/η` term is what makes
the average strictly antitone rather than merely antitone, and forces the blow-up at `0⁺`.

Nothing here uses the dynamics: trajectories enter only as the family of curves the
hypotheses and conclusions quantify over.
-/

open MeasureTheory intervalIntegral Set Filter Topology

namespace ContinuousSystem

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Comparison-function estimates -/

/-- The trajectories **have the uniform class `K` bound** `α` about `x_eq`: on every segment
starting at a time `t₀ ≥ 0` within `a` of `x_eq`, `‖x(t) - x_eq‖ ≤ α(‖x(t₀) - x_eq‖)`.

The radius `a` is read off `α : ClassK a b`: a class `K` function is defined on `[0, a)`, so the
locality of the bound is carried by its type.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), (4.19). -/
@[blueprint "def:continuousSystem-hasUniformClassKBound"
  (title := "Uniform class $\\mathcal{K}$ bound")
  (statement := /-- The trajectories of $s$ \emph{have the uniform class $\mathcal{K}$ bound}
    $\alpha : [0, a) \to [0, b)$ about $x_{\mathrm{eq}}$ when
    \[
      \|x(t) - x_{\mathrm{eq}}\| \le \alpha(\|x(t_0) - x_{\mathrm{eq}}\|)
    \]
    for every trajectory on a segment $[t_0, t_1]$ with $t_0 \ge 0$ and
    $\|x(t_0) - x_{\mathrm{eq}}\| < a$, and every $t \in [t_0, t_1]$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), (4.19). -/)]
def HasUniformClassKBound (s : ContinuousSystem E Unit Y) (x_eq : E) {a b : ℝ} (α : ClassK a b) :
    Prop :=
  ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E), s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) →
    ‖x t₀ - x_eq‖ < a → ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ α.toFun ‖x t₀ - x_eq‖

/-- The same estimate with a class `K∞` bound, for every initial state: a class `K∞` function
is defined on all of `[0, ∞)`, so no radius restriction survives.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), (4.20). -/
@[blueprint "def:continuousSystem-hasUniformClassKInftyBound"
  (title := "Uniform class $\\mathcal{K}_{\\infty}$ bound")
  (statement := /-- The trajectories of $s$ \emph{have the uniform class
    $\mathcal{K}_{\infty}$ bound} $\alpha$ about $x_{\mathrm{eq}}$ when
    $\|x(t) - x_{\mathrm{eq}}\| \le \alpha(\|x(t_0) - x_{\mathrm{eq}}\|)$ for every trajectory
    on a segment $[t_0, t_1]$ with $t_0 \ge 0$ and every $t \in [t_0, t_1]$, with no
    restriction on the initial state.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), (4.20). -/)]
def HasUniformClassKInftyBound (s : ContinuousSystem E Unit Y) (x_eq : E) (α : ClassKInfty) :
    Prop :=
  ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E), s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) →
    ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ α.toFun ‖x t₀ - x_eq‖

/-! ## T̄ — optimal uniform convergence time -/

private def validTSet (sys : ContinuousSystem E Unit Y) (x_eq : E) (η r : ℝ) : Set ℝ :=
  {T | 0 ≤ T ∧ ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
    sys.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < r →
      ∀ t ∈ Icc (t₀ + T) t₁, ‖x t - x_eq‖ < η}

/-- `Tbar_fn sys x_eq η r` is the infimum of valid convergence times from the `r`-ball to the
    `η`-ball: the smallest `T` that works for all trajectories simultaneously. -/
private noncomputable def Tbar_fn (sys : ContinuousSystem E Unit Y) (x_eq : E) (η r : ℝ) : ℝ :=
  sInf (validTSet sys x_eq η r)

private lemma validTSet_bddBelow (sys : ContinuousSystem E Unit Y) (x_eq : E) (η r : ℝ) :
    BddBelow (validTSet sys x_eq η r) :=
  ⟨0, fun _ hT => hT.1⟩

private lemma validTSet_nonempty {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {η : ℝ} (hη : 0 < η) {r : ℝ} (hr : r ∈ Set.Ioc 0 c) :
    (validTSet sys x_eq η r).Nonempty := by
  obtain ⟨T, hT_pos, hT_prop⟩ := hconv η hη
  exact ⟨T, hT_pos.le, fun t₀ ht₀ t₁ x hx h_init t ht =>
    hT_prop t₀ ht₀ t₁ x hx (h_init.trans_le hr.2) t ht⟩

private lemma Tbar_nonneg_of {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {η : ℝ} (hη : 0 < η) {r : ℝ} (hr : r ∈ Set.Ioc 0 c) :
    0 ≤ Tbar_fn sys x_eq η r :=
  le_csInf (validTSet_nonempty hconv hη hr) (fun _ hT => hT.1)

private lemma Tbar_antitone {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) :
    AntitoneOn (fun η => Tbar_fn sys x_eq η r) (Set.Ioi 0) := by
  intro η₁ hη₁ η₂ hη₂ h_le
  exact csInf_le_csInf (validTSet_bddBelow sys x_eq η₂ r) (validTSet_nonempty hconv hη₁ hr)
    fun T ⟨hT_nn, hT_prop⟩ => ⟨hT_nn, fun t₀ ht₀ t₁ x hx h_init t ht =>
      (hT_prop t₀ ht₀ t₁ x hx h_init t ht).trans_le h_le⟩

private lemma Tbar_intervalIntegrable {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) :
    IntervalIntegrable (fun s => Tbar_fn sys x_eq s r) MeasureTheory.volume a b := by
  apply AntitoneOn.intervalIntegrable
  exact (Tbar_antitone hconv hr).mono fun s hs => by
    rw [Set.uIcc_of_le hab] at hs; exact Set.mem_Ioi.mpr (ha.trans_le hs.1)

private lemma Tbar_intervalIntegrable_of_pos {sys : ContinuousSystem E Unit Y} {x_eq : E}
    {c : ℝ} (hconv : sys.HasUniformConvergenceTime x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun s => Tbar_fn sys x_eq s r) MeasureTheory.volume a b := by
  rcases le_total a b with hab | hab
  · exact Tbar_intervalIntegrable hconv hr hab ha
  · exact (Tbar_intervalIntegrable hconv hr hab hb).symm

private lemma Tbar_zero_of_classK_bound {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : sys.HasUniformClassKBound x_eq α)
    {a : ℝ} (ha_lt_aα : a < a_α) (ha_le_c : a ≤ c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 a) {η : ℝ} (h_le : α.toFun r ≤ η) :
    Tbar_fn sys x_eq η r = 0 := by
  have hr_lt_aα : r < a_α := hr.2.trans_lt ha_lt_aα
  have hr_Ico : r ∈ Set.Ico 0 a_α := ⟨hr.1.le, hr_lt_aα⟩
  have h_alpha_pos : 0 < α.toFun r := (α.pos_iff hr_Ico).mpr hr.1
  have hη_pos : 0 < η := h_alpha_pos.trans_le h_le
  refine le_antisymm (csInf_le (validTSet_bddBelow sys x_eq η r) ⟨le_refl 0, ?_⟩)
    (le_csInf (validTSet_nonempty hconv hη_pos ⟨hr.1, hr.2.trans ha_le_c⟩) (fun _ hT => hT.1))
  intro t₀ ht₀ t₁ x hx h_init t ht
  have h_stab := hα_bound t₀ ht₀ t₁ x hx (h_init.trans hr_lt_aα) t ⟨by linarith [ht.1], ht.2⟩
  have h_strict := (α.strict_mono_iff ⟨norm_nonneg _, h_init.trans hr_lt_aα⟩ hr_Ico).mpr h_init
  exact (h_stab.trans_lt h_strict).trans_le h_le

private lemma Tbar_mono_r {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {r₁ r₂ : ℝ} (hr₂ : r₂ ∈ Set.Ioc 0 c) (h_le : r₁ ≤ r₂) {η : ℝ} (hη : 0 < η) :
    Tbar_fn sys x_eq η r₁ ≤ Tbar_fn sys x_eq η r₂ :=
  csInf_le_csInf (validTSet_bddBelow sys x_eq η r₁) (validTSet_nonempty hconv hη hr₂)
    fun _T hT => ⟨hT.1, fun t₀ ht₀ t₁ x hx h_init t ht =>
      hT.2 t₀ ht₀ t₁ x hx (h_init.trans_le h_le) t ht⟩

/-- Unpacking the infimum: if `s > T̄(η, r)` then a trajectory starting within `r` has already
    reached the `η`-ball by elapsed time `s`. -/
private lemma norm_le_of_Tbar_lt {sys : ContinuousSystem E Unit Y} {x_eq : E} {η r s t₀ t₁ t : ℝ}
    {x : ℝ → E} (hne : (validTSet sys x_eq η r).Nonempty)
    (hlt : Tbar_fn sys x_eq η r < s) (ht₀ : 0 ≤ t₀)
    (hx : sys.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁)) (h_init : ‖x t₀ - x_eq‖ < r)
    (ht : t ∈ Icc (t₀ + s) t₁) :
    ‖x t - x_eq‖ ≤ η := by
  obtain ⟨_T, ⟨_, hT_prop⟩, hT_lt⟩ := exists_lt_of_csInf_lt hne hlt
  exact (hT_prop t₀ ht₀ t₁ x hx h_init t ⟨by linarith [ht.1], ht.2⟩).le

/-! ## W — sliding average of T̄ -/

/-- `W_fn sys x_eq r η = (2/η) ∫_{η/2}^{η} [T̄(s,r) + r/η] ds`
    (Sontag 1998). Strictly decreasing in `η`, strictly increasing in `r`. -/
private noncomputable def W_fn (sys : ContinuousSystem E Unit Y) (x_eq : E) (r η : ℝ) : ℝ :=
  (2 / η) * ∫ s in (η / 2)..η, (Tbar_fn sys x_eq s r + r / η)

private lemma W_ge_Tbar {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) {η : ℝ} (hη : 0 < η) :
    Tbar_fn sys x_eq η r + r / η ≤ W_fn sys x_eq r η := by
  have h_int_sum : IntervalIntegrable (fun s => Tbar_fn sys x_eq s r + r / η) volume (η / 2) η :=
    (Tbar_intervalIntegrable hconv hr (by linarith : η / 2 ≤ η) (half_pos hη)).add
      intervalIntegral.intervalIntegrable_const
  have h_anti := Tbar_antitone hconv hr
  have h_integral_bound :
      ∫ s in (η / 2)..η, Tbar_fn sys x_eq η r + r / η ≤
      ∫ s in (η / 2)..η, Tbar_fn sys x_eq s r + r / η := by
    refine intervalIntegral.integral_mono_on (by linarith)
      intervalIntegral.intervalIntegrable_const h_int_sum (fun s hs => ?_)
    have hs_pos : 0 < s := by linarith [hs.1]
    linarith [h_anti (Set.mem_Ioi.mpr hs_pos) (Set.mem_Ioi.mpr hη) hs.2]
  have h_const_int :
      ∫ s in (η / 2)..η, Tbar_fn sys x_eq η r + r / η =
      (η / 2) * (Tbar_fn sys x_eq η r + r / η) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  dsimp [W_fn]
  calc Tbar_fn sys x_eq η r + r / η
      = (2 / η) * ((η / 2) * (Tbar_fn sys x_eq η r + r / η)) := by
        rw [← mul_assoc, show (2 / η) * (η / 2) = 1 from by field_simp, one_mul]
    _ ≤ (2 / η) * ∫ s in (η / 2)..η, Tbar_fn sys x_eq s r + r / η := by
        rw [← h_const_int]; gcongr

/-- Splitting the constant out of the average: the `r/η` term integrates to `r/2`, so
    `W = (2/η)∫T̄ + r/η`. Every property of `W` is read off this form. -/
private lemma W_fn_eq {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) {η : ℝ} (hη : 0 < η) :
    W_fn sys x_eq r η = (2 / η) * (∫ s in (η / 2)..η, Tbar_fn sys x_eq s r) + r / η := by
  simp only [W_fn]
  rw [intervalIntegral.integral_add
    (Tbar_intervalIntegrable hconv hr (le_of_lt (half_lt_self hη)) (half_pos hη))
    intervalIntegral.intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul]
  have h_const : (η - η / 2) * (r / η) = r / 2 := by field_simp; ring
  rw [h_const]; field_simp [hη.ne']

private lemma W_fn_continuousOn {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) : ContinuousOn (W_fn sys x_eq r) (Set.Ioi 0) := by
  have h_int_cont : ContinuousOn (fun η => ∫ s in (η / 2)..η, Tbar_fn sys x_eq s r) (Set.Ioi 0) :=
    continuousOn_integral_endpoints (Tbar_intervalIntegrable_of_pos hconv hr)
      (continuousOn_id.div_const 2) continuousOn_id
      (fun η hη => by have : (0 : ℝ) < η := hη; linarith) (fun η hη => hη)
  have h_rhs_cont : ContinuousOn
      (fun η => (2 / η) * (∫ s in (η / 2)..η, Tbar_fn sys x_eq s r) + r / η) (Set.Ioi 0) := by
    refine ContinuousOn.add (ContinuousOn.mul ?_ h_int_cont) ?_ <;>
      exact fun η hη =>
        (continuousAt_const.div continuousAt_id (Set.mem_Ioi.mp hη).ne').continuousWithinAt
  exact h_rhs_cont.congr (fun η hη => W_fn_eq hconv hr hη)

private lemma W_fn_strictAntiOn {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) : StrictAntiOn (W_fn sys x_eq r) (Set.Ioi 0) := by
  -- The average of an antitone function is antitone; the `r/η` term is what makes it strict.
  have h_avg_anti : AntitoneOn (fun η => (2 / η) * ∫ s in (η / 2)..η, Tbar_fn sys x_eq s r)
      (Set.Ioi 0) := by
    refine AntitoneOn.congr (antitoneOn_integral_average
      (f := fun s => Tbar_fn sys x_eq s r) (a := fun η => η / 2) (b := fun η => η)
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

private lemma W_fn_tendsto_nhdsGT {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) :
    Filter.Tendsto (W_fn sys x_eq r) (𝓝[>] 0) Filter.atTop := by
  -- `W ≥ r/η`, which already blows up at `0⁺`.
  have h_lower_bound : ∀ᶠ η in 𝓝[>] (0 : ℝ), r / η ≤ W_fn sys x_eq r η := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    linarith [W_ge_Tbar hconv hr hη, Tbar_nonneg_of hconv hη hr]
  have h_r_div : Filter.Tendsto (fun η : ℝ => r / η) (𝓝[>] 0) Filter.atTop := by
    simpa [div_eq_mul_inv] using Filter.Tendsto.const_mul_atTop hr.1 tendsto_inv_nhdsGT_zero
  exact tendsto_atTop_mono' (𝓝[>] 0) h_lower_bound h_r_div

private lemma W_fn_tendsto_atTop {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : sys.HasUniformClassKBound x_eq α)
    {a : ℝ} (ha_le_c : a ≤ c) (ha_lt_aα : a < a_α)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 a) :
    Filter.Tendsto (W_fn sys x_eq r) Filter.atTop (nhds 0) := by
  have hr_c : r ∈ Set.Ioc 0 c := ⟨hr.1, hr.2.trans ha_le_c⟩
  have h_avg : Filter.Tendsto (fun η => (2 / η) * ∫ s in (η / 2)..η, Tbar_fn sys x_eq s r)
      Filter.atTop (nhds 0) := by
    have h := tendsto_integral_average_atTop_zero
      (f := fun s => Tbar_fn sys x_eq s r) (a := fun η => η / 2) (b := fun η => η)
      (fun s hs => Tbar_nonneg_of hconv hs hr_c)
      (Tbar_antitone hconv hr_c)
      (Tbar_intervalIntegrable_of_pos hconv hr_c)
      (by -- For large enough η the class K bound α(r) is a finite ceiling, so T̄ = 0 eventually.
        have h_eventually_zero : ∀ᶠ η in Filter.atTop, Tbar_fn sys x_eq η r = 0 := by
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

private lemma W_fn_mono_r {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {r₁ r₂ : ℝ} (hr₁ : r₁ ∈ Set.Ioc 0 c) (hr₂ : r₂ ∈ Set.Ioc 0 c) (h_le : r₁ ≤ r₂)
    {η : ℝ} (hη : 0 < η) :
    W_fn sys x_eq r₁ η ≤ W_fn sys x_eq r₂ η := by
  rw [W_fn_eq hconv hr₁ hη, W_fn_eq hconv hr₂ hη]
  refine add_le_add ?_ (div_le_div_of_nonneg_right h_le hη.le)
  gcongr
  exact intervalIntegral.integral_mono_on (half_le_self hη.le)
    (Tbar_intervalIntegrable_of_pos hconv hr₁ (η / 2) η (half_pos hη) hη)
    (Tbar_intervalIntegrable_of_pos hconv hr₂ (η / 2) η (half_pos hη) hη)
    fun x hx => Tbar_mono_r hconv hr₂ h_le (by linarith [hx.1])

/-! ## The inverse of `W` — the decay envelope -/

/-- The four facts about `W_fn sys x_eq r` that `Analysis/MonotoneFunctions` needs in order to
    invert it: continuous, strictly antitone, blowing up at `0⁺` and vanishing at `+∞`. -/
private lemma W_fn_invertible {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : sys.HasUniformClassKBound x_eq α)
    {a : ℝ} (ha_le_c : a ≤ c) (ha_lt_aα : a < a_α)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 a) :
    ContinuousOn (W_fn sys x_eq r) (Set.Ioi 0) ∧ StrictAntiOn (W_fn sys x_eq r) (Set.Ioi 0) ∧
      Filter.Tendsto (W_fn sys x_eq r) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (W_fn sys x_eq r) (𝓝[>] 0) Filter.atTop :=
  have hr_c : r ∈ Set.Ioc 0 c := ⟨hr.1, hr.2.trans ha_le_c⟩
  ⟨W_fn_continuousOn hconv hr_c, W_fn_strictAntiOn hconv hr_c,
    W_fn_tendsto_atTop hconv α hα_bound ha_le_c ha_lt_aα hr, W_fn_tendsto_nhdsGT hconv hr_c⟩

private lemma invFunOn_mono_r {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : sys.HasUniformClassKBound x_eq α)
    {a : ℝ} (ha_le_c : a ≤ c) (ha_lt_aα : a < a_α)
    {r₁ r₂ : ℝ} (hr₁ : r₁ ∈ Set.Ioc 0 a) (hr₂ : r₂ ∈ Set.Ioc 0 a) (h_le : r₁ ≤ r₂)
    {s : ℝ} (hs : 0 < s) :
    Function.invFunOn (W_fn sys x_eq r₁) (Set.Ioi 0) s ≤
      Function.invFunOn (W_fn sys x_eq r₂) (Set.Ioi 0) s := by
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
    within `invFunOn (W_fn sys x_eq r) (Ioi 0) (t - t₀)` of `x_eq` at every later time. -/
private lemma U_decay_bound {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : sys.HasUniformClassKBound x_eq α)
    {a : ℝ} (ha_le_c : a ≤ c) (ha_lt_aα : a < a_α)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 a)
    {t₀ t₁ : ℝ} (ht₀ : 0 ≤ t₀) {x : ℝ → E} (hx : sys.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁))
    (h_init : ‖x t₀ - x_eq‖ < r) {t : ℝ} (ht : t ∈ Ioc t₀ t₁) :
    ‖x t - x_eq‖ ≤ Function.invFunOn (W_fn sys x_eq r) (Set.Ioi 0) (t - t₀) := by
  obtain ⟨hc, hanti, hz, htop⟩ := W_fn_invertible hconv α hα_bound ha_le_c ha_lt_aα hr
  have hr_c : r ∈ Set.Ioc 0 c := ⟨hr.1, hr.2.trans ha_le_c⟩
  have hs : 0 < t - t₀ := sub_pos.mpr ht.1
  set U := Function.invFunOn (W_fn sys x_eq r) (Set.Ioi 0) (t - t₀) with hU_def
  have hU_pos : 0 < U := invFunOn_pos hc hz htop hs
  -- `U` is the radius whose *optimal* convergence time the elapsed time `t - t₀` exceeds …
  have h_Tbar_lt : Tbar_fn sys x_eq U r < t - t₀ := by
    calc Tbar_fn sys x_eq U r
        < Tbar_fn sys x_eq U r + r / U := lt_add_of_pos_right _ (div_pos hr.1 hU_pos)
      _ ≤ W_fn sys x_eq r U            := W_ge_Tbar hconv hr_c hU_pos
      _ = t - t₀                     := apply_invFunOn_eq hc hz htop hs
  -- … so `t - t₀` is itself a valid convergence time to the `U`-ball.
  exact norm_le_of_Tbar_lt (validTSet_nonempty hconv hU_pos hr_c) h_Tbar_lt ht₀ hx h_init
    ⟨by linarith, ht.2⟩

/-! ## The local envelope -/

/-- **Local uniform decay envelope.** Uniform convergence times on the `c`-ball together with a
    uniform class `K` bound `α` produce a *single* singular class `L` function `U` — one
    function of elapsed time alone — bounding every trajectory that starts within `a` of `x_eq`.

    This is the time-decay half of the class `KL` characterization: `α` carries the dependence
    on the initial deviation and `U` the decay in elapsed time.

    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.5. -/
@[blueprint "lem:continuousSystem-exists-classLSingular-decayBound"
  (title := "Local uniform decay envelope")
  (latexEnv := "lemma")
  (statement := /-- Suppose the trajectories of $s$ have a uniform convergence time from the
    ball of radius $c$ (\cref{def:continuousSystem-hasUniformConvergenceTime}) and a uniform
    class $\mathcal{K}$ bound $\alpha$ defined on $[0, a_\alpha)$
    (\cref{def:continuousSystem-hasUniformClassKBound}).  Let $0 < a \le c$ with $a < a_\alpha$.
    Then there is a singular class $\mathcal{L}$ function $U$ (\cref{def:isClassLSingular}) such
    that
    \[
      \|x(t) - x_{\mathrm{eq}}\| \le U(t - t_{0})
    \]
    for every trajectory on a segment $[t_0, t_1]$ with $t_0 \ge 0$ and
    $\|x(t_0) - x_{\mathrm{eq}}\| < a$, and every $t \in (t_0, t_1]$.

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
theorem exists_classLSingular_decayBound {sys : ContinuousSystem E Unit Y} {x_eq : E} {c : ℝ}
    (hconv : sys.HasUniformConvergenceTime x_eq c)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : sys.HasUniformClassKBound x_eq α)
    {a : ℝ} (ha : 0 < a) (ha_le_c : a ≤ c) (ha_lt_aα : a < a_α) :
    ∃ U : ClassLSingular,
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E), sys.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) →
        ‖x t₀ - x_eq‖ < a → ∀ t ∈ Ioc t₀ t₁, ‖x t - x_eq‖ ≤ U.toFun (t - t₀) := by
  obtain ⟨hc, hanti, hz, htop⟩ :=
    W_fn_invertible hconv α hα_bound ha_le_c ha_lt_aα (⟨ha, le_rfl⟩ : a ∈ Set.Ioc 0 a)
  exact ⟨{ toFun        := Function.invFunOn (W_fn sys x_eq a) (Set.Ioi 0)
           continuous   := invFunOn_continuousOn hc hanti hz htop
           pos          := fun _ hs => invFunOn_pos hc hz htop hs
           anti         := (strictAntiOn_invFunOn hc hanti hz htop).antitoneOn
           tendsto_zero := invFunOn_tendsto_zero hc hanti hz htop
           tendsto_top  := invFunOn_tendsto_atTop hc hanti hz htop },
    fun _ ht₀ _ _ hx h_init _ ht =>
      U_decay_bound hconv α hα_bound ha_le_c ha_lt_aα ⟨ha, le_rfl⟩ ht₀ hx h_init ht⟩

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
private lemma HasUniformClassKInftyBound.toClassK {sys : ContinuousSystem E Unit Y} {x_eq : E}
    {α : ClassKInfty} (h : sys.HasUniformClassKInftyBound x_eq α) {b : ℝ} (hb : 0 < b) :
    sys.HasUniformClassKBound x_eq (mk_ClassK_from_KInfty α hb) :=
  fun t₀ ht₀ t₁ x hx _ t ht => h t₀ ht₀ t₁ x hx t ht

/-- **Global uniform decay envelope.** Uniform convergence times from every ball together with a
    uniform class `K∞` bound produce a family `U` of decay envelopes, indexed by the radius of
    the ball the trajectory starts in: `U r` is positive, antitone and vanishing at `+∞`, the
    family is monotone in `r`, and `U r (t - t₀)` bounds every trajectory starting within `r` of
    `x_eq`.

    The four shape conditions are exactly the hypotheses of
    `ClassKLGlobal.of_KInfty_LSingular_family`, which is what consumes this result.

    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.5 (global case). -/
@[blueprint "lem:continuousSystem-exists-decayBound-family"
  (title := "Global uniform decay envelope")
  (latexEnv := "lemma")
  (statement := /-- Suppose the trajectories of $s$ have a uniform convergence time from every
    ball (\cref{def:continuousSystem-hasUniformConvergenceTime}) and a uniform class
    $\mathcal{K}_{\infty}$ bound (\cref{def:continuousSystem-hasUniformClassKInftyBound}).  Then
    there is a family $U : (0,\infty) \times (0,\infty) \to \mathbb{R}$ with
    \begin{enumerate}
      \item $U(r, s) > 0$ for all $r > 0$ and $s > 0$;
      \item $U(r, \cdot)$ antitone on $(0,\infty)$ for each $r > 0$;
      \item $U(r, s) \to 0$ as $s \to \infty$, for each $r > 0$;
      \item $r \mapsto U(r+1, s)$ monotone on $[0,\infty)$ for each $s > 0$;
      \item $\|x(t) - x_{\mathrm{eq}}\| \le U(r, t - t_{0})$ for every $r > 0$, every trajectory
        on a segment $[t_0, t_1]$ with $t_0 \ge 0$ and $\|x(t_0) - x_{\mathrm{eq}}\| < r$, and
        every $t \in (t_0, t_1]$.
    \end{enumerate}
    Conditions (1)--(4) are exactly the hypotheses of
    \cref{lem:classKLGlobal-of-KInfty-LSingular-family}; (5) is the decay bound.  Unlike the
    local case (\cref{lem:continuousSystem-exists-classLSingular-decayBound}) no single envelope
    can serve every initial state, so the radius remains a parameter.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.5 (global case).
  -/)
  (proof := /-- Every radius is finite, so at radius $r$ the global hypotheses restrict to the
    local ones (a uniform convergence time from the $r$-ball, and the class $\mathcal{K}_{\infty}$
    bound read as a class $\mathcal{K}$ bound on $[0, r+1)$).  Take $U(r, \cdot)$ to be the
    envelope of \cref{lem:continuousSystem-exists-classLSingular-decayBound} at that radius,
    namely the inverse of $W(r, \cdot)$.  Conditions (1)--(3) and (5) are then that lemma's
    conclusions, and (4) holds because $W$ is monotone in $r$ — a larger ball has larger optimal
    convergence times — so inverting reverses nothing. -/)]
theorem exists_decayBound_family {sys : ContinuousSystem E Unit Y} {x_eq : E} (α : ClassKInfty)
    (hGUC : ∀ c > 0, sys.HasUniformConvergenceTime x_eq c)
    (h_bound : sys.HasUniformClassKInftyBound x_eq α) :
    ∃ U : ℝ → ℝ → ℝ,
      (∀ r > 0, ∀ s > 0, 0 < U r s) ∧
      (∀ r > 0, AntitoneOn (U r) (Set.Ioi 0)) ∧
      (∀ r > 0, Filter.Tendsto (U r) Filter.atTop (nhds 0)) ∧
      (∀ s > 0, MonotoneOn (fun r => U (r + 1) s) (Set.Ici 0)) ∧
      (∀ r > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
        sys.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < r →
          ∀ t ∈ Ioc t₀ t₁, ‖x t - x_eq‖ ≤ U r (t - t₀)) := by
  -- At radius `r` the global hypotheses restrict to the local ones, with `c = r` and the class
  -- `K∞` bound read as a class `K` bound on `[0, r+1)`.
  have shape : ∀ r : ℝ, 0 < r →
      ContinuousOn (W_fn sys x_eq r) (Set.Ioi 0) ∧ StrictAntiOn (W_fn sys x_eq r) (Set.Ioi 0) ∧
        Filter.Tendsto (W_fn sys x_eq r) Filter.atTop (nhds 0) ∧
        Filter.Tendsto (W_fn sys x_eq r) (𝓝[>] 0) Filter.atTop := fun r hr =>
    W_fn_invertible (hGUC r hr) (mk_ClassK_from_KInfty α (by linarith : (0:ℝ) < r + 1))
      (h_bound.toClassK _) le_rfl (by linarith) ⟨hr, le_rfl⟩
  refine ⟨fun r => Function.invFunOn (W_fn sys x_eq r) (Set.Ioi 0), ?_, ?_, ?_, ?_, ?_⟩
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
  · intro r hr t₀ ht₀ t₁ x hx h_init t ht
    exact U_decay_bound (hGUC r hr) (mk_ClassK_from_KInfty α (by linarith : (0:ℝ) < r + 1))
      (h_bound.toClassK _) le_rfl (by linarith) ⟨hr, le_rfl⟩ ht₀ hx h_init ht


/-! ## Class `K` bounds -/

/-- Stability of `x_eq` uniformly over a set `T` of initial times: one `δ(ε)` for every `t₀ ∈ T`.
`T = [0, ∞)` is uniform stability and `T = {t₀}` is stability at `t₀`; the class `K`
characterizations of both are this one. -/
private def StableOn (s : ContinuousSystem E Unit Y) (x_eq : E) (T : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t₀ ∈ T, ∀ (t₁ : ℝ) (x : ℝ → E),
    s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < δ →
      ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ < ε

/-- The deviations from `x_eq` reachable, from an initial time in `T`, by a trajectory that
started within `r` of `x_eq`.  A set of reals: its supremum, as a function of `r`, is what the
class `K` bound majorizes. -/
private def reachableDeviations (s : ContinuousSystem E Unit Y) (x_eq : E) (T : Set ℝ) (r : ℝ) :
    Set ℝ :=
  {d | ∃ t₀ ∈ T, ∃ (t₁ : ℝ) (x : ℝ → E), s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) ∧
    ‖x t₀ - x_eq‖ ≤ r ∧ ∃ t ∈ Icc t₀ t₁, d = ‖x t - x_eq‖}

/-- The worst deviation from `x_eq` reachable from the `r`-ball, from an initial time in `T`. -/
private noncomputable def worstDeviation (s : ContinuousSystem E Unit Y) (x_eq : E) (T : Set ℝ)
    (r : ℝ) : ℝ :=
  sSup (reachableDeviations s x_eq T r)

section WorstDeviation

variable {s : ContinuousSystem E Unit Y} {x_eq : E} {T : Set ℝ}

private lemma worstDeviation_nonneg (r : ℝ) : 0 ≤ worstDeviation s x_eq T r :=
  Real.sSup_nonneg fun _ ⟨_, _, _, _, _, _, _, _, hd⟩ => hd ▸ norm_nonneg _

private lemma le_worstDeviation {r : ℝ} (hbdd : BddAbove (reachableDeviations s x_eq T r))
    {t₀ t₁ t : ℝ} {x : ℝ → E} (ht₀ : t₀ ∈ T) (hx : s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁))
    (h_init : ‖x t₀ - x_eq‖ ≤ r) (ht : t ∈ Icc t₀ t₁) :
    ‖x t - x_eq‖ ≤ worstDeviation s x_eq T r :=
  le_csSup hbdd ⟨t₀, ht₀, t₁, x, hx, h_init, t, ht, rfl⟩

private lemma worstDeviation_le {r ε : ℝ} (hε : 0 ≤ ε)
    (h_bound : ∀ t₀ ∈ T, ∀ (t₁ : ℝ) (x : ℝ → E), s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) →
      ‖x t₀ - x_eq‖ ≤ r → ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ ε) :
    worstDeviation s x_eq T r ≤ ε :=
  Real.sSup_le (fun _ ⟨t₀, ht₀, t₁, x, hx, h_init, t, ht, hd⟩ =>
    hd ▸ h_bound t₀ ht₀ t₁ x hx h_init t ht) hε

/-- A larger starting ball can only reach further, as long as its worst deviation is finite. -/
private lemma worstDeviation_mono {r₁ r₂ : ℝ} (hbdd : BddAbove (reachableDeviations s x_eq T r₂))
    (h_le : r₁ ≤ r₂) : worstDeviation s x_eq T r₁ ≤ worstDeviation s x_eq T r₂ :=
  worstDeviation_le (worstDeviation_nonneg r₂) fun _ ht₀ _ _ hx h_init _ ht =>
    le_worstDeviation hbdd ht₀ hx (h_init.trans h_le) ht

/-- `ω(0) = 0`: under stability, a trajectory starting *at* `x_eq` stays within every `ε`. -/
private lemma worstDeviation_zero (h : StableOn s x_eq T) : worstDeviation s x_eq T 0 = 0 := by
  refine le_antisymm (worstDeviation_le le_rfl fun t₀ ht₀ t₁ x hx h_init t ht => ?_)
    (worstDeviation_nonneg 0)
  by_contra h_pos
  obtain ⟨δ, hδ, h_bound⟩ := h _ (not_le.mp h_pos)
  exact lt_irrefl _ (h_bound t₀ ht₀ t₁ x hx (h_init.trans_lt hδ) t ht)

/-- A function vanishing at `0`, nonnegative on `S` and uniformly small on small arguments in `S`
is continuous at `0` within `S`. -/
private lemma continuousWithinAt_zero_of_small {ω : ℝ → ℝ} {S : Set ℝ} (hω_zero : ω 0 = 0)
    (hω_nonneg : ∀ r ∈ S, 0 ≤ ω r)
    (h_small : ∀ ε > 0, ∃ δ > 0, ∀ r ∈ S, r < δ → ω r ≤ ε) : ContinuousWithinAt ω S 0 := by
  refine Metric.continuousWithinAt_iff.mpr fun ε hε => ?_
  obtain ⟨δ, hδ, h⟩ := h_small (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun {r} hr hdr => ?_⟩
  rw [hω_zero, Real.dist_eq, sub_zero, abs_of_nonneg (hω_nonneg r hr)]
  have : r < δ := (le_abs_self r).trans_lt (by simpa [Real.dist_eq] using hdr)
  linarith [h r hr this]

/-- Under stability the worst deviation is continuous at `0`: stability at `ε` bounds it by `ε`
on `[0, δ)`. -/
private lemma worstDeviation_continuousWithinAt (h : StableOn s x_eq T) (S : Set ℝ) :
    ContinuousWithinAt (worstDeviation s x_eq T) S 0 := by
  refine continuousWithinAt_zero_of_small (worstDeviation_zero h)
    (fun r _ => worstDeviation_nonneg r) fun ε hε => ?_
  obtain ⟨δ, hδ, h_bound⟩ := h ε hε
  exact ⟨δ, hδ, fun r _ hr => worstDeviation_le hε.le fun t₀ ht₀ t₁ x hx h_init t ht =>
    (h_bound t₀ ht₀ t₁ x hx (h_init.trans_lt hr) t ht).le⟩

/-- **Stability gives a class `K` bound**, uniformly over `T`: a continuous strictly increasing
majorant of the worst deviation, which vanishes and is continuous at `0` by stability, and is
monotone. -/
private lemma exists_classK_of_stableOn (h : StableOn s x_eq T) :
    ∃ (a b : ℝ) (α : ClassK a b), ∀ t₀ ∈ T, ∀ (t₁ : ℝ) (x : ℝ → E),
      s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < a →
        ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ α.toFun ‖x t₀ - x_eq‖ := by
  -- Fix the tolerance `1` and take the radius `δ₀` stability supplies for it.  Working on
  -- `a := δ₀ / 2` rather than `δ₀` gives the strict `a < δ₀` that bounds `ω` by `1` on `[0, a]`.
  obtain ⟨δ₀, hδ₀, h_one⟩ := h 1 one_pos
  set a := δ₀ / 2
  have ha : 0 < a := half_pos hδ₀
  have ha_lt_δ₀ : a < δ₀ := half_lt_self hδ₀
  set ω : ℝ → ℝ := worstDeviation s x_eq T
  have hbdd_of_le : ∀ r ≤ a, BddAbove (reachableDeviations s x_eq T r) := fun r hr =>
    ⟨1, fun _ ⟨t₀, ht₀, t₁, x, hx, h_init, t, ht, hd⟩ =>
      hd ▸ (h_one t₀ ht₀ t₁ x hx (h_init.trans_lt (hr.trans_lt ha_lt_δ₀)) t ht).le⟩
  have hω_mono : MonotoneOn ω (Icc 0 a) := fun _ _ r₂ ⟨_, hr₂⟩ h_le =>
    worstDeviation_mono (hbdd_of_le r₂ hr₂) h_le
  obtain ⟨g, b, hb, hg_zero, hg_a, hg_cont, hg_mono, hg_bound⟩ :=
    exists_strictMono_upper_bound a ha ω (worstDeviation_zero h) hω_mono
      (worstDeviation_continuousWithinAt h _)
  refine ⟨a, b, ClassK.of_strictMono ha hb g hg_zero hg_a hg_cont hg_mono,
    fun t₀ ht₀ t₁ x hx h_init t ht => ?_⟩
  calc ‖x t - x_eq‖
      ≤ ω ‖x t₀ - x_eq‖ := le_worstDeviation (hbdd_of_le _ h_init.le) ht₀ hx le_rfl ht
    _ ≤ g ‖x t₀ - x_eq‖ := hg_bound _ (norm_nonneg _) h_init.le

/-- **A class `K` bound gives stability**, uniformly over `T`: `α` is continuous at `0` with
`α(0) = 0`, so some radius `δ` has `α(δ) < ε`. -/
private lemma stableOn_of_classK {a b : ℝ} (α : ClassK a b)
    (hα : ∀ t₀ ∈ T, ∀ (t₁ : ℝ) (x : ℝ → E), s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) →
      ‖x t₀ - x_eq‖ < a → ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ α.toFun ‖x t₀ - x_eq‖) :
    StableOn s x_eq T := by
  intro ε hε
  obtain ⟨δ_c, hδ_c, h_near⟩ := Metric.continuousWithinAt_iff.mp (α.continuous 0 ⟨le_rfl, α.ha⟩)
    ε hε
  -- Halving both radii is only to make the two comparisons below strict.
  set δ := min (δ_c / 2) (a / 2)
  have hδ_pos : 0 < δ := lt_min (half_pos hδ_c) (half_pos α.ha)
  have hδ_a : δ < a := (min_le_right ..).trans_lt (half_lt_self α.ha)
  have hδ_lt : δ < δ_c := (min_le_left ..).trans_lt (half_lt_self hδ_c)
  have hαδ : α.toFun δ < ε := by
    have h := h_near ⟨hδ_pos.le, hδ_a⟩ (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hδ_pos]
      exact hδ_lt)
    rw [α.map_zero, Real.dist_eq, sub_zero] at h
    exact (abs_lt.mp h).2
  refine ⟨δ, hδ_pos, fun t₀ ht₀ t₁ x hx h_init t ht => ?_⟩
  calc ‖x t - x_eq‖
      ≤ α.toFun ‖x t₀ - x_eq‖ := hα t₀ ht₀ t₁ x hx (h_init.trans hδ_a) t ht
    _ < α.toFun δ := (α.strict_mono_iff ⟨norm_nonneg _, h_init.trans hδ_a⟩
        ⟨hδ_pos.le, hδ_a⟩).mpr h_init
    _ < ε := hαδ

end WorstDeviation

/-- **Class `K` characterization of uniform stability**: `x_eq` is uniformly stable if and only
if the trajectories have a uniform class `K` bound.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.5. -/
@[blueprint "lem:continuousSystem-uniformlyStable-iff-classK"
  (title := "Class $\\mathcal{K}$ characterization of uniform stability")
  (latexEnv := "lemma")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is uniformly stable
    (\cref{def:continuousSystem-uniformlyStable}) if and only if the trajectories have a
    uniform class $\mathcal{K}$ bound (\cref{def:continuousSystem-hasUniformClassKBound}):
    there is a class $\mathcal{K}$ function $\alpha$ on $[0, a)$ with
    \[
      \|x(t) - x_{\mathrm{eq}}\| \le \alpha(\|x(t_0) - x_{\mathrm{eq}}\|)
    \]
    for every trajectory on a segment $[t_0, t_1]$ with $t_0 \ge 0$ and
    $\|x(t_0) - x_{\mathrm{eq}}\| < a$, and every $t \in [t_0, t_1]$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.5, first half. -/)
  (proof := /-- Forward: the worst deviation $\omega(r)$ reachable from the $r$-ball is
    nondecreasing, vanishes at $0$ and is continuous there by uniform stability; a continuous
    strictly increasing majorant (\cref{lem:exists-strictMono-upper-bound}) is the class
    $\mathcal{K}$ bound.  Backward: $\alpha$ is continuous at $0$ with $\alpha(0) = 0$, so a
    small radius $\delta$ has $\alpha(\delta) < \varepsilon$. -/)]
theorem uniformlyStable_iff_classK (s : ContinuousSystem E Unit Y) (x_eq : E) :
    s.UniformlyStable x_eq ↔ ∃ (a b : ℝ) (α : ClassK a b), s.HasUniformClassKBound x_eq α :=
  ⟨fun h => exists_classK_of_stableOn (T := Ici 0) h,
    fun ⟨_, _, α, hα⟩ => stableOn_of_classK (T := Ici 0) α hα⟩

/-- **Class `K` characterization of stability**: `x_eq` is stable if and only if, for each initial
time `t₀ ≥ 0`, the trajectories starting then have a class `K` bound.  The bound may depend on
`t₀`; one bound for all `t₀` is uniform stability (`uniformlyStable_iff_classK`). -/
@[blueprint "lem:continuousSystem-stable-iff-classK"
  (title := "Class $\\mathcal{K}$ characterization of stability")
  (latexEnv := "lemma")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is stable
    (\cref{def:continuousSystem-stable}) if and only if for each $t_0 \ge 0$ there is a class
    $\mathcal{K}$ function $\alpha_{t_0}$ on $[0, a_{t_0})$ with
    $\|x(t) - x_{\mathrm{eq}}\| \le \alpha_{t_0}(\|x(t_0) - x_{\mathrm{eq}}\|)$ for every
    trajectory on a segment $[t_0, t_1]$ with $\|x(t_0) - x_{\mathrm{eq}}\| < a_{t_0}$, and every
    $t \in [t_0, t_1]$.  A single $\alpha$ for all $t_0$ is uniform stability
    (\cref{lem:continuousSystem-uniformlyStable-iff-classK}). -/)
  (proof := /-- The argument of \cref{lem:continuousSystem-uniformlyStable-iff-classK} with the
    initial time fixed. -/)]
theorem stable_iff_classK (s : ContinuousSystem E Unit Y) (x_eq : E) :
    s.Stable x_eq ↔ ∀ t₀ : ℝ, 0 ≤ t₀ → ∃ (a b : ℝ) (α : ClassK a b), ∀ (t₁ : ℝ) (x : ℝ → E),
      s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < a →
        ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ α.toFun ‖x t₀ - x_eq‖ := by
  constructor
  · intro h t₀ ht₀
    have h_at : StableOn s x_eq {t₀} := fun ε hε => by
      obtain ⟨δ, hδ, h_bound⟩ := h ε hε t₀ ht₀
      exact ⟨δ, hδ, by rintro _ rfl; exact h_bound⟩
    obtain ⟨a, b, α, hα⟩ := exists_classK_of_stableOn h_at
    exact ⟨a, b, α, hα t₀ rfl⟩
  · intro h ε hε t₀ ht₀
    obtain ⟨a, b, α, hα⟩ := h t₀ ht₀
    obtain ⟨δ, hδ, h_bound⟩ := stableOn_of_classK (T := {t₀}) α (by rintro _ rfl; exact hα) ε hε
    exact ⟨δ, hδ, h_bound t₀ rfl⟩

/-- Global uniform stability gives a uniform class `K∞` bound: `δ(ε) → ∞` makes the worst
deviation finite from every radius, which is what makes its majorant class `K∞`. -/
private lemma exists_classKInfty_of_globallyUniformlyStable {s : ContinuousSystem E Unit Y}
    {x_eq : E} (h : s.GloballyUniformlyStable x_eq) :
    ∃ α : ClassKInfty, s.HasUniformClassKInftyBound x_eq α := by
  obtain ⟨δ, hδ_pos, hδ_top, hδ_stab⟩ := h
  have h_stable : StableOn s x_eq (Ici 0) := fun ε hε => ⟨δ ε, hδ_pos ε hε, hδ_stab ε hε⟩
  set ω : ℝ → ℝ := worstDeviation s x_eq (Ici 0)
  -- Every radius `r` lies below some `δ(M)`, which bounds the deviations from the `r`-ball by `M`.
  have hbdd : ∀ r ≥ 0, BddAbove (reachableDeviations s x_eq (Ici 0) r) := fun r _ => by
    obtain ⟨M, hM_pos, hM_gt⟩ :=
      ((eventually_gt_atTop 0).and (hδ_top (Ioi_mem_atTop r))).exists
    exact ⟨M, fun _ ⟨t₀, ht₀, t₁, x, hx, h_init, t, ht, hd⟩ =>
      hd ▸ (hδ_stab M hM_pos t₀ ht₀ t₁ x hx (h_init.trans_lt hM_gt) t ht).le⟩
  have hω_mono : MonotoneOn ω (Ici 0) := fun _ _ r₂ hr₂ h_le =>
    worstDeviation_mono (hbdd r₂ hr₂) h_le
  obtain ⟨α, hα⟩ := exists_classKInfty_upper_bound ω (worstDeviation_zero h_stable) hω_mono
    (worstDeviation_continuousWithinAt h_stable _)
  refine ⟨α, fun t₀ ht₀ t₁ x hx t ht => ?_⟩
  calc ‖x t - x_eq‖
      ≤ ω ‖x t₀ - x_eq‖ := le_worstDeviation (hbdd _ (norm_nonneg _)) ht₀ hx le_rfl ht
    _ ≤ α.toFun ‖x t₀ - x_eq‖ := hα _ (mem_Ici.mpr (norm_nonneg _))

/-! ## Class `KL` bounds -/

/-- A single function of elapsed time, tending to `0`, that bounds every trajectory from the
`c`-ball gives a uniform convergence time from it: past the time it drops below `η`, so does
every deviation. -/
private lemma hasUniformConvergenceTime_of_tendsto {s : ContinuousSystem E Unit Y} {x_eq : E}
    {c : ℝ} {g : ℝ → ℝ} (hg : Tendsto g atTop (𝓝 0))
    (h_bound : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
      s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < c →
        ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ g (t - t₀)) :
    s.HasUniformConvergenceTime x_eq c := by
  intro η hη
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hg (Iio_mem_nhds hη))
  -- `max T 0 + 1` only makes the convergence time positive.
  refine ⟨max T 0 + 1, by linarith [le_max_right T 0], fun t₀ ht₀ t₁ x hx h_init t ht => ?_⟩
  exact (h_bound t₀ ht₀ t₁ x hx h_init t ⟨by linarith [ht.1, le_max_right T 0], ht.2⟩).trans_lt
    (hT _ (by linarith [ht.1, le_max_left T 0]))

/-- A class `KL` bound on the trajectories from the `a`-ball gives a uniform convergence time
from every smaller ball, of radius `c < a`: every deviation is at most `β(c, t - t₀) → 0`.  The
radius `a` itself is out of reach in general, since `β(ρ, ·)` need not decay uniformly as
`ρ → a`. -/
@[blueprint "lem:continuousSystem-hasUniformConvergenceTime-of-classKL"
  (title := "Uniform convergence from a class $\\mathcal{KL}$ bound")
  (latexEnv := "lemma")
  (statement := /-- Let $\beta$ be class $\mathcal{KL}$ on $[0, a) \times [0, \infty)$
    (\cref{def:isClassKL}), and suppose every trajectory on a segment $[t_0, t_1]$, $t_0 \ge 0$,
    with $\|x(t_0) - x_{\mathrm{eq}}\| < a$ satisfies
    $\|x(t) - x_{\mathrm{eq}}\| \le \beta(\|x(t_0) - x_{\mathrm{eq}}\|, t - t_0)$ on the segment.
    Then for every $c < a$, trajectories from the ball of radius $c$ have a uniform convergence
    time (\cref{def:continuousSystem-hasUniformConvergenceTime}). -/)
  (proof := /-- For $c < 0$ no trajectory starts in the ball.  Otherwise every deviation is at
    most $\beta(c, t - t_0)$, by monotonicity of $\beta$ in its first argument, and
    $\beta(c, \cdot) \to 0$. -/)]
lemma hasUniformConvergenceTime_of_classKL {s : ContinuousSystem E Unit Y} {x_eq : E} {a c : ℝ}
    (β : ClassKL a) (hc : c < a)
    (hβ : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E), s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) →
      ‖x t₀ - x_eq‖ < a → ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ β.toFun ‖x t₀ - x_eq‖ (t - t₀)) :
    s.HasUniformConvergenceTime x_eq c := by
  rcases lt_or_ge c 0 with hc₀ | hc₀
  · -- No trajectory starts within a negative radius.
    exact hasUniformConvergenceTime_of_tendsto (g := fun _ => 0) tendsto_const_nhds
      fun t₀ _ t₁ x _ h_init => (lt_asymm hc₀ ((norm_nonneg _).trans_lt h_init)).elim
  have hc_mem : c ∈ Ico 0 a := ⟨hc₀, hc⟩
  refine hasUniformConvergenceTime_of_tendsto (β.tendsto_zero c hc_mem)
    fun t₀ ht₀ t₁ x hx h_init t ht => ?_
  have h_init_mem : ‖x t₀ - x_eq‖ ∈ Ico 0 a := ⟨norm_nonneg _, h_init.trans hc⟩
  calc ‖x t - x_eq‖
      ≤ β.toFun ‖x t₀ - x_eq‖ (t - t₀) := hβ t₀ ht₀ t₁ x hx h_init_mem.2 t ht
    _ ≤ β.toFun c (t - t₀) :=
        (β.strict_mono_r _ (sub_nonneg.mpr ht.1) h_init_mem hc_mem h_init).le

/-- Geometric-mean cap: a nonnegative `x` with `x ≤ A` and `x ≤ B` also has `x ≤ √(A·B)`.  This
is what combines a class `K` bound and a decay bound into one class `KL` bound. -/
private lemma le_sqrt_mul_of_le_of_le {x A B : ℝ} (hx : 0 ≤ x) (hA : x ≤ A) (hB : x ≤ B) :
    x ≤ Real.sqrt (A * B) := by
  rw [← Real.sqrt_sq hx]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- **Class `KL` characterization of uniform asymptotic stability**: `x_eq` is uniformly
asymptotically stable if and only if the trajectories from some ball have a class `KL` bound.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.5. -/
@[blueprint "lem:continuousSystem-uniformlyAsymptoticallyStable-iff-classKL"
  (title := "Class $\\mathcal{KL}$ characterization of uniform asymptotic stability")
  (latexEnv := "lemma")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is uniformly asymptotically stable
    (\cref{def:continuousSystem-uniformlyAsymptoticallyStable}) if and only if there are a class
    $\mathcal{KL}$ function $\beta$ on $[0, a) \times [0, \infty)$ (\cref{def:isClassKL}) with
    \[
      \|x(t) - x_{\mathrm{eq}}\| \le \beta(\|x(t_0) - x_{\mathrm{eq}}\|, t - t_0)
    \]
    for every trajectory on a segment $[t_0, t_1]$ with $t_0 \ge 0$ and
    $\|x(t_0) - x_{\mathrm{eq}}\| < a$, and every $t \in [t_0, t_1]$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.5, second half. -/)
  (proof := /-- Forward: uniform stability gives a class $\mathcal{K}$ bound $\alpha$
    (\cref{lem:continuousSystem-uniformlyStable-iff-classK}) and, with the uniform convergence
    time, a decay envelope $U$ (\cref{lem:continuousSystem-exists-classLSingular-decayBound});
    $\beta = \min(\alpha, \sqrt{\alpha\, U})$ is class $\mathcal{KL}$
    (\cref{lem:classKL-mk-singular-cap}) and bounds the trajectories.  Backward: $\beta(\cdot, 0)$
    is continuous at $0$, which gives uniform stability, and
    \cref{lem:continuousSystem-hasUniformConvergenceTime-of-classKL} gives the convergence
    time. -/)]
theorem uniformlyAsymptoticallyStable_iff_classKL (s : ContinuousSystem E Unit Y) (x_eq : E) :
    s.UniformlyAsymptoticallyStable x_eq ↔ ∃ (a : ℝ) (β : ClassKL a),
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E), s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) →
        ‖x t₀ - x_eq‖ < a → ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ β.toFun ‖x t₀ - x_eq‖ (t - t₀) := by
  constructor
  · rintro ⟨hUS, c, hc_pos, hconv⟩
    obtain ⟨a_α, b_α, α, hα_bound⟩ := (uniformlyStable_iff_classK s x_eq).mp hUS
    set a := min (a_α / 2) c
    have ha : 0 < a := lt_min (by linarith [α.ha]) hc_pos
    have ha_le_c : a ≤ c := min_le_right _ _
    have ha_lt_aα : a < a_α := (min_le_left _ _).trans_lt (half_lt_self α.ha)
    -- `β := min (α ·) (√(α · * U ·))`: the first factor carries the class `K` behaviour in the
    -- initial deviation, the second the decay in elapsed time.
    let α_res : ClassK a (α.toFun a) := α.restrict ha ha_lt_aα
    obtain ⟨U, hU⟩ := exists_classLSingular_decayBound hconv α hα_bound ha ha_le_c ha_lt_aα
    refine ⟨a, ClassKL.mk_singular_cap α_res U, fun t₀ ht₀ t₁ x hx h_init t ht => ?_⟩
    have h_α : ‖x t - x_eq‖ ≤ α_res.toFun ‖x t₀ - x_eq‖ :=
      hα_bound t₀ ht₀ t₁ x hx (h_init.trans ha_lt_aα) t ht
    simp only [ClassKL.mk_singular_cap]
    rcases ht.1.eq_or_lt with rfl | ht_strict
    · simp [h_α]
    · rw [if_neg (sub_pos.mpr ht_strict).ne']
      exact le_min h_α (le_sqrt_mul_of_le_of_le (norm_nonneg _) h_α
        (hU t₀ ht₀ t₁ x hx h_init t ⟨ht_strict, ht.2⟩))
  · rintro ⟨a, β, hβ⟩
    have ha : 0 < a := β.ha
    refine ⟨fun ε hε => ?_, a / 2, half_pos ha, hasUniformConvergenceTime_of_classKL β
      (half_lt_self ha) hβ⟩
    -- Uniform stability: continuity of `β(·, 0)` at `0` gives `δ(ε)`.
    obtain ⟨δ, hδ_pos, h_near⟩ :=
      Metric.continuousWithinAt_iff.mp (β.continuous_r le_rfl 0 ⟨le_rfl, ha⟩) ε hε
    refine ⟨min δ (a / 2), lt_min hδ_pos (half_pos ha), fun t₀ ht₀ t₁ x hx h_init t ht => ?_⟩
    have hr : ‖x t₀ - x_eq‖ ∈ Ico 0 a :=
      ⟨norm_nonneg _, h_init.trans ((min_le_right ..).trans_lt (half_lt_self ha))⟩
    have ht_sub : 0 ≤ t - t₀ := sub_nonneg.mpr ht.1
    have h_decay : β.toFun ‖x t₀ - x_eq‖ (t - t₀) ≤ β.toFun ‖x t₀ - x_eq‖ 0 :=
      β.anti_s _ hr (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht_sub) ht_sub
    have h_small : β.toFun ‖x t₀ - x_eq‖ 0 < ε := by
      have h := h_near hr (by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
        exact h_init.trans_le (min_le_left ..))
      rwa [β.map_zero 0 le_rfl, Real.dist_eq, sub_zero,
        abs_of_nonneg (β.nonneg _ hr 0 le_rfl)] at h
    linarith [hβ t₀ ht₀ t₁ x hx hr.2 t ht]

/-- **Class `KL` characterization of global uniform asymptotic stability**: `x_eq` is globally
uniformly asymptotically stable if and only if there is a global class `KL` bound `β` on *every*
trajectory, with no restriction on the initial state.

The conditions on `β` are spelled out rather than packaged as `ClassKLGlobal` because the two do
not coincide: this statement needs radial unboundedness of `β(·, 0)`, which `ClassKLGlobal` does
not carry, and does not need its `nonneg` field.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.5. -/
@[blueprint "lem:continuousSystem-globallyUniformlyAsymptoticallyStable-iff-classKL"
  (title := "Class $\\mathcal{KL}$ characterization, global case")
  (latexEnv := "lemma")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is globally uniformly asymptotically stable
    (\cref{def:continuousSystem-globallyUniformlyAsymptoticallyStable}) if and only if there is
    a $\beta : [0,\infty) \times [0,\infty) \to \mathbb{R}$ that is
    \begin{enumerate}
      \item zero at the origin: $\beta(0, s) = 0$ for $s \ge 0$;
      \item jointly continuous on $[0,\infty) \times [0,\infty)$;
      \item strictly increasing in $r$ for each fixed $s \ge 0$;
      \item radially unbounded: $\beta(r, 0) \to \infty$ as $r \to \infty$;
      \item antitone in $s$ for each fixed $r \ge 0$, with $\beta(r,s) \to 0$ as
        $s \to \infty$;
    \end{enumerate}
    such that $\|x(t) - x_{\mathrm{eq}}\| \le \beta(\|x(t_0) - x_{\mathrm{eq}}\|, t - t_0)$ for
    every trajectory on a segment $[t_0, t_1]$ with $t_0 \ge 0$ and every $t \in [t_0, t_1]$,
    with no restriction on the initial state.

    Condition (4) is what makes the characterization \emph{global}: without it $\beta$ is class
    $\mathcal{KL}$ on a bounded radius and the statement collapses to the local one
    (\cref{lem:continuousSystem-uniformlyAsymptoticallyStable-iff-classKL}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.5, global case. -/)
  (proof := /-- Forward: global uniform stability gives a class $\mathcal{K}_\infty$ bound, the
    convergence times from every ball a family of decay envelopes
    (\cref{lem:continuousSystem-exists-decayBound-family}), and
    \cref{lem:classKLGlobal-of-KInfty-LSingular-family} combines them.  Backward:
    $\alpha = \beta(\cdot, 0)$ is class $\mathcal{K}_\infty$ and $\delta = \alpha^{-1}$ gives
    global uniform stability; from the $r$-ball every deviation is at most $\beta(r, \cdot) \to 0$.
    -/)]
theorem globallyUniformlyAsymptoticallyStable_iff_classKL (s : ContinuousSystem E Unit Y)
    (x_eq : E) :
    s.GloballyUniformlyAsymptoticallyStable x_eq ↔ ∃ β : ℝ → ℝ → ℝ,
      (∀ σ ≥ 0, β 0 σ = 0) ∧
      ContinuousOn (Function.uncurry β) (Ici 0 ×ˢ Ici 0) ∧
      (∀ σ ≥ 0, StrictMonoOn (fun r => β r σ) (Ici 0)) ∧
      Tendsto (fun r => β r 0) atTop atTop ∧
      (∀ r ≥ 0, AntitoneOn (fun σ => β r σ) (Ici 0)) ∧
      (∀ r ≥ 0, Tendsto (fun σ => β r σ) atTop (𝓝 0)) ∧
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E), s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) →
        ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ β ‖x t₀ - x_eq‖ (t - t₀) := by
  constructor
  · rintro ⟨hGUS, hGUC⟩
    obtain ⟨α, hα⟩ := exists_classKInfty_of_globallyUniformlyStable hGUS
    obtain ⟨U, hU_pos, hU_anti, hU_tendsto, hU_mono_r, hU_decay⟩ :=
      exists_decayBound_family α hGUC hα
    obtain ⟨β, hβ_rtendsto, hβ_at_zero, hβ_at_pos⟩ :=
      ClassKLGlobal.of_KInfty_LSingular_family α U hU_pos hU_anti hU_tendsto hU_mono_r
    refine ⟨β.toFun, β.map_zero, β.continuous, β.strict_mono_r, hβ_rtendsto, β.anti_s,
      β.tendsto_zero, fun t₀ ht₀ t₁ x hx t ht => ?_⟩
    have h_α : ‖x t - x_eq‖ ≤ α.toFun ‖x t₀ - x_eq‖ := hα t₀ ht₀ t₁ x hx t ht
    rcases ht.1.eq_or_lt with rfl | ht_strict
    · rw [sub_self]
      exact h_α.trans (hβ_at_zero _ (norm_nonneg _))
    have h_sub_pos : 0 < t - t₀ := sub_pos.mpr ht_strict
    rcases (norm_nonneg (x t₀ - x_eq)).eq_or_lt with hr_zero | hr_pos
    · -- Starting at `x_eq`, the trajectory stays there.
      have h_zero : ‖x t - x_eq‖ = 0 :=
        le_antisymm (h_α.trans (by rw [← hr_zero, α.map_zero])) (norm_nonneg _)
      rw [h_zero, ← hr_zero, β.map_zero (t - t₀) h_sub_pos.le]
    · -- The geometric-mean cap chains to `β`.
      have h_U : ‖x t - x_eq‖ ≤ U (‖x t₀ - x_eq‖ + 1) (t - t₀) :=
        hU_decay _ (by positivity) t₀ ht₀ t₁ x hx (by linarith) t ⟨ht_strict, ht.2⟩
      exact (le_min h_α (le_sqrt_mul_of_le_of_le (norm_nonneg _) h_α h_U)).trans
        (hβ_at_pos _ (norm_nonneg _) _ h_sub_pos)
  · rintro ⟨β, hβ_zero, hβ_cont, hβ_mono, hβ_rtendsto, hβ_anti, hβ_stendsto, hβ_bound⟩
    let α : ClassKInfty := ClassKInfty.of_strictMono (fun r => β r 0) (hβ_zero 0 le_rfl)
      ((hβ_cont.comp (continuousOn_id.prodMk continuousOn_const)
        (fun r hr => mk_mem_prod hr (mem_Ici.mpr le_rfl))).congr (fun r _ => rfl))
      (hβ_mono 0 le_rfl) hβ_rtendsto
    refine ⟨⟨α.invFun, fun ε hε => (α.symm.pos_iff hε.le).mpr hε, α.symm.tendsto_atTop,
      fun ε hε t₀ ht₀ t₁ x hx h_init t ht => ?_⟩, fun r hr => ?_⟩
    · -- Global uniform stability, with `δ = α⁻¹` for `α = β(·, 0)`.
      have ht_sub : 0 ≤ t - t₀ := sub_nonneg.mpr ht.1
      calc ‖x t - x_eq‖
          ≤ β ‖x t₀ - x_eq‖ (t - t₀) := hβ_bound t₀ ht₀ t₁ x hx t ht
        _ ≤ β ‖x t₀ - x_eq‖ 0 := hβ_anti _ (mem_Ici.mpr (norm_nonneg _)) (mem_Ici.mpr le_rfl)
            (mem_Ici.mpr ht_sub) ht_sub
        _ = α.toFun ‖x t₀ - x_eq‖ := rfl
        _ < α.toFun (α.invFun ε) := (α.strict_mono_iff (mem_Ici.mpr (norm_nonneg _))
            (α.symm.maps_to (mem_Ici.mpr hε.le))).mpr h_init
        _ = ε := α.right_inv_apply (mem_Ici.mpr hε.le)
    · -- From the `r`-ball every deviation is at most `β(r, ·) → 0`.
      refine hasUniformConvergenceTime_of_tendsto (hβ_stendsto r hr.le)
        fun t₀ ht₀ t₁ x hx h_init t ht => ?_
      calc ‖x t - x_eq‖
          ≤ β ‖x t₀ - x_eq‖ (t - t₀) := hβ_bound t₀ ht₀ t₁ x hx t ht
        _ ≤ β r (t - t₀) := (hβ_mono (t - t₀) (sub_nonneg.mpr ht.1)
            (mem_Ici.mpr (norm_nonneg _)) (mem_Ici.mpr hr.le) h_init).le


/-! ## Bounds on solutions over `[t₀, ∞)`

A bound on every segment restricts to every solution on `[t₀, ∞)`, so the forward directions
need no hypothesis.  The converse needs forward completeness, and only from the ball on which
the bound is claimed: a bound on solutions over `[t₀, ∞)` says nothing about a segment that does
not extend to one. -/

/-- A bound on every trajectory segment holds on every solution over `[t₀, ∞)`, restricted to
`[t₀, t]`. -/
private lemma ray_of_segment {s : ContinuousSystem E Unit Y} {P : ℝ → E → Prop}
    {Q : ℝ → ℝ → E → E → Prop}
    (h : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E), s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) →
      P t₀ (x t₀) → ∀ t ∈ Icc t₀ t₁, Q t₀ t (x t₀) (x t)) :
    ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x : ℝ → E, s.IsTrajectoryOn (fun _ => ()) x (Ici t₀) →
      P t₀ (x t₀) → ∀ t : ℝ, t₀ ≤ t → Q t₀ t (x t₀) (x t) :=
  fun t₀ ht₀ x hx hP t ht =>
    h t₀ ht₀ t x (IsIntegralCurveOn.mono hx Icc_subset_Ici_self) hP t ⟨ht, le_rfl⟩

/-- If segments starting where `P` holds extend to solutions over `[t₀, ∞)`, a bound on every
such solution holds on every such segment: extend the segment and restrict back. -/
private lemma segment_of_ray {s : ContinuousSystem E Unit Y} {P : ℝ → E → Prop}
    {Q : ℝ → ℝ → E → E → Prop}
    (hfc : ∀ t₀ : ℝ, 0 ≤ t₀ → s.IsForwardCompleteOn (fun _ => ()) t₀ {x₀ | P t₀ x₀})
    (h : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x : ℝ → E, s.IsTrajectoryOn (fun _ => ()) x (Ici t₀) →
      P t₀ (x t₀) → ∀ t : ℝ, t₀ ≤ t → Q t₀ t (x t₀) (x t)) :
    ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E), s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) →
      P t₀ (x t₀) → ∀ t ∈ Icc t₀ t₁, Q t₀ t (x t₀) (x t) := by
  intro t₀ ht₀ t₁ x hx hP t ht
  have h_le : t₀ ≤ t₁ := ht.1.trans ht.2
  obtain ⟨y, hy, hyx⟩ := hfc t₀ ht₀ t₁ x h_le hx hP
  have hy₀ : y t₀ = x t₀ := hyx (left_mem_Icc.mpr h_le)
  have h_y := h t₀ ht₀ y hy (hy₀ ▸ hP) t ht.1
  rwa [hy₀, hyx ht] at h_y

/-- Completeness from the ball of radius `c` gives completeness from every smaller ball. -/
private lemma isForwardCompleteOn_of_le {s : ContinuousSystem E Unit Y} {x_eq : E} {c a : ℝ}
    (hfc : ∀ t₀ : ℝ, 0 ≤ t₀ → s.IsForwardCompleteOn (fun _ => ()) t₀ (Metric.ball x_eq c))
    (ha : a ≤ c) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    s.IsForwardCompleteOn (fun _ => ()) t₀ {x₀ | ‖x₀ - x_eq‖ < a} :=
  fun t₁ x h_le hx hx₀ =>
    hfc t₀ ht₀ t₁ x h_le hx (mem_ball_iff_norm.mpr (lt_of_lt_of_le hx₀ ha))

/-- **A uniformly stable equilibrium has a class `K` bound on every solution over `[t₀, ∞)`.**
No completeness is needed: such a solution restricts to every segment. -/
theorem UniformlyStable.exists_classK_Ici {s : ContinuousSystem E Unit Y} {x_eq : E}
    (h : s.UniformlyStable x_eq) :
    ∃ (a b : ℝ) (α : ClassK a b), ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x : ℝ → E,
      s.IsTrajectoryOn (fun _ => ()) x (Ici t₀) → ‖x t₀ - x_eq‖ < a →
        ∀ t : ℝ, t₀ ≤ t → ‖x t - x_eq‖ ≤ α.toFun ‖x t₀ - x_eq‖ := by
  obtain ⟨a, b, α, hα⟩ := (uniformlyStable_iff_classK s x_eq).mp h
  exact ⟨a, b, α, ray_of_segment (P := fun _ x₀ => ‖x₀ - x_eq‖ < a)
    (Q := fun _ _ x₀ x => ‖x - x_eq‖ ≤ α.toFun ‖x₀ - x_eq‖) hα⟩

/-- **A uniformly asymptotically stable equilibrium has a class `KL` bound on every solution
over `[t₀, ∞)`.**  No completeness is needed: such a solution restricts to every segment. -/
theorem UniformlyAsymptoticallyStable.exists_classKL_Ici {s : ContinuousSystem E Unit Y}
    {x_eq : E} (h : s.UniformlyAsymptoticallyStable x_eq) :
    ∃ (a : ℝ) (β : ClassKL a), ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x : ℝ → E,
      s.IsTrajectoryOn (fun _ => ()) x (Ici t₀) → ‖x t₀ - x_eq‖ < a →
        ∀ t : ℝ, t₀ ≤ t → ‖x t - x_eq‖ ≤ β.toFun ‖x t₀ - x_eq‖ (t - t₀) := by
  obtain ⟨a, β, hβ⟩ := (uniformlyAsymptoticallyStable_iff_classKL s x_eq).mp h
  exact ⟨a, β, ray_of_segment (P := fun _ x₀ => ‖x₀ - x_eq‖ < a)
    (Q := fun t₀ t x₀ x => ‖x - x_eq‖ ≤ β.toFun ‖x₀ - x_eq‖ (t - t₀)) hβ⟩

/-- **A globally uniformly asymptotically stable equilibrium has a global class `KL` bound on
every solution over `[t₀, ∞)`.**  No completeness is needed: such a solution restricts to every
segment. -/
theorem GloballyUniformlyAsymptoticallyStable.exists_classKL_Ici
    {s : ContinuousSystem E Unit Y} {x_eq : E}
    (h : s.GloballyUniformlyAsymptoticallyStable x_eq) :
    ∃ β : ℝ → ℝ → ℝ,
      (∀ σ ≥ 0, β 0 σ = 0) ∧
      ContinuousOn (Function.uncurry β) (Ici 0 ×ˢ Ici 0) ∧
      (∀ σ ≥ 0, StrictMonoOn (fun r => β r σ) (Ici 0)) ∧
      Tendsto (fun r => β r 0) atTop atTop ∧
      (∀ r ≥ 0, AntitoneOn (fun σ => β r σ) (Ici 0)) ∧
      (∀ r ≥ 0, Tendsto (fun σ => β r σ) atTop (𝓝 0)) ∧
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x : ℝ → E, s.IsTrajectoryOn (fun _ => ()) x (Ici t₀) →
        ∀ t : ℝ, t₀ ≤ t → ‖x t - x_eq‖ ≤ β ‖x t₀ - x_eq‖ (t - t₀) := by
  obtain ⟨β, h0, hc, hm, ht, ha, hz, hβ⟩ :=
    (globallyUniformlyAsymptoticallyStable_iff_classKL s x_eq).mp h
  exact ⟨β, h0, hc, hm, ht, ha, hz, fun t₀ ht₀ x hx => ray_of_segment (P := fun _ _ => True)
    (Q := fun t₀ t x₀ x => ‖x - x_eq‖ ≤ β ‖x₀ - x_eq‖ (t - t₀))
    (fun t₀ ht₀ t₁ x hx _ => hβ t₀ ht₀ t₁ x hx) t₀ ht₀ x hx trivial⟩

/-- **Class `K` characterization of uniform stability, over `[t₀, ∞)`**: if the system is
forward complete from some ball about `x_eq`, then `x_eq` is uniformly stable if and only if
there is a class `K` bound on every solution over `[t₀, ∞)` from some ball.  The forward
direction needs no completeness (`UniformlyStable.exists_classK_Ici`); the converse needs it,
since otherwise the bound says nothing about solutions that escape in finite time. -/
@[blueprint "lem:continuousSystem-uniformlyStable-iff-classK-of-isForwardCompleteOn"
  (title := "Class $\\mathcal{K}$ characterization")
  (latexEnv := "lemma")
  (statement := /-- Let the system be forward complete from some ball $B(x_{\mathrm{eq}}, c)$ at
    every $t_0 \ge 0$ (\cref{def:continuousSystem-isForwardCompleteOn}).  Then $x_{\mathrm{eq}}$
    is uniformly stable if and only if there is a class $\mathcal{K}$ function $\alpha$ on
    $[0, a)$ with $\|x(t) - x_{\mathrm{eq}}\| \le \alpha(\|x(t_0) - x_{\mathrm{eq}}\|)$ for every
    solution $x$ on $[t_0, \infty)$ with $t_0 \ge 0$ and $\|x(t_0) - x_{\mathrm{eq}}\| < a$, and
    every $t \ge t_0$.  The forward direction holds without completeness. -/)
  (proof := /-- \cref{lem:continuousSystem-uniformlyStable-iff-classK}, with the bound moved
    between segments and solutions on $[t_0, \infty)$.  Forward: restrict a solution to
    $[t_0, t]$.  Converse: shrink the radius to $a' = \min(c, a/2)$, restricting $\alpha$
    (\cref{lem:classK-restrict}); a segment starting within $a'$ extends by completeness to a
    solution on $[t_0, \infty)$, which the bound covers. -/)]
theorem uniformlyStable_iff_classK_of_isForwardCompleteOn {s : ContinuousSystem E Unit Y}
    {x_eq : E}
    (hfc : ∃ c > 0, ∀ t₀ : ℝ, 0 ≤ t₀ →
      s.IsForwardCompleteOn (fun _ => ()) t₀ (Metric.ball x_eq c)) :
    s.UniformlyStable x_eq ↔ ∃ (a b : ℝ) (α : ClassK a b), ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x : ℝ → E,
      s.IsTrajectoryOn (fun _ => ()) x (Ici t₀) → ‖x t₀ - x_eq‖ < a →
        ∀ t : ℝ, t₀ ≤ t → ‖x t - x_eq‖ ≤ α.toFun ‖x t₀ - x_eq‖ := by
  refine ⟨UniformlyStable.exists_classK_Ici, ?_⟩
  rintro ⟨a, b, α, hα⟩
  obtain ⟨c, hc : 0 < c, hfc⟩ := hfc
  have ha' : 0 < min c (a / 2) := lt_min hc (half_pos α.ha)
  have ha'a : min c (a / 2) < a := (min_le_right _ _).trans_lt (half_lt_self α.ha)
  refine (uniformlyStable_iff_classK s x_eq).mpr ⟨_, _, α.restrict ha' ha'a, ?_⟩
  exact segment_of_ray (P := fun _ x₀ => ‖x₀ - x_eq‖ < min c (a / 2))
    (Q := fun _ _ x₀ x => ‖x - x_eq‖ ≤ α.toFun ‖x₀ - x_eq‖)
    (isForwardCompleteOn_of_le hfc (min_le_left _ _))
    fun t₀ ht₀ x hx hx₀ => hα t₀ ht₀ x hx (hx₀.trans ha'a)

/-- **Class `KL` characterization of uniform asymptotic stability, over `[t₀, ∞)`**: if the
system is forward complete from some ball about `x_eq`, then `x_eq` is uniformly asymptotically
stable if and only if the solutions over `[t₀, ∞)` from some ball have a class `KL` bound.  The
forward direction needs no completeness (`UniformlyAsymptoticallyStable.exists_classKL_Ici`). -/
@[blueprint
  "lem:continuousSystem-uniformlyAsymptoticallyStable-iff-classKL-of-isForwardCompleteOn"
  (title := "Class $\\mathcal{KL}$ characterization for forward-complete systems")
  (latexEnv := "lemma")
  (statement := /-- Let the system be forward complete from some ball $B(x_{\mathrm{eq}}, c)$ at
    every $t_0 \ge 0$ (\cref{def:continuousSystem-isForwardCompleteOn}).  Then $x_{\mathrm{eq}}$
    is uniformly asymptotically stable if and only if there is a class $\mathcal{KL}$ function
    $\beta$ on $[0, a) \times [0, \infty)$ with
    $\|x(t) - x_{\mathrm{eq}}\| \le \beta(\|x(t_0) - x_{\mathrm{eq}}\|, t - t_0)$ for every
    solution $x$ on $[t_0, \infty)$ with $t_0 \ge 0$ and $\|x(t_0) - x_{\mathrm{eq}}\| < a$, and
    every $t \ge t_0$.  The forward direction holds without completeness. -/)
  (proof := /-- \cref{lem:continuousSystem-uniformlyAsymptoticallyStable-iff-classKL}, with the
    bound moved between segments and solutions on $[t_0, \infty)$ as in
    \cref{lem:continuousSystem-uniformlyStable-iff-classK-of-isForwardCompleteOn}, shrinking the
    radius to $\min(c, a)$ (\cref{lem:classKL-restrict}). -/)]
theorem uniformlyAsymptoticallyStable_iff_classKL_of_isForwardCompleteOn
    {s : ContinuousSystem E Unit Y} {x_eq : E}
    (hfc : ∃ c > 0, ∀ t₀ : ℝ, 0 ≤ t₀ →
      s.IsForwardCompleteOn (fun _ => ()) t₀ (Metric.ball x_eq c)) :
    s.UniformlyAsymptoticallyStable x_eq ↔ ∃ (a : ℝ) (β : ClassKL a), ∀ t₀ : ℝ, 0 ≤ t₀ →
      ∀ x : ℝ → E, s.IsTrajectoryOn (fun _ => ()) x (Ici t₀) → ‖x t₀ - x_eq‖ < a →
        ∀ t : ℝ, t₀ ≤ t → ‖x t - x_eq‖ ≤ β.toFun ‖x t₀ - x_eq‖ (t - t₀) := by
  refine ⟨UniformlyAsymptoticallyStable.exists_classKL_Ici, ?_⟩
  rintro ⟨a, β, hβ⟩
  obtain ⟨c, hc : 0 < c, hfc⟩ := hfc
  refine (uniformlyAsymptoticallyStable_iff_classKL s x_eq).mpr
    ⟨_, β.restrict (lt_min hc β.ha) (min_le_right _ _), ?_⟩
  exact segment_of_ray (P := fun _ x₀ => ‖x₀ - x_eq‖ < min c a)
    (Q := fun t₀ t x₀ x => ‖x - x_eq‖ ≤ β.toFun ‖x₀ - x_eq‖ (t - t₀))
    (isForwardCompleteOn_of_le hfc (min_le_left _ _))
    fun t₀ ht₀ x hx hx₀ => hβ t₀ ht₀ x hx (hx₀.trans_le (min_le_right _ _))

/-- **Class `KL` characterization of global uniform asymptotic stability, over `[t₀, ∞)`**: for a
forward complete system, `x_eq` is globally uniformly asymptotically stable if and only if there
is a global class `KL` bound on every solution over `[t₀, ∞)`.  The forward direction needs no
completeness (`GloballyUniformlyAsymptoticallyStable.exists_classKL_Ici`). -/
@[blueprint
  "lem:continuousSystem-globallyUniformlyAsymptoticallyStable-iff-classKL-of-isForwardComplete"
  (title := "Class $\\mathcal{KL}$ characterization for forward-complete systems, global case")
  (latexEnv := "lemma")
  (statement := /-- Let the system be forward complete
    (\cref{def:continuousSystem-isForwardComplete}).  Then $x_{\mathrm{eq}}$ is globally
    uniformly asymptotically stable if and only if there is a $\beta$ with the properties of
    \cref{lem:continuousSystem-globallyUniformlyAsymptoticallyStable-iff-classKL} and
    $\|x(t) - x_{\mathrm{eq}}\| \le \beta(\|x(t_0) - x_{\mathrm{eq}}\|, t - t_0)$ for every
    solution $x$ on $[t_0, \infty)$ with $t_0 \ge 0$, and every $t \ge t_0$.  The forward
    direction holds without completeness. -/)
  (proof := /-- \cref{lem:continuousSystem-globallyUniformlyAsymptoticallyStable-iff-classKL},
    with the bound moved between segments and solutions on $[t_0, \infty)$ as in
    \cref{lem:continuousSystem-uniformlyStable-iff-classK-of-isForwardCompleteOn}. -/)]
theorem globallyUniformlyAsymptoticallyStable_iff_classKL_of_isForwardComplete
    {s : ContinuousSystem E Unit Y} {x_eq : E} (hfc : s.IsForwardComplete (fun _ => ())) :
    s.GloballyUniformlyAsymptoticallyStable x_eq ↔ ∃ β : ℝ → ℝ → ℝ,
      (∀ σ ≥ 0, β 0 σ = 0) ∧
      ContinuousOn (Function.uncurry β) (Ici 0 ×ˢ Ici 0) ∧
      (∀ σ ≥ 0, StrictMonoOn (fun r => β r σ) (Ici 0)) ∧
      Tendsto (fun r => β r 0) atTop atTop ∧
      (∀ r ≥ 0, AntitoneOn (fun σ => β r σ) (Ici 0)) ∧
      (∀ r ≥ 0, Tendsto (fun σ => β r σ) atTop (𝓝 0)) ∧
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x : ℝ → E, s.IsTrajectoryOn (fun _ => ()) x (Ici t₀) →
        ∀ t : ℝ, t₀ ≤ t → ‖x t - x_eq‖ ≤ β ‖x t₀ - x_eq‖ (t - t₀) := by
  refine ⟨GloballyUniformlyAsymptoticallyStable.exists_classKL_Ici,
    fun ⟨β, h0, hc, hm, ht, ha, hz, hβ⟩ =>
      (globallyUniformlyAsymptoticallyStable_iff_classKL s x_eq).mpr
        ⟨β, h0, hc, hm, ht, ha, hz, ?_⟩⟩
  exact fun t₀ ht₀ t₁ x hx => segment_of_ray (P := fun _ _ => True)
    (Q := fun t₀ t x₀ x => ‖x - x_eq‖ ≤ β ‖x₀ - x_eq‖ (t - t₀)) (fun t₀ _ => hfc t₀)
    (fun t₀ ht₀ x hx _ => hβ t₀ ht₀ x hx) t₀ ht₀ t₁ x hx trivial

end ContinuousSystem

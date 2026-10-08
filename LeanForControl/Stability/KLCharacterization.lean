import LeanForControl.Stability.DefsNonAutonomous
import LeanForControl.Stability.KLCharacterizationTools
import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKInfty
import LeanForControl.Comparison.ClassKL
import LeanForControl.Comparison.ComparisonFunctions

import LeanForControl.Analysis.MonotoneFunctions

import Architect




variable {n : ℕ}

/-!
# `Stability.KLCharacterization`

Class K / KL characterisations of uniform stability for non-autonomous ODEs `ẋ = f(t, x)`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.).

## Main results

* **Class-K characterization of uniform stability** (`uniformlyStableNA_iff_classK`):
  `UniformlyStableNA` iff there exist a class K function `α` and `c > 0` (independent of
  `t₀`) such that `‖x(t) - x_eq‖ ≤ α(‖x(t₀) - x_eq‖)` for all `t ≥ t₀ ≥ 0`,
  `‖x(t₀) - x_eq‖ < c`.

* **Class-KL characterization of uniform asymptotic stability**
  (`uniformlyAsymptoticStableNA_iff_classKL`): `UniformlyAsymptoticStableNA` iff there exist
  a class KL function `β` and `c > 0` (independent of `t₀`) such that
  `‖x(t) - x_eq‖ ≤ β(‖x(t₀) - x_eq‖, t − t₀)` for all `t ≥ t₀ ≥ 0`, `‖x(t₀) - x_eq‖ < c`.

* **Class-KL characterization of global uniform asymptotic stability**
  (`globallyUniformlyAsymptoticStableNA_iff_classKL`): `GloballyUniformlyAsymptoticStableNA`
  iff the same class-KL bound holds for every initial state (no restriction on
  `‖x(t₀) - x_eq‖`).
-/

open Set Filter Topology

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)




/-- The distances from `x_eq` attainable by a trajectory that started in the closed ball of
radius `r` about `x_eq`.

A set of *reals*, not of states: its elements are the values `‖φ t - x_eq‖`. Its supremum,
as a function of `r`, is the class `K` majorant built by `uniformlyStable_implies_classK` —
uniform stability says exactly that this set is bounded, and monotone in `r`. -/
private def normsReachableFromBall (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (r : ℝ) : Set ℝ :=
  {d | ∃ (φ : ℝ → ℝⁿ) (t₀ t : ℝ), 0 ≤ t₀ ∧ t₀ ≤ t ∧ IsTrajectoryNA φ f t₀ ∧
       ‖φ t₀ - x_eq‖ ≤ r ∧ d = ‖φ t - x_eq‖}

/-- The deviation of a trajectory at any time is reachable from its own initial radius. -/
private lemma mem_normsReachableFromBall {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {r : ℝ}
    {φ : ℝ → ℝⁿ} {t₀ t : ℝ} (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t) (hφ : IsTrajectoryNA φ f t₀)
    (h_init : ‖φ t₀ - x_eq‖ ≤ r) :
    ‖φ t - x_eq‖ ∈ normsReachableFromBall f x_eq r :=
  ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩

/-- A function vanishing at `0`, nonnegative on `S` and uniformly small on small arguments in `S`
is continuous at `0` within `S`.  This is how stability makes the worst-deviation function `ω`
continuous at `0`. -/
private lemma continuousWithinAt_zero_of_small {ω : ℝ → ℝ} {S : Set ℝ} (hω_zero : ω 0 = 0)
    (hω_nonneg : ∀ s ∈ S, 0 ≤ ω s)
    (h_small : ∀ ε > 0, ∃ δ > 0, ∀ s ∈ S, s < δ → ω s ≤ ε) : ContinuousWithinAt ω S 0 := by
  refine Metric.continuousWithinAt_iff.mpr fun ε hε => ?_
  obtain ⟨δ, hδ, h⟩ := h_small (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun {s} hs hds => ?_⟩
  rw [hω_zero, Real.dist_eq, sub_zero, abs_of_nonneg (hω_nonneg s hs)]
  have : s < δ := (le_abs_self s).trans_lt (by simpa [Real.dist_eq] using hds)
  linarith [h s hs this]

/-! ### The worst-deviation function -/

/-- The worst deviation from `x_eq` reachable by a trajectory that started within `r` of it,
i.e. the supremum of `normsReachableFromBall f x_eq r`.

Uniform stability says exactly that this is finite and small with `r`; the class `K` (and
`K∞`) bounds below are continuous strictly-increasing majorants of it. -/
private noncomputable def worstDeviation (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (r : ℝ) : ℝ :=
  sSup (normsReachableFromBall f x_eq r)

/-- The worst deviation is nonnegative: it is a supremum of norms (and `sSup ∅ = 0`). -/
private lemma worstDeviation_nonneg (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (r : ℝ) :
    0 ≤ worstDeviation f x_eq r :=
  Real.sSup_nonneg fun _ ⟨_, _, _, _, _, _, _, hd⟩ => hd ▸ norm_nonneg _

/-- A trajectory's deviation is at most the worst deviation from any ball containing its
initial state, provided that worst deviation is finite. -/
private lemma le_worstDeviation {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {r : ℝ}
    (hbdd : BddAbove (normsReachableFromBall f x_eq r))
    {φ : ℝ → ℝⁿ} {t₀ t : ℝ} (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t) (hφ : IsTrajectoryNA φ f t₀)
    (h_init : ‖φ t₀ - x_eq‖ ≤ r) :
    ‖φ t - x_eq‖ ≤ worstDeviation f x_eq r :=
  le_csSup hbdd (mem_normsReachableFromBall ht₀ ht hφ h_init)

/-- To bound the worst deviation by `ε ≥ 0`, bound every deviation reachable from the ball. -/
private lemma worstDeviation_le {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {r ε : ℝ} (hε : 0 ≤ ε)
    (h_bound : ∀ (φ : ℝ → ℝⁿ) (t₀ t : ℝ), 0 ≤ t₀ → t₀ ≤ t → IsTrajectoryNA φ f t₀ →
      ‖φ t₀ - x_eq‖ ≤ r → ‖φ t - x_eq‖ ≤ ε) :
    worstDeviation f x_eq r ≤ ε :=
  Real.sSup_le (fun _ ⟨φ, t₀, t, ht₀, ht, hφ, h_init, hd⟩ =>
    hd ▸ h_bound φ t₀ t ht₀ ht hφ h_init) hε

/-- `ω 0 = 0`: a trajectory starting *at* a stable equilibrium never leaves it. -/
private lemma worstDeviation_zero {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (hS : StableNA f x_eq) :
    worstDeviation f x_eq 0 = 0 := by
  refine le_antisymm ?_ (worstDeviation_nonneg f x_eq 0)
  refine worstDeviation_le le_rfl fun φ t₀ t ht₀ ht hφ h_init => ?_
  have h_start : φ t₀ = x_eq :=
    sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h_init (norm_nonneg _)))
  simp [hφ.eq_of_stableNA hS ht₀ h_start ht]

/-- A larger starting ball can only reach further, as long as its worst deviation is
finite. -/
private lemma worstDeviation_mono {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {r₁ r₂ : ℝ}
    (hbdd : BddAbove (normsReachableFromBall f x_eq r₂)) (h_le : r₁ ≤ r₂) :
    worstDeviation f x_eq r₁ ≤ worstDeviation f x_eq r₂ :=
  worstDeviation_le (worstDeviation_nonneg f x_eq r₂) fun _ _ _ ht₀ ht hφ h_init =>
    le_worstDeviation hbdd ht₀ ht hφ (h_init.trans h_le)

/-- Under uniform stability the worst deviation is continuous at `0`: stability at `ε`
bounds it by `ε` on `[0, δ)`. -/
private lemma worstDeviation_continuousWithinAt {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (hUS : UniformlyStableNA f x_eq) (S : Set ℝ) :
    ContinuousWithinAt (worstDeviation f x_eq) S 0 := by
  refine continuousWithinAt_zero_of_small (worstDeviation_zero hUS.stableNA)
    (fun s _ => worstDeviation_nonneg f x_eq s) fun ε hε => ?_
  obtain ⟨δ, hδ, hUS_ε⟩ := hUS ε hε
  exact ⟨δ, hδ, fun s _ hs => worstDeviation_le hε.le fun φ t₀ t ht₀ ht hφ h_init =>
    (hUS_ε t₀ ht₀ φ hφ (h_init.trans_lt hs) t ht).le⟩

/-! ### Uniform stability gives class `K` bounds -/

/-- Uniform stability yields a class `K` bound on the deviation, on some initial radius. -/
private lemma uniformlyStable_implies_classK (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    (hUS : UniformlyStableNA f x_eq) :
    ∃ (a b : ℝ) (α : ClassK a b), HasUniformClassKBound f x_eq α := by
  -- The class `K` bound is a continuous strictly-increasing majorant of the worst deviation
  -- `ω`, which vanishes and is continuous at `0` by stability, and is monotone.
  -- Fix any tolerance — `1` will do — and take the radius `δ₀` stability supplies for it.
  -- We work on `a := δ₀ / 2` rather than on `δ₀` itself only to get the *strict* inequality
  -- `a < δ₀`, which is what lets `hbdd_of_le` bound `ω` by `1` on the whole of `[0, a]`.
  obtain ⟨δ₀, hδ₀, hUS_1⟩ := hUS 1 one_pos
  let a := δ₀ / 2
  have ha       : 0 < a   := half_pos hδ₀
  have ha_lt_δ₀ : a < δ₀  := half_lt_self hδ₀
  let ω : ℝ → ℝ := worstDeviation f x_eq
  -- Bounded by 1 whenever the initial radius is at most `a`, by stability at `ε = 1`.
  have hbdd_of_le : ∀ r ≤ a, BddAbove (normsReachableFromBall f x_eq r) := fun r hr =>
    ⟨1, fun d ⟨φ, t₀, t, ht₀, ht, hφ, h_init, heq⟩ =>
      heq ▸ le_of_lt
        (hUS_1 t₀ ht₀ φ hφ (h_init.trans_lt (hr.trans_lt ha_lt_δ₀)) t ht)⟩
  have hω_zero : ω 0 = 0 := worstDeviation_zero hUS.stableNA
  have hω_mono : MonotoneOn ω (Set.Icc 0 a) := fun _ _ s₂ ⟨_, hs₂⟩ hs₁₂ =>
    worstDeviation_mono (hbdd_of_le s₂ hs₂) hs₁₂
  have hω_cont : ContinuousWithinAt ω (Set.Icc 0 a) 0 :=
    worstDeviation_continuousWithinAt hUS _
  -- Class K majorant: exists_strictMono_upper_bound lifts it to a strictly increasing bound
  obtain ⟨b, α, hα_bound⟩ : ∃ (b : ℝ) (α : ClassK a b),
      ∀ r ∈ Set.Ico 0 a, ω r ≤ α.toFun r := by
    obtain ⟨g, b, hb, hg_zero, hg_a, hg_cont, hg_mono, hg_bound⟩ :=
      exists_strictMono_upper_bound a ha ω hω_zero hω_mono hω_cont
    exact ⟨b, ClassK.of_strictMono ha hb g hg_zero hg_a hg_cont hg_mono,
      fun r hr => hg_bound r hr.1 hr.2.le⟩
  refine ⟨a, b, α, fun t₀ ht₀ φ hφ h_init t ht => ?_⟩
  have hr : ‖φ t₀ - x_eq‖ ∈ Set.Ico 0 a := ⟨norm_nonneg _, h_init⟩
  calc ‖φ t - x_eq‖
      ≤ ω ‖φ t₀ - x_eq‖       := le_worstDeviation (hbdd_of_le _ hr.2.le) ht₀ ht hφ le_rfl
    _ ≤ α.toFun ‖φ t₀ - x_eq‖ := hα_bound _ hr

/-- Global uniform stability yields a class `K∞` bound on the deviation, from every initial
state. -/
private lemma globallyUniformlyStable_implies_classKInfty (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    (hGUS : ∃ δ : ℝ → ℝ, (∀ ε > 0, 0 < δ ε) ∧ Filter.Tendsto δ Filter.atTop Filter.atTop ∧
      ∀ ε > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
        IsTrajectoryNA φ f t₀ → ‖φ t₀ - x_eq‖ < δ ε → ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ < ε) :
    ∃ α : ClassKInfty, HasUniformClassKInftyBound f x_eq α := by
  -- As in the local case, majorize the worst deviation `ω`; now `δ(ε) → ∞` makes `ω` finite
  -- for *every* radius, which is what makes the majorant class `K∞`.
  obtain ⟨δ, hδ_pos, hδ_top, hδ_stab⟩ := hGUS
  -- Global uniform stability is in particular uniform stability.
  have hUS : UniformlyStableNA f x_eq := fun ε hε => ⟨δ ε, hδ_pos ε hε, hδ_stab ε hε⟩
  let ω : ℝ → ℝ := worstDeviation f x_eq
  -- δ(ε) → ∞ means every r-ball has a bounding M: take ε with δ(ε) > r
  have hbdd_of_le : ∀ r ≥ 0, BddAbove (normsReachableFromBall f x_eq r) := fun r _ => by
    have h_eventual : ∀ᶠ ε in Filter.atTop, 0 < ε ∧ r < δ ε :=
      (Filter.eventually_gt_atTop 0).and (hδ_top (Filter.Ioi_mem_atTop r))
    obtain ⟨M, hM_pos, hM_gt_r⟩ := h_eventual.exists
    exact ⟨M, fun _ ⟨φ, t₀, t, ht₀, ht, hφ, h_init, heq⟩ =>
      heq ▸ (hδ_stab M hM_pos t₀ ht₀ φ hφ (by linarith) t ht).le⟩
  have hω_zero : ω 0 = 0 := worstDeviation_zero hUS.stableNA
  have hω_mono : MonotoneOn ω (Set.Ici 0) := fun _ _ r₂ hr₂ h_le =>
    worstDeviation_mono (hbdd_of_le r₂ hr₂) h_le
  have hω_cont : ContinuousWithinAt ω (Set.Ici 0) 0 :=
    worstDeviation_continuousWithinAt hUS _
  obtain ⟨α, hα_bound⟩ := exists_classKInfty_upper_bound ω hω_zero hω_mono hω_cont
  refine ⟨α, fun t₀ ht₀ φ hφ t ht => ?_⟩
  calc ‖φ t - x_eq‖
      ≤ ω ‖φ t₀ - x_eq‖       := le_worstDeviation (hbdd_of_le _ (norm_nonneg _)) ht₀ ht hφ le_rfl
    _ ≤ α.toFun ‖φ t₀ - x_eq‖ := hα_bound _ (Set.mem_Ici.mpr (norm_nonneg _))

/-- **Class-K characterization of uniform stability**: The equilibrium `x_eq` is uniformly
    stable if and only if there exist
    a class K function `α` on `[0, c)` and a constant `c > 0` (independent of `t₀`) such that
    every trajectory with `‖φ t₀ - x_eq‖ < c` satisfies
    `‖φ t - x_eq‖ ≤ α(‖φ t₀ - x_eq‖)` for all `t ≥ t₀ ≥ 0`.

    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.5. -/
@[blueprint "lem:uniformlyStableNA-iff-classK"
  (title := "Class $\\mathcal{K}$ characterization of uniform stability")
  (latexEnv := "lemma")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ of $\dot{x} = f(t,x)$ is
    \emph{uniformly stable} (\cref{def:uniformlyStableNA}) if and only if there exist a
    class $\mathcal{K}$ function $\alpha$ on $[0,a)$, with $a$ independent of $t_{0}$,
    such that
    \[
      \|\varphi(t) - x_{\mathrm{eq}}\| \le \alpha(\|\varphi(t_{0}) - x_{\mathrm{eq}}\|)
      \quad \forall\, t \ge t_{0} \ge 0,\;
      \forall\, \|\varphi(t_{0}) - x_{\mathrm{eq}}\| < a.
    \]
    This is the first half of Khalil's Lemma 4.5; the displayed bound is his (4.19).  Both
    sides quantify over the same trajectories — those defined on $[t_{0},\infty)$ — so the
    equivalence is between two descriptions of one class of solutions, not between two
    classes. -/)]
theorem uniformlyStableNA_iff_classK (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) :
    UniformlyStableNA f x_eq ↔
    ∃ (a b : ℝ) (α : ClassK a b), HasUniformClassKBound f x_eq α := by
  refine ⟨uniformlyStable_implies_classK f x_eq, ?_⟩
  · rintro ⟨a, b, α, hα⟩ ε hε
    -- `α` is continuous at `0` with `α 0 = 0`, so some radius `δ` has `α δ < ε`.
    have h_cont := α.continuous 0 ⟨le_refl 0, α.ha⟩
    rw [Metric.continuousWithinAt_iff] at h_cont
    rcases h_cont ε hε with ⟨δ_c, hδ_c_pos, hδ_c⟩
    -- Halving both radii is only to make the two comparisons below strict.
    let δ := min (δ_c / 2) (a / 2)
    have hδ_pos : 0 < δ   := lt_min (half_pos hδ_c_pos) (half_pos α.ha)
    have hδ_a   : δ < a   := (min_le_right ..).trans_lt (half_lt_self α.ha)
    have hδ_lt  : δ < δ_c := (min_le_left ..).trans_lt (half_lt_self hδ_c_pos)
    have hαδ : α.toFun δ < ε := by
      have h_alpha := hδ_c ⟨hδ_pos.le, hδ_a⟩
        (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ_pos]; exact hδ_lt)
      rw [α.map_zero, Real.dist_eq, sub_zero] at h_alpha
      exact (abs_lt.mp h_alpha).2
    refine ⟨δ, hδ_pos, fun t₀ ht₀ φ hφ h_init t ht => ?_⟩
    calc ‖φ t - x_eq‖
        ≤ α.toFun ‖φ t₀ - x_eq‖ := hα t₀ ht₀ φ hφ (h_init.trans hδ_a) t ht
      _ < α.toFun δ             := (α.strict_mono_iff ⟨norm_nonneg _, h_init.trans hδ_a⟩
                                     ⟨hδ_pos.le, hδ_a⟩).mpr h_init
      _ < ε                     := hαδ


/-! ### Two shared steps of the class `KL` characterizations -/

/-- Geometric-mean cap: a nonnegative `x` with `x ≤ A` and `x ≤ B` also has `x ≤ √(A·B)`,
since `x² ≤ A·B`.  This is what lets a class `K` bound and a decay bound be combined into
one class `KL` bound without losing either. -/
private lemma le_sqrt_mul_of_le_of_le {x A B : ℝ} (hx : 0 ≤ x) (hA : x ≤ A) (hB : x ≤ B) :
    x ≤ Real.sqrt (A * B) := by
  rw [← Real.sqrt_sq hx]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- If every trajectory starting within `c` of `x_eq` has deviation at most `g (t - t₀)`, for
one `g` tending to `0`, then trajectories from the `c`-ball have a uniform convergence time:
past the time `g` drops below `η`, so does every deviation. -/
private lemma locallyHasUniformConvergenceTime_of_tendsto_zero {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    {c : ℝ} {g : ℝ → ℝ} (hg : Tendsto g atTop (𝓝 0))
    (h_bound : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f t₀ →
      ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ g (t - t₀)) :
    LocallyHasUniformConvergenceTime f x_eq c := by
  intro η hη
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hg (Iio_mem_nhds hη))
  -- `max T 0 + 1` only makes the convergence time positive.
  refine ⟨max T 0 + 1, by linarith [le_max_right T 0], ?_⟩
  intro t₀ ht₀ φ hφ h_init t ht
  have h_elapsed : T ≤ t - t₀ := by linarith [le_max_left T 0, le_max_right T 0]
  exact (h_bound t₀ ht₀ φ hφ h_init t (by linarith [le_max_right T 0])).trans_lt
    (hT _ h_elapsed)

/-! ### UAS → ClassKL (forward direction) -/

/-- Uniform asymptotic stability yields a class `KL` bound on the deviation, on some initial
radius. -/
private lemma uniformlyAsymptoticStableNA_implies_classKL (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    (hUAS : UniformlyAsymptoticStableNA f x_eq) :
    ∃ (a : ℝ) (β : ClassKL a),
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
        IsTrajectoryNA φ f t₀ → ‖φ t₀ - x_eq‖ < a →
        ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ β.toFun (‖φ t₀ - x_eq‖) (t - t₀) := by
  obtain ⟨hUS, c, hc_pos, hconv⟩ := hUAS
  obtain ⟨a_α, b_α, α, hα_bound⟩ := (uniformlyStableNA_iff_classK f x_eq).mp hUS
  let a := min (a_α / 2) c
  have ha : 0 < a := lt_min (by linarith [α.ha]) hc_pos
  have ha_le_aα2 : a ≤ a_α / 2 := min_le_left _ _
  have ha_le_c   : a ≤ c        := min_le_right _ _
  have ha_lt_aα  : a < a_α      := ha_le_aα2.trans_lt (half_lt_self α.ha)
  -- `β := min (α_res ·) (√(α_res · * U_inv ·))` — the first factor carries the class `K`
  -- behaviour in the initial deviation, the second the decay in elapsed time.
  let α_res : ClassK a (α.toFun a) := α.restrict ha ha_lt_aα
  obtain ⟨U_inv, hU_decay⟩ :=
    exists_classLSingular_decayBound hconv α hα_bound ha ha_le_c ha_lt_aα
  refine ⟨a, ClassKL.mk_singular_cap α_res U_inv, ?_⟩
  intro t₀ ht₀ φ hφ h_init t ht
  have h_α : ‖φ t - x_eq‖ ≤ α_res.toFun ‖φ t₀ - x_eq‖ :=
    hα_bound t₀ ht₀ φ hφ (h_init.trans ha_lt_aα) t ht
  simp only [ClassKL.mk_singular_cap]
  rcases ht.eq_or_lt with rfl | ht_strict
  · simp [h_α]
  · have h_sub_ne : t - t₀ ≠ 0 := (sub_pos.mpr ht_strict).ne'
    simp only [if_neg h_sub_ne]
    have h_U : ‖φ t - x_eq‖ ≤ U_inv.toFun (t - t₀) :=
      hU_decay t₀ ht₀ φ hφ h_init t ht_strict
    exact le_min h_α (le_sqrt_mul_of_le_of_le (norm_nonneg _) h_α h_U)


/-- **Class-KL characterization of uniform asymptotic stability**: The equilibrium `x_eq`
    is uniformly asymptotically stable if and only
    if there exist a class KL function `β` on `[0, c)` and a constant `c > 0` (independent of
    `t₀`) such that every trajectory with `‖φ t₀ - x_eq‖ < c` satisfies
    `‖φ t - x_eq‖ ≤ β(‖φ t₀ - x_eq‖, t − t₀)` for all `t ≥ t₀ ≥ 0`.

    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.5. -/
@[blueprint "lem:uniformlyAsymptoticStableNA-iff-classKL"
  (title := "Class $\\mathcal{KL}$ characterization of uniform asymptotic stability")
  (latexEnv := "lemma")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{uniformly asymptotically
    stable} (\cref{def:uniformlyAsymptoticStableNA}) if and only if there exist a class
    $\mathcal{KL}$ function $\beta$ and a positive constant $c$, independent of $t_{0}$,
    such that
    \[
      \|\varphi(t) - x_{\mathrm{eq}}\| \le \beta(\|\varphi(t_{0}) - x_{\mathrm{eq}}\|,\, t - t_{0})
      \quad \forall\, t \ge t_{0} \ge 0,\; \forall\, \|\varphi(t_{0}) - x_{\mathrm{eq}}\| < c.
    \]
    This is the second half of Khalil's Lemma 4.5. -/)]
theorem uniformlyAsymptoticStableNA_iff_classKL (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) :
    UniformlyAsymptoticStableNA f x_eq ↔
    ∃ (a : ℝ) (β : ClassKL a),
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
        IsTrajectoryNA φ f t₀ → ‖φ t₀ - x_eq‖ < a →
        ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ β.toFun (‖φ t₀ - x_eq‖) (t - t₀) := by
  refine ⟨uniformlyAsymptoticStableNA_implies_classKL f x_eq, ?_⟩
  -- Backward: ∃ ClassKL bound → UAS
  rintro ⟨a, β, hβ⟩
  have ha : 0 < a := β.ha
  have ha2 : (a / 2 : ℝ) ∈ Set.Ico 0 a := ⟨by positivity, half_lt_self ha⟩
  refine ⟨?_, a / 2, half_pos ha, ?_⟩
  · -- Uniform stability: continuity of β(·, 0) at 0 gives δ(ε)
    intro ε hε
    have h_cont := β.continuous_r le_rfl 0 ⟨le_refl 0, ha⟩
    rw [Metric.continuousWithinAt_iff] at h_cont
    obtain ⟨δ, hδ_pos, hδ⟩ := h_cont ε hε
    refine ⟨min δ (a / 2), lt_min hδ_pos (half_pos ha),
            fun t₀ ht₀ φ hφ h_init t ht => ?_⟩
    have hr : ‖φ t₀ - x_eq‖ ∈ Set.Ico 0 a :=
      ⟨norm_nonneg _, h_init.trans ((min_le_right ..).trans_lt (half_lt_self ha))⟩
    have ht_sub : 0 ≤ t - t₀ := sub_nonneg.mpr ht
    have h_decay : β.toFun ‖φ t₀ - x_eq‖ (t - t₀) ≤ β.toFun ‖φ t₀ - x_eq‖ 0 :=
      β.anti_s _ hr (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht_sub) ht_sub
    have h_dist : dist (‖φ t₀ - x_eq‖) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
      exact h_init.trans_le (min_le_left ..)
    have h_small : β.toFun ‖φ t₀ - x_eq‖ 0 < ε := by
      have h_near := hδ hr h_dist
      rwa [β.map_zero 0 le_rfl, Real.dist_eq, sub_zero,
        abs_of_nonneg (β.nonneg _ hr 0 le_rfl)] at h_near
    linarith [hβ t₀ ht₀ φ hφ hr.2 t ht]
  · -- Convergence: every trajectory from the `a/2`-ball is bounded by `β(a/2, ·) → 0`
    refine locallyHasUniformConvergenceTime_of_tendsto_zero (β.tendsto_zero (a / 2) ha2)
      fun t₀ ht₀ φ hφ h_init t ht => ?_
    have hr : ‖φ t₀ - x_eq‖ ∈ Set.Ico 0 a :=
      ⟨norm_nonneg _, h_init.trans (half_lt_self ha)⟩
    calc ‖φ t - x_eq‖
        ≤ β.toFun ‖φ t₀ - x_eq‖ (t - t₀) := hβ t₀ ht₀ φ hφ hr.2 t ht
      _ ≤ β.toFun (a / 2) (t - t₀) :=
          (β.strict_mono_r _ (sub_nonneg.mpr ht) hr ha2 h_init).le





/-- **Class-KL characterization of global uniform asymptotic stability**: the equilibrium
`x_eq` is globally uniformly asymptotically stable if and only if there is a global class KL
bound `β` with `‖φ t - x_eq‖ ≤ β(‖φ t₀ - x_eq‖, t − t₀)` for **every** trajectory and every
`t ≥ t₀ ≥ 0`, with no restriction on the initial size.

The conditions on `β` are spelled out rather than packaged as `ClassKLGlobal` because the two
do not coincide: this statement needs radial unboundedness of `β(·, 0)`, which
`ClassKLGlobal` does not carry, and does not need its `nonneg` field.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.5. -/
@[blueprint "lem:globallyUniformlyAsymptoticStableNA-iff-classKL"
  (title := "Class $\\mathcal{KL}$ characterization, global case")
  (latexEnv := "lemma")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{globally uniformly
    asymptotically stable} (\cref{def:globallyUniformlyAsymptoticStableNA}) if and only if
    there is a $\beta : [0,\infty) \times [0,\infty) \to \mathbb{R}$ that is
    \begin{enumerate}
      \item zero at the origin: $\beta(0, s) = 0$ for $s \ge 0$;
      \item jointly continuous on $[0,\infty) \times [0,\infty)$;
      \item strictly increasing in $r$ for each fixed $s \ge 0$;
      \item radially unbounded: $\beta(r, 0) \to \infty$ as $r \to \infty$;
      \item antitone in $s$ for each fixed $r \ge 0$, with $\beta(r,s) \to 0$ as
        $s \to \infty$;
    \end{enumerate}
    such that
    \[
      \|\varphi(t) - x_{\mathrm{eq}}\| \le \beta(\|\varphi(t_{0}) - x_{\mathrm{eq}}\|,
             \, t - t_{0})
      \quad \forall\, t \ge t_{0} \ge 0,
    \]
    with no restriction on the initial state $\varphi(t_{0})$.

    Condition (4) is what makes the characterization \emph{global}: without it $\beta$ is
    class $\mathcal{KL}$ on a bounded radius and the statement collapses to the local one
    (\cref{lem:uniformlyAsymptoticStableNA-iff-classKL}).

    This is the global case of Khalil's Lemma 4.5. -/)]
theorem globallyUniformlyAsymptoticStableNA_iff_classKL (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) :
    GloballyUniformlyAsymptoticStableNA f x_eq ↔
    ∃ β : ℝ → ℝ → ℝ,
      (∀ s ≥ 0, β 0 s = 0) ∧
      (ContinuousOn (Function.uncurry β) (Set.Ici 0 ×ˢ Set.Ici 0)) ∧
      (∀ s ≥ 0, StrictMonoOn (fun r => β r s) (Set.Ici 0)) ∧
      (Filter.Tendsto (fun r => β r 0) Filter.atTop Filter.atTop) ∧
      (∀ r ≥ 0, AntitoneOn (fun s => β r s) (Set.Ici 0)) ∧
      (∀ r ≥ 0, Filter.Tendsto (fun s => β r s) Filter.atTop (nhds 0)) ∧
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
        IsTrajectoryNA φ f t₀ →
        ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ β (‖φ t₀ - x_eq‖) (t - t₀) := by
  constructor
  · intro hGUAS
    obtain ⟨hGUS, hGUC⟩ := hGUAS
    obtain ⟨α, h_global_α_bound⟩ := globallyUniformlyStable_implies_classKInfty f x_eq hGUS
    obtain ⟨U, hU_pos, hU_anti, hU_tendsto, hU_mono_r, hU_decay⟩ :=
      exists_decayBound_family α hGUC h_global_α_bound
    obtain ⟨β, hβ_rtendsto, hβ_at_zero, hβ_at_pos⟩ :=
      ClassKLGlobal.of_KInfty_LSingular_family α U hU_pos hU_anti hU_tendsto hU_mono_r
    refine ⟨β.toFun, β.map_zero, β.continuous, β.strict_mono_r, hβ_rtendsto, β.anti_s,
            β.tendsto_zero, ?_⟩
    intro t₀ ht₀ φ hφ t ht
    have h_α : ‖φ t - x_eq‖ ≤ α.toFun ‖φ t₀ - x_eq‖ := h_global_α_bound t₀ ht₀ φ hφ t ht
    rcases ht.eq_or_lt with rfl | ht_strict
    · simp only [sub_self]; exact h_α.trans (hβ_at_zero _ (norm_nonneg _))
    · have h_sub_pos : 0 < t - t₀ := sub_pos.mpr ht_strict
      rcases (norm_nonneg (φ t₀ - x_eq)).eq_or_lt with hr_zero | hr_pos
      · -- r = 0: state at equilibrium
        have hr_eq : ‖φ t₀ - x_eq‖ = 0 := hr_zero.symm
        have h_t_zero : ‖φ t - x_eq‖ = 0 :=
          le_antisymm (h_α.trans (by rw [hr_eq, α.map_zero])) (norm_nonneg _)
        simp only [h_t_zero, hr_eq]; linarith [β.map_zero (t - t₀) h_sub_pos.le]
      · -- r > 0: geometric mean bound chains to β
        have h_U : ‖φ t - x_eq‖ ≤ U (‖φ t₀ - x_eq‖ + 1) (t - t₀) :=
          hU_decay _ (by positivity) t₀ ht₀ φ hφ (by linarith) t ht_strict
        exact (le_min h_α (le_sqrt_mul_of_le_of_le (norm_nonneg _) h_α h_U)).trans
          (hβ_at_pos _ (norm_nonneg _) _ h_sub_pos)
  · -- Backward: ∃ Global ClassKL bound → GUAS
    rintro ⟨β, hβ_zero, hβ_cont, hβ_mono, hβ_rtendsto, hβ_anti, hβ_stendsto, hβ_bound⟩
    let α : ClassKInfty := ClassKInfty.of_strictMono (fun r => β r 0)
      (hβ_zero 0 le_rfl)
      ((hβ_cont.comp (continuousOn_id.prodMk continuousOn_const)
        (fun r hr => Set.mk_mem_prod hr (Set.mem_Ici.mpr le_rfl))).congr (fun r _ => rfl))
      (hβ_mono 0 le_rfl) hβ_rtendsto
    refine ⟨?_, ?_⟩ -- Split into Uniform Stability and Global Uniform Convergence
    · -- Global Uniform Stability (∃ δ, ...)
      -- Take `δ := α⁻¹`, where `α := β(·, 0)` is class `K∞`.
      refine ⟨α.invFun, ?_, α.symm.tendsto_atTop, ?_⟩
      · -- Prove δ(ε) > 0 for ε > 0
        intro ε hε
        exact (α.symm.pos_iff hε.le).mpr hε
      · -- Prove the trajectory stays within ε
        intro ε hε t₀ ht₀ φ hφ h_init t ht
        have ht_sub : 0 ≤ t - t₀ := sub_nonneg.mpr ht
        -- Decay over time: β(‖x₀‖, t - t₀) ≤ β(‖x₀‖, 0)
        have h_decay : β ‖φ t₀ - x_eq‖ (t - t₀) ≤ β ‖φ t₀ - x_eq‖ 0 :=
          hβ_anti ‖φ t₀ - x_eq‖ (Set.mem_Ici.mpr (norm_nonneg _))
            (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht_sub) ht_sub
        calc ‖φ t - x_eq‖
          _ ≤ β ‖φ t₀ - x_eq‖ (t - t₀) := hβ_bound t₀ ht₀ φ hφ t ht
          _ ≤ β ‖φ t₀ - x_eq‖ 0        := h_decay
          _ = α.toFun ‖φ t₀ - x_eq‖    := rfl
          _ < α.toFun (α.invFun ε)      :=
              (α.strict_mono_iff (Set.mem_Ici.mpr (norm_nonneg _))
                (α.symm.maps_to (Set.mem_Ici.mpr hε.le))).mpr h_init
          _ = ε                         := α.right_inv_apply (Set.mem_Ici.mpr hε.le)
    · -- Global Uniform Convergence: from the `r`-ball, deviations are bounded by `β(r, ·) → 0`
      intro r hr_pos
      have hr_ici : r ∈ Set.Ici 0 := Set.mem_Ici.mpr hr_pos.le
      refine locallyHasUniformConvergenceTime_of_tendsto_zero (hβ_stendsto r hr_ici)
        fun t₀ ht₀ φ hφ h_init t ht => ?_
      have h_init_ici : ‖φ t₀ - x_eq‖ ∈ Set.Ici 0 := Set.mem_Ici.mpr (norm_nonneg _)
      calc ‖φ t - x_eq‖
          ≤ β ‖φ t₀ - x_eq‖ (t - t₀) := hβ_bound t₀ ht₀ φ hφ t ht
        _ ≤ β r (t - t₀) := (hβ_mono (t - t₀) (sub_nonneg.mpr ht) h_init_ici hr_ici h_init).le

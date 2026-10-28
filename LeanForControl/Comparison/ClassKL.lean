import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Exp

import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKInfty
import LeanForControl.Comparison.ClassL

import Architect

open Set Filter Topology MeasureTheory intervalIntegral



-- ─── Class KL ─────────────────────────────────────────────────────────────────

/-! ### Class KL

A *class KL* function `β(r, s)` is class K in `r` for each fixed `s`, and for each
fixed `r` it is non-increasing in `s` and tends to zero as `s → ∞`.
It arises as the bound in asymptotic stability estimates: `‖x(t)‖ ≤ β(‖x₀‖, t)`. -/

/-- A class KL function `β : [0,a) × [0,∞) → ℝ`:
    class K in the first argument, antitone and tending to 0 in the second. 
    
    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.3. Differences:
    - Khalil says `β(·, s)` is class `K`; here `map_zero`, `continuous` and `strict_mono_r` spell
      that out, so no `ClassK` instance is required for each `s`.
    - Continuity is joint on `[0,a) × [0,∞)`, matching Khalil's `β` continuous.
    - Khalil asks `β(r, ·)` to be decreasing; here it is only non-increasing (`anti_s`).  Nothing
      is lost: `β(r, s) + α(r) e^{-s}`, with `α` class `K`, is a strictly decreasing majorant. -/
@[blueprint "def:isClassKL"
  (title := "Class $\\mathcal{KL}$ function")
  (statement := /-- A \emph{class $\mathcal{KL}$} function on $[0,a) \times [0,\infty)$
    is continuous, class $\mathcal{K}$ in the first argument, and for each fixed $r > 0$
    is non-increasing and tends to $0$ as $s \to \infty$. It arises as the bound
    $\|x(t)\| \le \beta(\|x_0\|, t)$ in asymptotic stability estimates.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.3.  Difference: Khalil says
    $\beta(\cdot, s)$ is class $\mathcal{K}$; here that is spelled out as separate fields, so no
    class $\mathcal{K}$ instance is required for each $s$.  Khalil also asks $\beta(r, \cdot)$ to
    be decreasing; non-increasing loses nothing, since $\beta(r, s) + \alpha(r) e^{-s}$, with
    $\alpha$ class $\mathcal{K}$, is a strictly decreasing majorant.
  -/)]
structure ClassKL (a : ℝ) where
  ha : 0 < a
  /-- The forward function of a class KL function. -/
  toFun : ℝ → ℝ → ℝ
  map_zero      : ∀ s ≥ 0, toFun 0 s = 0
  continuous    : ContinuousOn (Function.uncurry toFun) (Set.Ico 0 a ×ˢ Set.Ici 0)
  strict_mono_r : ∀ s ≥ 0, StrictMonoOn (fun r => toFun r s) (Set.Ico 0 a)
  nonneg        : ∀ r ∈ Set.Ico 0 a, ∀ s ≥ 0, 0 ≤ toFun r s
  anti_s        : ∀ r ∈ Set.Ico 0 a, AntitoneOn (fun s => toFun r s) (Set.Ici 0)
  tendsto_zero  : ∀ r ∈ Set.Ico 0 a,
      Filter.Tendsto (fun s => toFun r s) Filter.atTop (nhds 0)


-- ─── ClassKL Basic API ────────────────────────────────────────────────────────

@[simp]
theorem ClassKL.map_zero_r {a : ℝ} (β : ClassKL a) {s : ℝ} (hs : 0 ≤ s) :
    β.toFun 0 s = 0 :=
  β.map_zero s hs

/-- Restrict a class KL function on `[0, a)` to a smaller radius `[0, a')`. -/
@[blueprint "lem:classKL-restrict"
  (title := "Restriction of a class $\\mathcal{KL}$ function")
  (statement := /-- If $\beta$ is class $\mathcal{KL}$ on $[0, a) \times [0, \infty)$ and
    $0 < a' \le a$, then $\beta$ is class $\mathcal{KL}$ on $[0, a') \times [0, \infty)$. -/)]
def ClassKL.restrict {a : ℝ} (β : ClassKL a) {a' : ℝ} (ha' : 0 < a') (h : a' ≤ a) :
    ClassKL a' where
  ha                 := ha'
  toFun              := β.toFun
  map_zero           := β.map_zero
  continuous         := β.continuous.mono
    (Set.prod_mono (Set.Ico_subset_Ico_right h) subset_rfl)
  strict_mono_r s hs := (β.strict_mono_r s hs).mono (Set.Ico_subset_Ico_right h)
  nonneg r hr        := β.nonneg r (Set.Ico_subset_Ico_right h hr)
  anti_s r hr        := β.anti_s r (Set.Ico_subset_Ico_right h hr)
  tendsto_zero r hr  := β.tendsto_zero r (Set.Ico_subset_Ico_right h hr)

@[simp]
theorem ClassKL.tendsto_zero_s {a : ℝ} (β : ClassKL a) {r : ℝ} (hr : r ∈ Set.Ico 0 a) :
    Filter.Tendsto (fun s => β.toFun r s) Filter.atTop (nhds 0) :=
  β.tendsto_zero r hr

@[gcongr]
theorem ClassKL.mono_r {a : ℝ} (β : ClassKL a) {r₁ r₂ : ℝ} {s : ℝ}
    (hr₁ : r₁ ∈ Set.Ico 0 a) (hr₂ : r₂ ∈ Set.Ico 0 a) (hs : 0 ≤ s)
    (h : r₁ ≤ r₂) : β.toFun r₁ s ≤ β.toFun r₂ s :=
  (β.strict_mono_r s hs).monotoneOn hr₁ hr₂ h

@[gcongr]
theorem ClassKL.anti_s_mono {a : ℝ} (β : ClassKL a) {r : ℝ} {s₁ s₂ : ℝ}
    (hr : r ∈ Set.Ico 0 a) (hs₁ : s₁ ∈ Set.Ici 0) (hs₂ : s₂ ∈ Set.Ici 0)
    (h : s₁ ≤ s₂) : β.toFun r s₂ ≤ β.toFun r s₁ :=
  β.anti_s r hr hs₁ hs₂ h

/-- Product of a class K function and a class L function is class KL.
    `β(r, s) = α(r) * γ(s)`. -/
@[blueprint "lem:classKL-mk-mul"
  (title := "Class $\\mathcal{KL}$ from a class $\\mathcal{K}$ times a class $\\mathcal{L}$")
  (statement := /-- If $\alpha$ is class $\mathcal{K}$ on $[0,a)$ and $\gamma$ is class
    $\mathcal{L}$, then $\beta(r, s) := \alpha(r)\gamma(s)$ is class $\mathcal{KL}$ on
    $[0,a)$. -/)]
noncomputable def ClassKL.mk_mul {a b : ℝ} (α : ClassK a b) (γ : ClassL) : ClassKL a where
  ha := α.ha
  toFun r s := α.toFun r * γ.toFun s
  map_zero s _ := by simp [α.map_zero]
  continuous := ContinuousOn.mul
    (α.continuous.comp continuous_fst.continuousOn (fun p hp => hp.1))
    (γ.continuous.comp continuous_snd.continuousOn (fun p hp => hp.2))
  strict_mono_r s hs x hx y hy hxy :=
    -- Strict monotonicity is preserved because γ(s) is strictly positive
    mul_lt_mul_of_pos_right (α.strict_mono hx hy hxy) (γ.pos s hs)
  nonneg r hr s hs :=
    mul_nonneg (α.maps_to hr).1 (γ.pos s hs).le
  anti_s r hr s₁ hs₁ s₂ hs₂ hs :=
    -- Reverses direction properly because α(r) ≥ 0
    mul_le_mul_of_nonneg_left (γ.anti.antitoneOn hs₁ hs₂ hs) (α.maps_to hr).1
  tendsto_zero r hr := by
    -- The limit as s → ∞ of α(r) * γ(s) is α(r) * 0 = 0
    simpa only [mul_zero] using Filter.Tendsto.const_mul (α.toFun r) γ.tendsto_zero


/-- Pointwise minimum of a class KL function and a class K function of the radius alone is
class KL: `min(β(r,s), α(r))`.

Capping a class KL bound by a function of the initial condition alone preserves the class, and
lets a bound obtained only as a *majorant* — from a smoothing construction, say — be pulled back
inside a prescribed range. The bounded-domain twin of `ClassKLGlobal.min_KInfty`. -/
@[blueprint "lem:classKL-min-classK"
  (title := "Capping a class $\\mathcal{KL}$ function by a class $\\mathcal{K}$ function")
  (statement := /-- If $\beta$ is class $\mathcal{KL}$ on $[0,a)$ and $\alpha$ is class
    $\mathcal{K}$ on $[0,a)$, then $(r, s) \mapsto \min\bigl(\beta(r,s), \alpha(r)\bigr)$ is
    class $\mathcal{KL}$ on $[0,a)$.

    Capping a class $\mathcal{KL}$ bound by a function of the initial condition alone preserves
    the class.  Its use is to recover a range condition: a bound obtained only as a majorant —
    from a smoothing construction, say — carries no upper control, and capping restores it
    without disturbing the bound, since the minimum still dominates whatever $\beta$
    dominated. -/)
  (proof := /-- Each field is inherited.  The minimum of two strictly increasing functions of
    $r$ is strictly increasing; $\alpha$ does not depend on $s$, so antitonicity in $s$ survives
    the minimum; and $\min(\beta(r,s), \alpha(r)) \to \min(0, \alpha(r)) = 0$ as
    $s \to \infty$ because $\alpha \ge 0$. -/)]
noncomputable def ClassKL.min_classK {a b : ℝ} (β : ClassKL a) (α : ClassK a b) : ClassKL a where
  ha            := β.ha
  toFun r s     := min (β.toFun r s) (α.toFun r)
  map_zero s hs := by rw [β.map_zero s hs, α.map_zero, min_self]
  continuous    := β.continuous.inf
    (α.continuous.comp continuousOn_fst (fun p hp => hp.1))
  strict_mono_r s hs x hx y hy hxy := by
    apply lt_min
    · exact (min_le_left _ _).trans_lt (β.strict_mono_r s hs hx hy hxy)
    · exact (min_le_right _ _).trans_lt (α.strict_mono hx hy hxy)
  nonneg r hr s hs := le_min (β.nonneg r hr s hs) (α.maps_to hr).1
  anti_s r hr s₁ hs₁ s₂ hs₂ hs := min_le_min (β.anti_s r hr hs₁ hs₂ hs) le_rfl
  tendsto_zero r hr := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (β.tendsto_zero r hr)
    · filter_upwards [eventually_ge_atTop 0] with s hs
      exact le_min (β.nonneg r hr s hs) (α.maps_to hr).1
    · filter_upwards [] with s; exact min_le_left _ _

/-- If `U → 0` at `+∞`, then so does `s ↦ min c (√(c * U s))` for any `c ≥ 0`.  The `min` keeps
    the bound at most `c`; the square root is what makes it vanish. -/
@[blueprint "lem:tendstoMinSqrtMulZero"
  (title := "Decay of a geometric-mean cap")
  (latexEnv := "lemma")
  (statement := /-- Let $c \ge 0$ and let $U : \mathbb{R} \to \mathbb{R}$ satisfy
    $U(s) \to 0$ as $s \to +\infty$.  Then
    $\min\bigl(c, \sqrt{c\,U(s)}\bigr) \to 0$ as $s \to +\infty$. -/)]
lemma tendsto_min_sqrt_mul_zero {c : ℝ} (hc : 0 ≤ c)
    {U : ℝ → ℝ} (hU : Filter.Tendsto U Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun s => min c (Real.sqrt (c * U s))) Filter.atTop (nhds 0) := by
  refine squeeze_zero
    (fun s => le_min hc (Real.sqrt_nonneg _))
    (fun s => min_le_right _ _)
    ?_
  have h_mul : Filter.Tendsto (fun s => c * U s) Filter.atTop (nhds 0) := by
    simpa using Filter.Tendsto.const_mul c hU
  simpa [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp h_mul

/-- If `0 ≤ x ≤ u` then `x ≤ √(x u)`, so `min x (√(x u)) = x`: once `U` dominates `α`, the
    geometric-mean cap is inactive. -/
private lemma min_sqrt_mul_eq_left {x u : ℝ} (hx : 0 ≤ x) (hxu : x ≤ u) :
    min x (Real.sqrt (x * u)) = x := by
  apply min_eq_left
  -- `x² ≤ x u`, and taking square roots gives `x ≤ √(x u)`.
  have h_sq_le : x * x ≤ x * u := mul_le_mul_of_nonneg_left hxu hx
  calc x = Real.sqrt (x * x) := (Real.sqrt_mul_self hx).symm
    _ ≤ Real.sqrt (x * u) := Real.sqrt_le_sqrt h_sq_le

/-- The function behind `ClassKL.mk_singular_cap`: `α(r)` at `s = 0`, and
    `min(α(r), √(α(r) U(s)))` for `s ≠ 0`.  Definitionally equal to that structure's `toFun`. -/
private noncomputable def singularCap {a b : ℝ} (α : ClassK a b) (U : ClassLSingular)
    (r s : ℝ) : ℝ :=
  if s = 0 then α.toFun r else min (α.toFun r) (Real.sqrt (α.toFun r * U.toFun s))

/-- Continuity of the singular cap at a point `(r₀, s₀)` with `s₀ > 0`: nearby points also have
    `s > 0`, where the cap is the continuous `min(α(r), √(α(r) U(s)))`. -/
private lemma continuousWithinAt_singularCap_of_pos {a b : ℝ} (α : ClassK a b)
    (U : ClassLSingular) {r₀ s₀ : ℝ} (hr₀ : r₀ ∈ Ico 0 a) (hs₀ : 0 < s₀) :
    ContinuousWithinAt (Function.uncurry (singularCap α U)) (Ico 0 a ×ˢ Ici 0) (r₀, s₀) := by
  -- Step 1. The `min` branch is continuous at `(r₀, s₀)`, as a composition of continuous maps.
  have h_alpha : ContinuousWithinAt (fun p : ℝ × ℝ => α.toFun p.1)
      (Ico 0 a ×ˢ Ici 0) (r₀, s₀) :=
    (α.continuous r₀ hr₀).comp continuous_fst.continuousWithinAt (fun _ hp => hp.1)
  -- `U` is continuous on `(0, ∞)`, an open set containing `s₀`.
  have h_U : ContinuousWithinAt (fun p : ℝ × ℝ => U.toFun p.2) (Ico 0 a ×ˢ Ici 0) (r₀, s₀) :=
    ((U.continuous s₀ hs₀).continuousAt (Ioi_mem_nhds hs₀)).comp_continuousWithinAt
      continuous_snd.continuousWithinAt
  have h_sqrt := Real.continuous_sqrt.continuousAt.comp_continuousWithinAt (h_alpha.mul h_U)
  have h_min : ContinuousWithinAt
      (fun p : ℝ × ℝ => min (α.toFun p.1) (Real.sqrt (α.toFun p.1 * U.toFun p.2)))
      (Ico 0 a ×ˢ Ici 0) (r₀, s₀) :=
    continuous_min.continuousAt.tendsto.comp (h_alpha.tendsto.prodMk_nhds h_sqrt)
  -- Step 2. Near `(r₀, s₀)` we have `s > 0`, so the cap agrees with the `min` branch.
  have h_eq : Function.uncurry (singularCap α U) =ᶠ[𝓝[Ico 0 a ×ˢ Ici 0] (r₀, s₀)]
      fun p => min (α.toFun p.1) (Real.sqrt (α.toFun p.1 * U.toFun p.2)) := by
    have h_snd : Tendsto (fun p : ℝ × ℝ => p.2) (𝓝[Ico 0 a ×ˢ Ici 0] (r₀, s₀)) (𝓝 s₀) :=
      continuous_snd.continuousWithinAt
    filter_upwards [h_snd.eventually (Ioi_mem_nhds hs₀)] with p hp_pos
    exact if_neg hp_pos.ne'
  exact h_min.congr_of_eventuallyEq h_eq (if_neg hs₀.ne')

/-- Continuity of the singular cap at a point `(r₀, 0)` of the edge `s = 0`.

    Pick a buffer radius `r₁ ∈ (r₀, a)`.  Since `U(s) → ∞` as `s → 0⁺`, near `(r₀, 0)` we have
    `α(r) < α(r₁) < U(s)`, so the cap is inactive and the function is just the continuous
    `α(r)`.  This covers the corner `r₀ = 0` as well. -/
private lemma continuousWithinAt_singularCap_of_zero {a b : ℝ} (α : ClassK a b)
    (U : ClassLSingular) {r₀ : ℝ} (hr₀ : r₀ ∈ Ico 0 a) :
    ContinuousWithinAt (Function.uncurry (singularCap α U)) (Ico 0 a ×ˢ Ici 0) (r₀, 0) := by
  -- Step 1. The proxy `α(r)` is continuous at `(r₀, 0)`.
  have h_alpha : ContinuousWithinAt (fun p : ℝ × ℝ => α.toFun p.1)
      (Ico 0 a ×ˢ Ici 0) (r₀, 0) :=
    (α.continuous r₀ hr₀).comp continuous_fst.continuousWithinAt (fun _ hp => hp.1)
  -- Step 2. Pick a buffer radius `r₁ ∈ (r₀, a)`.
  obtain ⟨r₁, hr₀_lt_r₁, hr₁_lt_a⟩ := exists_between hr₀.2
  have hr₁ : r₁ ∈ Ico 0 a := ⟨hr₀.1.trans hr₀_lt_r₁.le, hr₁_lt_a⟩
  -- Step 3. `U(s) → ∞` as `s → 0⁺`, so `U(s) > α(r₁)` for small `s > 0`; restated on the full
  -- neighbourhood `𝓝 0`, with `0 < s` as a hypothesis.
  have h_U_large : ∀ᶠ s in 𝓝 0, 0 < s → α.toFun r₁ < U.toFun s :=
    eventually_nhdsWithin_iff.mp (U.tendsto_top (eventually_gt_atTop (α.toFun r₁)))
  -- Step 4. Near `(r₀, 0)` the cap agrees with `α(r)`.
  have h_eq : Function.uncurry (singularCap α U) =ᶠ[𝓝[Ico 0 a ×ˢ Ici 0] (r₀, 0)]
      fun p => α.toFun p.1 := by
    -- Pull `r < r₁` and `h_U_large` back along `fst`/`snd` to a neighbourhood of `(r₀, 0)`.
    filter_upwards [
      continuous_fst.continuousWithinAt.eventually (Iio_mem_nhds hr₀_lt_r₁),
      continuous_snd.continuousWithinAt.eventually h_U_large,
      self_mem_nhdsWithin
    ] with ⟨r, s⟩ (hr_lt : r < r₁) hs_U ⟨hr, hs⟩
    simp only [Function.uncurry_apply_pair, singularCap]
    split_ifs with hs_zero
    · -- Case `s = 0`: the cap is `α(r)` by definition.
      rfl
    · -- Case `s > 0`: `α(r) < α(r₁) < U(s)`, so the cap is inactive.
      have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs_zero)
      have h_alpha_le_U : α.toFun r ≤ U.toFun s :=
        (α.strict_mono hr hr₁ hr_lt).le.trans (hs_U hs_pos).le
      exact min_sqrt_mul_eq_left (α.maps_to hr).1 h_alpha_le_U
  exact h_alpha.congr_of_eventuallyEq h_eq (if_pos rfl)

/-- Sontag-style KL construction from a class K spatial bound and a singular class L time decay.
    `β(r, 0) = α(r)` and `β(r, s) = min(α(r), √(α(r) * U(s)))` for `s > 0`. -/
@[blueprint "lem:classKL-mk-singular-cap"
  (title := "Class $\\mathcal{KL}$ from a singular class $\\mathcal{L}$ cap")
  (statement := /-- Let $\alpha$ be class $\mathcal{K}$ on $[0,a)$ and let $U$ be a singular
    class $\mathcal{L}$ function (positive, antitone, $U(s) \to 0$ as $s \to \infty$ and
    $U(s) \to \infty$ as $s \to 0^{+}$).  Then
    \[
      \beta(r, s) := \begin{cases}
        \alpha(r) & s = 0, \\
        \min\bigl(\alpha(r), \sqrt{\alpha(r)U(s)}\bigr) & s > 0,
      \end{cases}
    \]
    is class $\mathcal{KL}$ on $[0,a)$. -/)
  (proof := /-- Every field but continuity is immediate from the corresponding property of
    $\alpha$ and $U$, the decay in $s$ being \cref{lem:tendstoMinSqrtMulZero}.  Continuity is
    checked in two regimes.  For $s > 0$ the $\min$ branch is a composition of continuous
    maps.  At $(r, 0)$, pick a buffer radius $r_1 \in (r, a)$; since $U(s) \to \infty$ as
    $s \to 0^{+}$, on a neighbourhood we have $\alpha(r_1) < U(s)$, hence
    $\alpha(r') \le U(s)$ and so $\alpha(r') \le \sqrt{\alpha(r')U(s)}$ — the minimum is
    locally just $\alpha$, which is continuous. -/)]
noncomputable def ClassKL.mk_singular_cap {a b : ℝ} (α : ClassK a b) (U : ClassLSingular) :
    ClassKL a where
  ha := α.ha

  toFun r s := if s = 0 then α.toFun r
               else min (α.toFun r) (Real.sqrt (α.toFun r * U.toFun s))

  map_zero s hs := by
    split_ifs with h0
    · exact α.map_zero
    · simp [α.map_zero]

  nonneg r hr s hs := by
    split_ifs with h0
    · exact (α.maps_to hr).1
    · exact le_min (α.maps_to hr).1 (Real.sqrt_nonneg _)

  strict_mono_r s hs := by
    split_ifs with h0
    · -- s = 0: β(r, 0) = α(r), strictly mono by hypothesis
      exact α.strict_mono
    · -- s > 0: both α(r) and √(α(r)*U(s)) are strictly increasing in r
      intro r₁ hr₁ r₂ hr₂ h_lt
      have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm h0)
      have h_α_lt : α.toFun r₁ < α.toFun r₂ := α.strict_mono hr₁ hr₂ h_lt
      exact min_lt_min h_α_lt (Real.sqrt_lt_sqrt
        (mul_nonneg (α.maps_to hr₁).1 (U.pos s hs_pos).le)
        (mul_lt_mul_of_pos_right h_α_lt (U.pos s hs_pos)))

  anti_s r hr s₁ hs₁ s₂ hs₂ hle := by
    rcases (Set.mem_Ici.mp hs₁).eq_or_lt with rfl | hs₁pos
    · rcases (Set.mem_Ici.mp hs₂).eq_or_lt with rfl | hs₂pos
      · exact le_rfl
      · simp only [if_true, if_neg hs₂pos.ne']
        exact min_le_left _ _
    · rcases (Set.mem_Ici.mp hs₂).eq_or_lt with rfl | hs₂pos
      · linarith
      · simp only [if_neg hs₁pos.ne', if_neg hs₂pos.ne']
        gcongr
        · exact (α.maps_to hr).1
        · exact U.anti (Set.mem_Ioi.mpr hs₁pos) (Set.mem_Ioi.mpr hs₂pos) hle

  tendsto_zero r hr := by
    have h_α : 0 ≤ α.toFun r := (α.maps_to hr).1
    apply (tendsto_min_sqrt_mul_zero h_α U.tendsto_zero).congr'
    filter_upwards [Filter.eventually_ne_atTop 0] with s hs
    exact (if_neg hs).symm

  continuous := by
    -- Two regimes, according to whether (r₀, s₀) lies on the edge s = 0:
    -- • s₀ = 0: U(s) → ∞ as s → 0⁺ makes the cap inactive nearby, so β agrees with α(r).
    -- • s₀ > 0: nearby s > 0 too, where β = min(α(r), √(α(r) U(s))) is a composition of
    --   continuous functions.
    rintro ⟨r₀, s₀⟩ ⟨hr₀, hs₀⟩
    rcases (mem_Ici.mp hs₀).eq_or_lt with rfl | hs₀_pos
    · -- Case s₀ = 0: on the edge.
      exact continuousWithinAt_singularCap_of_zero α U hr₀
    · -- Case s₀ > 0: off the edge.
      exact continuousWithinAt_singularCap_of_pos α U hr₀ hs₀_pos




/-- A class KL function is continuous in `r` for each fixed `s ≥ 0`: the section of the joint
    continuity in the `continuous` field. -/
@[fun_prop]
theorem ClassKL.continuous_r {a : ℝ} (β : ClassKL a) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (fun r => β.toFun r s) (Set.Ico 0 a) :=
  (β.continuous.comp (continuousOn_id.prodMk (continuousOn_const))
    (fun _ hr => Set.mk_mem_prod hr hs)).congr (fun _ _ => rfl)


/-- If `f s → 0` as `s → ∞` and eventually `f s ∈ S`, and `α` is continuous at `0` within `S`
with `α 0 = 0`, then `α (f s) → 0`.  This is the `tendsto_zero` field of every
post-composition `α ∘ β` below, with `S` the domain of `α` and `f = β(r, ·)`. -/
private lemma tendsto_zero_comp_of_continuousWithinAt {α f : ℝ → ℝ} {S : Set ℝ}
    (hα_cont : ContinuousWithinAt α S 0) (hα_zero : α 0 = 0)
    (hf : Tendsto f atTop (𝓝 0)) (hf_mem : ∀ᶠ s in atTop, f s ∈ S) :
    Tendsto (fun s => α (f s)) atTop (𝓝 0) := by
  have hf_within : Tendsto f atTop (𝓝[S] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f hf hf_mem
  have h_comp := hα_cont.tendsto.comp hf_within
  rwa [hα_zero] at h_comp

/-- Post-composing a class KL function with a class K∞ function yields class KL.
    (Applies `α` to the output of `β`.) 
    
    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.2, fifth bullet, with `α₁` of class
    `K∞` — no range hypothesis is then needed. -/
@[blueprint "lem:classKL-comp-left-KInfty"
  (title := "Post-composition with a class $\\mathcal{K}_{\\infty}$ function")
  (statement := /-- If $\beta$ is class $\mathcal{KL}$ on $[0,a)$ and $\alpha$ is class
    $\mathcal{K}_{\infty}$, then $(r, s) \mapsto \alpha(\beta(r, s))$ is class $\mathcal{KL}$
    on $[0,a)$.  This is \cref{lem:classKL-comp-left-K} with the range hypothesis discharged by
    $\alpha$ being defined on all of $[0,\infty)$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.2, fifth bullet, with $\alpha_1$
    of class $\mathcal{K}_{\infty}$; no range hypothesis is then needed.
  -/)]
def ClassKL.comp_left_KInfty {a : ℝ} (β : ClassKL a) (α : ClassKInfty) : ClassKL a where
  ha            := β.ha
  toFun r s     := α.toFun (β.toFun r s)
  map_zero s hs := by simp only [β.map_zero s hs, α.map_zero]

  continuous s hs := by
    apply
    α.continuous.comp (β.continuous) (fun p hp => β.nonneg p.1 hp.1 p.2 hp.2)
    exact hs
  strict_mono_r s hs x hx y hy hxy :=
    α.strict_mono (β.nonneg x hx s hs) (β.nonneg y hy s hs)
      (β.strict_mono_r s hs hx hy hxy)
  nonneg r hr s hs := α.maps_to (β.nonneg r hr s hs)
  anti_s r hr s₁ hs₁ s₂ hs₂ hs :=
    α.strict_mono.monotoneOn (β.nonneg r hr s₂ hs₂) (β.nonneg r hr s₁ hs₁)
      (β.anti_s r hr hs₁ hs₂ hs)
  tendsto_zero r hr := by
    have hβ_ici : ∀ᶠ s in Filter.atTop, β.toFun r s ∈ Set.Ici 0 := by
      filter_upwards [eventually_ge_atTop 0] with s hs
      exact β.nonneg r hr s hs
    exact tendsto_zero_comp_of_continuousWithinAt
      (α.continuous.continuousWithinAt self_mem_Ici) α.map_zero (β.tendsto_zero r hr) hβ_ici

/-- Post-composing a class KL function with a class K function yields class KL,
    provided the range of `β` is strictly within the domain of `α`. 
    
    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.2, fifth bullet (the outer `α₁`).
    The `h_range` hypothesis is additional: `α₁` is only defined on `[0,b)`, so `β`'s values must
    land there. Khalil leaves that implicit. -/
@[blueprint "lem:classKL-comp-left-K"
  (title := "Post-composition with a class $\\mathcal{K}$ function")
  (statement := /-- Let $\beta$ be class $\mathcal{KL}$ on $[0,a)$ and $\alpha$ be class
    $\mathcal{K}$ on $[0,b)$, and suppose $\beta(r, s) < b$ for every $r \in [0,a)$ and
    $s \ge 0$.  Then $(r, s) \mapsto \alpha(\beta(r, s))$ is class $\mathcal{KL}$ on
    $[0,a)$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.2, fifth bullet (the outer
    $\alpha_1$).  The range hypothesis is additional: $\alpha_1$ is defined only on $[0,b)$, so
    $\beta$'s values must land there, which Khalil leaves implicit.
  -/)]
def ClassKL.comp_left_K {a b c : ℝ} (β : ClassKL a) (α : ClassK b c)
    (h_range : ∀ r ∈ Set.Ico 0 a, ∀ s ≥ 0, β.toFun r s < b) : ClassKL a where
  ha            := β.ha
  toFun r s     := α.toFun (β.toFun r s)
  map_zero s hs := by simp only [β.map_zero s hs, α.map_zero]

  continuous := by
    apply α.continuous.comp β.continuous
    intro p hp
    exact ⟨β.nonneg p.1 hp.1 p.2 hp.2, h_range p.1 hp.1 p.2 hp.2⟩

  strict_mono_r s hs x hx y hy hxy :=
    α.strict_mono ⟨β.nonneg x hx s hs, h_range x hx s hs⟩
                  ⟨β.nonneg y hy s hs, h_range y hy s hs⟩
                  (β.strict_mono_r s hs hx hy hxy)

  nonneg r hr s hs := (α.maps_to ⟨β.nonneg r hr s hs, h_range r hr s hs⟩).1

  anti_s r hr s₁ hs₁ s₂ hs₂ hs :=
    α.strict_mono.monotoneOn ⟨β.nonneg r hr s₂ hs₂, h_range r hr s₂ hs₂⟩
                             ⟨β.nonneg r hr s₁ hs₁, h_range r hr s₁ hs₁⟩
                             (β.anti_s r hr hs₁ hs₂ hs)

  tendsto_zero r hr := by
    have hβ_ico : ∀ᶠ s in Filter.atTop, β.toFun r s ∈ Set.Ico 0 b := by
      filter_upwards [eventually_ge_atTop 0] with s hs
      exact ⟨β.nonneg r hr s hs, h_range r hr s hs⟩
    exact tendsto_zero_comp_of_continuousWithinAt
      (α.continuous.continuousWithinAt ⟨le_refl 0, α.ha⟩) α.map_zero (β.tendsto_zero r hr) hβ_ico



/-- Pre-composing a class KL function with a class K function yields class KL.
    (Applies `α` to the first argument of `β`.) 
    
    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.2, fifth bullet (the inner `α₂`). -/
@[blueprint "lem:classKL-comp-right"
  (title := "Pre-composition in the radius argument")
  (statement := /-- If $\beta$ is class $\mathcal{KL}$ on $[0,b)$ and $\alpha$ is class
    $\mathcal{K}$ on $[0,a) \to [0,b)$, then $(r, s) \mapsto \beta(\alpha(r), s)$ is class
    $\mathcal{KL}$ on $[0,a)$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.2, fifth bullet (the inner
    $\alpha_2$).
  -/)]
def ClassKL.comp_right {a b : ℝ} (β : ClassKL b) (α : ClassK a b) : ClassKL a where
  ha            := α.ha
  toFun r s     := β.toFun (α.toFun r) s
  map_zero s hs := by simp only [α.map_zero, β.map_zero s hs]
  continuous s hs  := by
    apply β.continuous.comp
      ((α.continuous.comp continuousOn_fst (fun p hp => hp.1)).prodMk continuousOn_snd)
      (fun p hp => ⟨α.maps_to hp.1, hp.2⟩)
    exact hs

  strict_mono_r s hs x hx y hy hxy :=
    β.strict_mono_r s hs (α.maps_to hx) (α.maps_to hy) (α.strict_mono hx hy hxy)
  nonneg r hr s hs   := β.nonneg (α.toFun r) (α.maps_to hr) s hs
  anti_s r hr        := β.anti_s (α.toFun r) (α.maps_to hr)
  tendsto_zero r hr  := β.tendsto_zero (α.toFun r) (α.maps_to hr)




/-! ### Bookkeeping lemmas -/

/-- If `σ(y, 0) ≤ y`, a class `KL` function maps `[0, d)` into itself at every time `s ≥ 0`:
by decay in `s`, `0 ≤ σ(y, s) ≤ σ(y, 0) ≤ y < d`. -/
theorem ClassKL.toFun_mem_Ico {d : ℝ} (σ : ClassKL d)
    (hσ_zero : ∀ y ∈ Set.Ico 0 d, σ.toFun y 0 ≤ y) {y s : ℝ} (hy : y ∈ Set.Ico 0 d)
    (hs : 0 ≤ s) :
    σ.toFun y s ∈ Set.Ico 0 d := by
  have h_decay : σ.toFun y s ≤ σ.toFun y 0 :=
    σ.anti_s y hy (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
  exact ⟨σ.nonneg y hy s hs, (h_decay.trans (hσ_zero y hy)).trans_lt hy.2⟩

/-- **Sandwiching a class `KL` function.**  Given `σ : ClassKL d` with `σ(y, 0) ≤ y`, a class `K`
function `α₁` whose range `[0, b₁)` contains `[0, d)`, and a class `K` function `α₂` with
`α₂(c) = d`, the composite `β(ρ, s) = α₁⁻¹(σ(α₂(ρ), s))` is class `KL` on `[0, c)`.  This is how
a class `KL` bound on a Lyapunov function becomes one on the state. -/
theorem ClassKL.exists_comp_sandwich {r b₁ b₂ c d : ℝ}
    (α₁ : ClassK r b₁) (α₂ : ClassK r b₂) {σ : ClassKL d}
    (hσ_zero : ∀ y ∈ Set.Ico 0 d, σ.toFun y 0 ≤ y)
    (hc_pos : 0 < c) (hc_lt_r : c < r) (h_α₂_c : α₂.toFun c = d) (hd_lt_b₁ : d < b₁) :
    ∃ β : ClassKL c, ∀ ρ s, β.toFun ρ s = α₁.invFun (σ.toFun (α₂.toFun ρ) s) := by
  /- `ClassKL.comp_left` takes a `ClassKInfty`, so `β` is assembled in two steps: first
     `σ ∘ α₂` by `comp_right`, then `α₁⁻¹ ∘ (σ ∘ α₂)` by `comp_left_K`. -/
  -- Step 1. The inner composite `σ(α₂(ρ), s)`, with `α₂` restricted to `[0, c) → [0, d)`.
  set inner := σ.comp_right (α₂.restrictTo hc_pos hc_lt_r h_α₂_c)
  have h_inner_eq : ∀ ρ s, inner.toFun ρ s = σ.toFun (α₂.toFun ρ) s := fun ρ s =>
    congrArg (fun y => σ.toFun y s) (α₂.restrictTo_toFun hc_pos hc_lt_r h_α₂_c ρ)
  -- Step 2. Its values stay below `d < b₁`, inside the domain of `α₁⁻¹`.
  have h_range : ∀ ρ ∈ Set.Ico 0 c, ∀ s ≥ 0, inner.toFun ρ s < b₁ := fun ρ hρ s hs => by
    rw [h_inner_eq]
    exact (σ.toFun_mem_Ico hσ_zero (α₂.toFun_mem_Ico hc_lt_r h_α₂_c hρ) hs).2.trans hd_lt_b₁
  -- Step 3. Post-compose with `α₁⁻¹`.
  exact ⟨inner.comp_left_K α₁.symm h_range, fun ρ s => congrArg α₁.invFun (h_inner_eq ρ s)⟩



-- ─── Class KL Global ─────────────────────────────────────────────────────────

/-! ### Class KL Global

A *global class KL* function `β(r, s)` is like `ClassKL` but defined on all of
`[0, ∞) × [0, ∞)`: class K in the first argument (continuous, strictly increasing, zero at
zero), antitone and tending to 0 in the second.  As in Khalil, `β(·, s)` need not be unbounded;
`ClassKLGlobal.exists_le_radiallyUnbounded` dominates any `β` by one with `β(·, 0)` unbounded,
for the one argument that needs it. -/

/-- A global class KL function `β : [0,∞) × [0,∞) → ℝ`: class K in the first argument,
    antitone and tending to 0 in the second.  `β(·, s)` need not be unbounded.

    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.3 with `a = ∞`. -/
@[blueprint "def:isClassKLGlobal"
  (title := "Global class $\\mathcal{KL}$ function")
  (statement := /-- A \emph{global class $\mathcal{KL}$} function is a map
    $\beta : [0,\infty) \times [0,\infty) \to \mathbb{R}$, jointly continuous, that is
    class $\mathcal{K}$ in the first argument (strictly increasing, zero at zero) and, for each
    fixed $r \ge 0$, is antitone and tends to $0$ as $s \to \infty$.  As in Khalil,
    $\beta(\cdot, s)$ need not be unbounded.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.3 with $a = \infty$.
  -/)]
structure ClassKLGlobal where
  /-- The forward function. -/
  toFun : ℝ → ℝ → ℝ
  map_zero      : ∀ s ≥ 0, toFun 0 s = 0
  continuous    : ContinuousOn (Function.uncurry toFun) (Set.Ici 0 ×ˢ Set.Ici 0)
  strict_mono_r : ∀ s ≥ 0, StrictMonoOn (fun r => toFun r s) (Set.Ici 0)
  nonneg        : ∀ r ≥ 0, ∀ s ≥ 0, 0 ≤ toFun r s
  anti_s        : ∀ r ≥ 0, AntitoneOn (fun s => toFun r s) (Set.Ici 0)
  tendsto_zero  : ∀ r ≥ 0, Filter.Tendsto (fun s => toFun r s) Filter.atTop (nhds 0)

/-- **Every global class `KL` function has a radially unbounded majorant**: a global class `KL`
function `β' ≥ β` with `β'(r, 0) → ∞`.  A global class `KL` function need not be radially
unbounded itself (`r / (1 + r) · e^{-s}` is not); `β(r, s) + r e^{-s}` is a majorant that is. -/
@[blueprint "lem:classKLGlobal-exists-le-radiallyUnbounded"
  (title := "Radially unbounded majorant of a class $\\mathcal{KL}$ function")
  (latexEnv := "lemma")
  (statement := /-- For every global class $\mathcal{KL}$ function $\beta$
    (\cref{def:isClassKLGlobal}) there is a global class $\mathcal{KL}$ function $\beta'$ with
    $\beta(r, s) \le \beta'(r, s)$ for $r, s \ge 0$ and $\beta'(r, 0) \to \infty$ as
    $r \to \infty$. -/)
  (proof := /-- $\beta'(r, s) = \beta(r, s) + r e^{-s}$. -/)]
theorem ClassKLGlobal.exists_le_radiallyUnbounded (β : ClassKLGlobal) :
    ∃ β' : ClassKLGlobal, (∀ r, 0 ≤ r → ∀ s, β.toFun r s ≤ β'.toFun r s) ∧
      Tendsto (fun r => β'.toFun r 0) atTop atTop := by
  let β' : ClassKLGlobal :=
    { toFun := fun r s => β.toFun r s + r * Real.exp (-s)
      map_zero := fun s hs => by simp [β.map_zero s hs]
      continuous :=
        β.continuous.add (continuous_fst.mul (continuous_snd.neg.rexp)).continuousOn
      strict_mono_r := fun s hs a ha b hb hab =>
        add_lt_add (β.strict_mono_r s hs ha hb hab) (mul_lt_mul_of_pos_right hab (Real.exp_pos _))
      nonneg := fun r hr s hs => add_nonneg (β.nonneg r hr s hs) (mul_nonneg hr (Real.exp_pos _).le)
      anti_s := fun r hr => (β.anti_s r hr).add fun a _ b _ hab =>
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hab)) hr
      tendsto_zero := fun r hr => by
        simpa using (β.tendsto_zero r hr).add (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul r) }
  refine ⟨β', fun r hr s => le_add_of_nonneg_right (mul_nonneg hr (Real.exp_pos _).le), ?_⟩
  simpa [β'] using tendsto_atTop_add_left_of_le' atTop 0
    ((eventually_ge_atTop 0).mono fun r hr => β.nonneg r hr 0 le_rfl) tendsto_id

/-- A global class KL function is nondecreasing in `r`. -/
@[gcongr]
theorem ClassKLGlobal.mono_r (β : ClassKLGlobal) {r₁ r₂ s : ℝ} (hr₁ : 0 ≤ r₁) (hs : 0 ≤ s)
    (h : r₁ ≤ r₂) : β.toFun r₁ s ≤ β.toFun r₂ s :=
  (β.strict_mono_r s hs).monotoneOn hr₁ (hr₁.trans h) h

/-- A global class KL function is nonincreasing in `s`. -/
@[gcongr]
theorem ClassKLGlobal.anti_s_mono (β : ClassKLGlobal) {r s₁ s₂ : ℝ} (hr : 0 ≤ r) (hs₁ : 0 ≤ s₁)
    (h : s₁ ≤ s₂) : β.toFun r s₂ ≤ β.toFun r s₁ :=
  β.anti_s r hr hs₁ (hs₁.trans h) h

/-- A global class KL function is continuous in `r` for each fixed `s ≥ 0`: the section of the
    joint continuity in the `continuous` field. -/
@[fun_prop]
theorem ClassKLGlobal.continuous_r {a : ℝ} (β : ClassKLGlobal) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (fun r => β.toFun r s) (Set.Ico 0 a) := by
  apply (β.continuous.comp (continuousOn_id.prodMk continuousOn_const)
        (fun x hx => Set.mk_mem_prod hx.1 hs)).congr
  intro x _
  simp

/-- Post-composing a global class KL function with a class K∞ function yields global class KL.
    (Applies `α` to the output of `β`.)

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.2, fifth bullet (the outer `α₁`),
in the global case `a = ∞`. -/
@[blueprint "lem:classKLGlobal-comp-left"
  (title := "Post-composition, global case")
  (statement := /-- If $\beta$ is global class $\mathcal{KL}$ and $\alpha$ is class
    $\mathcal{K}_{\infty}$, then $(r, s) \mapsto \alpha(\beta(r, s))$ is global class
    $\mathcal{KL}$.  No range hypothesis is needed, since $\alpha$ is defined on all of
    $[0,\infty)$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.2, fifth bullet (the outer
    $\alpha_1$), in the global case $a = \infty$. -/)]
def ClassKLGlobal.comp_left (β : ClassKLGlobal) (α : ClassKInfty) : ClassKLGlobal where
  toFun r s     := α.toFun (β.toFun r s)
  map_zero s hs := by simp only [β.map_zero s hs, α.map_zero]
  continuous s hs := by
    apply α.continuous.comp (β.continuous) (fun p hp => β.nonneg p.1 hp.1 p.2 hp.2)
    exact hs
  strict_mono_r s hs x hx y hy hxy :=
    α.strict_mono (β.nonneg x hx s hs) (β.nonneg y hy s hs)
      (β.strict_mono_r s hs hx hy hxy)
  nonneg r hr s hs := α.maps_to (β.nonneg r hr s hs)
  anti_s r hr s₁ hs₁ s₂ hs₂ hs :=
    α.strict_mono.monotoneOn (β.nonneg r hr s₂ hs₂) (β.nonneg r hr s₁ hs₁)
      (β.anti_s r hr hs₁ hs₂ hs)
  tendsto_zero r hr := by
    have hβ_ici : ∀ᶠ s in Filter.atTop, β.toFun r s ∈ Set.Ici 0 := by
      filter_upwards [eventually_ge_atTop 0] with s hs
      exact β.nonneg r hr s hs
    exact tendsto_zero_comp_of_continuousWithinAt
      (α.continuous.continuousWithinAt self_mem_Ici) α.map_zero (β.tendsto_zero r hr) hβ_ici

/-- Product of a class K∞ function and a class L function is global class KL.
    `β(r, s) = α(r) * γ(s)`. -/
@[blueprint "lem:classKLGlobal-mk-mul"
  (title := "Global class $\\mathcal{KL}$ from a product")
  (statement := /-- If $\alpha$ is class $\mathcal{K}_{\infty}$ and $\gamma$ is class
    $\mathcal{L}$, then $\beta(r, s) := \alpha(r)\gamma(s)$ is global class
    $\mathcal{KL}$. -/)]
noncomputable def ClassKLGlobal.mk_mul (α : ClassKInfty) (γ : ClassL) : ClassKLGlobal where
  toFun r s     := α.toFun r * γ.toFun s
  map_zero s hs := by simp [α.map_zero]
  continuous    := ContinuousOn.mul
    (α.continuous.comp continuous_fst.continuousOn (fun p hp => hp.1))
    (γ.continuous.comp continuous_snd.continuousOn (fun p hp => hp.2))
  strict_mono_r s hs x hx y hy hxy :=
    mul_lt_mul_of_pos_right (α.strict_mono hx hy hxy) (γ.pos s hs)
  nonneg r hr s hs := mul_nonneg (α.maps_to hr) (γ.pos s hs).le
  anti_s r hr s₁ hs₁ s₂ hs₂ hs :=
    mul_le_mul_of_nonneg_left (γ.anti.antitoneOn hs₁ hs₂ hs) (α.maps_to hr)
  tendsto_zero r hr := by
    simpa only [mul_zero] using Filter.Tendsto.const_mul (α.toFun r) γ.tendsto_zero

/-- Pointwise min of a global class KL and a class K∞ function (in the r-argument) is
    global class KL. -/
@[blueprint "lem:classKLGlobal-min-KInfty"
  (title := "Capping a global class $\\mathcal{KL}$ function")
  (statement := /-- If $\beta$ is global class $\mathcal{KL}$ and $\alpha$ is class
    $\mathcal{K}_{\infty}$, then $(r, s) \mapsto \min\bigl(\beta(r, s), \alpha(r)\bigr)$ is
    global class $\mathcal{KL}$ — capping a $\mathcal{KL}$ bound by a function of the initial
    condition alone preserves the class. -/)]
noncomputable def ClassKLGlobal.min_KInfty (β : ClassKLGlobal) (α : ClassKInfty) :
    ClassKLGlobal where
  toFun r s     := min (β.toFun r s) (α.toFun r)
  map_zero s hs := by rw [β.map_zero s hs, α.map_zero, min_self]
  continuous    := β.continuous.inf (α.continuous.comp continuous_fst.continuousOn
                    (fun p hp => hp.1))
  strict_mono_r s hs x hx y hy hxy := by
    apply lt_min
    · exact (min_le_left _ _).trans_lt (β.strict_mono_r s hs hx hy hxy)
    · exact (min_le_right _ _).trans_lt (α.strict_mono hx hy hxy)
  nonneg r hr s hs := le_min (β.nonneg r hr s hs) (α.maps_to hr)
  anti_s r hr s₁ hs₁ s₂ hs₂ hs :=
    min_le_min (β.anti_s r hr hs₁ hs₂ hs) le_rfl
  tendsto_zero r hr := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (β.tendsto_zero r hr)
    · filter_upwards [eventually_ge_atTop 0] with s hs
      exact le_min (β.nonneg r hr s hs) (α.maps_to hr)
    · filter_upwards [] with s; exact min_le_left _ _

/-- Pre-composing a global class KL function with a class K∞ function yields global class KL.
    (Applies `α` to the first argument of `β`.)

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.2, fifth bullet (the inner `α₂`),
in the global case `a = ∞`. -/
@[blueprint "lem:classKLGlobal-comp-right"
  (title := "Pre-composition in the radius argument, global case")
  (statement := /-- If $\beta$ is global class $\mathcal{KL}$ and $\alpha$ is class
    $\mathcal{K}_{\infty}$, then $(r, s) \mapsto \beta(\alpha(r), s)$ is global class
    $\mathcal{KL}$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.2, fifth bullet (the inner
    $\alpha_2$), in the global case $a = \infty$. -/)]
def ClassKLGlobal.comp_right (β : ClassKLGlobal) (α : ClassKInfty) : ClassKLGlobal where
  toFun r s     := β.toFun (α.toFun r) s
  map_zero s hs := by simp only [α.map_zero, β.map_zero s hs]
  continuous s hs :=   by
    apply β.continuous.comp
      ((α.continuous.comp continuousOn_fst (fun p hp => hp.1)).prodMk continuousOn_snd)
      (fun p hp => ⟨α.maps_to hp.1, hp.2⟩)
    exact hs
  strict_mono_r s hs x hx y hy hxy :=
    β.strict_mono_r s hs (α.maps_to hx) (α.maps_to hy) (α.strict_mono hx hy hxy)
  nonneg r hr s hs := β.nonneg (α.toFun r) (α.maps_to hr) s hs
  anti_s r hr        := β.anti_s (α.toFun r) (α.maps_to hr)
  tendsto_zero r hr  := β.tendsto_zero (α.toFun r) (α.maps_to hr)

/-- The sum of two global class KL functions is global class KL. -/
@[blueprint "lem:classKLGlobal-add"
  (title := "Sum of global class $\\mathcal{KL}$ functions")
  (statement := /-- If $\beta$ and $\beta'$ are global class $\mathcal{KL}$, so is
    $\beta + \beta'$. -/)]
def ClassKLGlobal.add (β β' : ClassKLGlobal) : ClassKLGlobal where
  toFun r s     := β.toFun r s + β'.toFun r s
  map_zero s hs := by rw [β.map_zero s hs, β'.map_zero s hs, add_zero]
  continuous    := β.continuous.add β'.continuous
  strict_mono_r s hs := (β.strict_mono_r s hs).add (β'.strict_mono_r s hs)
  nonneg r hr s hs := add_nonneg (β.nonneg r hr s hs) (β'.nonneg r hr s hs)
  anti_s r hr   := (β.anti_s r hr).add (β'.anti_s r hr)
  tendsto_zero r hr := by simpa using (β.tendsto_zero r hr).add (β'.tendsto_zero r hr)

/-- A positive multiple of a global class KL function is global class KL. -/
@[blueprint "lem:classKLGlobal-smul"
  (title := "Positive multiple of a global class $\\mathcal{KL}$ function")
  (statement := /-- If $\beta$ is global class $\mathcal{KL}$ and $c > 0$, then $c\beta$ is
    global class $\mathcal{KL}$. -/)]
def ClassKLGlobal.smul (β : ClassKLGlobal) (c : ℝ) (hc : 0 < c) : ClassKLGlobal where
  toFun r s     := c * β.toFun r s
  map_zero s hs := by rw [β.map_zero s hs, mul_zero]
  continuous    := continuousOn_const.mul β.continuous
  strict_mono_r s hs x hx y hy hxy := mul_lt_mul_of_pos_left (β.strict_mono_r s hs hx hy hxy) hc
  nonneg r hr s hs := mul_nonneg hc.le (β.nonneg r hr s hs)
  anti_s r hr s₁ hs₁ s₂ hs₂ hs := mul_le_mul_of_nonneg_left (β.anti_s r hr hs₁ hs₂ hs) hc.le
  tendsto_zero r hr := by simpa using (β.tendsto_zero r hr).const_mul c

/-- Slowing the time argument of a global class KL function by a factor `c > 0` gives a global
class KL function. -/
@[blueprint "lem:classKLGlobal-timeScale"
  (title := "Rescaling time in a global class $\\mathcal{KL}$ function")
  (statement := /-- If $\beta$ is global class $\mathcal{KL}$ and $c > 0$, then
    $(r, s) \mapsto \beta(r, s/c)$ is global class $\mathcal{KL}$. -/)]
noncomputable def ClassKLGlobal.timeScale (β : ClassKLGlobal) (c : ℝ) (hc : 0 < c) :
    ClassKLGlobal where
  toFun r s     := β.toFun r (s / c)
  map_zero _ hs := β.map_zero _ (div_nonneg hs hc.le)
  continuous    := β.continuous.comp (continuousOn_fst.prodMk (continuousOn_snd.div_const c))
    fun _ hp => ⟨hp.1, mem_Ici.2 (div_nonneg hp.2 hc.le)⟩
  strict_mono_r _ hs := β.strict_mono_r _ (div_nonneg hs hc.le)
  nonneg r hr _ hs := β.nonneg r hr _ (div_nonneg hs hc.le)
  anti_s r hr _ hs₁ _ hs₂ hs := β.anti_s r hr (div_nonneg hs₁ hc.le) (div_nonneg hs₂ hc.le)
    (div_le_div_of_nonneg_right hs hc.le)
  tendsto_zero r hr := (β.tendsto_zero r hr).comp (tendsto_id.atTop_div_const hc)

/-- **Composition with a radius that may shrink in time.**  If `β` is global class KL and
`a(r, s)` is continuous, vanishes at `r = 0`, is strictly increasing in `r` and nonincreasing in
`s`, then `β(a(r, s), s)` is global class KL: it decays because `β(a(r, s), s) ≤ β(a(r, 0), s)`.
This generalizes `comp_right`, where `a(r, s) = α(r)`. -/
@[blueprint "lem:classKLGlobal-comp-antitone"
  (title := "Composition with a nonincreasing radius")
  (statement := /-- Let $\beta$ be global class $\mathcal{KL}$ and let
    $a : [0, \infty)^2 \to \mathbb{R}$ be continuous, with $a(0, s) = 0$, strictly increasing
    in $r$ and nonincreasing in $s$.  Then $(r, s) \mapsto \beta(a(r, s), s)$ is global class
    $\mathcal{KL}$. -/)
  (proof := /-- Each property of $\beta$ transfers, using $a \ge 0$; for the limit,
    $0 \le \beta(a(r, s), s) \le \beta(a(r, 0), s) \to 0$. -/)]
noncomputable def ClassKLGlobal.comp_antitone (β : ClassKLGlobal) (a : ℝ → ℝ → ℝ)
    (ha_zero : ∀ s ≥ 0, a 0 s = 0) (ha_cont : ContinuousOn (Function.uncurry a) (Ici 0 ×ˢ Ici 0))
    (ha_mono : ∀ s ≥ 0, StrictMonoOn (fun r => a r s) (Ici 0))
    (ha_anti : ∀ r ≥ 0, AntitoneOn (fun s => a r s) (Ici 0)) : ClassKLGlobal :=
  have ha_nonneg : ∀ r ≥ 0, ∀ s ≥ 0, 0 ≤ a r s := fun r hr s hs =>
    ha_zero s hs ▸ (ha_mono s hs).monotoneOn (mem_Ici.2 le_rfl) hr hr
  { toFun r s     := β.toFun (a r s) s
    map_zero s hs := by rw [ha_zero s hs, β.map_zero s hs]
    continuous    := β.continuous.comp (ha_cont.prodMk continuousOn_snd)
      fun p hp => ⟨ha_nonneg p.1 hp.1 p.2 hp.2, hp.2⟩
    strict_mono_r s hs x hx y hy hxy := β.strict_mono_r s hs (ha_nonneg x hx s hs)
      (ha_nonneg y hy s hs) (ha_mono s hs hx hy hxy)
    nonneg r hr s hs := β.nonneg _ (ha_nonneg r hr s hs) s hs
    anti_s r hr s₁ hs₁ s₂ hs₂ hs :=
      (β.mono_r (ha_nonneg r hr s₂ hs₂) hs₂ (ha_anti r hr hs₁ hs₂ hs)).trans
        (β.anti_s _ (ha_nonneg r hr s₁ hs₁) hs₁ hs₂ hs)
    tendsto_zero r hr := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (β.tendsto_zero _ (ha_nonneg r hr 0 le_rfl)) ?_ ?_
      · filter_upwards [eventually_ge_atTop 0] with s hs
        exact β.nonneg _ (ha_nonneg r hr s hs) s hs
      · filter_upwards [eventually_ge_atTop 0] with s hs
        exact β.mono_r (ha_nonneg r hr s hs) hs (ha_anti r hr (mem_Ici.2 le_rfl) hs hs) }

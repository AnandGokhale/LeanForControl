import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Basic
import Architect


/-!
# Smoothing of monotone functions

One `axiom` and two proved results. A Lyapunov function's sublevel data gives only
*monotone* bounds; the comparison-function machinery needs *strictly* monotone continuous ones.
These say the gap can always be closed, in either direction.

The upper (majorant) direction is proved by averaging: `s + ⨍_{[s, 2s]} φ`. It needs `φ` to be
continuous at `0`, since a continuous majorant vanishing at `0` cannot sit above a jump there.
The lower (minorant) direction is still an `axiom`.
-/

/-- A monotonically non-decreasing positive function can be lower-bounded by a strictly monotonic
continuous function. -/
@[blueprint "lem:exists-strictMono-lower-bound"
  (title := "Class $\\mathcal{K}$ minorant of a positive monotone function") (latexEnv := "lemma")
  (statement := /-- \textbf{Assumed without proof.}  Let $r > 0$ and let
    $\psi : \mathbb{R} \to \mathbb{R}$ satisfy $\psi(0) = 0$, $\psi(s) > 0$ for
    $s \in (0, r]$, and $\psi$ nondecreasing on $[0, r]$.  Then there are $b > 0$ and a
    function $f$ with $f(0) = 0$, $f(r) = b$, $f$ continuous and strictly increasing on
    $[0, r]$, and $f(s) \le \psi(s)$ for all $s \in [0, r]$.

    That is: a positive nondecreasing function admits a class $\mathcal{K}$ minorant on any
    bounded interval.  This is what turns a positive-definite $V$ into the lower comparison
    bound of \cref{thm:lyapunov-class-K-bounds}. -/)]
axiom exists_strictMono_lower_bound (r : ℝ) (hr : 0 < r) (ψ : ℝ → ℝ)
    (hψ_zero : ψ 0 = 0)
    (hψ_pos : ∀ s, 0 < s → s ≤ r → 0 < ψ s)
    (hψ_mono : ∀ s₁ s₂, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ r → ψ s₁ ≤ ψ s₂) :
    ∃ (f : ℝ → ℝ) (b : ℝ), 0 < b ∧
      f 0 = 0 ∧ f r = b ∧
      ContinuousOn f (Set.Icc 0 r) ∧
      StrictMonoOn f (Set.Icc 0 r) ∧
      ∀ s, 0 ≤ s → s ≤ r → f s ≤ ψ s


open Set Filter Topology MeasureTheory in
/-- A monotonically non-decreasing function on `[0, ∞)` that is continuous at `0` with value `0`
    can be upper-bounded by a strictly monotonic continuous function that tends to `+∞`.

The continuity hypothesis cannot be dropped: the unit step (`0` at `0`, `1` after) has no
continuous majorant vanishing at `0`. -/
@[blueprint "lem:exists-strictMono-upper-bound-global"
  (title := "Class $\\mathcal{K}_{\\infty}$ majorant of a monotone function") (latexEnv := "lemma")
  (statement := /-- Let $\varphi : \mathbb{R} \to \mathbb{R}$ satisfy $\varphi(0) = 0$, be
    monotone on $[0, \infty)$, and be continuous at $0$ from the right.  Then there is an
    $f$ with $f(0) = 0$, continuous and strictly increasing on $[0, \infty)$,
    $f(s) \to \infty$ as $s \to \infty$, and $\varphi(s) \le f(s)$ for all $s \ge 0$.

    That is: a nondecreasing function admits a class $\mathcal{K}_{\infty}$ majorant.  The
    unbounded domain is what distinguishes this from
    \cref{lem:exists-strictMono-upper-bound}, which it implies.

    Continuity at $0$ is necessary: the unit step has no continuous majorant vanishing at
    $0$. -/)
  (proof := /-- Take $f(s) = s + g(s)$ with $g(s) = \int_1^2 \varphi(su)\,du$, the average of
    $\varphi$ over $[s, 2s]$ (with $\varphi$ clamped to $\varphi(\max(t,0))$ so that it is
    monotone, hence integrable, on all of $\mathbb{R}$).  Monotonicity of $\varphi$ gives
    $\varphi(s) \le g(s) \le \varphi(2s)$ and that $g$ is nondecreasing, so $f$ is strictly
    increasing, $f \ge \varphi$, and $f(s) \ge s \to \infty$.  For $s > 0$,
    $g(s) = s^{-1}\bigl(\Phi(2s) - \Phi(s)\bigr)$ with $\Phi$ the (continuous) primitive of
    $\varphi$, so $g$ is continuous there; at $0$, $0 \le g(s) \le \varphi(2s) \to 0$ by
    continuity of $\varphi$ at $0$. -/)]
theorem exists_strictMono_upper_bound_global (φ : ℝ → ℝ)
    (hφ_zero : φ 0 = 0)
    (hφ_mono : MonotoneOn φ (Set.Ici 0))
    (hφ_cont : ContinuousWithinAt φ (Set.Ici 0) 0) :
    ∃ f : ℝ → ℝ,
      f 0 = 0 ∧
      ContinuousOn f (Set.Ici 0) ∧
      StrictMonoOn f (Set.Ici 0) ∧
      Filter.Tendsto f Filter.atTop Filter.atTop ∧
      ∀ s ≥ 0, φ s ≤ f s := by
  /- We take `f s = s + g s`, where `g s` is the average of `φ` over `[s, 2s]`.
     The window lies to the right of `s`, so `g ≥ φ`; it shrinks to `0` with `s`, so `g`
     inherits continuity at `0` from `φ`; and the `s` term makes `f` strictly increasing. -/

  -- Step 1. Clamp the argument at `0`, so that `ψ` is monotone (hence integrable) on all of `ℝ`.
  set ψ : ℝ → ℝ := fun t => φ (max t 0)
  have hψ_mono : Monotone ψ := fun x y h =>
    hφ_mono (le_max_right x 0) (le_max_right y 0) (max_le_max h le_rfl)
  have hψ_eq : ∀ s ≥ 0, ψ s = φ s := fun s hs => by simp [ψ, max_eq_left hs]
  have hψ_nonneg : ∀ t, 0 ≤ ψ t := fun t =>
    hφ_zero ▸ hφ_mono (le_refl (0 : ℝ)) (le_max_right t 0) (le_max_right t 0)
  have hψ_int : ∀ a b, IntervalIntegrable ψ volume a b := fun _ _ =>
    hψ_mono.intervalIntegrable
  -- Step 2. The average `g s = ∫₁² ψ(s u) du` of `ψ` over `[s, 2s]`.
  set g : ℝ → ℝ := fun s => ∫ u in (1 : ℝ)..2, ψ (s * u)
  have hg_int : ∀ s ≥ 0, IntervalIntegrable (fun u => ψ (s * u)) volume 1 2 := fun s hs =>
    (hψ_mono.comp fun _ _ h => mul_le_mul_of_nonneg_left h hs).intervalIntegrable
  have hg_zero : g 0 = 0 := by simp [g, ψ, hφ_zero]
  -- `g` is nondecreasing, because `ψ` is.
  have hg_mono : MonotoneOn g (Ici 0) := fun s hs s' hs' hss' =>
    intervalIntegral.integral_mono_on (by norm_num) (hg_int s hs) (hg_int s' hs') fun u hu =>
      hψ_mono (mul_le_mul_of_nonneg_right hss' (by linarith [hu.1]))
  -- `φ s ≤ g s ≤ φ (2s)`: for `u ∈ [1, 2]`, `ψ s ≤ ψ (s u) ≤ ψ (2s)`, and the window has
  -- length `1`.
  have hg_ge : ∀ s ≥ 0, φ s ≤ g s := fun s hs => by
    have h := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 2)
      intervalIntegrable_const (hg_int s hs) fun u hu =>
        hψ_mono (le_mul_of_one_le_right hs hu.1)
    norm_num [hψ_eq s hs] at h
    exact h
  have hg_le : ∀ s ≥ 0, g s ≤ φ (2 * s) := fun s hs => by
    have h := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 2)
      (hg_int s hs) intervalIntegrable_const fun u hu =>
        hψ_mono (by nlinarith [hu.2] : s * u ≤ 2 * s)
    norm_num [hψ_eq (2 * s) (by linarith)] at h
    exact h
  have hg_nonneg : ∀ s ≥ 0, 0 ≤ g s := fun s hs =>
    (hψ_eq s hs ▸ hψ_nonneg s).trans (hg_ge s hs)
  -- Step 3. `g` is continuous on `[0, ∞)`.
  -- At `0`: `g` is squeezed between `0` and `φ (2s)`, which tends to `φ 0 = 0`.
  have hg_cont_zero : ContinuousWithinAt g (Ici 0) 0 := by
    have h_upper : Tendsto (fun s => φ (2 * s)) (𝓝[≥] 0) (𝓝 0) := by
      have h := hφ_cont.comp_of_eq (continuousWithinAt_id.const_mul 2)
        (fun s (hs : 0 ≤ s) => by simp only [mem_Ici, id]; linarith) (mul_zero 2)
      simpa [hφ_zero] using h.tendsto
    rw [ContinuousWithinAt, hg_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
      (eventually_nhdsWithin_of_forall hg_nonneg) (eventually_nhdsWithin_of_forall hg_le)
  -- At `s > 0`: substituting `x = s u` gives `g s = s⁻¹ (Φ (2s) - Φ s)`, where `Φ` is the
  -- (continuous) primitive of `ψ`.
  set Φ : ℝ → ℝ := fun b => ∫ x in (0 : ℝ)..b, ψ x
  have hΦ_cont : Continuous Φ := intervalIntegral.continuous_primitive hψ_int 0
  have hg_eq : ∀ s ≠ 0, g s = s⁻¹ * (Φ (s * 2) - Φ (s * 1)) := fun s hs => by
    simp only [g, Φ]
    rw [intervalIntegral.integral_comp_mul_left _ hs, smul_eq_mul,
      intervalIntegral.integral_interval_sub_left (hψ_int _ _) (hψ_int _ _)]
  have hg_cont_pos : ∀ s > 0, ContinuousAt g s := fun s hs => by
    have h : ContinuousAt (fun t => t⁻¹ * (Φ (t * 2) - Φ (t * 1))) s :=
      (continuousAt_inv₀ hs.ne').mul (by fun_prop)
    exact h.congr ((eventually_ne_nhds hs.ne').mono fun t ht => (hg_eq t ht).symm)
  have hg_cont : ContinuousOn g (Ici 0) := by
    intro s hs
    rcases (mem_Ici.mp hs).eq_or_lt with rfl | hs_pos
    · exact hg_cont_zero
    · exact (hg_cont_pos s hs_pos).continuousWithinAt
  -- Step 4. `f s = s + g s` has every required property.
  refine ⟨fun s => s + g s, ?_, ?_, ?_, ?_, ?_⟩
  · -- `f 0 = 0`
    simp [hg_zero]
  · -- continuous
    exact continuousOn_id.add hg_cont
  · -- strictly increasing: `s` is strictly increasing and `g` is nondecreasing
    intro s hs s' hs' hss'
    exact add_lt_add_of_lt_of_le hss' (hg_mono hs hs' hss'.le)
  · -- unbounded: `f s ≥ s`
    refine tendsto_atTop_mono' _ ((eventually_ge_atTop 0).mono fun s hs => ?_) tendsto_id
    simpa using hg_nonneg s hs
  · -- majorizes `φ`: `φ s ≤ g s ≤ s + g s`
    intro s hs
    linarith [hg_ge s hs]

/-- A monotonically non-decreasing function on `[0, r]`, continuous at `0` with value `0`, can be
    upper-bounded by a strictly monotonic continuous function.

Proved by clamping `φ` beyond `r` and invoking the global version. -/
@[blueprint "lem:exists-strictMono-upper-bound"
  (title := "Class $\\mathcal{K}$ majorant on a bounded interval")
  (latexEnv := "lemma")
  (statement := /-- Let $r > 0$ and let $\varphi$ satisfy $\varphi(0) = 0$, be monotone on
    $[0, r]$, and be continuous at $0$ from the right.  Then there are $b > 0$ and an $f$ with
    $f(0) = 0$, $f(r) = b$, $f$ continuous and strictly increasing on $[0, r]$, and
    $\varphi(s) \le f(s)$ for all $s \in [0, r]$. -/)
  (proof := /-- Clamp $\varphi$ to $\varphi_{\mathrm{ext}}(s) = \varphi(\min(s, r))$, which
    is monotone on all of $[0,\infty)$, still vanishes at $0$ and agrees with $\varphi$ near
    $0$ (so is still continuous there), and apply
    \cref{lem:exists-strictMono-upper-bound-global}.  Restricting the resulting majorant to
    $[0, r]$ gives $f$; $b = f(r) > 0$ because $f$ is strictly increasing from $f(0) = 0$. -/)]
lemma exists_strictMono_upper_bound (r : ℝ) (hr : 0 < r) (φ : ℝ → ℝ)
    (hφ_zero : φ 0 = 0)
    (hφ_mono : MonotoneOn φ (Set.Icc 0 r))
    (hφ_cont : ContinuousWithinAt φ (Set.Icc 0 r) 0) :
    ∃ (f : ℝ → ℝ) (b : ℝ), 0 < b ∧
      f 0 = 0 ∧ f r = b ∧
      ContinuousOn f (Set.Icc 0 r) ∧
      StrictMonoOn f (Set.Icc 0 r) ∧
      ∀ s, 0 ≤ s → s ≤ r → φ s ≤ f s := by
  -- Extend φ to [0, ∞) by clamping: φ_ext s = φ s for s ≤ r, φ r for s > r
  let φ_ext : ℝ → ℝ := fun s => if s ≤ r then φ s else φ r
  have hφ_ext_zero : φ_ext 0 = 0 := by simp [φ_ext, hr.le, hφ_zero]
  have hφ_ext_mono : MonotoneOn φ_ext (Set.Ici 0) := by
    intro s₁ hs₁ s₂ _ h_le
    simp only [φ_ext]
    split_ifs with h1 h2
    · exact hφ_mono ⟨hs₁, h_le.trans h2⟩ ⟨hs₁.trans h_le, h2⟩ h_le   -- both ≤ r
    · exact hφ_mono ⟨hs₁, h1⟩ ⟨hr.le, le_rfl⟩ h1                     -- s₁ ≤ r < s₂
    · linarith [not_le.mp h1]                -- s₁ > r, s₂ ≤ r: impossible
    · exact le_refl _                        -- both > r
  -- φ_ext agrees with φ on [0, r], which is a neighbourhood of 0 within [0, ∞)
  have hφ_ext_cont : ContinuousWithinAt φ_ext (Set.Ici 0) 0 :=
    (hφ_cont.congr (fun s hs => if_pos hs.2) (if_pos hr.le)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE hr)
  -- Apply the global version to φ_ext
  obtain ⟨f, hf_zero, hf_cont, hf_mono, _, hf_bound⟩ :=
    exists_strictMono_upper_bound_global φ_ext hφ_ext_zero hφ_ext_mono hφ_ext_cont
  refine ⟨f, f r, ?_, hf_zero, rfl,
    hf_cont.mono Set.Icc_subset_Ici_self,
    hf_mono.mono Set.Icc_subset_Ici_self,
    fun s hs₁ hs₂ => ?_⟩
  · -- f r > 0: f strictly mono, f 0 = 0, r > 0
    have h := hf_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hr.le) hr
    linarith [hf_zero ▸ h]
  · -- φ s ≤ φ_ext s ≤ f s for s ≤ r
    have h := hf_bound s hs₁
    simp only [φ_ext, if_pos hs₂] at h
    exact h

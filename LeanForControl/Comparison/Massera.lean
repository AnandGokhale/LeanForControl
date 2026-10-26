import LeanForControl.Comparison.ClassKInfty
import LeanForControl.Analysis.MonotoneFunctions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Architect

/-!
# `Comparison.Massera` — Massera's lemma

Given a rate `g(t) → 0` and a weight `h(t)`, Massera's lemma builds a class `K∞` function `G`
with class `K∞` derivative that flattens `g` enough for `∫ G(u)` and `∫ G'(u) h` to converge,
uniformly over every `u ≤ g`.  It is the step that turns a class `KL` estimate into a
convergent Lyapunov integral `V(t, x) = ∫_t^∞ G(‖φ(τ; t, x)‖) dτ` (Khalil's Theorem 4.16).

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma C.1; Massera (1956).

## The construction

Khalil's `η` is a strictly decreasing function above `g` that blows up at `0⁺`; here
`η(t) = g(t) + 1/t`, which lies above `g` for every `t > 0`.  With `θ = η⁻¹`,
`G'(s) = e^{-θ(s)} / h(θ(s))`, so that `G'(u(t)) ≤ e^{-t} / h(t)` whenever `u(t) ≤ g(t)`, and
`G(r) = ∫_0^r G'`.  Both integrals are then dominated by multiples of `e^{-t}`.
-/

open Set Filter Topology MeasureTheory

/-- **The inverse rate.**  For `g` as in Massera's lemma there is `θ`, continuous and strictly
decreasing on `(0, ∞)` with `θ(s) → ∞` as `s → 0⁺`, such that `θ(s) ≥ t` whenever
`0 < s ≤ g(t)`: the inverse of `η(t) = g(t) + 1/t`. -/
private lemma massera_rate {g : ℝ → ℝ} (hg_pos : ∀ t, 0 ≤ t → 0 < g t)
    (hg_cont : ContinuousOn g (Ici 0)) (hg_anti : StrictAntiOn g (Ici 0))
    (hg_lim : Tendsto g atTop (𝓝 0)) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Ioi 0) ∧ StrictAntiOn θ (Ioi 0) ∧ (∀ s, 0 < s → 0 < θ s) ∧
      Tendsto θ (𝓝[>] 0) atTop ∧ ∀ t, 0 < t → ∀ s, 0 < s → s ≤ g t → t ≤ θ s := by
  set η : ℝ → ℝ := fun t => g t + t⁻¹
  have hη_cont : ContinuousOn η (Ioi 0) :=
    (hg_cont.mono Ioi_subset_Ici_self).add (continuousOn_inv₀.mono fun t (ht : 0 < t) => ht.ne')
  have hη_anti : StrictAntiOn η (Ioi 0) := fun a (ha : 0 < a) b (hb : 0 < b) hab =>
    add_lt_add (hg_anti (mem_Ici.2 ha.le) (mem_Ici.2 hb.le) hab) ((inv_lt_inv₀ hb ha).2 hab)
  have hη_zero : Tendsto η atTop (𝓝 0) := by simpa using hg_lim.add tendsto_inv_atTop_zero
  have hη_top : Tendsto η (𝓝[>] 0) atTop := by
    refine tendsto_atTop_mono' _ ?_ tendsto_inv_nhdsGT_zero
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    linarith [hg_pos t ht.le]
  have hθ_anti := strictAntiOn_invFunOn hη_cont hη_anti hη_zero hη_top
  refine ⟨Function.invFunOn η (Ioi 0), invFunOn_continuousOn hη_cont hη_anti hη_zero hη_top,
    hθ_anti, fun s hs => invFunOn_pos hη_cont hη_zero hη_top hs,
    invFunOn_tendsto_atTop hη_cont hη_anti hη_zero hη_top, fun t ht s hs hst => ?_⟩
  have hηt : g t < η t := lt_add_of_pos_right _ (inv_pos.2 ht)
  calc t
      = Function.invFunOn η (Ioi 0) (η t) := (hη_anti.injOn.leftInvOn_invFunOn ht).symm
    _ ≤ Function.invFunOn η (Ioi 0) s :=
        hθ_anti.antitoneOn hs ((hg_pos t ht.le).trans hηt) (hst.trans hηt.le)

/-- **Massera's lemma.**  Let `g` be positive, continuous and strictly decreasing on `[0, ∞)`
with `g(t) → 0`, and `h` positive, continuous and nondecreasing on `[0, ∞)`.  There is a class
`K∞` function `G` whose derivative `G'` is class `K∞`, and constants `k₁, k₂ > 0`, such that
`∫_0^∞ G(u(t)) dt ≤ k₁` and `∫_0^∞ G'(u(t)) h(t) dt ≤ k₂` for every continuous `u` with
`0 ≤ u ≤ g`, both integrals converging.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma C.1.  Differences:
- `G` and `G'` are class `K∞` rather than class `K` on `[0, ∞)`: only their values on `[0, g(0)]`
  enter the integrals, so they can be extended to be unbounded.
- Convergence of the integrals is part of the conclusion; Khalil leaves it implicit. -/
@[blueprint "lem:classKInfty-massera"
  (title := "Massera's lemma")
  (latexEnv := "lemma")
  (statement := /-- Let $g : [0, \infty) \to \mathbb{R}$ be positive, continuous and strictly
    decreasing with $g(t) \to 0$, and $h : [0, \infty) \to \mathbb{R}$ positive, continuous and
    nondecreasing.  There is a class $\mathcal{K}_\infty$ function $G$
    (\cref{def:isClassKInfty}) whose derivative $G'$ is class $\mathcal{K}_\infty$, and
    constants $k_1, k_2 > 0$, such that for every continuous $u$ with $0 \le u(t) \le g(t)$
    the integrals below converge and
    \[
      \int_0^\infty G(u(t))\,dt \le k_1, \qquad \int_0^\infty G'(u(t))\,h(t)\,dt \le k_2.
    \]

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma C.1.  Differences: $G$ and
    $G'$ are class $\mathcal{K}_\infty$ rather than class $\mathcal{K}$ on $[0, \infty)$, since
    only their values on $[0, g(0)]$ matter; convergence of the integrals is stated. -/)
  (proof := /-- Let $\eta(t) = g(t) + 1/t$: continuous and strictly decreasing on $(0, \infty)$,
    with $\eta \to \infty$ at $0^+$, $\eta \to 0$ at $\infty$, and $\eta > g$.  Its inverse
    $\theta = \eta^{-1}$ (\cref{lem:invFunOnContinuousOn}) satisfies $\theta(s) \ge t$ whenever
    $0 < s \le g(t)$.  Let
    \[
      G'(s) = \frac{e^{-\theta(s)}}{h(\theta(s))} + \max(s - g(0), 0), \qquad
      G(r) = \int_0^r G'(s)\,ds,
    \]
    so that $G'(s) \le e^{-t}/h(t)$ for $0 \le s \le g(t)$.  Then $G'(u(t))\,h(t) \le e^{-t}$
    and $G(u(t)) \le u(t)\,e^{-t}/h(t) \le (g(0)/h(0))\,e^{-t}$, so $k_1 = g(0)/h(0)$ and
    $k_2 = 1$.  Khalil's piecewise-linear $\eta$ is replaced by $g(t) + 1/t$, which lies above
    $g$ for every $t > 0$, so no splitting at $t_1$ is needed. -/)]
theorem ClassKInfty.massera {g h : ℝ → ℝ}
    (hg_pos : ∀ t, 0 ≤ t → 0 < g t) (hg_cont : ContinuousOn g (Ici 0))
    (hg_anti : StrictAntiOn g (Ici 0)) (hg_lim : Tendsto g atTop (𝓝 0))
    (hh_pos : ∀ t, 0 ≤ t → 0 < h t) (hh_cont : ContinuousOn h (Ici 0))
    (hh_mono : MonotoneOn h (Ici 0)) :
    ∃ G G' : ClassKInfty, (∀ r, 0 ≤ r → HasDerivAt G (G' r) r) ∧
      ∃ k₁ > 0, ∃ k₂ > 0, ∀ u : ℝ → ℝ, ContinuousOn u (Ici 0) →
        (∀ t, 0 ≤ t → 0 ≤ u t ∧ u t ≤ g t) →
        IntegrableOn (fun t => G (u t)) (Ioi 0) ∧ ∫ t in Ioi 0, G (u t) ≤ k₁ ∧
        IntegrableOn (fun t => G' (u t) * h t) (Ioi 0) ∧ ∫ t in Ioi 0, G' (u t) * h t ≤ k₂ := by
  -- Step 1. The inverse rate `θ = η⁻¹`, with `θ(s) ≥ t` whenever `0 < s ≤ g(t)`.
  obtain ⟨θ, hθ_cont, hθ_anti, hθ_pos, hθ_top, hθ_ge⟩ :=
    massera_rate hg_pos hg_cont hg_anti hg_lim
  have hg0 : 0 < g 0 := hg_pos 0 le_rfl
  have hh0 : 0 < h 0 := hh_pos 0 le_rfl
  have hg_le : ∀ t, 0 ≤ t → g t ≤ g 0 := fun t ht =>
    hg_anti.antitoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  have hh_ge : ∀ t, 0 ≤ t → h 0 ≤ h t := fun t ht =>
    hh_mono (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  -- Step 2. `G' = H`: Khalil's `e^{-θ(s)} / h(θ(s))`, plus `(s - g(0))⁺`, which vanishes where
  -- the integrals look and makes `H` unbounded.  Its key property is the bound `hH_le`.
  set H₀ : ℝ → ℝ := fun s => if 0 < s then Real.exp (-θ s) / h (θ s) else 0
  set H : ℝ → ℝ := fun s => H₀ s + max (s - g 0) 0
  have hH₀_pos : ∀ s, 0 < s → H₀ s = Real.exp (-θ s) / h (θ s) := fun s hs => if_pos hs
  have hH₀_zero : ∀ s, s ≤ 0 → H₀ s = 0 := fun s hs => if_neg (not_lt.2 hs)
  have hhθ : ∀ s, 0 < s → 0 < h (θ s) := fun s hs => hh_pos _ (hθ_pos s hs).le
  -- The key bound: below `g(t)`, `H ≤ e^{-t} / h(t)`.
  have hH_le : ∀ t, 0 < t → ∀ s, 0 ≤ s → s ≤ g t → H s ≤ Real.exp (-t) / h t := by
    intro t ht s hs hst
    have h_max : max (s - g 0) 0 = 0 := max_eq_right (by linarith [hg_le t ht.le])
    rcases hs.eq_or_lt with rfl | hs
    · simpa only [H, hH₀_zero 0 le_rfl, h_max, add_zero] using
        div_nonneg (Real.exp_pos _).le (hh_pos t ht.le).le
    calc H s
        = Real.exp (-θ s) / h (θ s) := by simp only [H, hH₀_pos s hs, h_max, add_zero]
      _ ≤ Real.exp (-t) / h t :=
          div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.2 (by linarith [hθ_ge t ht s hs hst]))
            (hh_pos t ht.le) (hh_mono (mem_Ici.2 ht.le) (mem_Ici.2 (hθ_pos s hs).le)
              (hθ_ge t ht s hs hst))
  -- Step 3. `H` is class `K∞` (continuous, zero at zero, strictly increasing, unbounded), and so
  -- is its integral `G(r) = ∫_0^r H`, with `G' = H`.
  have hH_cont : Continuous H := by
    refine Continuous.add ?_ ((continuous_id.sub continuous_const).max continuous_const)
    -- `H₀` is continuous: its two pieces meet continuously at `0`, the only boundary point.
    rw [← continuousOn_univ]
    refine ContinuousOn.if' (fun a ha => ?_) (fun a ha => ?_) ?_ continuousOn_const
    · -- At `0⁺` the formula is squeezed to `0` by `e^{-θ(s)} / h(0) → 0`.
      obtain rfl : a = 0 := by simpa [show {x : ℝ | 0 < x} = Ioi 0 from rfl] using ha.2
      suffices h : Tendsto (fun s => Real.exp (-θ s) / h (θ s)) (𝓝[>] 0) (𝓝 0) by simpa using h
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp hθ_top).div_const (h 0)) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
        exact div_nonneg (Real.exp_pos _).le (hhθ s hs).le
      · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
        exact div_le_div_of_nonneg_left (Real.exp_pos _).le hh0 (hh_ge _ (hθ_pos s hs).le)
    · obtain rfl : a = 0 := by simpa [show {x : ℝ | 0 < x} = Ioi 0 from rfl] using ha.2
      simpa using tendsto_const_nhds
    · -- On `(0, ∞)`, by its formula.
      exact ((Real.continuous_exp.comp_continuousOn hθ_cont.neg).div
        (hh_cont.comp hθ_cont fun s hs => mem_Ici.2 (hθ_pos s hs).le)
          fun s hs => (hhθ s hs).ne').mono fun s hs => hs.2
  have hH_zero : H 0 = 0 := by
    change H₀ 0 + max (0 - g 0) 0 = 0
    rw [hH₀_zero 0 le_rfl, max_eq_right (by linarith)]
    simp
  have hH_mono : StrictMonoOn H (Ici 0) := by
    intro a (ha : 0 ≤ a) b (hb : 0 ≤ b) hab
    have hb_pos : 0 < b := ha.trans_lt hab
    have h₀ : H₀ a < H₀ b := by
      rcases ha.eq_or_lt with rfl | ha_pos
      · rw [hH₀_zero 0 le_rfl, hH₀_pos b hb_pos]
        exact div_pos (Real.exp_pos _) (hhθ b hb_pos)
      rw [hH₀_pos a ha_pos, hH₀_pos b hb_pos]
      calc Real.exp (-θ a) / h (θ a)
          < Real.exp (-θ b) / h (θ a) :=
            div_lt_div_of_pos_right (Real.exp_lt_exp.2 (neg_lt_neg (hθ_anti ha_pos hb_pos hab)))
              (hhθ a ha_pos)
        _ ≤ Real.exp (-θ b) / h (θ b) :=
            div_le_div_of_nonneg_left (Real.exp_pos _).le (hhθ b hb_pos)
              (hh_mono (mem_Ici.2 (hθ_pos b hb_pos).le) (mem_Ici.2 (hθ_pos a ha_pos).le)
                (hθ_anti ha_pos hb_pos hab).le)
    exact add_lt_add_of_lt_of_le h₀ (max_le_max (by linarith) le_rfl)
  set H' : ClassKInfty := ClassKInfty.of_strictMono H hH_zero hH_cont.continuousOn hH_mono (by
    -- `H(s) ≥ s - g(0) → ∞`.
    refine tendsto_atTop_mono (fun s => ?_) (tendsto_atTop_add_const_right _ (-g 0) tendsto_id)
    calc id s + -g 0
        ≤ max (s - g 0) 0 := by rw [id, ← sub_eq_add_neg]; exact le_max_left _ _
      _ ≤ H s := le_add_of_nonneg_left (by
          rcases le_or_gt s 0 with hs | hs
          · rw [hH₀_zero s hs]
          · rw [hH₀_pos s hs]
            exact div_nonneg (Real.exp_pos _).le (hhθ s hs).le))
  set G : ClassKInfty := H'.integral
  refine ⟨G, H', fun r hr => H'.hasDerivAt_integral hr, g 0 / h 0, div_pos hg0 hh0, 1, one_pos,
    fun u hu_cont hu => ?_⟩
  -- Step 4. Along `u ≤ g`, both integrands are dominated by multiples of `e^{-t}`.
  have hu' : ContinuousOn u (Ioi 0) := hu_cont.mono Ioi_subset_Ici_self
  have h_Hu : ∀ t, 0 < t → H (u t) * h t ≤ Real.exp (-t) := fun t ht => by
    have h := hH_le t ht (u t) (hu t ht.le).1 (hu t ht.le).2
    rwa [le_div_iff₀ (hh_pos t ht.le)] at h
  have h_Gu : ∀ t, 0 < t → G (u t) ≤ g 0 / h 0 * Real.exp (-t) := fun t ht => by
    obtain ⟨hu0, hug⟩ := hu t ht.le
    calc G (u t)
        = ∫ s in (0 : ℝ)..u t, H s := H'.integral_apply hu0
      _ ≤ ∫ _s in (0 : ℝ)..u t, Real.exp (-t) / h t :=
          intervalIntegral.integral_mono_on hu0 (hH_cont.intervalIntegrable _ _)
            intervalIntegrable_const fun s hs => hH_le t ht s hs.1 (hs.2.trans hug)
      _ = u t * (Real.exp (-t) / h t) := by simp [mul_div_assoc]
      _ ≤ g 0 * (Real.exp (-t) / h 0) :=
          mul_le_mul (hug.trans (hg_le t ht.le))
            (div_le_div_of_nonneg_left (Real.exp_pos _).le hh0 (hh_ge t ht.le))
            (div_nonneg (Real.exp_pos _).le (hh_pos t ht.le).le) hg0.le
      _ = g 0 / h 0 * Real.exp (-t) := by ring
  have h_int₁ : IntegrableOn (fun t => G (u t)) (Ioi 0) :=
    Integrable.mono' ((integrableOn_exp_neg_Ioi 0).const_mul (g 0 / h 0))
      ((G.continuous.comp hu' fun t ht => (hu t (le_of_lt ht)).1).aestronglyMeasurable
        measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        rw [Real.norm_of_nonneg (G.maps_to (hu t (le_of_lt ht)).1)]
        exact h_Gu t ht)
  have h_int₂ : IntegrableOn (fun t => H (u t) * h t) (Ioi 0) :=
    Integrable.mono' (integrableOn_exp_neg_Ioi 0)
      (((hH_cont.comp_continuousOn hu').mul (hh_cont.mono Ioi_subset_Ici_self)).aestronglyMeasurable
        measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        rw [Real.norm_of_nonneg (show 0 ≤ H (u t) * h t from mul_nonneg
          (H'.maps_to (hu t (le_of_lt ht)).1) (hh_pos t (le_of_lt ht)).le)]
        exact h_Hu t ht)
  refine ⟨h_int₁, ?_, h_int₂, ?_⟩
  · calc ∫ t in Ioi 0, G (u t)
        ≤ ∫ t in Ioi 0, g 0 / h 0 * Real.exp (-t) :=
          setIntegral_mono_on h_int₁ ((integrableOn_exp_neg_Ioi 0).const_mul _) measurableSet_Ioi
            h_Gu
      _ = g 0 / h 0 := by rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  · calc ∫ t in Ioi 0, H (u t) * h t
        ≤ ∫ t in Ioi 0, Real.exp (-t) :=
          setIntegral_mono_on h_int₂ (integrableOn_exp_neg_Ioi 0) measurableSet_Ioi h_Hu
      _ = 1 := integral_exp_neg_Ioi_zero

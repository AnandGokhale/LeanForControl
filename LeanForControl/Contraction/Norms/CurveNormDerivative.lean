import LeanForControl.Contraction.Norms.RegularPairing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Architect

/-!
# `Contraction.Norms.CurveNormDerivative` — differentiating the norm along a curve

* `le_ofNorm`, `neg_ofNorm_neg_le` — the Deimling sandwich: every regular pairing lies between the
  left and the right derivative of the norm.
* `hasDerivWithinAt_norm_sq` — along a curve, the right derivative of `‖x(t)‖²` is `2 ⟦ẋ; x⟧` for
  the regular pairing of the norm.
* `hasDerivAt_norm_sq` — the curve norm derivative formula: wherever `‖x(t)‖²` is differentiable,
  its derivative is `2 ⟦ẋ; x⟧`, for every regular pairing.
* `norm_le_exp_integral_of_pairing_le` — if `⟦ẋ(r); x(r)⟧ ≤ b(r) ‖x(r)‖²` along a curve, then
  `‖x(t)‖ ≤ exp (∫_{t₀}^t b) ‖x(t₀)‖`.

References: A. V. Proskurnikov and F. Bullo, *Regular Pairings for Nonquadratic Lyapunov
Functions and Contraction Analysis*, SIAM J. Control Optim. 64(1):496–521 (2026),
doi:10.1137/24M1689685, Theorem 3.5 (iii) and (v), and Lemma A.1.
-/

open Set Filter Topology Asymptotics
open scoped LogNorm

namespace RegularPairing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Deimling's inequality**: every regular pairing lies below the regular pairing of the norm,
`⟦x; y⟧ ≤ ‖y‖ · d⁺/dh ‖y + h x‖ |_{h = 0}`. -/
@[blueprint "thm:regularPairing-le-ofNorm"
  (title := "Deimling's inequality")
  (statement := /-- For a regular pairing (\cref{def:regularPairing}) and the regular pairing
    $\pair{\cdot}{\cdot}_+$ of the norm (\cref{def:regularPairing-ofNorm}),
    \[ -\pair{-x}{y}_+ \le \pair{x}{y} \le \pair{x}{y}_+ \qquad \text{for all } x, y. \]

    Reference: Proskurnikov and Bullo, SIAM J. Control Optim. (2026), Theorem 3.5 (iii). -/)
  (proof := /-- By partial linearity and Cauchy--Schwarz, for $h > 0$,
    $h \pair{x}{y} + \|y\|^2 = \pair{y + h x}{y} \le \|y + h x\| \, \|y\|$, so
    $\pair{x}{y} \le \|y\| \, (\|y + h x\| - \|y\|)/h$; let $h \to 0^+$.  The lower bound is the
    upper bound for $-x$, with $0 = \pair{0}{y} \le \pair{x}{y} + \pair{-x}{y}$. -/)]
theorem le_ofNorm (p : RegularPairing E) (x y : E) : ⟦x; y⟧_p ≤ ⟦x; y⟧ := by
  refine ge_of_tendsto (((hasDerivWithinAt_iff_tendsto_slope' (s := Ioi 0)
    (lt_irrefl (0 : ℝ))).1 (hasDerivWithinAt_norm_add_smul x y)).const_mul ‖y‖) ?_
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  have h1 := p.add_smul_self (h • x) y 1
  rw [one_smul, p.smul_left h hh.le, add_comm (h • x)] at h1
  have h2 := p.le_norm_mul_norm (y + h • x) y
  rw [slope_def_field]
  simp only [zero_smul, add_zero, sub_zero]
  rw [mul_div_assoc', le_div_iff₀ hh]
  nlinarith

/-- The lower half of the Deimling sandwich, `-[-x, y]₊ ≤ ⟦x; y⟧`. -/
theorem neg_ofNorm_neg_le (p : RegularPairing E) (x y : E) : -⟦-x; y⟧ ≤ ⟦x; y⟧_p := by
  have h := p.add_left_le x (-x) y
  rw [add_neg_cancel, zero_left] at h
  linarith [p.le_ofNorm (-x) y]

/-- **The right derivative of the squared norm along a curve** is twice the regular pairing of the
norm: if `x` has right derivative `v` at `t`, then `‖x(·)‖²` has right derivative
`2 [v, x(t)]₊` there. -/
@[blueprint "lem:hasDerivWithinAt-norm-sq"
  (title := "Right derivative of the norm along a curve")
  (latexEnv := "lemma")
  (statement := /-- If a curve $x : \mathbb{R} \to X$ has right derivative $v$ at $t$, then
    $s \mapsto \|x(s)\|^2$ has right derivative $2 \pair{v}{x(t)}_+$ at $t$, where
    $\pair{\cdot}{\cdot}_+$ is the regular pairing of the norm
    (\cref{def:regularPairing-ofNorm}).

    Reference: Proskurnikov and Bullo, SIAM J. Control Optim. (2026), Lemma A.1. -/)
  (proof := /-- $\bigl| \|x(s)\| - \|x(t) + (s - t) v\| \bigr| \le \|x(s) - x(t) - (s - t) v\| =
    o(s - t)$, so $\|x(\cdot)\|$ has the right derivative of $s \mapsto \|x(t) + (s - t) v\|$, and
    the product rule gives the square. -/)]
theorem hasDerivWithinAt_norm_sq {x : ℝ → E} {v : E} {t : ℝ}
    (hx : HasDerivWithinAt x v (Ioi t) t) :
    HasDerivWithinAt (fun s => ‖x s‖ ^ 2) (2 * ⟦v; x t⟧) (Ioi t) t := by
  set D := derivWithin (fun h : ℝ => ‖x t + h • v‖) (Ioi 0) 0
  have hk : HasDerivWithinAt (fun s => ‖x t + (s - t) • v‖) D (Ioi t) t := by
    have := HasDerivWithinAt.scomp t
      (by rw [sub_self]; exact hasDerivWithinAt_norm_add_smul v (x t))
      ((hasDerivAt_id' t).sub_const t).hasDerivWithinAt
      (fun s (hs : t < s) => sub_pos.2 hs : MapsTo (· - t) (Ioi t) (Ioi 0))
    simpa only [Function.comp_def, one_smul] using this
  have hn : HasDerivWithinAt (fun s => ‖x s‖) D (Ioi t) t := by
    rw [hasDerivWithinAt_iff_isLittleO] at hx hk ⊢
    refine (hk.add (IsBigO.trans_isLittleO (IsBigO.of_bound 1
      (f := fun s => ‖x s‖ - ‖x t + (s - t) • v‖) (Eventually.of_forall fun s => ?_))
      hx)).congr_left fun s => ?_
    · rw [one_mul, Real.norm_eq_abs, ← sub_add_eq_sub_sub]
      exact abs_norm_sub_norm_le _ _
    · simp only [sub_self, zero_smul, add_zero]
      ring
  convert hn.mul hn using 1
  · ext s
    simp [sq]
  · rw [ofNorm_apply]
    ring

/-- **The curve norm derivative formula**: for every regular pairing, wherever `‖x(t)‖²` is
differentiable its derivative is `2 ⟦ẋ(t); x(t)⟧`. -/
@[blueprint "thm:hasDerivAt-norm-sq"
  (title := "Curve norm derivative formula")
  (statement := /-- Let $\pair{\cdot}{\cdot}$ be a regular pairing (\cref{def:regularPairing}) and
    $x : \mathbb{R} \to X$ differentiable at $t$.  If $s \mapsto \|x(s)\|^2$ is differentiable at
    $t$, then
    \[ \frac{d}{dt} \|x(t)\|^2 = 2 \pair{\dot x(t)}{x(t)}. \]

    Reference: Proskurnikov and Bullo, SIAM J. Control Optim. (2026), Theorem 3.5 (v). -/)
  (proof := /-- By \cref{lem:hasDerivWithinAt-norm-sq}, applied to $x$ and to the time-reversed
    curve $s \mapsto x(-s)$, the derivative equals both $2 \pair{\dot x}{x}_+$ and
    $-2 \pair{-\dot x}{x}_+$.  Deimling's inequality (\cref{thm:regularPairing-le-ofNorm}) puts
    $2 \pair{\dot x}{x}$ between them. -/)]
theorem hasDerivAt_norm_sq (p : RegularPairing E) {x : ℝ → E} {v : E} {t : ℝ}
    (hx : HasDerivAt x v t) (hd : DifferentiableAt ℝ (fun s => ‖x s‖ ^ 2) t) :
    HasDerivAt (fun s => ‖x s‖ ^ 2) (2 * ⟦v; x t⟧_p) t := by
  have hR := (uniqueDiffWithinAt_Ioi t).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt
    (hasDerivWithinAt_norm_sq hx.hasDerivWithinAt)
  have hx' : HasDerivAt x v (-(-t)) := by rwa [_root_.neg_neg]
  have hd' : HasDerivAt (fun s => ‖x s‖ ^ 2) (deriv (fun s => ‖x s‖ ^ 2) t) (-(-t)) := by
    rw [_root_.neg_neg]
    exact hd.hasDerivAt
  have hL := (uniqueDiffWithinAt_Ioi (-t)).eq_deriv _
    (hd'.scomp (-t) (hasDerivAt_neg (-t))).hasDerivWithinAt
    (hasDerivWithinAt_norm_sq (hx'.scomp (-t) (hasDerivAt_neg (-t))).hasDerivWithinAt)
  simp only [neg_smul, one_smul, _root_.neg_neg] at hL
  rw [show 2 * p v (x t) = deriv (fun s => ‖x s‖ ^ 2) t by
    linarith [p.le_ofNorm v (x t), p.neg_ofNorm_neg_le v (x t)]]
  exact hd.hasDerivAt

/-- **Exponential bound from a pairing bound**: if `⟦ẋ(r); x(r)⟧ ≤ b(r) ‖x(r)‖²` along a curve with
right derivatives, then `‖x(t)‖ ≤ exp (∫_{t₀}^t b) ‖x(t₀)‖`. -/
@[blueprint "thm:norm-le-exp-integral-of-pairing-le"
  (title := "Exponential bound from a pairing bound")
  (statement := /-- Let $b$ be continuous and $x$ continuous on $[t_0, t_1]$, with right
    derivative $w(r)$ at every $r \in [t_0, t_1)$ satisfying
    $\pair{w(r)}{x(r)} \le b(r) \|x(r)\|^2$ for the regular pairing of the norm
    (\cref{def:regularPairing-ofNorm}).  Then for $t \in [t_0, t_1]$
    \[ \|x(t)\| \le \exp\Bigl( \int_{t_0}^{t} b(\tau) \, d\tau \Bigr) \|x(t_0)\|. \] -/)
  (proof := /-- With $M(r) = \int_{t_0}^r b$, the function $e^{-2M} \|x\|^2$ has right derivative
    $e^{-2M}(-2 b \|x\|^2 + 2 \pair{w}{x}) \le 0$ (\cref{lem:hasDerivWithinAt-norm-sq}), so it is
    nonincreasing on $[t_0, t_1]$. -/)]
theorem norm_le_exp_integral_of_pairing_le {x w : ℝ → E} {b : ℝ → ℝ} {t₀ t₁ : ℝ}
    (hb : Continuous b) (hx : ContinuousOn x (Icc t₀ t₁))
    (hx' : ∀ r ∈ Ico t₀ t₁, HasDerivWithinAt x (w r) (Ici r) r)
    (hw : ∀ r ∈ Ico t₀ t₁, ⟦w r; x r⟧ ≤ b r * ‖x r‖ ^ 2) :
    ∀ t ∈ Icc t₀ t₁, ‖x t‖ ≤ Real.exp (∫ τ in t₀..t, b τ) * ‖x t₀‖ := by
  intro t ht
  set M : ℝ → ℝ := fun r => ∫ τ in t₀..r, b τ
  have hM (r : ℝ) : HasDerivAt M (b r) r := (hb.integral_hasStrictDerivAt t₀ r).hasDerivAt
  have hMc : Continuous M := continuous_iff_continuousAt.2 fun r => (hM r).continuousAt
  -- `g = e^{-2M} ‖x‖²` has a nonpositive right derivative, so `g t ≤ g t₀ = ‖x t₀‖²`
  set g : ℝ → ℝ := fun r => Real.exp (-(2 * M r)) * ‖x r‖ ^ 2
  have hle := image_le_of_deriv_right_le_deriv_boundary (f := g)
    (f' := fun r => Real.exp (-(2 * M r)) * (-(2 * b r)) * ‖x r‖ ^ 2 +
      Real.exp (-(2 * M r)) * (2 * ⟦w r; x r⟧))
    (B := fun _ => ‖x t₀‖ ^ 2) (B' := fun _ => 0) (a := t₀) (b := t)
    ((Real.continuous_exp.comp (continuous_const.mul hMc).neg).continuousOn.mul
      ((hx.mono (Icc_subset_Icc_right ht.2)).norm.pow 2))
    (fun r hr => (((hM r).const_mul 2).neg.exp).hasDerivWithinAt.mul
      (hasDerivWithinAt_Ioi_iff_Ici.1 (hasDerivWithinAt_norm_sq
        ((hx' r ⟨hr.1, hr.2.trans_le ht.2⟩).mono Ioi_subset_Ici_self))))
    (by simp [g, M]) continuousOn_const (fun r _ => hasDerivWithinAt_const _ _ _)
    (fun r hr => by
      have h := hw r ⟨hr.1, hr.2.trans_le ht.2⟩
      have he := Real.exp_pos (-(2 * M r))
      nlinarith) (right_mem_Icc.2 ht.1)
  -- `‖x t‖² ≤ e^{2 M t} ‖x t₀‖²`
  have hsq : ‖x t‖ ^ 2 ≤ (Real.exp (M t) * ‖x t₀‖) ^ 2 := by
    have h2 : Real.exp (-(2 * M t)) * Real.exp (M t) ^ 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have he := Real.exp_pos (-(2 * M t))
    simp only [g] at hle
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **Exponential bound from a pairing bound, with a forcing term**: if
`⟦ẋ(r); x(r)⟧ ≤ a(r) ‖x(r)‖² + b(r) ‖x(r)‖` along a curve with right derivatives, with `b ≥ 0`,
then `‖x(t)‖ ≤ exp (∫_{t₀}^t a) ‖x(t₀)‖ + ∫_{t₀}^t exp (∫_τ^t a) b(τ) dτ`. -/
@[blueprint "thm:norm-le-exp-integral-add-of-pairing-le"
  (title := "Exponential bound from a pairing bound, with a forcing term")
  (statement := /-- Let $a, b$ be continuous with $b \ge 0$, and $x$ continuous on $[t_0, t_1]$
    with right derivative $w(r)$ at every $r \in [t_0, t_1)$ satisfying
    $\pair{w(r)}{x(r)} \le a(r) \|x(r)\|^2 + b(r) \|x(r)\|$ for the regular pairing of the norm
    (\cref{def:regularPairing-ofNorm}).  Then for $t \in [t_0, t_1]$
    \[ \|x(t)\| \le e^{\int_{t_0}^{t} a} \|x(t_0)\|
      + \int_{t_0}^{t} e^{\int_{\tau}^{t} a} \, b(\tau) \, d\tau. \] -/)
  (proof := /-- For $\varepsilon > 0$ let $m_\varepsilon = \sqrt{\|x\|^2 + \varepsilon^2}$, which
    is positive and has right derivative $\pair{w}{x} / m_\varepsilon$
    (\cref{lem:hasDerivWithinAt-norm-sq}).  Since $\|x\| \le m_\varepsilon$ and
    $\|x\|^2 = m_\varepsilon^2 - \varepsilon^2$, this is at most
    $a m_\varepsilon + b + |a| \varepsilon$, so with $M = \int_{t_0} a$ the function
    $e^{-M} m_\varepsilon - \int_{t_0} e^{-M} (b + |a| \varepsilon)$ is nonincreasing.  As
    $\varepsilon \to 0$, $m_\varepsilon(t_0) \le \|x(t_0)\| + \varepsilon$ gives the bound. -/)]
theorem norm_le_exp_integral_add_of_pairing_le {x w : ℝ → E} {a b : ℝ → ℝ} {t₀ t₁ : ℝ}
    (ha : Continuous a) (hb : Continuous b) (hx : ContinuousOn x (Icc t₀ t₁))
    (hx' : ∀ r ∈ Ico t₀ t₁, HasDerivWithinAt x (w r) (Ici r) r)
    (hb0 : ∀ r ∈ Ico t₀ t₁, 0 ≤ b r)
    (hw : ∀ r ∈ Ico t₀ t₁, ⟦w r; x r⟧ ≤ a r * ‖x r‖ ^ 2 + b r * ‖x r‖) :
    ∀ t ∈ Icc t₀ t₁, ‖x t‖ ≤ Real.exp (∫ τ in t₀..t, a τ) * ‖x t₀‖ +
      ∫ τ in t₀..t, Real.exp (∫ σ in τ..t, a σ) * b τ := by
  intro t ht
  set M : ℝ → ℝ := fun r => ∫ τ in t₀..r, a τ
  have hM (r : ℝ) : HasDerivAt M (a r) r := (ha.integral_hasStrictDerivAt t₀ r).hasDerivAt
  have hMc : Continuous M := continuous_iff_continuousAt.2 fun r => (hM r).continuousAt
  have hEc : Continuous fun τ => Real.exp (-M τ) := Real.continuous_exp.comp hMc.neg
  -- for `ε > 0`, `m = √(‖x‖² + ε²)` satisfies `m t ≤ e^{M t} (m t₀ + ∫ e^{-M} (b + |a| ε))`
  have key (ε : ℝ) (hε : 0 < ε) : √(‖x t‖ ^ 2 + ε ^ 2) ≤ Real.exp (M t) *
      (√(‖x t₀‖ ^ 2 + ε ^ 2) + ∫ τ in t₀..t, Real.exp (-M τ) * (b τ + |a τ| * ε)) := by
    set m : ℝ → ℝ := fun r => √(‖x r‖ ^ 2 + ε ^ 2)
    have hpos (r : ℝ) : 0 < ‖x r‖ ^ 2 + ε ^ 2 := by positivity
    have hc : Continuous fun τ => Real.exp (-M τ) * (b τ + |a τ| * ε) :=
      hEc.mul (hb.add (ha.abs.mul continuous_const))
    have hle := image_le_of_deriv_right_le_deriv_boundary (f := fun r => Real.exp (-M r) * m r)
      (f' := fun r => Real.exp (-M r) * (-a r) * m r +
        Real.exp (-M r) * (2 * ⟦w r; x r⟧ / (2 * m r)))
      (B := fun r => m t₀ + ∫ τ in t₀..r, Real.exp (-M τ) * (b τ + |a τ| * ε))
      (B' := fun r => Real.exp (-M r) * (b r + |a r| * ε)) (a := t₀) (b := t)
      (hEc.continuousOn.mul
        ((((hx.mono (Icc_subset_Icc_right ht.2)).norm.pow 2).add continuousOn_const).sqrt))
      (fun r hr => ((hM r).neg.exp).hasDerivWithinAt.mul
        (((hasDerivWithinAt_Ioi_iff_Ici.1 (hasDerivWithinAt_norm_sq
          ((hx' r ⟨hr.1, hr.2.trans_le ht.2⟩).mono Ioi_subset_Ici_self))).add_const
            (ε ^ 2)).sqrt (hpos r).ne'))
      (by simp [M, m])
      ((continuous_const.add (continuous_iff_continuousAt.2 fun r =>
        (hc.integral_hasStrictDerivAt t₀ r).hasDerivAt.continuousAt)).continuousOn)
      (fun r _ => ((hc.integral_hasStrictDerivAt t₀ r).hasDerivAt.const_add _).hasDerivWithinAt)
      (fun r hr => by
        have hr' : r ∈ Ico t₀ t₁ := ⟨hr.1, hr.2.trans_le ht.2⟩
        have hmr : 0 < m r := Real.sqrt_pos.2 (hpos r)
        have hm2 : m r ^ 2 = ‖x r‖ ^ 2 + ε ^ 2 := Real.sq_sqrt (hpos r).le
        have hxm : ‖x r‖ ≤ m r := by
          simpa using Real.abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε) :
            ‖x r‖ ^ 2 ≤ ‖x r‖ ^ 2 + ε ^ 2)
        have hεm : ε ≤ m r := by
          simpa [abs_of_pos hε] using Real.abs_le_sqrt (le_add_of_nonneg_left (sq_nonneg ‖x r‖) :
            ε ^ 2 ≤ ‖x r‖ ^ 2 + ε ^ 2)
        -- `-a m + ⟦w; x⟧ / m ≤ b + |a| ε`, from `‖x‖² = m² - ε²`, `‖x‖ ≤ m` and `ε ≤ m`
        have hin : -a r * m r + ⟦w r; x r⟧ / m r ≤ b r + |a r| * ε := by
          rw [show -a r * m r + ⟦w r; x r⟧ / m r = (-a r * m r ^ 2 + ⟦w r; x r⟧) / m r by
            field_simp, div_le_iff₀ hmr]
          nlinarith [hw r hr', mul_le_mul_of_nonneg_left hxm (hb0 r hr'),
            mul_le_mul_of_nonneg_left hεm (mul_nonneg (abs_nonneg (a r)) hε.le),
            mul_le_mul_of_nonneg_right (neg_le_abs (a r)) (sq_nonneg ε),
            congrArg (fun z => a r * z) hm2]
        calc Real.exp (-M r) * (-a r) * m r + Real.exp (-M r) * (2 * ⟦w r; x r⟧ / (2 * m r))
            = Real.exp (-M r) * (-a r * m r + ⟦w r; x r⟧ / m r) := by
              rw [mul_div_mul_left _ _ two_ne_zero]; ring
          _ ≤ Real.exp (-M r) * (b r + |a r| * ε) :=
              mul_le_mul_of_nonneg_left hin (Real.exp_pos _).le)
      (right_mem_Icc.2 ht.1)
    -- multiply by `e^{M t}`
    have h1 : Real.exp (M t) * Real.exp (-M t) = 1 := by rw [← Real.exp_add]; simp
    calc m t = Real.exp (M t) * (Real.exp (-M t) * m t) := by rw [← mul_assoc, h1, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
  -- the forcing term in the form `∫ e^{∫_τ^t a} b`, and the `ε`-terms
  have hsplit (τ : ℝ) : ∫ σ in τ..t, a σ = M t - M τ :=
    (intervalIntegral.integral_interval_sub_left (ha.intervalIntegrable _ _)
      (ha.intervalIntegrable _ _)).symm
  have hT : ∫ τ in t₀..t, Real.exp (∫ σ in τ..t, a σ) * b τ =
      Real.exp (M t) * ∫ τ in t₀..t, Real.exp (-M τ) * b τ := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext τ
    rw [hsplit, sub_eq_add_neg, Real.exp_add]
    ring
  set K := ∫ τ in t₀..t, Real.exp (-M τ) * |a τ|
  have hK : 0 ≤ K := intervalIntegral.integral_nonneg ht.1 fun _ _ => by positivity
  have hI (ε : ℝ) : ∫ τ in t₀..t, Real.exp (-M τ) * (b τ + |a τ| * ε) =
      (∫ τ in t₀..t, Real.exp (-M τ) * b τ) + ε * K := by
    calc _ = ∫ τ in t₀..t, (Real.exp (-M τ) * b τ + ε * (Real.exp (-M τ) * |a τ|)) := by
          congr 1; ext τ; ring
      _ = _ := by
          have hf : IntervalIntegrable (fun τ => Real.exp (-M τ) * b τ) MeasureTheory.volume t₀ t :=
            (hEc.mul hb).intervalIntegrable _ _
          have hg : IntervalIntegrable (fun τ => ε * (Real.exp (-M τ) * |a τ|))
              MeasureTheory.volume t₀ t :=
            (continuous_const.mul (hEc.mul ha.abs)).intervalIntegrable _ _
          rw [intervalIntegral.integral_add hf hg, intervalIntegral.integral_const_mul]
  -- `ε → 0`: the bound up to `e^{M t} ε (1 + K)`, for every `ε > 0`
  rw [hT]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε := δ / (Real.exp (M t) * (1 + K))
  have hε : 0 < ε := div_pos hδ (mul_pos (Real.exp_pos _) (by linarith))
  have hεδ : Real.exp (M t) * (ε * (1 + K)) = δ := by
    simp only [ε]
    field_simp
  have hx₀ : √(‖x t₀‖ ^ 2 + ε ^ 2) ≤ ‖x t₀‖ + ε :=
    (Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (x t₀)] :
      ‖x t₀‖ ^ 2 + ε ^ 2 ≤ (‖x t₀‖ + ε) ^ 2)).trans_eq (Real.sqrt_sq (by positivity))
  have hxt : ‖x t‖ ≤ √(‖x t‖ ^ 2 + ε ^ 2) := by
    simpa using Real.abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε) :
      ‖x t‖ ^ 2 ≤ ‖x t‖ ^ 2 + ε ^ 2)
  have hk := key ε hε
  rw [hI] at hk
  have hE := Real.exp_pos (M t)
  nlinarith [mul_le_mul_of_nonneg_left hx₀ hE.le]

end RegularPairing

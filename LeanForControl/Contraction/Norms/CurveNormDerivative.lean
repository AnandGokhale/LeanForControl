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

end RegularPairing

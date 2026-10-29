import LeanForControl.Contraction.Norms.RegularPairing
import Architect

/-!
# `Contraction.Norms.CurveNormDerivative` — differentiating the norm along a curve

* `le_ofNorm`, `neg_ofNorm_neg_le` — the Deimling sandwich: every regular pairing lies between the
  left and the right derivative of the norm.
* `hasDerivWithinAt_norm_sq` — along a curve, the right derivative of `‖x(t)‖²` is `2 ⟦ẋ; x⟧` for
  the regular pairing of the norm.
* `hasDerivAt_norm_sq` — the curve norm derivative formula: wherever `‖x(t)‖²` is differentiable,
  its derivative is `2 ⟦ẋ; x⟧`, for every regular pairing.

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

end RegularPairing

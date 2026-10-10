import LeanForControl.Stability.DefsDiscrete
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.ProperSpace

import Architect

/-!
# `Stability.LyapunovDiscrete`

Lyapunov's direct method for autonomous discrete-time systems `x(k+1) = f(x(k))`.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems*, Encyclopedia of
Systems and Control Engineering, vol. 2 (2026), pp. 142–154, Theorem 2 (after Kellett and Braun
(2023) and Haddad and Chellaboina (2008)).

## Main results

The rows of Theorem 2 proved here, writing `ΔV(x) = V(f x) - V x`:

* **Stability** (`lyapunovStableDT_of_lyapunov`, row 1): `V > 0` and `ΔV ≤ 0` on `D \ {x_eq}`.
* **Local exponential stability** (`locallyExponentiallyStableDT_of_lyapunov`, row 4):
  `c₁ ‖x - x_eq‖ᵖ ≤ V x ≤ c₂ ‖x - x_eq‖ᵖ` and `ΔV ≤ -c₃ V` on `D`.
* **Global exponential stability** (`globallyExponentiallyStableDT_of_lyapunov`, row 4 with
  `D` the whole space).
* **Local asymptotic stability** (`localAsymptoticStableDT_of_lyapunov`, row 2): `V > 0` and
  `ΔV < 0` on `D \ {x_eq}`.
* **Global asymptotic stability** (`globalAsymptoticStableDT_of_lyapunov`, row 3): as row 2 on
  the whole space, with `V` radially unbounded.

## Continuity of `f`

Theorem 2 assumes no continuity of `f`, but every row except global exponential stability needs
some, for two different reasons.

* **S and LES: continuity at `x_eq`.**  A discrete-time trajectory can jump from inside a small
  ball to far outside it in one step without crossing the sphere in between, and nothing in
  `ΔV ≤ 0` prevents that.  On `ℝ`, with `V x = x² / (1 + x⁴)` and `f x = 1 / x²` for
  `0 < |x| < 1` (`f x = x` otherwise), `V` is positive definite and `ΔV ≤ 0` everywhere, yet
  `x₀ = 10⁻³` jumps to `x₁ = 10⁶`, so `0` is not stable.  Continuity at `x_eq` keeps one step
  from a small ball inside `D`.
* **LAS and GAS: continuity on `D`.**  `ΔV < 0` gives no rate of decrease, so the proof passes
  to a limit point `y` of the trajectory and needs `V (f y) = V y` there; without continuity at
  `y`, a trajectory can stall at a point where `V` would otherwise keep decreasing.  The
  counterexamples are in the docstrings of the two theorems.

The exponent `p` only needs to be positive; Theorem 2 asks for `p ≥ 1`.
-/

open Filter Topology Metric Set

variable {E : Type*} [NormedAddCommGroup E]

/-! ## Geometric decay from a Lyapunov sandwich -/

/-- Taking `p`-th roots in a Lyapunov sandwich: `c₁ yᵖ ≤ qᵏ c₂ zᵖ` gives
`y ≤ (c₂ / c₁)^(1/p) (q^(1/p))ᵏ z`. -/
private lemma le_of_rpow_sandwich {c₁ c₂ p q y z : ℝ} (k : ℕ) (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂)
    (hp : 0 < p) (hq : 0 ≤ q) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : c₁ * y ^ p ≤ q ^ k * (c₂ * z ^ p)) :
    y ≤ (c₂ / c₁) ^ p⁻¹ * (q ^ p⁻¹) ^ k * z := by
  -- Step 1. Divide by `c₁`: `yᵖ ≤ (c₂ / c₁) qᵏ zᵖ`.
  have h_pow : y ^ p ≤ c₂ / c₁ * q ^ k * z ^ p := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc₁]
    linarith
  -- Step 2. `(qᵏ)^(1/p) = (q^(1/p))ᵏ`.
  have h_comm : (q ^ k) ^ p⁻¹ = (q ^ p⁻¹) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq, ← Real.rpow_mul hq,
      mul_comm]
  -- Step 3. Take `p`-th roots of both sides.
  calc y = (y ^ p) ^ p⁻¹ := (Real.rpow_rpow_inv hy hp.ne').symm
    _ ≤ (c₂ / c₁ * q ^ k * z ^ p) ^ p⁻¹ :=
      Real.rpow_le_rpow (by positivity) h_pow (by positivity)
    _ = (c₂ / c₁) ^ p⁻¹ * (q ^ p⁻¹) ^ k * z := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
        (by positivity), h_comm, Real.rpow_rpow_inv hz hp.ne']

/-- `ΔV ≤ -c₃ V` is the one-step contraction `V (f x) ≤ (1 - c₃) V x`. -/
private lemma le_one_sub_mul_of_deltaV {a b c₃ : ℝ} (h : a - b ≤ -c₃ * b) :
    a ≤ (1 - c₃) * b := by
  linarith

/-! ## Global exponential stability -/

/-- **Lyapunov's theorem for global exponential stability (discrete time).**  If
`c₁ ‖x - x_eq‖ᵖ ≤ V x ≤ c₂ ‖x - x_eq‖ᵖ` and `ΔV x ≤ -c₃ V x` for every `x`, with
`0 < c₁ ≤ c₂`, `p > 0` and `0 < c₃ < 1`, then `x_eq` is globally exponentially stable, with rate
`ρ = (1 - c₃)^(1/p)` and constant `C = (c₂ / c₁)^(1/p)`.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems* (2026),
Theorem 2, row 4 with `𝒟 = ℝⁿ`.  They ask for `p ≥ 1`; `p > 0` suffices. -/
@[blueprint "thm:globallyExponentiallyStableDT-of-lyapunov"
  (title := "Lyapunov theorem for global exponential stability (discrete time)")
  (statement := /-- Let $0 < c_1 \le c_2$, $p > 0$ and $0 < c_3 < 1$, and let
    $V : E \to \mathbb{R}$ satisfy, for every $x$,
    \[
      c_1 \|x - x_{\mathrm{eq}}\|^{p} \le V(x) \le c_2 \|x - x_{\mathrm{eq}}\|^{p},
      \qquad
      \Delta V(x) = V(f(x)) - V(x) \le -c_3 V(x).
    \]
    Then $x_{\mathrm{eq}}$ is globally exponentially stable for $x_{k+1} = f(x_k)$
    (\cref{def:globallyExponentiallyStableDT}), with $C = (c_2/c_1)^{1/p}$ and
    $\rho = (1 - c_3)^{1/p}$.

    Reference: Jungers and van de Wouw, \emph{Discrete-time nonlinear control systems}
    (2026), Theorem 2, row 4 with $\mathcal{D} = \mathbb{R}^{n}$.  They ask for $p \ge 1$;
    $p > 0$ suffices. -/)
  (proof := /-- The decrease condition is $V(f(x)) \le (1 - c_3) V(x)$, so by induction
    $V(x_k) \le (1 - c_3)^{k} V(x_0)$.  Sandwiching,
    $c_1 \|x_k - x_{\mathrm{eq}}\|^{p} \le (1 - c_3)^{k} c_2 \|x_0 - x_{\mathrm{eq}}\|^{p}$, and
    taking $p$-th roots gives the geometric bound. -/)]
theorem globallyExponentiallyStableDT_of_lyapunov {f : E → E} {x_eq : E} {V : E → ℝ}
    {c₁ c₂ c₃ p : ℝ} (hc₁ : 0 < c₁) (hc₁₂ : c₁ ≤ c₂) (hp : 0 < p) (hc₃ : 0 < c₃)
    (hc₃_lt : c₃ < 1)
    (hV_lower : ∀ x, c₁ * ‖x - x_eq‖ ^ p ≤ V x) (hV_upper : ∀ x, V x ≤ c₂ * ‖x - x_eq‖ ^ p)
    (hΔV : ∀ x, V (f x) - V x ≤ -c₃ * V x) :
    GloballyExponentiallyStableDT f x_eq := by
  /- `V` contracts by `q = 1 - c₃` at every step, and the sandwich turns the contraction of `V`
     into a geometric bound on the distance to `x_eq`. -/
  set q := 1 - c₃ with hq_def
  have hq_pos : 0 < q := by linarith
  -- Step 1. `V(x_k) ≤ qᵏ V(x₀)`, by induction on `k`.
  have hV_iter : ∀ x₀ : E, ∀ k : ℕ, V (f^[k] x₀) ≤ q ^ k * V x₀ := by
    intro x₀ k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', pow_succ']
      calc V (f (f^[k] x₀)) ≤ q * V (f^[k] x₀) := le_one_sub_mul_of_deltaV (hΔV _)
        _ ≤ q * (q ^ k * V x₀) := by gcongr
        _ = q * q ^ k * V x₀ := by ring
  -- Step 2. Sandwich and take `p`-th roots.
  refine ⟨(c₂ / c₁) ^ p⁻¹, Real.rpow_pos_of_pos (div_pos (hc₁.trans_le hc₁₂) hc₁) _,
    q ^ p⁻¹, Real.rpow_pos_of_pos hq_pos _,
    Real.rpow_lt_one hq_pos.le (by linarith) (inv_pos.mpr hp), fun x₀ k => ?_⟩
  have h_sandwich : c₁ * ‖f^[k] x₀ - x_eq‖ ^ p ≤ q ^ k * (c₂ * ‖x₀ - x_eq‖ ^ p) :=
    (hV_lower _).trans ((hV_iter x₀ k).trans (by gcongr; exact hV_upper x₀))
  exact le_of_rpow_sandwich k hc₁ (hc₁.le.trans hc₁₂) hp hq_pos.le (norm_nonneg _)
    (norm_nonneg _) h_sandwich

/-! ## Local exponential stability -/

/-- **Lyapunov's theorem for local exponential stability (discrete time).**  Let `D` be an open
neighbourhood of the fixed point `x_eq`, with `f` continuous at `x_eq`.  If
`c₁ ‖x - x_eq‖ᵖ ≤ V x ≤ c₂ ‖x - x_eq‖ᵖ` and `ΔV x ≤ -c₃ V x` for every `x ∈ D`, with
`0 < c₁ ≤ c₂`, `p > 0` and `0 < c₃ < 1`, then `x_eq` is locally exponentially stable.

Continuity of `f` at `x_eq` is not in Theorem 2 but is needed: see the module docstring.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems* (2026),
Theorem 2, row 4 with `𝒟 ⊊ ℝⁿ`. -/
@[blueprint "thm:locallyExponentiallyStableDT-of-lyapunov"
  (title := "Lyapunov theorem for local exponential stability (discrete time)")
  (statement := /-- Let $\mathcal{D}$ be an open set containing $x_{\mathrm{eq}}$, with
    $f(x_{\mathrm{eq}}) = x_{\mathrm{eq}}$ and $f$ continuous at $x_{\mathrm{eq}}$.  Let
    $0 < c_1 \le c_2$, $p > 0$ and $0 < c_3 < 1$, and let $V : E \to \mathbb{R}$ satisfy, for
    every $x \in \mathcal{D}$,
    \[
      c_1 \|x - x_{\mathrm{eq}}\|^{p} \le V(x) \le c_2 \|x - x_{\mathrm{eq}}\|^{p},
      \qquad
      \Delta V(x) \le -c_3 V(x).
    \]
    Then $x_{\mathrm{eq}}$ is locally exponentially stable
    (\cref{def:locallyExponentiallyStableDT}).

    Continuity of $f$ at $x_{\mathrm{eq}}$ is not among the hypotheses of the reference, but
    without it a trajectory can leave $\mathcal{D}$ in a single step.

    Reference: Jungers and van de Wouw, \emph{Discrete-time nonlinear control systems}
    (2026), Theorem 2, row 4 with $\mathcal{D} \subsetneq \mathbb{R}^{n}$. -/)
  (proof := /-- Choose $r_0 > 0$ so that the ball $B(x_{\mathrm{eq}}, r_0)$ lies in
    $\mathcal{D}$ and $f$ maps it into $\mathcal{D}$, and let $C = (c_2/c_1)^{1/p} \ge 1$ and
    $\delta = r_0 / (2C)$.  By induction, a trajectory with
    $\|x_0 - x_{\mathrm{eq}}\| \le \delta$ stays in $B(x_{\mathrm{eq}}, r_0)$ and satisfies
    $V(x_k) \le (1 - c_3)^{k} V(x_0)$: the decrease applies at $x_k \in \mathcal{D}$, and
    $x_{k+1} = f(x_k) \in \mathcal{D}$, so the sandwich gives
    $\|x_{k+1} - x_{\mathrm{eq}}\| \le C\delta = r_0/2$.  The geometric bound then follows as
    in \cref{thm:globallyExponentiallyStableDT-of-lyapunov}. -/)]
theorem locallyExponentiallyStableDT_of_lyapunov {f : E → E} {x_eq : E} {V : E → ℝ}
    {D : Set E} {c₁ c₂ c₃ p : ℝ} (hD : IsOpen D) (hx_eq : x_eq ∈ D) (hf_eq : f x_eq = x_eq)
    (hf_cont : ContinuousAt f x_eq) (hc₁ : 0 < c₁) (hc₁₂ : c₁ ≤ c₂) (hp : 0 < p)
    (hc₃ : 0 < c₃) (hc₃_lt : c₃ < 1)
    (hV_lower : ∀ x ∈ D, c₁ * ‖x - x_eq‖ ^ p ≤ V x)
    (hV_upper : ∀ x ∈ D, V x ≤ c₂ * ‖x - x_eq‖ ^ p)
    (hΔV : ∀ x ∈ D, V (f x) - V x ≤ -c₃ * V x) :
    LocallyExponentiallyStableDT f x_eq := by
  /- As in the global case, but the decrease and the sandwich only hold on `D`.  Continuity of
     `f` at `x_eq` keeps one step from a small ball inside `D`, and the sandwich then keeps the
     trajectory in that ball. -/
  set q := 1 - c₃ with hq_def
  have hq_pos : 0 < q := by linarith
  have hc₂ : 0 < c₂ := hc₁.trans_le hc₁₂
  -- Step 1. A radius `r₀` such that `B(x_eq, r₀) ⊆ D` and `f (B(x_eq, r₀)) ⊆ D`.
  obtain ⟨r, hr, h_ball_D⟩ := Metric.isOpen_iff.mp hD x_eq hx_eq
  obtain ⟨r', hr', h_step⟩ := Metric.continuousAt_iff.mp hf_cont r hr
  set r₀ := min r r' with hr₀_def
  have hr₀ : 0 < r₀ := lt_min hr hr'
  have h_mem_D : ∀ x, ‖x - x_eq‖ < r₀ → x ∈ D := fun x hx =>
    h_ball_D (mem_ball_iff_norm.mpr (hx.trans_le (min_le_left _ _)))
  have h_step_D : ∀ x, ‖x - x_eq‖ < r₀ → f x ∈ D := fun x hx => by
    have h := h_step (x := x) (by rw [dist_eq_norm]; exact hx.trans_le (min_le_right _ _))
    rw [hf_eq] at h
    exact h_ball_D h
  -- Step 2. The constants `C = (c₂ / c₁)^(1/p) ≥ 1`, `ρ = q^(1/p) < 1` and `δ = r₀ / (2C)`.
  set C := (c₂ / c₁) ^ p⁻¹ with hC_def
  set ρ := q ^ p⁻¹ with hρ_def
  have hC_one : 1 ≤ C := Real.one_le_rpow ((one_le_div hc₁).mpr hc₁₂) (inv_pos.mpr hp).le
  have hC_pos : 0 < C := one_pos.trans_le hC_one
  have hρ_pos : 0 < ρ := Real.rpow_pos_of_pos hq_pos _
  have hρ_lt : ρ < 1 := Real.rpow_lt_one hq_pos.le (by linarith) (inv_pos.mpr hp)
  set δ := r₀ / (2 * C) with hδ_def
  have hδ_pos : 0 < δ := div_pos hr₀ (by positivity)
  have hCδ : C * δ = r₀ / 2 := by rw [hδ_def]; field_simp
  have hδ_lt : δ < r₀ := by
    calc δ ≤ C * δ := le_mul_of_one_le_left hδ_pos.le hC_one
      _ = r₀ / 2 := hCδ
      _ < r₀ := half_lt_self hr₀
  -- Step 3. From a `δ`-start the trajectory stays in `B(x_eq, r₀)` and `V` contracts by `q`.
  have h_traj : ∀ x₀ : E, ‖x₀ - x_eq‖ ≤ δ → ∀ k : ℕ,
      ‖f^[k] x₀ - x_eq‖ < r₀ ∧ V (f^[k] x₀) ≤ q ^ k * V x₀ := by
    intro x₀ hx₀ k
    have hx₀_D : x₀ ∈ D := h_mem_D x₀ (hx₀.trans_lt hδ_lt)
    induction k with
    | zero => exact ⟨by simpa using hx₀.trans_lt hδ_lt, by simp⟩
    | succ k ih =>
      obtain ⟨h_in, h_V⟩ := ih
      rw [Function.iterate_succ_apply']
      -- the decrease applies at `x_k ∈ D`
      have h_V_succ : V (f (f^[k] x₀)) ≤ q ^ (k + 1) * V x₀ := by
        rw [pow_succ']
        calc V (f (f^[k] x₀)) ≤ q * V (f^[k] x₀) :=
              le_one_sub_mul_of_deltaV (hΔV _ (h_mem_D _ h_in))
          _ ≤ q * (q ^ k * V x₀) := by gcongr
          _ = q * q ^ k * V x₀ := by ring
      -- `x_{k+1} = f x_k ∈ D`, so the sandwich bounds its distance by `C ρ^(k+1) δ ≤ r₀ / 2`
      have h_sandwich : c₁ * ‖f (f^[k] x₀) - x_eq‖ ^ p ≤ q ^ (k + 1) * (c₂ * ‖x₀ - x_eq‖ ^ p) :=
        (hV_lower _ (h_step_D _ h_in)).trans (h_V_succ.trans (by gcongr; exact hV_upper x₀ hx₀_D))
      have h_dist := le_of_rpow_sandwich (k + 1) hc₁ hc₂.le hp hq_pos.le (norm_nonneg _)
        (norm_nonneg _) h_sandwich
      refine ⟨?_, h_V_succ⟩
      calc ‖f (f^[k] x₀) - x_eq‖ ≤ C * ρ ^ (k + 1) * ‖x₀ - x_eq‖ := h_dist
        _ ≤ C * 1 * δ := by
          gcongr
          exact pow_le_one₀ hρ_pos.le hρ_lt.le
        _ = r₀ / 2 := by rw [mul_one, hCδ]
        _ < r₀ := half_lt_self hr₀
  -- Step 4. The geometric bound, from the sandwich at `x_k ∈ D`.
  refine ⟨δ, hδ_pos, C, hC_pos, ρ, hρ_pos, hρ_lt, fun x₀ hx₀ k => ?_⟩
  obtain ⟨h_in, h_V⟩ := h_traj x₀ hx₀ k
  have hx₀_D : x₀ ∈ D := h_mem_D x₀ (hx₀.trans_lt hδ_lt)
  exact le_of_rpow_sandwich k hc₁ hc₂.le hp hq_pos.le (norm_nonneg _) (norm_nonneg _)
    ((hV_lower _ (h_mem_D _ h_in)).trans (h_V.trans (by gcongr; exact hV_upper x₀ hx₀_D)))

/-! ## Stability -/

/-- **Lyapunov's stability theorem (discrete time).**  Let `D` be an open neighbourhood of the
fixed point `x_eq` in a finite-dimensional (proper) space, with `f` continuous at `x_eq`.  If
`V` is continuous on `D`, vanishes at `x_eq`, is positive on `D \ {x_eq}`, and
`ΔV x ≤ 0` there, then `x_eq` is stable.

Continuity of `f` at `x_eq` is not in Theorem 2 but is needed: see the module docstring.
Properness gives a positive minimum of `V` on a compact annulus around `x_eq`.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems* (2026),
Theorem 2, row 1. -/
@[blueprint "thm:lyapunovStableDT-of-lyapunov"
  (title := "Lyapunov's stability theorem (discrete time)")
  (statement := /-- Let $E$ be finite-dimensional, $\mathcal{D} \subseteq E$ an open set
    containing $x_{\mathrm{eq}}$, with $f(x_{\mathrm{eq}}) = x_{\mathrm{eq}}$ and $f$ continuous
    at $x_{\mathrm{eq}}$.  Let $V$ be continuous on $\mathcal{D}$ with
    $V(x_{\mathrm{eq}}) = 0$ and, for every $x \in \mathcal{D} \setminus \{x_{\mathrm{eq}}\}$,
    \[
      V(x) > 0, \qquad \Delta V(x) = V(f(x)) - V(x) \le 0.
    \]
    Then $x_{\mathrm{eq}}$ is stable (\cref{def:lyapunovStableDT}).

    Continuity of $f$ at $x_{\mathrm{eq}}$ is not among the hypotheses of the reference, but it
    cannot be dropped: on $\mathbb{R}$, $V(x) = x^2/(1 + x^4)$ and $f(x) = 1/x^2$ for
    $0 < |x| < 1$ ($f(x) = x$ otherwise) satisfy everything else, yet $x_0 = 10^{-3}$ jumps to
    $x_1 = 10^{6}$.

    Reference: Jungers and van de Wouw, \emph{Discrete-time nonlinear control systems}
    (2026), Theorem 2, row 1. -/)
  (proof := /-- Given $\varepsilon$, shrink it so that the closed ball of radius
    $\varepsilon'$ lies in $\mathcal{D}$, and choose $s \le \varepsilon'$ so that $f$ maps the
    ball of radius $s$ into the ball of radius $\varepsilon'$.  On the compact annulus
    $s \le \|x - x_{\mathrm{eq}}\| \le \varepsilon'$, $V$ has a positive minimum $m$; choose
    $\delta < s$ with $V < m$ on the ball of radius $\delta$.  By induction, a trajectory with
    $\|x_0 - x_{\mathrm{eq}}\| \le \delta$ keeps $\|x_k - x_{\mathrm{eq}}\| < s$ and
    $V(x_k) < m$: the next state is within $\varepsilon'$ by the choice of $s$, has
    $V(x_{k+1}) \le V(x_k) < m$, and so cannot lie in the annulus. -/)]
theorem lyapunovStableDT_of_lyapunov [ProperSpace E] {f : E → E} {x_eq : E} {V : E → ℝ}
    {D : Set E} (hD : IsOpen D) (hx_eq : x_eq ∈ D) (hf_eq : f x_eq = x_eq)
    (hf_cont : ContinuousAt f x_eq) (hV_cont : ContinuousOn V D) (hV_zero : V x_eq = 0)
    (hV_pos : ∀ x ∈ D, x ≠ x_eq → 0 < V x)
    (hΔV : ∀ x ∈ D, x ≠ x_eq → V (f x) - V x ≤ 0) :
    LyapunovStableDT f x_eq := by
  /- The continuous-time argument stops a trajectory at the first time it reaches a sphere; in
     discrete time it could jump over the sphere instead.  Continuity of `f` at `x_eq` rules
     that out for one step from a small ball, and a level set of `V` below its minimum on an
     annulus then traps the trajectory in that ball. -/
  intro ε hε
  -- Step 1. Radii `s ≤ ε' ≤ ε` with `closedBall x_eq ε' ⊆ D` and `f (ball x_eq s) ⊆ ball x_eq ε'`.
  obtain ⟨r, hr, h_ball_D⟩ := Metric.isOpen_iff.mp hD x_eq hx_eq
  set ε' := min ε (r / 2) with hε'_def
  have hε' : 0 < ε' := lt_min hε (half_pos hr)
  have h_closedBall_D : closedBall x_eq ε' ⊆ D := fun x hx =>
    h_ball_D ((mem_closedBall.mp hx).trans_lt ((min_le_right _ _).trans_lt (half_lt_self hr)))
  obtain ⟨r', hr', h_step⟩ := Metric.continuousAt_iff.mp hf_cont ε' hε'
  set s := min r' ε' / 2 with hs_def
  have hs : 0 < s := half_pos (lt_min hr' hε')
  have hs_lt_r' : s < r' := (half_lt_self (lt_min hr' hε')).trans_le (min_le_left _ _)
  have hs_lt_ε' : s < ε' := (half_lt_self (lt_min hr' hε')).trans_le (min_le_right _ _)
  -- Step 2. `V` has a positive lower bound `m` on the annulus `A = {s ≤ ‖x - x_eq‖ ≤ ε'}`.
  set A := closedBall x_eq ε' \ ball x_eq s with hA_def
  have hA_D : A ⊆ D := diff_subset.trans h_closedBall_D
  have hA_ne : ∀ x ∈ A, x ≠ x_eq := fun x hx h_eq => hx.2 (h_eq ▸ mem_ball_self hs)
  obtain ⟨m, hm_pos, hm_le⟩ : ∃ m > 0, ∀ x ∈ A, m ≤ V x := by
    by_cases hA : A.Nonempty
    · obtain ⟨x_min, hx_min, h_min⟩ :=
        (isCompact_closedBall x_eq ε' |>.diff isOpen_ball).exists_isMinOn hA (hV_cont.mono hA_D)
      exact ⟨V x_min, hV_pos _ (hA_D hx_min) (hA_ne _ hx_min), fun x hx => h_min hx⟩
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hA⟩
  -- Step 3. `δ < s` such that `V < m` on `closedBall x_eq δ`, by continuity of `V` at `x_eq`.
  obtain ⟨η, hη, h_V_small⟩ :=
    Metric.continuousAt_iff.mp (hV_cont.continuousAt (hD.mem_nhds hx_eq)) m hm_pos
  set δ := min η s / 2 with hδ_def
  have hδ : 0 < δ := half_pos (lt_min hη hs)
  have hδ_lt_η : δ < η := (half_lt_self (lt_min hη hs)).trans_le (min_le_left _ _)
  have hδ_lt_s : δ < s := (half_lt_self (lt_min hη hs)).trans_le (min_le_right _ _)
  refine ⟨δ, hδ, fun x₀ hx₀ k => ?_⟩
  -- Step 4. By induction, `‖x_k - x_eq‖ < s` and `V(x_k) < m`.
  have h_trap : ∀ k : ℕ, ‖f^[k] x₀ - x_eq‖ < s ∧ V (f^[k] x₀) < m := by
    intro k
    induction k with
    | zero =>
      have h_V₀ := h_V_small (x := x₀) (by rw [dist_eq_norm]; exact hx₀.trans_lt hδ_lt_η)
      rw [hV_zero, Real.dist_eq, sub_zero] at h_V₀
      exact ⟨by simpa using hx₀.trans_lt hδ_lt_s, by simpa using (le_abs_self _).trans_lt h_V₀⟩
    | succ k ih =>
      obtain ⟨h_in, h_V⟩ := ih
      rw [Function.iterate_succ_apply']
      set y := f^[k] x₀ with hy_def
      have hy_D : y ∈ D :=
        h_closedBall_D (mem_closedBall_iff_norm.mpr (h_in.trans hs_lt_ε').le)
      -- one step from the ball of radius `s` lands within `ε'` of `x_eq`
      have h_fy_near : ‖f y - x_eq‖ < ε' := by
        have h := h_step (x := y) (by rw [dist_eq_norm]; exact h_in.trans hs_lt_r')
        rwa [hf_eq, dist_eq_norm] at h
      -- `V` does not increase along the step
      have h_V_fy : V (f y) < m := by
        rcases eq_or_ne y x_eq with h_eq | h_ne
        · rw [h_eq, hf_eq, hV_zero]; exact hm_pos
        · linarith [hΔV y hy_D h_ne]
      -- so `f y` is not in the annulus, hence within `s` of `x_eq`
      refine ⟨?_, h_V_fy⟩
      by_contra h_far
      have h_fy_A : f y ∈ A :=
        ⟨mem_closedBall_iff_norm.mpr h_fy_near.le, fun h => h_far (mem_ball_iff_norm.mp h)⟩
      exact (hm_le _ h_fy_A).not_gt h_V_fy
  exact ((h_trap k).1.trans (hs_lt_ε'.trans_le (min_le_left _ _))).le

/-! ## Asymptotic stability -/

/-- **The ω-limit argument.**  If a trajectory stays in a compact set `K` on which `f` and `V`
are continuous, `V` does not increase along `f`, and strictly decreases away from `x_eq`, then
the trajectory converges to `x_eq`.

`V(x_k)` is nonincreasing and bounded below on `K`, so it converges to some `L`.  Any cluster
point `y` of the trajectory has `V y = L`, and by continuity of `f` at `y` so does `f y`; strict
decrease away from `x_eq` then forces `y = x_eq`.  A sequence in a compact set whose only cluster
point is `x_eq` converges to it. -/
private lemma tendsto_of_lyapunov_strict_decrease [ProperSpace E] {f : E → E} {x_eq : E}
    {V : E → ℝ} {K : Set E} (hK : IsCompact K) (hf_cont : ∀ y ∈ K, ContinuousAt f y)
    (hV_cont : ∀ y ∈ K, ContinuousAt V y) (h_dec : ∀ x ∈ K, V (f x) ≤ V x)
    (h_strict : ∀ x ∈ K, x ≠ x_eq → V (f x) < V x) {x₀ : E}
    (h_in : ∀ k : ℕ, f^[k] x₀ ∈ K) :
    Tendsto (fun k : ℕ => f^[k] x₀) atTop (𝓝 x_eq) := by
  set x : ℕ → E := fun k => f^[k] x₀ with hx_def
  have hx_succ : ∀ k, x (k + 1) = f (x k) := fun k => Function.iterate_succ_apply' f k x₀
  -- Step 1. `V(x_k)` is nonincreasing and bounded below, so it converges to `L`.
  have hVx_anti : Antitone (fun k => V (x k)) :=
    antitone_nat_of_succ_le fun k => by rw [hx_succ]; exact h_dec _ (h_in k)
  have hVx_bdd : BddBelow (Set.range fun k => V (x k)) := by
    obtain ⟨b, hb⟩ := hK.bddBelow_image (continuousOn_of_forall_continuousAt hV_cont)
    exact ⟨b, by rintro _ ⟨k, rfl⟩; exact hb ⟨x k, h_in k, rfl⟩⟩
  set L := ⨅ k, V (x k) with hL_def
  have hL : Tendsto (fun k => V (x k)) atTop (𝓝 L) := tendsto_atTop_ciInf hVx_anti hVx_bdd
  -- Step 2. Every cluster point of the trajectory is `x_eq`.
  refine hK.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall h_in) fun y hyK hy => ?_
  obtain ⟨ψ, hψ, hψ_tendsto⟩ := hy.tendsto_subseq
  -- `V y = L`: along the subsequence, `V(x_{ψ j}) → V y` and `→ L`
  have hVy : V y = L :=
    tendsto_nhds_unique ((hV_cont y hyK).tendsto.comp hψ_tendsto) (hL.comp hψ.tendsto_atTop)
  -- the next states `x_{ψ j + 1} = f(x_{ψ j})` converge to `f y`, which lies in `K`
  have hfy_tendsto : Tendsto (fun j => x (ψ j + 1)) atTop (𝓝 (f y)) := by
    simp_rw [hx_succ]
    exact (hf_cont y hyK).tendsto.comp hψ_tendsto
  have hfyK : f y ∈ K :=
    hK.isClosed.mem_of_tendsto hfy_tendsto (Eventually.of_forall fun j => h_in _)
  -- `V (f y) = L`: along the shifted subsequence, `V(x_{ψ j + 1}) → V (f y)` and `→ L`
  have hVfy : V (f y) = L :=
    tendsto_nhds_unique ((hV_cont _ hfyK).tendsto.comp hfy_tendsto)
      ((hL.comp (tendsto_add_atTop_nat 1)).comp hψ.tendsto_atTop)
  -- so `V` does not decrease at `y`, which forces `y = x_eq`
  by_contra hne
  exact (h_strict y hyK hne).ne (hVfy.trans hVy.symm)

/-- **Lyapunov's theorem for local asymptotic stability (discrete time).**  Let `D` be an open
neighbourhood of the fixed point `x_eq` in a finite-dimensional (proper) space, with `f` and `V`
continuous on `D`.  If `V` vanishes at `x_eq` and `V > 0`, `ΔV < 0` on `D \ {x_eq}`, then
`x_eq` is locally asymptotically stable.

Continuity of `f` on `D` is not in Theorem 2 but cannot be dropped: a discontinuity lets a
trajectory stall at a point where `V` would otherwise keep decreasing.  On `ℝ` with
`V x = |x|`, let `f` be odd with `f 0 = 0`, `f x = x / 2` for `x > 1`, and
`f x = (2⁻ⁿ⁻¹ + x) / 2` on each interval `(2⁻ⁿ⁻¹, 2⁻ⁿ]`.  Then `|f x| < |x|` for `x ≠ 0`, but a
trajectory starting in `(2⁻ⁿ⁻¹, 2⁻ⁿ]` stays there and converges to `2⁻ⁿ⁻¹`.  Such stalls occur
at every scale, so no neighbourhood of `0` is attracted to it.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems* (2026),
Theorem 2, row 2. -/
@[blueprint "thm:localAsymptoticStableDT-of-lyapunov"
  (title := "Lyapunov theorem for local asymptotic stability (discrete time)")
  (statement := /-- Let $E$ be finite-dimensional, $\mathcal{D} \subseteq E$ an open set
    containing $x_{\mathrm{eq}}$, with $f(x_{\mathrm{eq}}) = x_{\mathrm{eq}}$ and $f$, $V$
    continuous on $\mathcal{D}$.  If $V(x_{\mathrm{eq}}) = 0$ and, for every
    $x \in \mathcal{D} \setminus \{x_{\mathrm{eq}}\}$,
    \[
      V(x) > 0, \qquad \Delta V(x) = V(f(x)) - V(x) < 0,
    \]
    then $x_{\mathrm{eq}}$ is locally asymptotically stable
    (\cref{def:localAsymptoticStableDT}).

    Continuity of $f$ on $\mathcal{D}$ is not among the hypotheses of the reference, but it
    cannot be dropped.  With $V(x) = |x|$ on $\mathbb{R}$, let $f$ be odd with $f(0) = 0$ and
    $f(x) = (2^{-n-1} + x)/2$ on each interval $(2^{-n-1}, 2^{-n}]$: then $\Delta V < 0$ away
    from $0$, but a trajectory starting in $(2^{-n-1}, 2^{-n}]$ converges to $2^{-n-1}$, at
    every scale.

    Reference: Jungers and van de Wouw, \emph{Discrete-time nonlinear control systems}
    (2026), Theorem 2, row 2. -/)
  (proof := /-- Stability is \cref{thm:lyapunovStableDT-of-lyapunov}.  For attractivity, choose
    a closed ball $K \subseteq \mathcal{D}$ around $x_{\mathrm{eq}}$ and, by stability, a
    $\delta$ whose trajectories stay in $K$.  Along such a trajectory $V(x_k)$ is nonincreasing
    and bounded below, so it converges to some $L$.  A cluster point $y$ of the trajectory, which
    exists in the compact set $K$, has $V(y) = L$; by continuity of $f$ at $y$,
    $x_{k+1} = f(x_k)$ clusters at $f(y)$, so $V(f(y)) = L$ too.  Then $\Delta V(y) = 0$, so
    $y = x_{\mathrm{eq}}$.  A sequence in a compact set whose only cluster point is
    $x_{\mathrm{eq}}$ converges to it. -/)]
theorem localAsymptoticStableDT_of_lyapunov [ProperSpace E] {f : E → E} {x_eq : E}
    {V : E → ℝ} {D : Set E} (hD : IsOpen D) (hx_eq : x_eq ∈ D) (hf_eq : f x_eq = x_eq)
    (hf_cont : ContinuousOn f D) (hV_cont : ContinuousOn V D) (hV_zero : V x_eq = 0)
    (hV_pos : ∀ x ∈ D, x ≠ x_eq → 0 < V x)
    (hΔV : ∀ x ∈ D, x ≠ x_eq → V (f x) - V x < 0) :
    LocalAsymptoticStableDT f x_eq := by
  -- Step 1. Stability, from the non-strict version.
  have h_stable : LyapunovStableDT f x_eq :=
    lyapunovStableDT_of_lyapunov hD hx_eq hf_eq (hf_cont.continuousAt (hD.mem_nhds hx_eq))
      hV_cont hV_zero hV_pos fun x hx hne => (hΔV x hx hne).le
  refine ⟨h_stable, ?_⟩
  -- Step 2. A closed ball `K ⊆ D` and a `δ` whose trajectories stay in `K`.
  obtain ⟨r, hr, h_ball_D⟩ := Metric.isOpen_iff.mp hD x_eq hx_eq
  set K := closedBall x_eq (r / 2) with hK_def
  have hK_D : K ⊆ D := fun x hx =>
    h_ball_D ((mem_closedBall.mp hx).trans_lt (half_lt_self hr))
  obtain ⟨δ, hδ, h_stay⟩ := h_stable (r / 2) (half_pos hr)
  refine ⟨δ, hδ, fun x₀ hx₀ => ?_⟩
  -- Step 3. The ω-limit argument on `K`.
  refine tendsto_of_lyapunov_strict_decrease (isCompact_closedBall x_eq (r / 2))
    (fun y hy => hf_cont.continuousAt (hD.mem_nhds (hK_D hy)))
    (fun y hy => hV_cont.continuousAt (hD.mem_nhds (hK_D hy))) (fun x hx => ?_)
    (fun x hx hne => by linarith [hΔV x (hK_D hx) hne])
    (fun k => mem_closedBall_iff_norm.mpr (h_stay x₀ hx₀ k))
  -- `V` does not increase on `K`: at `x_eq` it is fixed, elsewhere it strictly decreases
  rcases eq_or_ne x x_eq with rfl | hne
  · rw [hf_eq]
  · linarith [hΔV x (hK_D hx) hne]

/-- **Lyapunov's theorem for global asymptotic stability (discrete time).**  In a
finite-dimensional (proper) space, let `f` and `V` be continuous with `f x_eq = x_eq`,
`V x_eq = 0`, `V > 0` and `ΔV < 0` away from `x_eq`, and `V` radially unbounded.  Then `x_eq` is
globally asymptotically stable.

Continuity of `f` is not in Theorem 2 but cannot be dropped.  On `ℝ` with `V x = |x|`, which is
radially unbounded, take `f x = x / 2` for `|x| ≤ 1` and `f x = sign x · (1 + |x|) / 2`
otherwise: `ΔV < 0` away from `0`, yet the trajectory from `2` converges to `1`.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems* (2026),
Theorem 2, row 3. -/
@[blueprint "thm:globalAsymptoticStableDT-of-lyapunov"
  (title := "Lyapunov theorem for global asymptotic stability (discrete time)")
  (statement := /-- Let $E$ be finite-dimensional, and let $f$ and $V$ be continuous with
    $f(x_{\mathrm{eq}}) = x_{\mathrm{eq}}$ and $V(x_{\mathrm{eq}}) = 0$.  If, for every
    $x \ne x_{\mathrm{eq}}$,
    \[
      V(x) > 0, \qquad \Delta V(x) = V(f(x)) - V(x) < 0,
    \]
    and $V(x) \to \infty$ as $\|x - x_{\mathrm{eq}}\| \to \infty$, then $x_{\mathrm{eq}}$ is
    globally asymptotically stable (\cref{def:globalAsymptoticStableDT}).

    Continuity of $f$ is not among the hypotheses of the reference but cannot be dropped: with
    $V(x) = |x|$ on $\mathbb{R}$, the map $f(x) = x/2$ for $|x| \le 1$,
    $f(x) = \operatorname{sign}(x)(1 + |x|)/2$ otherwise, has $\Delta V < 0$ away from $0$, yet
    the trajectory from $2$ converges to $1$.

    Reference: Jungers and van de Wouw, \emph{Discrete-time nonlinear control systems}
    (2026), Theorem 2, row 3. -/)
  (proof := /-- Stability is \cref{thm:lyapunovStableDT-of-lyapunov} with
    $\mathcal{D} = E$.  From any $x_0$, $V(x_k) \le V(x_0)$, and radial unboundedness bounds
    the sublevel set $\{V \le V(x_0)\}$, so the trajectory stays in a closed ball.  The
    ω-limit argument of \cref{thm:localAsymptoticStableDT-of-lyapunov} then applies on that
    ball. -/)]
theorem globalAsymptoticStableDT_of_lyapunov [ProperSpace E] {f : E → E} {x_eq : E}
    {V : E → ℝ} (hf_eq : f x_eq = x_eq) (hf_cont : Continuous f) (hV_cont : Continuous V)
    (hV_zero : V x_eq = 0) (hV_pos : ∀ x, x ≠ x_eq → 0 < V x)
    (hV_unbdd : ∀ M : ℝ, ∃ R : ℝ, ∀ x, R ≤ ‖x - x_eq‖ → M ≤ V x)
    (hΔV : ∀ x, x ≠ x_eq → V (f x) - V x < 0) :
    GlobalAsymptoticStableDT f x_eq := by
  -- `V` does not increase anywhere: at `x_eq` it is fixed, elsewhere it strictly decreases
  have h_dec : ∀ x, V (f x) ≤ V x := fun x => by
    rcases eq_or_ne x x_eq with rfl | hne
    · rw [hf_eq]
    · linarith [hΔV x hne]
  -- Step 1. Stability, from the non-strict version with `D` the whole space.
  have h_stable : LyapunovStableDT f x_eq :=
    lyapunovStableDT_of_lyapunov isOpen_univ (mem_univ x_eq) hf_eq hf_cont.continuousAt
      hV_cont.continuousOn hV_zero (fun x _ hne => hV_pos x hne)
      fun x _ hne => (hΔV x hne).le
  refine ⟨h_stable, fun x₀ => ?_⟩
  -- Step 2. The trajectory stays in the sublevel set `{V ≤ V x₀}`, which lies in a closed ball.
  have hV_traj : ∀ k : ℕ, V (f^[k] x₀) ≤ V x₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply']; exact (h_dec _).trans ih
  obtain ⟨R, hR⟩ := hV_unbdd (V x₀ + 1)
  have h_in : ∀ k : ℕ, f^[k] x₀ ∈ closedBall x_eq R := fun k => by
    rw [mem_closedBall_iff_norm]
    by_contra h_far
    linarith [hR _ (not_le.mp h_far).le, hV_traj k]
  -- Step 3. The ω-limit argument on that ball.
  exact tendsto_of_lyapunov_strict_decrease (isCompact_closedBall x_eq R)
    (fun y _ => hf_cont.continuousAt) (fun y _ => hV_cont.continuousAt) (fun x _ => h_dec x)
    (fun x _ hne => by linarith [hΔV x hne]) h_in


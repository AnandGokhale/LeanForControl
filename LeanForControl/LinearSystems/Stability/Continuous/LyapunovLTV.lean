import LeanForControl.LinearSystems.Solutions.CtsLTV
import LeanForControl.Stability.Continuous.Defs
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Architect

/-!
# `LinearSystems.Stability.Continuous.LyapunovLTV`

Hespanha's four stability conditions for `ẋ = A(t) x` (Definition 8.1), stated on the homogeneous
response `Φ(t, t₀) x₀`, proved *equivalent* to the stability predicates of
`Stability/Continuous/Defs.lean` for the unforced system `s.toContinuousSystem.zeroInput`: nothing
is re-defined, so a result proved on either side is available on the other.  The state space is
any complete real normed space, and each result needs only `Continuous s.A`.

## Main results

* **Definition 8.1(1)** — `stable_iff_boundedHomogeneousResponse`, through
  `stable_iff_boundedStateTransition` (a bound on `Φ(t, t₀)` itself);
  `uniformlyStable_iff_uniformlyBoundedStateTransition` makes the bound independent of `t₀`.
* **Definition 8.1(2)** — `locallyAsymptoticallyStable_iff_decayingHomogeneousResponse`.
* **Definition 8.1(3)** — `locallyExponentiallyStable_iff_decayingStateTransition`,
  `globallyExponentiallyStable_iff_decayingStateTransition`, and
  `locallyExponentiallyStable_iff_globallyExponentiallyStable`.
* **Definition 8.1(4)** — `unstable_iff_unboundedHomogeneousResponse`.
* **Khalil, Theorem 4.11** — `uniformlyAsymptoticallyStable_iff_decayingStateTransition` and
  `globallyUniformlyAsymptoticallyStable_iff_decayingStateTransition`: for a linear system,
  uniform asymptotic stability is already exponential.

## The argument

Every equivalence is two facts.

* **Trajectories are responses.**  The predicates quantify over trajectories, the textbook over
  initial conditions; `Φ` solves the equation and is its only solution
  (`ContinuousLTV.isTrajectoryOn_homogeneousResponse` and
  `ContinuousLTV.eq_homogeneousResponse_of_isTrajectoryOn`, in `Solutions/CtsLTV.lean`).
* **Homogeneity.**  The predicates bound the responses from a ball, the textbook from every state;
  the response from `r x₀` is `r` times the response from `x₀`, so a bound on a ball scales to
  every state (`ContinuousLinearMap.opNorm_le_of_ball`, `ContinuousLinearMap.opNorm_le_of_shell`).
  This is why a linear system has no nontrivial region of attraction.

The predicates quantify over trajectory segments; local asymptotic stability also asks for forward
completeness, which a linear system has (`ContinuousLTV.isForwardComplete_zeroInput`).  Some
printings of Hespanha write the estimate with `e^{λ(t-t₀)}`, a typo for `e^{-λ(t-t₀)}`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Definition 8.1; Khalil,
*Nonlinear Systems* (3rd ed.), Definitions 4.4 and 4.5, Theorem 4.11.
-/

namespace LinearSystems

open Matrix Set Filter Topology ContinuousLTV
open scoped Matrix.Norms.Operator

variable {E U Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-! ## Stability at a single initial time

Lyapunov stability and *uniform* Lyapunov stability differ only in where the quantifier on the
initial time sits — Khalil's whole distinction is the order of `∃ δ` and `∀ t₀`. The two lemmas
below are the content at a *fixed* `t₀`, with the margin `δ` and the bound `C` explicit, so that
each of the two theorems is nothing but quantifier placement on top of them. -/

/-- A margin gives a bound on the state transition matrix: if every response from the `δ`-ball
at `t₀` is within `ε` of the origin from time `a` on, then `‖Φ(t, t₀) x‖ ≤ (2ε/δ) ‖x‖` for
`t ≥ a`.

Apply the margin to the homogeneous response from each `x` in the `δ`-ball, and let homogeneity
scale that to every `x`.  With `a = t₀` and `ε = 1` this is a stability margin; with `a = t₀ + T`
it is a convergence time. -/
private lemma bound_of_margin (s : ContinuousLTV E U Y) (hA : Continuous s.A)
    {t₀ a δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hstab : ∀ (t₁ : ℝ) (φ : ℝ → E),
      s.toContinuousSystem.zeroInput.IsTrajectoryOn (fun _ => ()) φ (Icc t₀ t₁) →
        ‖φ t₀ - 0‖ < δ → ∀ t ∈ Icc a t₁, ‖φ t - 0‖ < ε) :
    ∀ t ≥ a, ∀ x : E,
      ‖s.stateTransition t t₀ x‖ ≤ 2 * ε / δ * ‖x‖ := by
  intro t ht x
  -- From the `δ`-ball the response is within `ε` of the origin at time `t`.
  have hball : ∀ y : E, ‖y‖ < δ → ‖s.stateTransition t t₀ y‖ ≤ ε := by
    intro y hy
    have htraj := IsIntegralCurveOn.mono (isTrajectoryOn_homogeneousResponse s hA t₀ y)
      (Icc_subset_Ici_self : Icc t₀ t ⊆ Ici t₀)
    have hy' : ‖s.stateTransition t₀ t₀ y - 0‖ < δ := by simpa using hy
    simpa using (hstab t _ htraj hy' t ⟨ht, le_rfl⟩).le
  -- On the shell `δ / 2 ≤ ‖y‖ < δ` that is a bound by `(2ε / δ) ‖y‖`, which scales everywhere.
  have hop := ContinuousLinearMap.opNorm_le_of_shell
    (f := s.stateTransition t t₀) hδ
    (by positivity : (0 : ℝ) ≤ 2 * ε / δ) (c := (2 : ℝ)) (by norm_num) fun y hy1 hy2 => by
      rw [Real.norm_two] at hy1
      have h2 : ε ≤ 2 * ε / δ * ‖y‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ]; nlinarith
      simpa using (hball y hy2).trans h2
  simpa using ContinuousLinearMap.le_of_opNorm_le _ hop x

/-- A bound on the state transition matrix at `t₀` gives a stability margin there.

Every trajectory is its own homogeneous response, so the bound applies to it directly; the
margin `ε/(C+1)` is then real arithmetic. No positivity hypothesis on `ε` is needed: for
`ε ≤ 0` the margin hypothesis is already impossible. -/
private lemma margin_of_bound (s : ContinuousLTV E U Y) (hA : Continuous s.A)
    {t₀ C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t ≥ t₀, ∀ x : E, ‖s.stateTransition t t₀ x‖ ≤ C * ‖x‖)
    {ε : ℝ} :
    ∀ (t₁ : ℝ) (φ : ℝ → E),
      s.toContinuousSystem.zeroInput.IsTrajectoryOn (fun _ => ()) φ (Icc t₀ t₁) →
        ‖φ t₀ - 0‖ < ε / (C + 1) → ∀ t ∈ Icc t₀ t₁, ‖φ t - 0‖ < ε := by
  intro t₁ φ hφ hφ0 t ht
  rw [sub_zero] at hφ0 ⊢
  have h1 : ‖φ t‖ ≤ C * ‖φ t₀‖ := by
    rw [eq_homogeneousResponse_of_isTrajectoryOn s hA hφ ht]; exact hC t ht.1 (φ t₀)
  have h2 : ‖φ t₀‖ * (C + 1) < ε := (lt_div_iff₀ (by linarith)).1 hφ0
  have h3 : C * ‖φ t₀‖ + ‖φ t₀‖ < ε := by
    calc C * ‖φ t₀‖ + ‖φ t₀‖ = ‖φ t₀‖ * (C + 1) := by ring
      _ < ε := h2
  linarith [norm_nonneg (φ t₀)]

/-! ## Definition 8.1(1): Lyapunov stability -/

/-- The state-transition form of Definition 8.1(1): stability of `ẋ = A(t) x` is a bound
`‖Φ(t, t₀) x‖ ≤ C ‖x‖`, uniform in `t` but allowed to depend on `t₀`.

This is the workhorse behind `stable_iff_boundedHomogeneousResponse`; it is stated separately
because the bound on every state, not the per-initial-condition one, is what later results consume.
-/
@[blueprint "lem:continuousLTV-stable-iff-boundedStateTransition"
  (title := "Stability as a bound on the state transition matrix")
  (latexEnv := "lemma")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is a stable equilibrium (\cref{def:continuousSystem-stable}) of this system if and
    only if for every $t_{0} \ge 0$ there is $C$ with
    \[
      \|\Phi(t, t_{0})\, x\| \le C\,\|x\|, \qquad \forall\, t \ge t_{0},\ \forall\, x.
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.1(1).
  -/)
  (proof := /-- ($\Rightarrow$) Apply stability at $\varepsilon = 1$ to get $\delta(1, t_{0})$.
    Every response from the ball of radius $\delta$ stays inside the unit ball, and scaling
    turns that into the bound with $C = 2/\delta$.

    ($\Leftarrow$) Given $\varepsilon$, take $\delta = \varepsilon/(C+1)$.  A trajectory is its
    own response (\cref{thm:eq-homogeneousResponse-of-isTrajectoryOn}), so
    $\|\varphi(t)\| \le C\|\varphi(t_{0})\| < \varepsilon$. -/)]
theorem stable_iff_boundedStateTransition (s : ContinuousLTV E U Y)
    (hA : Continuous s.A) :
    s.toContinuousSystem.zeroInput.Stable (0 : E) ↔
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∃ C ≥ (0 : ℝ), ∀ t ≥ t₀, ∀ x : E,
        ‖s.stateTransition t t₀ x‖ ≤ C * ‖x‖ := by
  constructor
  · intro hS t₀ ht₀
    obtain ⟨δ, hδ, hstab⟩ := hS 1 one_pos t₀ ht₀
    exact ⟨2 * 1 / δ, by positivity, bound_of_margin s hA hδ one_pos hstab⟩
  · intro hbd ε hε t₀ ht₀
    obtain ⟨C, hC0, hC⟩ := hbd t₀ ht₀
    exact ⟨ε / (C + 1), div_pos hε (by linarith), margin_of_bound s hA hC0 hC⟩

/-- The system `ẋ = A(t) x` is (marginally) stable in the sense of Lyapunov — for every
initial condition `x(t₀) = x₀` the homogeneous state response
`x(t) = Φ(t, t₀) x₀` is bounded on `[t₀, ∞)` — exactly when the origin is a stable equilibrium
in the sense of `ContinuousSystem.Stable`.

The textbook's per-initial-condition form and the state-transition form are equivalent by
Banach–Steinhaus: a pointwise-bounded family of operators on a Banach space is
norm-bounded. -/
@[blueprint "thm:continuousLTV-stable-iff-boundedHomogeneousResponse"
  (title := "Lyapunov stability of a linear time-varying system")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is a stable equilibrium (\cref{def:continuousSystem-stable}) of this system if and
    only if, for every $t_{0} \ge 0$ and every initial condition $x_{0}$, the homogeneous state
    response
    $x(t) = \Phi(t, t_{0})\, x_{0}$ is bounded on $[t_{0}, \infty)$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.1(1).
  -/)
  (proof := /-- The state-transition form is
    \cref{lem:continuousLTV-stable-iff-boundedStateTransition}.  A bound on $\Phi$ gives
    the response bound $C\|x_{0}\|$; conversely a family of operators bounded at every point of
    a Banach space is norm-bounded, by the uniform boundedness principle. -/)]
theorem stable_iff_boundedHomogeneousResponse (s : ContinuousLTV E U Y)
    (hA : Continuous s.A) :
    s.toContinuousSystem.zeroInput.Stable (0 : E) ↔
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x₀ : E, ∃ C : ℝ, ∀ t ≥ t₀,
        ‖s.stateTransition t t₀ x₀‖ ≤ C := by
  rw [stable_iff_boundedStateTransition s hA]
  constructor
  · intro h t₀ ht₀ x₀
    obtain ⟨C, _, hC⟩ := h t₀ ht₀
    exact ⟨C * ‖x₀‖, fun t ht => hC t ht x₀⟩
  · intro h t₀ ht₀
    obtain ⟨C, hC⟩ := banach_steinhaus
      (g := fun i : {t : ℝ // t₀ ≤ t} =>
        s.stateTransition i.1 t₀)
      (fun x => by
        obtain ⟨C, hC⟩ := h t₀ ht₀ x
        exact ⟨C, fun i => hC i.1 i.2⟩)
    refine ⟨max C 0, le_max_right _ _, fun t ht x => ?_⟩
    exact (s.stateTransition t t₀).le_of_opNorm_le
      ((hC ⟨t, ht⟩).trans (le_max_left _ _)) x

/-- Uniform stability is the same bound made independent of the initial time.

Khalil separates uniform stability from stability by the order of the quantifiers on `δ` and
`t₀`; on the linear side that separation is visible as whether the constant `C` bounding the
response may depend on `t₀`. -/
@[blueprint "thm:continuousLTV-uniformlyStable-iff-uniformlyBoundedStateTransition"
  (title := "Uniform stability of a linear time-varying system")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is a uniformly stable equilibrium (\cref{def:continuousSystem-uniformlyStable}) of
    this system if and only if there is a single $C$ with
    \[
      \|\Phi(t, t_{0})\, x\| \le C\,\|x\|, \qquad \forall\, t \ge t_{0} \ge 0,\ \forall\, x.
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.1(1),
    with the margin independent of $t_{0}$.
  -/)
  (proof := /-- Identical to \cref{lem:continuousLTV-stable-iff-boundedStateTransition}, with the
    margin $\delta$ and the bound $C$ both carried outside the quantifier on $t_{0}$. -/)]
theorem uniformlyStable_iff_uniformlyBoundedStateTransition (s : ContinuousLTV E U Y)
    (hA : Continuous s.A) :
    s.toContinuousSystem.zeroInput.UniformlyStable (0 : E) ↔
      ∃ C ≥ (0 : ℝ), ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ t ≥ t₀, ∀ x : E,
        ‖s.stateTransition t t₀ x‖ ≤ C * ‖x‖ := by
  constructor
  · intro hS
    obtain ⟨δ, hδ, hstab⟩ := hS 1 one_pos
    exact ⟨2 * 1 / δ, by positivity,
      fun t₀ ht₀ => bound_of_margin s hA hδ one_pos (hstab t₀ ht₀)⟩
  · rintro ⟨C, hC0, hC⟩ ε hε
    exact ⟨ε / (C + 1), div_pos hε (by linarith),
      fun t₀ ht₀ => margin_of_bound s hA hC0 (hC t₀ ht₀)⟩

/-! ## Definition 8.1(2): asymptotic stability -/

/-- The system `ẋ = A(t) x` is asymptotically stable — stable,
and `x(t) = Φ(t, t₀) x₀ → 0` for every initial condition — exactly when the origin is
asymptotically stable in the sense of `ContinuousSystem.LocallyAsymptoticallyStable`.

The boundedness clause is stated because the textbook states it ("in addition"), not because
it is needed: a continuous response that converges is bounded. -/
@[blueprint "thm:continuousLTV-locallyAsymptoticallyStable-iff-decayingHomogeneousResponse"
  (title := "Asymptotic stability of a linear time-varying system")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is an asymptotically stable equilibrium
    (\cref{def:continuousSystem-locallyAsymptoticallyStable}) of this system if and only if, for
    every $t_{0} \ge 0$ and every $x_{0}$, the homogeneous response $t \mapsto \Phi(t, t_{0}) x_{0}$
    is bounded on $[t_{0}, \infty)$ and tends to $0$ as $t \to \infty$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.1(2).
  -/)
  (proof := /-- The stability conjunct is
    \cref{thm:continuousLTV-stable-iff-boundedHomogeneousResponse}.  For attractivity: an
    arbitrary $x_{0}$ is rescaled into the attractivity ball, and the limit scales back, since
    the response is linear in the initial state; conversely every trajectory is a response
    (\cref{thm:eq-homogeneousResponse-of-isTrajectoryOn}), so convergence of the responses is
    convergence of the trajectories, from any radius. -/)]
theorem locallyAsymptoticallyStable_iff_decayingHomogeneousResponse (s : ContinuousLTV E U Y)
    (hA : Continuous s.A) :
    s.toContinuousSystem.zeroInput.LocallyAsymptoticallyStable (0 : E) ↔
      (∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x₀ : E, ∃ C : ℝ, ∀ t ≥ t₀,
        ‖s.stateTransition t t₀ x₀‖ ≤ C) ∧
      (∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x₀ : E,
        Tendsto (fun t => s.stateTransition t t₀ x₀) atTop (𝓝 0)) := by
  constructor
  · rintro ⟨hS, hattr⟩
    refine ⟨(stable_iff_boundedHomogeneousResponse s hA).1 hS, fun t₀ ht₀ x₀ => ?_⟩
    obtain ⟨c, hc, -, hconv⟩ := hattr t₀ ht₀
    rcases eq_or_ne x₀ 0 with rfl | hx
    · have h0 : (fun t => s.stateTransition t t₀ (0 : E)) =
          fun _ : ℝ => (0 : E) := by
        funext t; simp
      rw [h0]
      exact tendsto_const_nhds
    have hx0 : 0 < ‖x₀‖ := norm_pos_iff.2 hx
    set r : ℝ := c / (2 * ‖x₀‖) with hr
    have hr0 : 0 < r := div_pos hc (by positivity)
    have hnorm : ‖r • x₀‖ = c / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hr]; field_simp
    have htraj := isTrajectoryOn_homogeneousResponse s hA t₀ (r • x₀)
    have hlim := hconv _ htraj (by
      simpa [hnorm] using
        (by linarith : c / 2 < c))
    have h2 := hlim.const_smul r⁻¹
    simpa [smul_smul,
      inv_mul_cancel₀ hr0.ne'] using h2
  · rintro ⟨hbd, hconv⟩
    refine ⟨(stable_iff_boundedHomogeneousResponse s hA).2 hbd,
      fun t₀ ht₀ => ⟨1, one_pos, fun t₁ x h_le hx _ =>
        isForwardComplete_zeroInput s hA t₀ t₁ x h_le hx (mem_univ _), fun φ hφ _ => ?_⟩⟩
    refine Filter.Tendsto.congr' ?_ (hconv t₀ ht₀ (φ t₀))
    filter_upwards [eventually_ge_atTop t₀] with t ht
    exact (eq_homogeneousResponse_of_isTrajectoryOn s hA
      (IsIntegralCurveOn.mono hφ Icc_subset_Ici_self) ⟨ht, le_rfl⟩).symm

/-! ## Definition 8.1(3): exponential stability -/

/-- Exponential stability in its global form: the response obeys
`‖x(t)‖ ≤ k e^{-γ(t - t₀)} ‖x(t₀)‖` for every initial condition. -/
@[blueprint "thm:continuousLTV-globallyExponentiallyStable-iff-decayingStateTransition"
  (title := "Global exponential stability of a linear time-varying system")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is a globally exponentially stable equilibrium
    (\cref{def:continuousSystem-globallyExponentiallyStable}) of this system if and only if there
    are $k, \gamma > 0$ with
    \[
      \|\Phi(t, t_{0})\, x\| \le k\, e^{-\gamma (t - t_{0})}\,\|x\|,
      \qquad \forall\, t \ge t_{0} \ge 0,\ \forall\, x.
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.1(3).
  -/)
  (proof := /-- Both directions are the trajectory characterization plus homogeneity: the
    exponential estimate along every trajectory is the estimate applied to the initial state,
    and conversely the estimate on any ball scales to the estimate everywhere. -/)]
theorem globallyExponentiallyStable_iff_decayingStateTransition
    (s : ContinuousLTV E U Y) (hA : Continuous s.A) :
    s.toContinuousSystem.zeroInput.GloballyExponentiallyStable (0 : E) ↔
      ∃ k > 0, ∃ γ > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ t ≥ t₀, ∀ x : E,
        ‖s.stateTransition t t₀ x‖ ≤ k * Real.exp (-γ * (t - t₀)) * ‖x‖ := by
  constructor
  · rintro ⟨k, hk, γ, hγ, hbd⟩
    refine ⟨k, hk, γ, hγ, fun t₀ ht₀ t ht x => ?_⟩
    have h1 : ‖s.stateTransition t t₀ x‖ ≤ k * ‖x‖ * Real.exp (-γ * (t - t₀)) := by
      simpa using
        hbd t₀ ht₀ t _ (IsIntegralCurveOn.mono (isTrajectoryOn_homogeneousResponse s hA t₀ x)
          Icc_subset_Ici_self) t ⟨ht, le_rfl⟩
    calc ‖s.stateTransition t t₀ x‖ ≤ k * ‖x‖ * Real.exp (-γ * (t - t₀)) := h1
      _ = k * Real.exp (-γ * (t - t₀)) * ‖x‖ := by ring
  · rintro ⟨k, hk, γ, hγ, hbd⟩
    refine ⟨k, hk, γ, hγ, fun t₀ ht₀ t₁ φ hφ t ht => ?_⟩
    rw [sub_zero, sub_zero, eq_homogeneousResponse_of_isTrajectoryOn s hA hφ ht]
    calc ‖s.stateTransition t t₀ (φ t₀)‖
        ≤ k * Real.exp (-γ * (t - t₀)) * ‖φ t₀‖ := hbd t₀ ht₀ t ht.1 (φ t₀)
      _ = k * ‖φ t₀‖ * Real.exp (-γ * (t - t₀)) := by ring

/-- Exponential stability in its local form. The right-hand side is the same as in
`globallyExponentiallyStable_iff_decayingStateTransition`: the radius `c` of the local
definition carries no information for a linear system. -/
@[blueprint "thm:continuousLTV-locallyExponentiallyStable-iff-decayingStateTransition"
  (title := "Exponential stability of a linear time-varying system")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is an exponentially stable equilibrium
    (\cref{def:continuousSystem-locallyExponentiallyStable}) of this system if and only if there are
    $k, \gamma > 0$ with
    \[
      \|\Phi(t, t_{0})\, x\| \le k\, e^{-\gamma (t - t_{0})}\,\|x\|,
      \qquad \forall\, t \ge t_{0} \ge 0,\ \forall\, x.
    \]
    The condition is the one in
    \cref{thm:continuousLTV-globallyExponentiallyStable-iff-decayingStateTransition}: the radius in
    the local definition carries no information here.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.1(3).
  -/)
  (proof := /-- The radius $c$ of the local definition is absorbed by the scaling argument;
    conversely the estimate is global exponential stability
    (\cref{thm:continuousLTV-globallyExponentiallyStable-iff-decayingStateTransition}), which is
    local. -/)]
theorem locallyExponentiallyStable_iff_decayingStateTransition (s : ContinuousLTV E U Y)
    (hA : Continuous s.A) :
    s.toContinuousSystem.zeroInput.LocallyExponentiallyStable (0 : E) ↔
      ∃ k > 0, ∃ γ > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ t ≥ t₀, ∀ x : E,
        ‖s.stateTransition t t₀ x‖ ≤ k * Real.exp (-γ * (t - t₀)) * ‖x‖ := by
  constructor
  · rintro ⟨c, hc, k, hk, γ, hγ, hbd⟩
    refine ⟨k, hk, γ, hγ, fun t₀ ht₀ t ht x => ?_⟩
    -- The estimate holds on the `c`-ball, and scales to every state.
    have hball : ∀ y ∈ Metric.ball (0 : E) c,
        ‖s.stateTransition t t₀ y‖ ≤
          k * Real.exp (-γ * (t - t₀)) * ‖y‖ := by
      intro y hy
      rw [mem_ball_zero_iff] at hy
      have hy' : ‖s.stateTransition t₀ t₀ y - 0‖ < c := by simpa using hy
      have h1 : ‖s.stateTransition t t₀ y‖ ≤ k * ‖y‖ * Real.exp (-γ * (t - t₀)) := by
        simpa using hbd t₀ ht₀ t _ (IsIntegralCurveOn.mono
          (isTrajectoryOn_homogeneousResponse s hA t₀ y) Icc_subset_Ici_self) hy' t ⟨ht, le_rfl⟩
      simpa [mul_right_comm] using h1
    simpa using ContinuousLinearMap.le_of_opNorm_le _
      (ContinuousLinearMap.opNorm_le_of_ball hc (by positivity) hball) x
  · intro h
    exact ((globallyExponentiallyStable_iff_decayingStateTransition s hA).mpr h)
      |>.locallyExponentiallyStable

/-- For a linear system, exponential stability is automatically global.

A linear system has no nontrivial region of attraction: the two definitions differ only by a
radius, and the response is homogeneous, so the radius scales away. -/
@[blueprint "cor:continuousLTV-locallyExponentiallyStable-iff-globallyExponentiallyStable"
  (title := "Local exponential stability is global, for a linear system")
  (latexEnv := "lemma")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is an exponentially stable equilibrium
    (\cref{def:continuousSystem-locallyExponentiallyStable}) of this system if and only if it is
    globally exponentially stable (\cref{def:continuousSystem-globallyExponentiallyStable}). -/)
  (proof := /-- Both are equivalent to the same estimate,
    \cref{thm:continuousLTV-locallyExponentiallyStable-iff-decayingStateTransition} and
    \cref{thm:continuousLTV-globallyExponentiallyStable-iff-decayingStateTransition}. -/)]
theorem locallyExponentiallyStable_iff_globallyExponentiallyStable (s : ContinuousLTV E U Y)
    (hA : Continuous s.A) :
    s.toContinuousSystem.zeroInput.LocallyExponentiallyStable (0 : E) ↔
      s.toContinuousSystem.zeroInput.GloballyExponentiallyStable (0 : E) :=
  (locallyExponentiallyStable_iff_decayingStateTransition s hA).trans
    (globallyExponentiallyStable_iff_decayingStateTransition s hA).symm

/-! ## Uniform asymptotic stability is exponential -/

/-- **For a linear time-varying system, uniform asymptotic stability is exponential**: the origin
of `ẋ = A(t) x` is uniformly asymptotically stable if and only if
`‖Φ(t, t₀) x‖ ≤ k e^{-γ(t - t₀)} ‖x‖`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.11. -/
@[blueprint "thm:continuousLTV-uniformlyAsymptoticallyStable-iff-decayingStateTransition"
  (title := "Uniform asymptotic stability of a linear time-varying system is exponential")
  (statement := /-- Consider the linear time-varying system $\dot x = A(t)\,x$ with $A$
    continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).  The origin is uniformly asymptotically stable
    (\cref{def:continuousSystem-uniformlyAsymptoticallyStable}) if and only if there are
    $k, \gamma > 0$ with
    \[
      \|\Phi(t, t_{0})\, x\| \le k\, e^{-\gamma (t - t_{0})}\,\|x\|,
      \qquad \forall\, t \ge t_{0} \ge 0,\ \forall\, x.
    \]

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.11. -/)
  (proof := /-- ($\Leftarrow$) The estimate is exponential stability
    (\cref{thm:continuousLTV-locallyExponentiallyStable-iff-decayingStateTransition}), which is
    uniform asymptotic stability.  ($\Rightarrow$) Uniform stability bounds
    $\|\Phi(t, t_0)\| \le C$
    (\cref{thm:continuousLTV-uniformlyStable-iff-uniformlyBoundedStateTransition}), and a uniform
    convergence time $T$ from the $c$-ball to the $c/(2e)$-ball gives $\|\Phi(t, t_0)\| \le 1/e$
    for $t \ge t_0 + T$, by homogeneity.  Splitting $[t_0, t]$ into $N = \lfloor (t - t_0)/T
    \rfloor$ windows of length $T$ and using $\Phi(t, t_0) = \Phi(t, t_0 + T)\,\Phi(t_0 + T, t_0)$
    gives $\|\Phi(t, t_0)\| \le \max(C, 1)\, e^{-N} \le e \max(C, 1)\, e^{-(t - t_0)/T}$. -/)]
theorem uniformlyAsymptoticallyStable_iff_decayingStateTransition (s : ContinuousLTV E U Y)
    (hA : Continuous s.A) :
    s.toContinuousSystem.zeroInput.UniformlyAsymptoticallyStable (0 : E) ↔
      ∃ k > 0, ∃ γ > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ t ≥ t₀, ∀ x : E,
        ‖s.stateTransition t t₀ x‖ ≤ k * Real.exp (-γ * (t - t₀)) * ‖x‖ := by
  constructor
  swap
  · intro h
    exact ((locallyExponentiallyStable_iff_decayingStateTransition s hA).mpr h)
      |>.uniformlyAsymptoticallyStable
  rintro ⟨hUS, c, hc, hconv⟩
  -- Step 1. A uniform bound `C' ≥ 1` on the state transition matrix.
  obtain ⟨C, hC0, hC⟩ := (uniformlyStable_iff_uniformlyBoundedStateTransition s hA).mp hUS
  set C' := max C 1
  have hC' : ∀ t₀, 0 ≤ t₀ → ∀ t ≥ t₀, ∀ x : E,
      ‖s.stateTransition t t₀ x‖ ≤ C' * ‖x‖ := fun t₀ ht₀ t ht x =>
    (hC t₀ ht₀ t ht x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- Step 2. After the convergence time `T`, the state transition matrix shrinks by `1/e`.
  obtain ⟨T, hT, hT_conv⟩ := hconv (c / (2 * Real.exp 1)) (by positivity)
  have h_window : ∀ t₀, 0 ≤ t₀ → ∀ t ≥ t₀ + T, ∀ x : E,
      ‖s.stateTransition t t₀ x‖ ≤ Real.exp (-1) * ‖x‖ := fun t₀ ht₀ t ht x => by
    have h := bound_of_margin s hA hc (by positivity) (hT_conv t₀ ht₀) t ht x
    have h_eq : 2 * (c / (2 * Real.exp 1)) / c = Real.exp (-1) := by
      rw [Real.exp_neg]
      field_simp
    rwa [h_eq] at h
  -- Step 3. Over `N` windows, `‖Φ(t, t₀) x‖ ≤ C' e^{-N} ‖x‖`, by the semigroup property.
  have h_steps : ∀ N : ℕ, ∀ t₀, 0 ≤ t₀ → ∀ t ≥ t₀ + N * T, ∀ x : E,
      ‖s.stateTransition t t₀ x‖ ≤ C' * Real.exp (-N) * ‖x‖ := by
    intro N
    induction N with
    | zero =>
      intro t₀ ht₀ t ht x
      simpa using hC' t₀ ht₀ t (by simpa using ht) x
    | succ N ih =>
      intro t₀ ht₀ t ht x
      push_cast at ht
      -- `Φ(t, t₀) = Φ(t, t₀ + T) Φ(t₀ + T, t₀)`: the first factor by induction, the second by one
      -- window.
      rw [← s.stateTransition_comp hA t (t₀ + T) t₀ x]
      calc ‖s.stateTransition t (t₀ + T) (s.stateTransition (t₀ + T) t₀ x)‖
          ≤ C' * Real.exp (-N) * ‖s.stateTransition (t₀ + T) t₀ x‖ :=
            ih (t₀ + T) (by linarith) t (by linarith) _
        _ ≤ C' * Real.exp (-N) * (Real.exp (-1) * ‖x‖) := by
            gcongr
            exact h_window t₀ ht₀ (t₀ + T) le_rfl x
        _ = C' * Real.exp (-↑(N + 1)) * ‖x‖ := by
            push_cast
            rw [show -((N : ℝ) + 1) = -N + -1 by ring, Real.exp_add]
            ring
  -- Step 4. With `N = ⌊(t - t₀)/T⌋`, `e^{-N} ≤ e · e^{-(t - t₀)/T}`.
  refine ⟨C' * Real.exp 1, by positivity, 1 / T, by positivity, fun t₀ ht₀ t ht x => ?_⟩
  set N := ⌊(t - t₀) / T⌋₊
  have hN_le : (N : ℝ) * T ≤ t - t₀ :=
    (le_div_iff₀ hT).mp (Nat.floor_le (div_nonneg (by linarith) hT.le))
  have hN_gt : (t - t₀) / T < N + 1 := Nat.lt_floor_add_one _
  calc ‖s.stateTransition t t₀ x‖
      ≤ C' * Real.exp (-N) * ‖x‖ := h_steps N t₀ ht₀ t (by linarith) x
    _ ≤ C' * Real.exp 1 * Real.exp (-(1 / T) * (t - t₀)) * ‖x‖ := by
        rw [show C' * Real.exp 1 * Real.exp (-(1 / T) * (t - t₀)) =
            C' * Real.exp (1 + -(1 / T) * (t - t₀)) by rw [mul_assoc, ← Real.exp_add]]
        gcongr
        rw [show -(1 / T) * (t - t₀) = -((t - t₀) / T) by ring]
        linarith

/-- **Khalil's Theorem 4.11, global form**: uniform asymptotic stability and its global version
coincide for a linear time-varying system, both being exponential decay of `Φ(t, t₀)`. -/
@[blueprint "cor:continuousLTV-globallyUniformlyAsymptoticallyStable-iff-decayingStateTransition"
  (title := "Global uniform asymptotic stability of a linear time-varying system")
  (latexEnv := "corollary")
  (statement := /-- Under the hypotheses of
    \cref{thm:continuousLTV-uniformlyAsymptoticallyStable-iff-decayingStateTransition}, the
    origin is globally uniformly asymptotically stable
    (\cref{def:continuousSystem-globallyUniformlyAsymptoticallyStable}) if and only if
    $\Phi(t, t_0)$ decays exponentially, uniformly in $t_0 \ge 0$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.11. -/)
  (proof := /-- Global uniform asymptotic stability is uniform asymptotic stability, hence
    exponential decay
    (\cref{thm:continuousLTV-uniformlyAsymptoticallyStable-iff-decayingStateTransition}); the
    decay is global exponential stability
    (\cref{thm:continuousLTV-globallyExponentiallyStable-iff-decayingStateTransition}), which is
    global uniform asymptotic stability. -/)]
theorem globallyUniformlyAsymptoticallyStable_iff_decayingStateTransition
    (s : ContinuousLTV E U Y) (hA : Continuous s.A) :
    s.toContinuousSystem.zeroInput.GloballyUniformlyAsymptoticallyStable (0 : E) ↔
      ∃ k > 0, ∃ γ > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ t ≥ t₀, ∀ x : E,
        ‖s.stateTransition t t₀ x‖ ≤ k * Real.exp (-γ * (t - t₀)) * ‖x‖ :=
  ⟨fun h => (uniformlyAsymptoticallyStable_iff_decayingStateTransition s hA).mp
      h.uniformlyAsymptoticallyStable,
    fun h => ((globallyExponentiallyStable_iff_decayingStateTransition s hA).mpr h)
      |>.globallyUniformlyAsymptoticallyStable⟩

/-! ## Definition 8.1(4): instability -/

/-- The system is unstable when it is not marginally stable:
some initial condition has an unbounded homogeneous response. -/
@[blueprint "thm:continuousLTV-unstable-iff-unboundedHomogeneousResponse"
  (title := "Instability of a linear time-varying system")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is unstable (\cref{def:continuousSystem-unstable}) for this system if and only if
    there are $t_{0} \ge 0$ and $x_{0}$ whose homogeneous response $t \mapsto \Phi(t, t_{0}) x_{0}$
    is unbounded on $[t_{0}, \infty)$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.1(4).
  -/)
  (proof := /-- The negation of \cref{thm:continuousLTV-stable-iff-boundedHomogeneousResponse}. -/)]
theorem unstable_iff_unboundedHomogeneousResponse (s : ContinuousLTV E U Y)
    (hA : Continuous s.A) :
    s.toContinuousSystem.zeroInput.Unstable (0 : E) ↔
      ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∃ x₀ : E, ∀ C : ℝ, ∃ t ≥ t₀,
        C < ‖s.stateTransition t t₀ x₀‖ := by
  rw [ContinuousSystem.Unstable, stable_iff_boundedHomogeneousResponse s hA]
  push Not
  rfl

end LinearSystems

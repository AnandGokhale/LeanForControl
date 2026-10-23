import LeanForControl.LinearSystems.Solutions.DiscLTV
import LeanForControl.Stability.Discrete.Defs
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Architect

/-!
# `LinearSystems.Stability.Discrete.LyapunovLTV`

Hespanha's Lyapunov-stability definition for a discrete-time linear time-varying system
`x(t+1) = A(t) x(t)`, read as *theorems* about the stability predicates of
`Stability/Discrete/Defs.lean`, applied to the unforced system `s.toDiscreteSystem.zeroInput`.
The discrete-time counterpart of `LinearSystems/Stability/Continuous/LyapunovLTV.lean`.

## Contents

* **Definition 8.2(1)** — `stable_iff_boundedHomogeneousResponse`, with its workhorse
  `stable_iff_boundedStateTransition` and the uniform version
  `uniformlyStable_iff_uniformlyBoundedStateTransition`.
* **Definition 8.2(2)** — `locallyAsymptoticallyStable_iff_decayingHomogeneousResponse`.
* **Definition 8.2(3)** — `locallyExponentiallyStable_iff_decayingStateTransition`, its global
  twin, and `locallyExponentiallyStable_iff_globallyExponentiallyStable`.
* **Definition 8.2(4)** — `unstable_iff_unboundedHomogeneousResponse`.

Every one is the trajectory characterization (`eq_discHomogeneousResponse_of_isTrajectoryOn`) plus
homogeneity (Mathlib's `ContinuousLinearMap.opNorm_le_of_ball` and `opNorm_le_of_shell`). Unlike
continuous time no regularity of `A` is needed, and no forward completeness enters: the state
transition matrix is a finite product, and trajectories always exist.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Definition 8.2.
-/

namespace LinearSystems

namespace DiscreteLTV

open Matrix Set Filter Topology

variable {X U Y : Type*} [Fintype X] [DecidableEq X] [Fintype U]

/-! ## Stability at a single initial time -/

/-- A stability margin at `t₀` gives a bound on the state transition matrix there. -/
private lemma bound_of_margin (s : DiscreteLTV X U Y ℝ) {t₀ : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hstab : ∀ φ : ℕ → X → ℝ, s.toDiscreteSystem.zeroInput.IsTrajectoryOn (fun _ => ()) φ
      (Ici t₀) → ‖φ t₀ - 0‖ < δ → ∀ t ≥ t₀, ‖φ t - 0‖ < 1) :
    ∀ t ≥ t₀, ∀ x : X → ℝ, ‖discStateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ 2 / δ * ‖x‖ := by
  intro t ht x
  -- From the `δ`-ball the response stays in the unit ball.
  have hball : ∀ y : X → ℝ, ‖y‖ < δ → ‖discStateTransitionMatrix s.A t t₀ *ᵥ y‖ ≤ 1 := by
    intro y hy
    have hφ := hstab _ (isTrajectoryOn_discHomogeneousResponse s t₀ y)
      (by simpa [discHomogeneousResponse_self] using hy) t ht
    simpa [discHomogeneousResponse] using hφ.le
  -- On the shell `δ / 2 ≤ ‖y‖ < δ` that is a bound by `(2 / δ) ‖y‖`, which scales everywhere.
  have hop := ContinuousLinearMap.opNorm_le_of_shell
    (f := LinearMap.toContinuousLinearMap (discStateTransitionMatrix s.A t t₀).mulVecLin) hδ
    (by positivity : (0 : ℝ) ≤ 2 / δ) (c := (2 : ℝ)) (by norm_num) fun y hy1 hy2 => by
      rw [Real.norm_two] at hy1
      have h2 : 1 ≤ 2 / δ * ‖y‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ]; linarith
      simpa using (hball y hy2).trans h2
  simpa using ContinuousLinearMap.le_of_opNorm_le _ hop x

/-- A bound on the state transition matrix at `t₀` gives a stability margin there. -/
private lemma margin_of_bound (s : DiscreteLTV X U Y ℝ) {t₀ : ℕ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t ≥ t₀, ∀ x : X → ℝ, ‖discStateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ C * ‖x‖)
    {ε : ℝ} :
    ∀ φ : ℕ → X → ℝ, s.toDiscreteSystem.zeroInput.IsTrajectoryOn (fun _ => ()) φ (Ici t₀) →
      ‖φ t₀ - 0‖ < ε / (C + 1) → ∀ t ≥ t₀, ‖φ t - 0‖ < ε := by
  intro φ hφ hφ0 t ht
  rw [sub_zero] at hφ0 ⊢
  have h1 : ‖φ t‖ ≤ C * ‖φ t₀‖ := by
    rw [eq_discHomogeneousResponse_of_isTrajectoryOn s hφ ht]; exact hC t ht (φ t₀)
  have h2 : ‖φ t₀‖ * (C + 1) < ε := (lt_div_iff₀ (by linarith)).1 hφ0
  nlinarith [norm_nonneg (φ t₀)]

/-! ## Definition 8.2(1): Lyapunov stability -/

/-- The state-transition form of Definition 8.2(1): stability of `x(t+1) = A(t) x(t)` is a bound
`‖Φ(t, t₀) x‖ ≤ C ‖x‖`, uniform in `t` but allowed to depend on `t₀`. -/
@[blueprint "lem:discreteLTV-stable-iff-boundedStateTransition"
  (title := "Discrete-time stability as a bound on the state transition matrix")
  (latexEnv := "lemma")
  (statement := /-- For the discrete-time linear system $x(t+1) = A(t)x(t)$ with state transition
    matrix $\Phi$ (\cref{def:discStateTransitionMatrix}), the origin is stable
    (\cref{def:discreteSystem-stable}) if and only if for every $t_0$ there is $C \ge 0$ with
    \[
      \|\Phi(t, t_0)\, x\| \le C\,\|x\|, \qquad \forall\, t \ge t_0,\ \forall\, x.
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.2(1).
  -/)
  (proof := /-- ($\Rightarrow$) Stability at $\varepsilon = 1$ gives a margin $\delta$; every
    response from the $\delta$-ball stays in the unit ball, and homogeneity scales that to the
    bound with $C = 2/\delta$.  ($\Leftarrow$) Given $\varepsilon$, take
    $\delta = \varepsilon/(C+1)$: a trajectory is its own homogeneous response
    (\cref{thm:eq-discHomogeneousResponse-of-isTrajectoryOn}). -/)]
theorem stable_iff_boundedStateTransition (s : DiscreteLTV X U Y ℝ) :
    s.toDiscreteSystem.zeroInput.Stable (0 : X → ℝ) ↔
      ∀ t₀ : ℕ, ∃ C ≥ (0 : ℝ), ∀ t ≥ t₀, ∀ x : X → ℝ,
        ‖discStateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ C * ‖x‖ := by
  constructor
  · intro hS t₀
    obtain ⟨δ, hδ, hstab⟩ := hS 1 one_pos t₀
    exact ⟨2 / δ, by positivity, bound_of_margin s hδ hstab⟩
  · intro hbd ε hε t₀
    obtain ⟨C, hC0, hC⟩ := hbd t₀
    exact ⟨ε / (C + 1), div_pos hε (by linarith), margin_of_bound s hC0 hC⟩

/-- **Hespanha, Definition 8.2(1).**  The system `x(t+1) = A(t) x(t)` is (marginally) stable —
every homogeneous response is bounded — exactly when the origin is stable.

The per-initial-condition form and the state-transition form are equivalent by
Banach–Steinhaus. -/
@[blueprint "thm:discreteLTV-stable-iff-boundedHomogeneousResponse"
  (title := "Lyapunov stability of a discrete-time linear time-varying system")
  (statement := /-- For the discrete-time linear system $x(t+1) = A(t)x(t)$, the origin is
    stable (\cref{def:discreteSystem-stable}) if and only if, for every $t_0$ and every initial
    condition $x_0$, the homogeneous response $x(t) = \Phi(t, t_0)\,x_0$
    (\cref{def:discHomogeneousResponse}) is bounded on $t \ge t_0$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.2(1).
  -/)
  (proof := /-- The state-transition form is
    \cref{lem:discreteLTV-stable-iff-boundedStateTransition}.  A bound on $\Phi$ bounds each
    response by $C\|x_0\|$; conversely a family of operators bounded at every point of a Banach
    space is norm-bounded, by the uniform boundedness principle. -/)]
theorem stable_iff_boundedHomogeneousResponse (s : DiscreteLTV X U Y ℝ) :
    s.toDiscreteSystem.zeroInput.Stable (0 : X → ℝ) ↔
      ∀ (t₀ : ℕ) (x₀ : X → ℝ), ∃ C : ℝ, ∀ t ≥ t₀,
        ‖discHomogeneousResponse s.A t₀ x₀ t‖ ≤ C := by
  rw [stable_iff_boundedStateTransition s]
  constructor
  · intro h t₀ x₀
    obtain ⟨C, _, hC⟩ := h t₀
    exact ⟨C * ‖x₀‖, fun t ht => hC t ht x₀⟩
  · intro h t₀
    obtain ⟨C, hC⟩ := banach_steinhaus
      (g := fun i : {t : ℕ // t₀ ≤ t} =>
        LinearMap.toContinuousLinearMap (discStateTransitionMatrix s.A i.1 t₀).mulVecLin)
      (fun x => by
        obtain ⟨C, hC⟩ := h t₀ x
        exact ⟨C, fun i => hC i.1 i.2⟩)
    refine ⟨max C 0, le_max_right _ _, fun t ht x => ?_⟩
    exact (LinearMap.toContinuousLinearMap
      (discStateTransitionMatrix s.A t t₀).mulVecLin).le_of_opNorm_le
      ((hC ⟨t, ht⟩).trans (le_max_left _ _)) x

/-- Uniform stability is the same bound made independent of the initial time. -/
@[blueprint "thm:discreteLTV-uniformlyStable-iff-uniformlyBoundedStateTransition"
  (title := "Uniform stability of a discrete-time linear time-varying system")
  (statement := /-- For the discrete-time linear system $x(t+1) = A(t)x(t)$, the origin is
    uniformly stable (\cref{def:discreteSystem-uniformlyStable}) if and only if there is a single
    $C$ with $\|\Phi(t, t_0)\, x\| \le C\,\|x\|$ for all $t \ge t_0$ and all $x$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.2(1),
    with the margin independent of $t_0$.
  -/)
  (proof := /-- As \cref{lem:discreteLTV-stable-iff-boundedStateTransition}, with the margin
    and the bound both carried outside the quantifier on $t_0$. -/)]
theorem uniformlyStable_iff_uniformlyBoundedStateTransition (s : DiscreteLTV X U Y ℝ) :
    s.toDiscreteSystem.zeroInput.UniformlyStable (0 : X → ℝ) ↔
      ∃ C ≥ (0 : ℝ), ∀ (t₀ t : ℕ), t₀ ≤ t → ∀ x : X → ℝ,
        ‖discStateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ C * ‖x‖ := by
  constructor
  · intro hS
    obtain ⟨δ, hδ, hstab⟩ := hS 1 one_pos
    exact ⟨2 / δ, by positivity, fun t₀ => bound_of_margin s hδ (hstab t₀)⟩
  · rintro ⟨C, hC0, hC⟩ ε hε
    exact ⟨ε / (C + 1), div_pos hε (by linarith), fun t₀ => margin_of_bound s hC0 (hC t₀)⟩

/-! ## Definition 8.2(2): asymptotic stability -/

/-- **Hespanha, Definition 8.2(2).**  The system is asymptotically stable — stable, and every
homogeneous response tends to `0` — exactly when the origin is locally asymptotically stable.
For a linear system the attractivity radius scales away. -/
@[blueprint "thm:discreteLTV-locallyAsymptoticallyStable-iff-decayingHomogeneousResponse"
  (title := "Asymptotic stability of a discrete-time linear time-varying system")
  (statement := /-- For the discrete-time linear system $x(t+1) = A(t)x(t)$, the origin is
    locally asymptotically stable
    (\cref{def:discreteSystem-locallyAsymptoticallyStable}) if and only if, for every $t_0$ and
    every $x_0$, the homogeneous response $t \mapsto \Phi(t, t_0)x_0$ is bounded on $t \ge t_0$
    and tends to $0$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.2(2).
  -/)
  (proof := /-- The stability conjunct is
    \cref{thm:discreteLTV-stable-iff-boundedHomogeneousResponse}.  For attractivity an
    arbitrary $x_0$ is rescaled into the attractivity ball and the limit scales back;
    conversely every trajectory is a response
    (\cref{thm:eq-discHomogeneousResponse-of-isTrajectoryOn}). -/)]
theorem locallyAsymptoticallyStable_iff_decayingHomogeneousResponse (s : DiscreteLTV X U Y ℝ) :
    s.toDiscreteSystem.zeroInput.LocallyAsymptoticallyStable (0 : X → ℝ) ↔
      (∀ (t₀ : ℕ) (x₀ : X → ℝ), ∃ C : ℝ, ∀ t ≥ t₀, ‖discHomogeneousResponse s.A t₀ x₀ t‖ ≤ C) ∧
      (∀ (t₀ : ℕ) (x₀ : X → ℝ), Tendsto (discHomogeneousResponse s.A t₀ x₀) atTop (𝓝 0)) := by
  constructor
  · rintro ⟨hS, hattr⟩
    refine ⟨(stable_iff_boundedHomogeneousResponse s).1 hS, fun t₀ x₀ => ?_⟩
    obtain ⟨c, hc, hconv⟩ := hattr t₀
    rcases eq_or_ne x₀ 0 with rfl | hx
    · have h0 : discHomogeneousResponse s.A t₀ (0 : X → ℝ) = fun _ => (0 : X → ℝ) := by
        funext t; simp [discHomogeneousResponse]
      rw [h0]
      exact tendsto_const_nhds
    have hx0 : 0 < ‖x₀‖ := norm_pos_iff.2 hx
    set r : ℝ := c / (2 * ‖x₀‖) with hr
    have hr0 : 0 < r := div_pos hc (by positivity)
    have hnorm : ‖r • x₀‖ = c / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hr]; field_simp
    have hlim := hconv _ (isTrajectoryOn_discHomogeneousResponse s t₀ (r • x₀)) (by
      simpa [discHomogeneousResponse_self, hnorm] using (by linarith : c / 2 < c))
    have h2 := hlim.const_smul r⁻¹
    simpa [discHomogeneousResponse, Matrix.mulVec_smul, smul_smul,
      inv_mul_cancel₀ hr0.ne'] using h2
  · rintro ⟨hbd, hconv⟩
    refine ⟨(stable_iff_boundedHomogeneousResponse s).2 hbd,
      fun t₀ => ⟨1, one_pos, fun φ hφ _ => ?_⟩⟩
    refine (hconv t₀ (φ t₀)).congr' ?_
    filter_upwards [eventually_ge_atTop t₀] with t ht
    exact (eq_discHomogeneousResponse_of_isTrajectoryOn s hφ ht).symm

/-! ## Definition 8.2(3): exponential stability -/

/-- Exponential stability in its global form: `‖x(t)‖ ≤ c ρ^{t - t₀} ‖x(t₀)‖` for every initial
condition, with `0 ≤ ρ < 1`. -/
@[blueprint "thm:discreteLTV-globallyExponentiallyStable-iff-decayingStateTransition"
  (title := "Global exponential stability of a discrete-time linear time-varying system")
  (statement := /-- For the discrete-time linear system $x(t+1) = A(t)x(t)$, the origin is
    globally exponentially stable (\cref{def:discreteSystem-globallyExponentiallyStable}) if and
    only if there are $c > 0$ and $0 \le \rho < 1$ with
    \[
      \|\Phi(t, t_0)\, x\| \le c\, \rho^{t - t_0}\,\|x\|, \qquad \forall\, t \ge t_0,\ \forall\, x.
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.2(3).
  -/)
  (proof := /-- The estimate along every trajectory is the estimate applied to its initial
    state, since a trajectory is its own homogeneous response; conversely the response from
    $x$ is a trajectory. -/)]
theorem globallyExponentiallyStable_iff_decayingStateTransition (s : DiscreteLTV X U Y ℝ) :
    s.toDiscreteSystem.zeroInput.GloballyExponentiallyStable (0 : X → ℝ) ↔
      ∃ c > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (t₀ t : ℕ), t₀ ≤ t → ∀ x : X → ℝ,
        ‖discStateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ c * ρ ^ (t - t₀) * ‖x‖ := by
  constructor
  · rintro ⟨c, hc, ρ, hρ0, hρ1, hbd⟩
    refine ⟨c, hc, ρ, hρ0, hρ1, fun t₀ t ht x => ?_⟩
    have h := hbd t₀ _ (isTrajectoryOn_discHomogeneousResponse s t₀ x) t ht
    simp only [discHomogeneousResponse, discStateTransitionMatrix_self, Matrix.one_mulVec,
      sub_zero] at h
    exact h.trans_eq (by ring)
  · rintro ⟨c, hc, ρ, hρ0, hρ1, hbd⟩
    refine ⟨c, hc, ρ, hρ0, hρ1, fun t₀ φ hφ t ht => ?_⟩
    rw [sub_zero, sub_zero, eq_discHomogeneousResponse_of_isTrajectoryOn s hφ ht]
    exact (hbd t₀ t ht (φ t₀)).trans_eq (by ring)

/-- Exponential stability in its local form.  The right-hand side is the same as in the global
case: the radius of the local definition carries no information for a linear system. -/
@[blueprint "thm:discreteLTV-locallyExponentiallyStable-iff-decayingStateTransition"
  (title := "Exponential stability of a discrete-time linear time-varying system")
  (statement := /-- For the discrete-time linear system $x(t+1) = A(t)x(t)$, the origin is
    locally exponentially stable (\cref{def:discreteSystem-locallyExponentiallyStable}) if and
    only if there are $c > 0$ and $0 \le \rho < 1$ with
    $\|\Phi(t, t_0)\, x\| \le c\, \rho^{t - t_0}\,\|x\|$ for all $t \ge t_0$ and all $x$: the
    condition of \cref{thm:discreteLTV-globallyExponentiallyStable-iff-decayingStateTransition}.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.2(3).
  -/)
  (proof := /-- As in the global case; the radius of the local definition is absorbed by the
    scaling argument, and radius $1$ serves in the converse. -/)]
theorem locallyExponentiallyStable_iff_decayingStateTransition (s : DiscreteLTV X U Y ℝ) :
    s.toDiscreteSystem.zeroInput.LocallyExponentiallyStable (0 : X → ℝ) ↔
      ∃ c > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (t₀ t : ℕ), t₀ ≤ t → ∀ x : X → ℝ,
        ‖discStateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ c * ρ ^ (t - t₀) * ‖x‖ := by
  constructor
  · rintro ⟨r, hr, c, hc, ρ, hρ0, hρ1, hbd⟩
    refine ⟨c, hc, ρ, hρ0, hρ1, fun t₀ t ht x => ?_⟩
    -- The estimate holds on the `r`-ball, and scales to every state.
    have hball : ∀ y ∈ Metric.ball (0 : X → ℝ) r,
        ‖LinearMap.toContinuousLinearMap (discStateTransitionMatrix s.A t t₀).mulVecLin y‖ ≤
          c * ρ ^ (t - t₀) * ‖y‖ := by
      intro y hy
      rw [mem_ball_zero_iff] at hy
      have h := hbd t₀ _ (isTrajectoryOn_discHomogeneousResponse s t₀ y)
        (by simpa [discHomogeneousResponse_self] using hy) t ht
      simp only [discHomogeneousResponse, discStateTransitionMatrix_self, Matrix.one_mulVec,
        sub_zero] at h
      simpa using h.trans_eq (by ring)
    simpa using ContinuousLinearMap.le_of_opNorm_le _
      (ContinuousLinearMap.opNorm_le_of_ball hr (mul_nonneg hc.le (pow_nonneg hρ0 _)) hball) x
  · rintro ⟨c, hc, ρ, hρ0, hρ1, hbd⟩
    refine ⟨1, one_pos, c, hc, ρ, hρ0, hρ1, fun t₀ φ hφ _ t ht => ?_⟩
    rw [sub_zero, sub_zero, eq_discHomogeneousResponse_of_isTrajectoryOn s hφ ht]
    exact (hbd t₀ t ht (φ t₀)).trans_eq (by ring)

omit [DecidableEq X] in
/-- For a linear system, local exponential stability is automatically global. -/
@[blueprint "cor:discreteLTV-locallyExponentiallyStable-iff-globallyExponentiallyStable"
  (title := "Local exponential stability is global, for a discrete-time linear system")
  (latexEnv := "lemma")
  (statement := /-- For the discrete-time linear system $x(t+1) = A(t)x(t)$, the origin is
    locally exponentially stable (\cref{def:discreteSystem-locallyExponentiallyStable}) if and
    only if it is globally exponentially stable
    (\cref{def:discreteSystem-globallyExponentiallyStable}). -/)
  (proof := /-- Both are equivalent to the same estimate:
    \cref{thm:discreteLTV-locallyExponentiallyStable-iff-decayingStateTransition} and
    \cref{thm:discreteLTV-globallyExponentiallyStable-iff-decayingStateTransition}. -/)]
theorem locallyExponentiallyStable_iff_globallyExponentiallyStable (s : DiscreteLTV X U Y ℝ) :
    s.toDiscreteSystem.zeroInput.LocallyExponentiallyStable (0 : X → ℝ) ↔
      s.toDiscreteSystem.zeroInput.GloballyExponentiallyStable (0 : X → ℝ) := by
  classical
  exact (locallyExponentiallyStable_iff_decayingStateTransition s).trans
    (globallyExponentiallyStable_iff_decayingStateTransition s).symm

/-! ## Definition 8.2(4): instability -/

/-- **Hespanha, Definition 8.2(4).**  The system is unstable when it is not marginally stable:
some initial condition has an unbounded homogeneous response. -/
@[blueprint "thm:discreteLTV-unstable-iff-unboundedHomogeneousResponse"
  (title := "Instability of a discrete-time linear time-varying system")
  (statement := /-- For the discrete-time linear system $x(t+1) = A(t)x(t)$, the origin is
    unstable (\cref{def:discreteSystem-unstable}) if and only if there are $t_0$ and $x_0$ whose
    homogeneous response $t \mapsto \Phi(t, t_0)x_0$ is unbounded on $t \ge t_0$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.2(4).
  -/)
  (proof := /-- The negation of
    \cref{thm:discreteLTV-stable-iff-boundedHomogeneousResponse}. -/)]
theorem unstable_iff_unboundedHomogeneousResponse (s : DiscreteLTV X U Y ℝ) :
    s.toDiscreteSystem.zeroInput.Unstable (0 : X → ℝ) ↔
      ∃ (t₀ : ℕ) (x₀ : X → ℝ), ∀ C : ℝ, ∃ t ≥ t₀,
        C < ‖discHomogeneousResponse s.A t₀ x₀ t‖ := by
  rw [DiscreteSystem.Unstable, stable_iff_boundedHomogeneousResponse s]
  push Not
  rfl

end DiscreteLTV

end LinearSystems

import LeanForControl.LinearSystems.Solutions.CtsLTV
import LeanForControl.Stability.DefsNonAutonomous
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Architect

/-!
# `LinearSystems.Stability.Continuous.LyapunovLTV`

Hespanha's Lyapunov-stability definition for a continuous-time linear time-varying system,
read as *theorems* about the non-autonomous stability predicates of
`Stability/DefsNonAutonomous.lean`.

The textbook states four conditions on the homogeneous state response `x(t) = Φ(t, t₀) x₀` of
`ẋ = A(t) x` and calls them stability, asymptotic stability, exponential stability and
instability. Nothing here re-defines any of those: each of the four is proved *equivalent*
to the predicate the nonlinear track already has, so a result proved on either side is
available on the other.

## Contents

Each result is stated about a `ContinuousLinearSystem`, since these are properties of a system,
and needs only `Continuous s.A` — the input and output matrices play no part in Lyapunov
stability.

* **Definition 8.1(1)** — `stableNA_linear_iff_boundedHomogenousTrajectory`: stability is
  boundedness of every homogeneous response. Its workhorse
  `stableNA_linear_iff_boundedStateTransition` gives the equivalent bound on `Φ(t, t₀)`
  itself, and `uniformlyStableNA_linear_iff` makes that bound independent of `t₀`.
* **Definition 8.1(2)** — `asymptoticStableNA_linear_iff`.
* **Definition 8.1(3)** — `exponentiallyStableNA_linear_iff` and its global twin
  `globallyExponentiallyStableNA_linear_iff`, with `exponentiallyStableNA_linear_iff_globally`
  recording that for a linear system the two coincide.
* **Definition 8.1(4)** — `unstableNA_linear_iff`.

Every one of them is the trajectory characterization plus homogeneity. The trajectory
characterization itself is solution theory and lives in `Solutions/CtsLTV.lean`:
`ContinuousLinearSystem.isTrajectory_homogeneousResponse` for existence and
`eq_homogeneousResponse_of_isIntegralCurveOn` for uniqueness.

## One state space, one set of stability predicates

Everything here lives in `X → ℝ` under the `L∞` norm — the space `Solutions/` works in,
because that is where matrix multiplication is submultiplicative and the Peano–Baker series
converges. `Stability/DefsNonAutonomous.lean` is stated over an arbitrary real normed space,
so its predicates apply here directly: there is no second notion of stability for linear
systems and no transport between state spaces.

The unforced system is `s.vectorField 0`, which `ContinuousLinearSystem.vectorField_zero_input`
reduces to `fun t z => s.A t *ᵥ z`. That reduction is what lets the left-hand sides speak about
the system while the proofs work with the state matrix.

## Why the equivalences are not definitional

Two things separate the textbook statements from the predicates:

* The textbook quantifies over *initial conditions*, the predicates over *trajectories*. The
  gap closes in both directions only because `Φ` both solves the equation
  (`ContinuousLinearSystem.isTrajectory_homogeneousResponse`) and is the unique solution
  (`eq_homogeneousResponse_of_isIntegralCurveOn`) — the second is where Grönwall enters,
  through `stateTransitionMatrix_mulVec_unique`.
* The textbook's bounds are on the response from *every* initial state; the predicates'
  bounds are on the response from a *ball*. Linearity is what makes these the same: the
  response from `r x₀` is `r` times the response from `x₀`, so a bound on any ball scales to
  a bound everywhere. This is why a linear system has no nontrivial region of attraction, and
  the reason `exponentiallyStableNA_linear_iff_globally` holds.

The sign in `Real.exp (-γ * (t - t₀))` is the decaying one; the estimate as printed in some
editions of Hespanha carries `e^{λ(t-t₀)}` with `λ > 0`, which is a typo for `e^{-λ(t-t₀)}`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Definition 8.1; Khalil,
*Nonlinear Systems* (3rd ed.), Definitions 4.4 and 4.5.
-/

namespace LinearSystems

open Matrix Set Filter Topology ContinuousLinearSystem
open scoped Matrix.Norms.Operator

variable {X U Y : Type*} [Fintype X] [DecidableEq X] [Fintype U]
variable {A : ℝ → Matrix X X ℝ}

/-! ## Trajectories of a linear system

"The solutions of `ẋ = A(t) x` from `t₀` are exactly the homogeneous responses `Φ(·, t₀) x₀`"
is solution theory and lives in `Solutions/CtsLTV.lean`, stated on the system:
`ContinuousLinearSystem.isTrajectoryOn_homogeneousResponse` for existence and
`ContinuousLinearSystem.eq_homogeneousResponse_of_isTrajectoryOn` for uniqueness. No bridging
is needed here, because `IsTrajectoryNA φ (s.vectorField 0) t₀` *is*
`s.IsTrajectoryOn 0 φ (Set.Ici t₀)` — both unfold to `IsIntegralCurveOn φ (s.vectorField 0)
(Set.Ici t₀)`.

That the origin is an equilibrium is likewise a property of the system,
`ContinuousLinearSystem.vectorField_apply_zero`. Everything below is those facts plus
homogeneity. -/

/-! ## Homogeneity

The two lemmas that turn a bound on the response from a ball into a bound on the response from
every state. This is the only place linearity is used beyond the trajectory characterization
above. -/

/-- A bound `‖Φ(t,t₀) x‖ ≤ K ‖x‖` holding only on a ball holds everywhere.

Scaling: `x` is rescaled into the ball, and both sides are homogeneous of degree one, so the
factor cancels. This is why a *local* estimate for a linear system is never weaker than the
global one. -/
private lemma norm_mulVec_le_of_ball_mul {t₀ t c K : ℝ} (hc : 0 < c)
    (h : ∀ x : X → ℝ, ‖x‖ < c → ‖stateTransitionMatrix A t t₀ *ᵥ x‖ ≤ K * ‖x‖)
    (x : X → ℝ) : ‖stateTransitionMatrix A t t₀ *ᵥ x‖ ≤ K * ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  set r : ℝ := c / (2 * ‖x‖) with hr
  have hr0 : 0 < r := div_pos hc (by positivity)
  have hnorm : ‖r • x‖ = c / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hr]; field_simp
  have hb := h (r • x) (by rw [hnorm]; linarith)
  rw [Matrix.mulVec_smul, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr0] at hb
  exact le_of_mul_le_mul_left (by linarith) hr0

/-- A response confined to the unit ball whenever the initial state is in the ball of radius
`c` obeys `‖Φ(t,t₀) x‖ ≤ (2/c) ‖x‖` everywhere.

The same scaling as `norm_mulVec_le_of_ball_mul`, for the shape the stability predicates
produce: an `ε`–`δ` statement bounds the response by a constant, not by a multiple of the
initial deviation, so the radius reappears in the conclusion. -/
private lemma norm_mulVec_le_of_ball {t₀ t c : ℝ} (hc : 0 < c)
    (h : ∀ x : X → ℝ, ‖x‖ < c → ‖stateTransitionMatrix A t t₀ *ᵥ x‖ ≤ 1)
    (x : X → ℝ) : ‖stateTransitionMatrix A t t₀ *ᵥ x‖ ≤ 2 / c * ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  set r : ℝ := c / (2 * ‖x‖) with hr
  have hr0 : 0 < r := div_pos hc (by positivity)
  have hnorm : ‖r • x‖ = c / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hr]; field_simp
  have hb := h (r • x) (by rw [hnorm]; linarith)
  rw [Matrix.mulVec_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr0] at hb
  have h1 : ‖stateTransitionMatrix A t t₀ *ᵥ x‖ ≤ 1 / r := by rw [le_div_iff₀ hr0]; linarith
  have h2 : 1 / r = 2 / c * ‖x‖ := by rw [hr]; field_simp
  linarith [h1, h2.ge]

/-! ## Stability at a single initial time

Lyapunov stability and *uniform* Lyapunov stability differ only in where the quantifier on the
initial time sits — Khalil's whole distinction is the order of `∃ δ` and `∀ t₀`. The two lemmas
below are the content at a *fixed* `t₀`, with the margin `δ` and the bound `C` explicit, so that
each of the two theorems is nothing but quantifier placement on top of them. -/

/-- A stability margin at `t₀` gives a bound on the state transition matrix there.

Apply the margin to the homogeneous response from each `x` in the `δ`-ball: it stays inside the
unit ball, and homogeneity scales that to every `x`. -/
private lemma bound_of_margin (s : ContinuousLinearSystem X U Y ℝ) (hA : Continuous s.A)
    {t₀ δ : ℝ} (hδ : 0 < δ)
    (hstab : ∀ φ : ℝ → X → ℝ, IsTrajectoryNA φ (s.vectorField 0) t₀ →
      ‖φ t₀ - 0‖ < δ → ∀ t ≥ t₀, ‖φ t - 0‖ < 1) :
    ∀ t ≥ t₀, ∀ x : X → ℝ,
      ‖stateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ 2 / δ * ‖x‖ := by
  intro t ht
  refine norm_mulVec_le_of_ball hδ fun x hx => ?_
  have htraj := isTrajectoryOn_homogeneousResponse s hA t₀ x
  have hx' : ‖homogeneousResponse s.A t₀ x t₀ - 0‖ < δ := by simpa using hx
  simpa [homogeneousResponse] using (hstab _ htraj hx' t ht).le

/-- A bound on the state transition matrix at `t₀` gives a stability margin there.

Every trajectory is its own homogeneous response, so the bound applies to it directly; the
margin `ε/(C+1)` is then real arithmetic. No positivity hypothesis on `ε` is needed: for
`ε ≤ 0` the margin hypothesis is already impossible. -/
private lemma margin_of_bound (s : ContinuousLinearSystem X U Y ℝ) (hA : Continuous s.A)
    {t₀ C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t ≥ t₀, ∀ x : X → ℝ, ‖stateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ C * ‖x‖)
    {ε : ℝ} :
    ∀ φ : ℝ → X → ℝ, IsTrajectoryNA φ (s.vectorField 0) t₀ →
      ‖φ t₀ - 0‖ < ε / (C + 1) → ∀ t ≥ t₀, ‖φ t - 0‖ < ε := by
  intro φ hφ hφ0 t ht
  rw [sub_zero] at hφ0 ⊢
  have h1 : ‖φ t‖ ≤ C * ‖φ t₀‖ := by
    rw [eq_homogeneousResponse_of_isTrajectoryOn s hA hφ ht]; exact hC t ht (φ t₀)
  have h2 : ‖φ t₀‖ * (C + 1) < ε := (lt_div_iff₀ (by linarith)).1 hφ0
  have h3 : C * ‖φ t₀‖ + ‖φ t₀‖ < ε := by
    calc C * ‖φ t₀‖ + ‖φ t₀‖ = ‖φ t₀‖ * (C + 1) := by ring
      _ < ε := h2
  linarith [norm_nonneg (φ t₀)]

/-! ## Definition 8.1(1): Lyapunov stability -/

/-- The state-transition form of Definition 8.1(1): stability of `ẋ = A(t) x` is a bound
`‖Φ(t, t₀) x‖ ≤ C ‖x‖`, uniform in `t` but allowed to depend on `t₀`.

This is the workhorse behind `stableNA_linear_iff`; it is stated separately because the bound
on every state, not the per-initial-condition one, is what later results consume. -/
@[blueprint "lem:stableNA-linear-iff-boundedStateTransition"
  (title := "Stability as a bound on the state transition matrix")
  (latexEnv := "lemma")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is a stable equilibrium (\cref{def:stableNA}) of this system if and only if
    for every $t_{0} \ge 0$ there is $C$ with
    \[
      \|\Phi(t, t_{0})\, x\| \le C\,\|x\|, \qquad \forall\, t \ge t_{0},\ \forall\, x.
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.1(1).
  -/)
  (proof := /-- ($\Rightarrow$) Apply stability at $\varepsilon = 1$ to get $\delta(1, t_{0})$.
    Every response from the ball of radius $\delta$ stays inside the unit ball, and scaling
    turns that into the bound with $C = 2/\delta$.

    ($\Leftarrow$) Given $\varepsilon$, take $\delta = \varepsilon/(C+1)$.  A trajectory is its
    own response (\cref{thm:eq-homogeneousResponse-of-isIntegralCurveOn}), so
    $\|\varphi(t)\| \le C\|\varphi(t_{0})\| < \varepsilon$. -/)]
theorem stableNA_linear_iff_boundedStateTransition (s : ContinuousLinearSystem X U Y ℝ)
    (hA : Continuous s.A) :
    StableNA (s.vectorField 0) (0 : X → ℝ) ↔
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∃ C ≥ (0 : ℝ), ∀ t ≥ t₀, ∀ x : X → ℝ,
        ‖stateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ C * ‖x‖ := by
  constructor
  · intro hS t₀ ht₀
    obtain ⟨δ, hδ, hstab⟩ := hS 1 one_pos t₀ ht₀
    exact ⟨2 / δ, by positivity, bound_of_margin s hA hδ hstab⟩
  · intro hbd ε hε t₀ ht₀
    obtain ⟨C, hC0, hC⟩ := hbd t₀ ht₀
    exact ⟨ε / (C + 1), div_pos hε (by linarith), margin_of_bound s hA hC0 hC⟩

/-- The system `ẋ = A(t) x` is (marginally) stable in the sense of Lyapunov — for every
initial condition `x(t₀) = x₀` the homogeneous state response
`x(t) = Φ(t, t₀) x₀` is bounded on `[t₀, ∞)` — exactly when the origin is a stable equilibrium
in the sense of `StableNA`.

The textbook's per-initial-condition form and the state-transition form are equivalent by
Banach–Steinhaus: a pointwise-bounded family of operators on a Banach space is
norm-bounded. -/
@[blueprint "thm:stableNA-linear-iff-boundedHomogenousTrajectory"
  (title := "Lyapunov stability of a linear time-varying system")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is a stable equilibrium (\cref{def:stableNA}) of this system if and only if,
    for every $t_{0} \ge 0$ and every initial condition $x_{0}$, the homogeneous state response
    $x(t) = \Phi(t, t_{0})\, x_{0}$ is bounded on $[t_{0}, \infty)$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.1(1).
  -/)
  (proof := /-- The state-transition form is
    \cref{lem:stableNA-linear-iff-boundedStateTransition}.  A bound on $\Phi$ gives
    the response bound $C\|x_{0}\|$; conversely a family of operators bounded at every point of
    a Banach space is norm-bounded, by the uniform boundedness principle. -/)]
theorem stableNA_linear_iff_boundedHomogenousTrajectory (s : ContinuousLinearSystem X U Y ℝ)
    (hA : Continuous s.A) :
    StableNA (s.vectorField 0) (0 : X → ℝ) ↔
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x₀ : X → ℝ, ∃ C : ℝ, ∀ t ≥ t₀,
        ‖homogeneousResponse s.A t₀ x₀ t‖ ≤ C := by
  rw [stableNA_linear_iff_boundedStateTransition s hA]
  constructor
  · intro h t₀ ht₀ x₀
    obtain ⟨C, _, hC⟩ := h t₀ ht₀
    exact ⟨C * ‖x₀‖, fun t ht => hC t ht x₀⟩
  · intro h t₀ ht₀
    obtain ⟨C, hC⟩ := banach_steinhaus
      (g := fun i : {t : ℝ // t₀ ≤ t} =>
        LinearMap.toContinuousLinearMap (stateTransitionMatrix s.A i.1 t₀).mulVecLin)
      (fun x => by
        obtain ⟨C, hC⟩ := h t₀ ht₀ x
        exact ⟨C, fun i => hC i.1 i.2⟩)
    refine ⟨max C 0, le_max_right _ _, fun t ht x => ?_⟩
    exact (LinearMap.toContinuousLinearMap
      (stateTransitionMatrix s.A t t₀).mulVecLin).le_of_opNorm_le
      ((hC ⟨t, ht⟩).trans (le_max_left _ _)) x

/-- Uniform stability is the same bound made independent of the initial time.

Khalil separates uniform stability from stability by the order of the quantifiers on `δ` and
`t₀`; on the linear side that separation is visible as whether the constant `C` bounding the
response may depend on `t₀`. -/
@[blueprint "thm:uniformlyStableNA-linear-iff"
  (title := "Uniform stability of a linear time-varying system")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is a uniformly stable equilibrium (\cref{def:uniformlyStableNA}) of this
    system if and only if there is a single $C$ with
    \[
      \|\Phi(t, t_{0})\, x\| \le C\,\|x\|, \qquad \forall\, t \ge t_{0} \ge 0,\ \forall\, x.
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.1(1),
    with the margin independent of $t_{0}$.
  -/)
  (proof := /-- Identical to \cref{lem:stableNA-linear-iff-boundedStateTransition}, with the
    margin $\delta$ and the bound $C$ both carried outside the quantifier on $t_{0}$. -/)]
theorem uniformlyStableNA_linear_iff (s : ContinuousLinearSystem X U Y ℝ)
    (hA : Continuous s.A) :
    UniformlyStableNA (s.vectorField 0) (0 : X → ℝ) ↔
      ∃ C ≥ (0 : ℝ), ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ t ≥ t₀, ∀ x : X → ℝ,
        ‖stateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ C * ‖x‖ := by
  constructor
  · intro hS
    obtain ⟨δ, hδ, hstab⟩ := hS 1 one_pos
    exact ⟨2 / δ, by positivity, fun t₀ ht₀ => bound_of_margin s hA hδ (hstab t₀ ht₀)⟩
  · rintro ⟨C, hC0, hC⟩ ε hε
    exact ⟨ε / (C + 1), div_pos hε (by linarith),
      fun t₀ ht₀ => margin_of_bound s hA hC0 (hC t₀ ht₀)⟩

/-! ## Definition 8.1(2): asymptotic stability -/

/-- The system `ẋ = A(t) x` is asymptotically stable — stable,
and `x(t) = Φ(t, t₀) x₀ → 0` for every initial condition — exactly when the origin is
asymptotically stable in the sense of `AsymptoticStableNA`.

The boundedness clause is stated because the textbook states it ("in addition"), not because
it is needed: a continuous response that converges is bounded. -/
@[blueprint "thm:asymptoticStableNA-linear-iff"
  (title := "Asymptotic stability of a linear time-varying system")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is an asymptotically stable equilibrium (\cref{def:asymptoticStableNA}) of
    this system if and only if, for every $t_{0} \ge 0$ and every $x_{0}$, the homogeneous
    response
    $t \mapsto \Phi(t, t_{0}) x_{0}$ is bounded on $[t_{0}, \infty)$ and tends to $0$ as
    $t \to \infty$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.1(2).
  -/)
  (proof := /-- The stability conjunct is
    \cref{thm:stableNA-linear-iff-boundedHomogenousTrajectory}.  For attractivity: an
    arbitrary $x_{0}$ is rescaled into the attractivity ball, and the limit scales back, since
    the response is linear in the initial state; conversely every trajectory is a response
    (\cref{thm:eq-homogeneousResponse-of-isIntegralCurveOn}), so convergence of the responses is
    convergence of the trajectories, from any radius. -/)]
theorem asymptoticStableNA_linear_iff (s : ContinuousLinearSystem X U Y ℝ)
    (hA : Continuous s.A) :
    AsymptoticStableNA (s.vectorField 0) (0 : X → ℝ) ↔
      (∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x₀ : X → ℝ, ∃ C : ℝ, ∀ t ≥ t₀,
        ‖homogeneousResponse s.A t₀ x₀ t‖ ≤ C) ∧
      (∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x₀ : X → ℝ,
        Tendsto (homogeneousResponse s.A t₀ x₀) atTop (𝓝 0)) := by
  constructor
  · rintro ⟨hS, hattr⟩
    refine ⟨(stableNA_linear_iff_boundedHomogenousTrajectory s hA).1 hS, fun t₀ ht₀ x₀ => ?_⟩
    obtain ⟨c, hc, hconv⟩ := hattr t₀ ht₀
    rcases eq_or_ne x₀ 0 with rfl | hx
    · have h0 : homogeneousResponse s.A t₀ (0 : X → ℝ) = fun _ : ℝ => (0 : X → ℝ) := by
        funext t; simp [homogeneousResponse]
      rw [h0]
      exact tendsto_const_nhds
    have hx0 : 0 < ‖x₀‖ := norm_pos_iff.2 hx
    set r : ℝ := c / (2 * ‖x₀‖) with hr
    have hr0 : 0 < r := div_pos hc (by positivity)
    have hnorm : ‖r • x₀‖ = c / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hr]; field_simp
    have htraj := isTrajectoryOn_homogeneousResponse s hA t₀ (r • x₀)
    have hlim := hconv _ htraj (by
      simpa [homogeneousResponse, stateTransitionMatrix_self, hnorm] using
        (by linarith : c / 2 < c))
    have h2 := hlim.const_smul r⁻¹
    simpa [homogeneousResponse, Matrix.mulVec_smul, smul_smul,
      inv_mul_cancel₀ hr0.ne'] using h2
  · rintro ⟨hbd, hconv⟩
    refine ⟨(stableNA_linear_iff_boundedHomogenousTrajectory s hA).2 hbd,
      fun t₀ ht₀ => ⟨1, one_pos, fun φ hφ _ => ?_⟩⟩
    refine Filter.Tendsto.congr' ?_ (hconv t₀ ht₀ (φ t₀))
    filter_upwards [eventually_ge_atTop t₀] with t ht
    exact (eq_homogeneousResponse_of_isTrajectoryOn s hA hφ ht).symm

/-! ## Definition 8.1(3): exponential stability -/

/-- Exponential stability in its global form: the response obeys
`‖x(t)‖ ≤ k e^{-γ(t - t₀)} ‖x(t₀)‖` for every initial condition. -/
@[blueprint "thm:globallyExponentiallyStableNA-linear-iff"
  (title := "Global exponential stability of a linear time-varying system")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is a globally exponentially stable equilibrium
    (\cref{def:globallyExponentiallyStableNA}) of this system if and only if there are
    $k, \gamma > 0$ with
    \[
      \|\Phi(t, t_{0})\, x\| \le k\, e^{-\gamma (t - t_{0})}\,\|x\|,
      \qquad \forall\, t \ge t_{0} \ge 0,\ \forall\, x.
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.1(3).
  -/)
  (proof := /-- Both directions are the trajectory characterization plus homogeneity: the
    exponential estimate along every trajectory is the estimate applied to the initial state,
    and conversely the estimate on any ball scales to the estimate everywhere. -/)]
theorem globallyExponentiallyStableNA_linear_iff (s : ContinuousLinearSystem X U Y ℝ)
    (hA : Continuous s.A) :
    GloballyExponentiallyStableNA (s.vectorField 0) (0 : X → ℝ) ↔
      ∃ k > 0, ∃ γ > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ t ≥ t₀, ∀ x : X → ℝ,
        ‖stateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ k * Real.exp (-γ * (t - t₀)) * ‖x‖ := by
  constructor
  · rintro ⟨k, hk, γ, hγ, hbd⟩
    refine ⟨k, hk, γ, hγ, fun t₀ ht₀ t ht => norm_mulVec_le_of_ball_mul (c := 1) one_pos
      fun x _ => ?_⟩
    have h1 : ‖stateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ k * ‖x‖ * Real.exp (-γ * (t - t₀)) := by
      simpa [homogeneousResponse, stateTransitionMatrix_self] using
        hbd t₀ ht₀ _ (isTrajectoryOn_homogeneousResponse s hA t₀ x) t ht
    calc ‖stateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ k * ‖x‖ * Real.exp (-γ * (t - t₀)) := h1
      _ = k * Real.exp (-γ * (t - t₀)) * ‖x‖ := by ring
  · rintro ⟨k, hk, γ, hγ, hbd⟩
    refine ⟨k, hk, γ, hγ, fun t₀ ht₀ φ hφ t ht => ?_⟩
    rw [sub_zero, sub_zero, eq_homogeneousResponse_of_isTrajectoryOn s hA hφ ht]
    calc ‖homogeneousResponse s.A t₀ (φ t₀) t‖
        ≤ k * Real.exp (-γ * (t - t₀)) * ‖φ t₀‖ := hbd t₀ ht₀ t ht (φ t₀)
      _ = k * ‖φ t₀‖ * Real.exp (-γ * (t - t₀)) := by ring

/-- Exponential stability in its local form. The right-hand side is the same as in
`globallyExponentiallyStableNA_linear_iff`: the radius `c` of the local definition carries no
information for a linear system. -/
@[blueprint "thm:exponentiallyStableNA-linear-iff"
  (title := "Exponential stability of a linear time-varying system")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is an exponentially stable equilibrium
    (\cref{def:exponentiallyStableNA}) of this system if and only if there are
    $k, \gamma > 0$ with
    \[
      \|\Phi(t, t_{0})\, x\| \le k\, e^{-\gamma (t - t_{0})}\,\|x\|,
      \qquad \forall\, t \ge t_{0} \ge 0,\ \forall\, x.
    \]
    The condition is the one in
    \cref{thm:globallyExponentiallyStableNA-linear-iff}: the radius in the local definition
    carries no information here.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.1(3).
  -/)
  (proof := /-- As in the global case; the radius $c$ of the local definition is absorbed by
    the scaling argument, and $c = 1$ serves in the converse. -/)]
theorem exponentiallyStableNA_linear_iff (s : ContinuousLinearSystem X U Y ℝ)
    (hA : Continuous s.A) :
    ExponentiallyStableNA (s.vectorField 0) (0 : X → ℝ) ↔
      ∃ k > 0, ∃ γ > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ t ≥ t₀, ∀ x : X → ℝ,
        ‖stateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ k * Real.exp (-γ * (t - t₀)) * ‖x‖ := by
  constructor
  · rintro ⟨c, hc, k, hk, γ, hγ, hbd⟩
    refine ⟨k, hk, γ, hγ, fun t₀ ht₀ t ht => norm_mulVec_le_of_ball_mul hc fun x hx => ?_⟩
    have hself : homogeneousResponse s.A t₀ x t₀ = x := by
      simp [homogeneousResponse, stateTransitionMatrix_self]
    have hx' : ‖homogeneousResponse s.A t₀ x t₀ - 0‖ < c := by rw [hself]; simpa using hx
    have hraw := hbd t₀ ht₀ _ (isTrajectoryOn_homogeneousResponse s hA t₀ x) hx' t ht
    rw [hself] at hraw
    have h1 : ‖stateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ k * ‖x‖ * Real.exp (-γ * (t - t₀)) := by
      simpa [homogeneousResponse] using hraw
    calc ‖stateTransitionMatrix s.A t t₀ *ᵥ x‖ ≤ k * ‖x‖ * Real.exp (-γ * (t - t₀)) := h1
      _ = k * Real.exp (-γ * (t - t₀)) * ‖x‖ := by ring
  · rintro ⟨k, hk, γ, hγ, hbd⟩
    refine ⟨1, one_pos, k, hk, γ, hγ, fun t₀ ht₀ φ hφ _ t ht => ?_⟩
    rw [sub_zero, sub_zero, eq_homogeneousResponse_of_isTrajectoryOn s hA hφ ht]
    calc ‖homogeneousResponse s.A t₀ (φ t₀) t‖
        ≤ k * Real.exp (-γ * (t - t₀)) * ‖φ t₀‖ := hbd t₀ ht₀ t ht (φ t₀)
      _ = k * ‖φ t₀‖ * Real.exp (-γ * (t - t₀)) := by ring

omit [DecidableEq X] in
/-- For a linear system, exponential stability is automatically global.

A linear system has no nontrivial region of attraction: the two definitions differ only by a
radius, and the response is homogeneous, so the radius scales away. -/
@[blueprint "cor:exponentiallyStableNA-linear-iff-globally"
  (title := "Local exponential stability is global, for a linear system")
  (latexEnv := "lemma")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is an exponentially stable equilibrium (\cref{def:exponentiallyStableNA}) of
    this system if and only if it is globally exponentially stable
    (\cref{def:globallyExponentiallyStableNA}). -/)
  (proof := /-- Both are equivalent to the same estimate,
    \cref{thm:exponentiallyStableNA-linear-iff} and
    \cref{thm:globallyExponentiallyStableNA-linear-iff}. -/)]
theorem exponentiallyStableNA_linear_iff_globally (s : ContinuousLinearSystem X U Y ℝ)
    (hA : Continuous s.A) :
    ExponentiallyStableNA (s.vectorField 0) (0 : X → ℝ) ↔
      GloballyExponentiallyStableNA (s.vectorField 0) (0 : X → ℝ) := by
  classical
  exact (exponentiallyStableNA_linear_iff s hA).trans
    (globallyExponentiallyStableNA_linear_iff s hA).symm

/-! ## Definition 8.1(4): instability -/

/-- The system is unstable when it is not marginally stable:
some initial condition has an unbounded homogeneous response. -/
@[blueprint "thm:unstableNA-linear-iff"
  (title := "Instability of a linear time-varying system")
  (statement := /-- Consider the linear time-varying system
    \[
      \dot x = A(t)\,x,
    \]
    with $A$ continuous, and write $\Phi(t,t_{0})$ for its state transition matrix
    (\cref{def:stateTransitionMatrix}).

    The origin is unstable (\cref{def:unstableNA}) for this system if and only if there are
    $t_{0} \ge 0$ and $x_{0}$ whose homogeneous response $t \mapsto \Phi(t, t_{0}) x_{0}$ is
    unbounded on $[t_{0}, \infty)$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Definition 8.1(4).
  -/)
  (proof := /-- The negation of \cref{thm:stableNA-linear-iff-boundedHomogenousTrajectory}. -/)]
theorem unstableNA_linear_iff (s : ContinuousLinearSystem X U Y ℝ)
    (hA : Continuous s.A) :
    UnstableNA (s.vectorField 0) (0 : X → ℝ) ↔
      ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∃ x₀ : X → ℝ, ∀ C : ℝ, ∃ t ≥ t₀,
        C < ‖homogeneousResponse s.A t₀ x₀ t‖ := by
  rw [UnstableNA, stableNA_linear_iff_boundedHomogenousTrajectory s hA]
  push Not
  rfl

end LinearSystems

import LeanForControl.LinearSystems.Solutions.CtsLTV
import LeanForControl.LinearSystems.Stability.Continuous.DefsLyapunovLTV
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

* **Trajectories** — `isTrajectoryNA_stateTransitionCLM` and
  `IsTrajectoryNA.eq_stateTransitionCLM`: the trajectories of `ẋ = A(t) x` from `t₀` are
  exactly the maps `t ↦ Φ(t, t₀) x₀`. Every statement below is this fact plus homogeneity.
* **Definition 8.1(1)** — `stableNA_linearVectorField_iff`, with the operator-norm form
  `stableNA_linearVectorField_iff_opNorm` and the time-uniform form
  `uniformlyStableNA_linearVectorField_iff`.
* **Definition 8.1(2)** — `asymptoticStableNA_linearVectorField_iff`.
* **Definition 8.1(3)** — `exponentiallyStableNA_linearVectorField_iff` and its global twin,
  with `exponentiallyStableNA_iff_globallyExponentiallyStableNA` recording that for a linear
  system the two coincide.
* **Definition 8.1(4)** — `unstableNA_linearVectorField_iff`.

## Why the equivalences are not definitional

Two things separate the textbook statements from the predicates:

* The textbook quantifies over *initial conditions*, the predicates over *trajectories*. The
  gap closes in both directions only because `Φ` both solves the equation
  (`isTrajectoryNA_stateTransitionCLM`) and is the unique solution
  (`IsTrajectoryNA.eq_stateTransitionCLM`) — the second is where Grönwall enters, through
  `stateTransitionMatrix_mulVec_unique`.
* The textbook's bounds are on the response from *every* initial state; the predicates'
  bounds are on the response from a *ball*. Linearity is what makes these the same: the
  response from `r x₀` is `r` times the response from `x₀`, so a bound on any ball scales to
  an operator bound. This is why a linear system has no nontrivial region of attraction, and
  the reason `exponentiallyStableNA_iff_globallyExponentiallyStableNA` holds.

The sign in `Real.exp (-γ * (t - t₀))` is the decaying one; the estimate as printed in some
editions of Hespanha carries `e^{λ(t-t₀)}` with `λ > 0`, which is a typo for `e^{-λ(t-t₀)}`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Definition 8.1; Khalil,
*Nonlinear Systems* (3rd ed.), Definitions 4.4 and 4.5.
-/

namespace LinearSystems

open Matrix Set Filter Topology
open scoped Matrix.Norms.Operator

variable {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The Euclidean-to-sup-norm identification of the state space, as a linear homeomorphism. -/
private noncomputable abbrev ofLpCLE : ℝⁿ ≃L[ℝ] (Fin n → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n => ℝ

/-- A continuous `A` is bounded on every compact time segment.

Every theorem imported from `Solutions/CtsLTV.lean` carries a hypothesis `‖A s‖ ≤ M` on the
segment it works over. Continuity supplies that hypothesis one segment at a time, which is
why `Continuous A` is the only assumption the results below need. -/
private lemma exists_norm_le_uIcc (hA : Continuous A) (a b : ℝ) :
    ∃ M : ℝ, ∀ s ∈ Set.uIcc a b, ‖A s‖ ≤ M :=
  isCompact_uIcc.exists_bound_of_continuousOn hA.continuousOn

/-- Being an integral curve of `x ↦ A(t) x` does not depend on which of the two norms the
state space carries: the identification is a linear homeomorphism, so it transports
derivatives both ways. -/
private lemma isIntegralCurveOn_linearVectorField_iff {φ : ℝ → ℝⁿ} {s : Set ℝ} :
    IsIntegralCurveOn φ (linearVectorField A) s ↔
      IsIntegralCurveOn (fun r => WithLp.ofLp (φ r)) (fun r v => A r *ᵥ v) s := by
  constructor
  · intro h t ht
    have hd :=
      (ofLpCLE (n := n)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t (h t ht)
    simpa [linearVectorField, Function.comp_def] using hd
  · intro h t ht
    have hd := (ofLpCLE (n := n)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t
      (h t ht)
    simpa [linearVectorField, Function.comp_def] using hd

/-! ## Trajectories of a linear system

The two halves of "the solutions of `ẋ = A(t) x` from `t₀` are exactly the maps
`t ↦ Φ(t, t₀) x₀`". Everything after this section is these two facts plus linearity. -/

/-- `t ↦ Φ(t, t₀) x₀` is a trajectory of `ẋ = A(t) x` on `[t₀, ∞)`, for every initial state.

This is what makes the stability predicates non-vacuous for a linear system: each of them
quantifies over trajectories, and hypotheses about them say nothing at all unless trajectories
exist. -/
@[blueprint "thm:isTrajectoryNA-stateTransitionCLM"
  (title := "The state transition operator generates trajectories")
  (statement := /-- For continuous $A$, every initial time $t_{0}$ and every initial state
    $x_{0} \in \mathbb{R}^{n}$, the map $t \mapsto \Phi(t, t_{0})\, x_{0}$
    (\cref{def:stateTransitionCLM}) is a trajectory of $\dot x = A(t) x$
    (\cref{def:isTrajectoryNA}) on $[t_{0}, \infty)$. -/)
  (proof := /-- Fix $t \ge t_{0}$ and work on $[t_{0}, t+1]$, where continuity of $A$ supplies
    a bound.  There $\Phi(\cdot, t_{0}) x_{0}$ satisfies the integral equation
    (\cref{lem:isIntegralSolution-stateTransitionMatrix-mulVec}), hence is an integral curve
    (\cref{lem:isIntegralSolution-isIntegralCurveOn}); since $t < t+1$, the segment is a
    neighbourhood of $t$ within $[t_{0}, \infty)$, so the derivative within the segment is the
    derivative within the ray.  The two state-space norms transport derivatives to each other,
    being related by a linear homeomorphism. -/)]
theorem isTrajectoryNA_stateTransitionCLM (hA : Continuous A) (t₀ : ℝ) (x₀ : ℝⁿ) :
    IsTrajectoryNA (fun t => stateTransitionCLM A t t₀ x₀) (linearVectorField A) t₀ := by
  refine isIntegralCurveOn_linearVectorField_iff.2 ?_
  simp only [stateTransitionCLM, Matrix.ofLp_toEuclideanCLM]
  intro t ht
  obtain ⟨M, hM⟩ := exists_norm_le_uIcc hA t₀ (t + 1)
  have hlt : t < t + 1 := by linarith
  have hle : t₀ ≤ t + 1 := le_trans ht hlt.le
  have hcont : ContinuousOn (fun s => stateTransitionMatrix A s t₀) (uIcc t₀ (t + 1)) :=
    continuousOn_stateTransitionMatrix hA hM
  have hFx : ContinuousOn (fun s => A s *ᵥ (stateTransitionMatrix A s t₀ *ᵥ WithLp.ofLp x₀))
      (uIcc t₀ (t + 1)) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (hA.continuousOn.prodMk ((continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
        (hcont.prodMk continuousOn_const)))
  have hcurve := (isIntegralSolution_stateTransitionMatrix_mulVec hA hM
    (WithLp.ofLp x₀)).isIntegralCurveOn hFx
  have htmem : t ∈ uIcc t₀ (t + 1) := by rw [uIcc_of_le hle]; exact ⟨ht, hlt.le⟩
  refine (hcurve t htmem).mono_of_mem_nhdsWithin ?_
  rw [uIcc_of_le hle]
  exact mem_nhdsWithin.2 ⟨Iio (t + 1), isOpen_Iio, hlt, fun r hr => ⟨hr.2, hr.1.le⟩⟩

/-- Every trajectory of `ẋ = A(t) x` is `Φ(t, t₀)` applied to its own initial state.

The converse half of `isTrajectoryNA_stateTransitionCLM`, and the one with content: it is
uniqueness of solutions, so it is where Grönwall enters. Together the two say that the
trajectories from `t₀` are *exactly* the responses `Φ(·, t₀) x₀`, which is what lets a
hypothesis about every trajectory become a hypothesis about the operator `Φ(t, t₀)`. -/
@[blueprint "thm:isTrajectoryNA-eq-stateTransitionCLM"
  (title := "Trajectories are state transition responses")
  (statement := /-- Let $A$ be continuous and let $\varphi$ be a trajectory of
    $\dot x = A(t)x$ from $t_{0}$ (\cref{def:isTrajectoryNA}).  Then
    \[
      \varphi(t) = \Phi(t, t_{0})\, \varphi(t_{0}), \qquad \forall\, t \ge t_{0}.
    \] -/)
  (proof := /-- On $[t_{0}, t]$ the trajectory satisfies the integral equation
    (\cref{lem:isIntegralCurveOn-isIntegralSolution}), so uniqueness for the Peano--Baker
    solution (\cref{thm:stateTransitionMatrix-mulVec-unique}) identifies it with
    $\Phi(\cdot, t_{0}) \varphi(t_{0})$ there.  Uniqueness is the Grönwall step; without it a
    trajectory could leave the response. -/)]
theorem IsTrajectoryNA.eq_stateTransitionCLM (hA : Continuous A) {φ : ℝ → ℝⁿ} {t₀ : ℝ}
    (hφ : IsTrajectoryNA φ (linearVectorField A) t₀) {t : ℝ} (ht : t₀ ≤ t) :
    φ t = stateTransitionCLM A t t₀ (φ t₀) := by
  obtain ⟨M, hM⟩ := exists_norm_le_uIcc hA t₀ t
  have hIcc : uIcc t₀ t = Icc t₀ t := uIcc_of_le ht
  have hcurve : IsIntegralCurveOn (fun r => WithLp.ofLp (φ r)) (fun r v => A r *ᵥ v)
      (uIcc t₀ t) := by
    rw [hIcc]
    exact fun r hr => (isIntegralCurveOn_linearVectorField_iff.1 hφ r (Icc_subset_Ici_self hr)).mono
      (Icc_subset_Ici_self)
  have hz_cont : ContinuousOn (fun r => WithLp.ofLp (φ r)) (uIcc t₀ t) :=
    fun r hr => (hcurve r hr).continuousWithinAt
  have hFx : ContinuousOn (fun r => A r *ᵥ WithLp.ofLp (φ r)) (uIcc t₀ t) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (hA.continuousOn.prodMk hz_cont)
  have hsol := hcurve.isIntegralSolution hFx
  have := stateTransitionMatrix_mulVec_unique hA hM (WithLp.ofLp (φ t₀)) hsol hz_cont t
    right_mem_uIcc
  simpa [stateTransitionCLM] using congrArg (WithLp.toLp 2) this

/-- `Φ(t₀, t₀)` is the identity operator. -/
@[simp, blueprint "lem:stateTransitionCLM-self"
  (title := "The state transition operator at its base time")
  (latexEnv := "lemma")
  (statement := /-- $\Phi(t_{0}, t_{0}) = I$ as an operator on $\mathbb{R}^{n}$. -/)
  (proof := /-- \cref{thm:stateTransitionMatrix-self} and the fact that the identification of
    matrices with operators is an algebra map. -/)]
theorem stateTransitionCLM_self (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ) :
    stateTransitionCLM A t₀ t₀ = 1 := by
  simp [stateTransitionCLM, stateTransitionMatrix_self]

/-- The origin is an equilibrium of every linear system.

The stability predicates take the equilibrium as a parameter; for a linear system it is always
`0`, which is why every statement below fixes `x_eq := 0`. -/
@[blueprint "lem:isEquilibriumNA-linearVectorField"
  (title := "The origin is the equilibrium of a linear system")
  (latexEnv := "lemma")
  (statement := /-- The origin is an equilibrium (\cref{def:isEquilibriumNA}) of
    $\dot x = A(t) x$ for every $A$. -/)]
theorem isEquilibriumNA_linearVectorField (A : ℝ → Matrix (Fin n) (Fin n) ℝ) :
    IsEquilibriumNA (linearVectorField A) (0 : ℝⁿ) := fun _ => by simp [linearVectorField]

/-! ## Homogeneity

The three lemmas that turn a statement about trajectories from a ball into a statement about
the operator `Φ(t, t₀)`, and back. This is the only place linearity is used beyond the
trajectory characterization above. -/

/-- A bound `‖Φ(t,t₀) x‖ ≤ K ‖x‖` holding only on a ball is an operator bound.

Scaling: `x` is rescaled into the ball, and both sides of the bound are homogeneous of
degree one, so the factor cancels. This is why a *local* estimate for a linear system is
never weaker than the global one. -/
private lemma opNorm_stateTransitionCLM_le_of_ball_mul {t₀ t c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (h : ∀ x : ℝⁿ, ‖x‖ < c → ‖stateTransitionCLM A t t₀ x‖ ≤ K * ‖x‖) :
    ‖stateTransitionCLM A t t₀‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  set r : ℝ := c / (2 * ‖x‖) with hr
  have hr0 : 0 < r := div_pos hc (by positivity)
  have hnorm : ‖r • x‖ = c / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hr]; field_simp
  have hb := h (r • x) (by rw [hnorm]; linarith)
  rw [map_smul, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr0] at hb
  exact le_of_mul_le_mul_left (by linarith) hr0

/-- A bound `‖Φ(t,t₀) x‖ ≤ K` holding only on the ball of radius `c` is the operator bound
`‖Φ(t,t₀)‖ ≤ 2K/c`.

The same scaling as `opNorm_stateTransitionCLM_le_of_ball_mul`, for the shape the stability
predicates produce: an `ε`–`δ` statement bounds the response by a constant, not by a multiple
of the initial deviation, so the radius reappears in the conclusion. -/
private lemma opNorm_stateTransitionCLM_le_of_ball {t₀ t c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (h : ∀ x : ℝⁿ, ‖x‖ < c → ‖stateTransitionCLM A t t₀ x‖ ≤ K) :
    ‖stateTransitionCLM A t t₀‖ ≤ 2 * K / c := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  set r : ℝ := c / (2 * ‖x‖) with hr
  have hr0 : 0 < r := div_pos hc (by positivity)
  have hnorm : ‖r • x‖ = c / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hr]; field_simp
  have hb := h (r • x) (by rw [hnorm]; linarith)
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr0] at hb
  have h1 : ‖stateTransitionCLM A t t₀ x‖ ≤ K / r := by rw [le_div_iff₀ hr0]; linarith
  have h2 : K / r = 2 * K / c * ‖x‖ := by rw [hr]; field_simp
  linarith [h1, h2.ge]

/-- The response along any trajectory is bounded by the operator norm times the initial
deviation. -/
private lemma norm_le_of_isTrajectoryNA (hA : Continuous A) {φ : ℝ → ℝⁿ} {t₀ : ℝ}
    (hφ : IsTrajectoryNA φ (linearVectorField A) t₀) {t : ℝ} (ht : t₀ ≤ t) :
    ‖φ t‖ ≤ ‖stateTransitionCLM A t t₀‖ * ‖φ t₀‖ := by
  rw [IsTrajectoryNA.eq_stateTransitionCLM hA hφ ht]
  exact (stateTransitionCLM A t t₀).le_opNorm _

/-! ## Definition 8.1(1): Lyapunov stability -/

/-- The operator form of Hespanha's Definition 8.1(1): stability of `ẋ = A(t) x` is a bound
on `‖Φ(t, t₀)‖`, uniform in `t` but allowed to depend on `t₀`.

This is the workhorse behind `stableNA_linearVectorField_iff`; it is stated separately because
the operator bound, not the per-initial-condition one, is what later results consume. -/
@[blueprint "lem:stableNA-linearVectorField-iff-opNorm"
  (title := "Stability as a bound on the transition operator")
  (latexEnv := "lemma")
  (statement := /-- For continuous $A$, the origin is a stable equilibrium
    (\cref{def:stableNA}) of $\dot x = A(t) x$ if and only if for every $t_{0} \ge 0$ there is
    $C$ with
    \[
      \|\Phi(t, t_{0})\| \le C, \qquad \forall\, t \ge t_{0}.
    \] -/)
  (proof := /-- ($\Rightarrow$) Apply stability at $\varepsilon = 1$ to get $\delta(1, t_{0})$.
    Every response from the ball of radius $\delta$ stays inside the unit ball, and scaling
    turns that into $\|\Phi(t,t_{0})\| \le 2/\delta$.

    ($\Leftarrow$) Given $\varepsilon$, take $\delta = \varepsilon/(C+1)$.  A trajectory is its
    own response (\cref{thm:isTrajectoryNA-eq-stateTransitionCLM}), so
    $\|\varphi(t)\| \le C\|\varphi(t_{0})\| < \varepsilon$. -/)]
theorem stableNA_linearVectorField_iff_opNorm (hA : Continuous A) :
    StableNA (linearVectorField A) (0 : ℝⁿ) ↔
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∃ C : ℝ, ∀ t ≥ t₀, ‖stateTransitionCLM A t t₀‖ ≤ C := by
  constructor
  · intro hS t₀ ht₀
    obtain ⟨δ, hδ, hstab⟩ := hS 1 one_pos t₀ ht₀
    refine ⟨2 * 1 / δ, fun t ht => opNorm_stateTransitionCLM_le_of_ball hδ zero_le_one
      fun x hx => ?_⟩
    have htraj := isTrajectoryNA_stateTransitionCLM hA t₀ x
    exact (by simpa using (hstab _ htraj (by simpa using hx) t ht).le :
      ‖stateTransitionCLM A t t₀ x‖ ≤ 1)
  · intro hbd ε hε t₀ ht₀
    obtain ⟨C, hC⟩ := hbd t₀ ht₀
    have hC'0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
    refine ⟨ε / (max C 0 + 1), by positivity, fun φ hφ hφ0 t ht => ?_⟩
    rw [sub_zero] at hφ0 ⊢
    have h1 : ‖φ t‖ ≤ max C 0 * ‖φ t₀‖ :=
      (norm_le_of_isTrajectoryNA hA hφ ht).trans
        (by gcongr; exact (hC t ht).trans (le_max_left _ _))
    have h2 : ‖φ t₀‖ * (max C 0 + 1) < ε :=
      (lt_div_iff₀ (by linarith)).1 hφ0
    nlinarith [norm_nonneg (φ t₀)]

/-- **Hespanha, Definition 8.1(1).** The system `ẋ = A(t) x` is (marginally) stable in the
sense of Lyapunov — for every initial condition `x(t₀) = x₀` the homogeneous state response
`x(t) = Φ(t, t₀) x₀` is bounded on `[t₀, ∞)` — exactly when the origin is a stable equilibrium
in the sense of `StableNA`.

The textbook's per-initial-condition form and the operator form are equivalent by
Banach–Steinhaus: a pointwise-bounded family of operators on a Banach space is
norm-bounded. -/
@[blueprint "thm:stableNA-linearVectorField-iff"
  (title := "Lyapunov stability of a linear time-varying system")
  (statement := /-- Hespanha, Definition 8.1(1).  For continuous $A$, the origin is a stable
    equilibrium (\cref{def:stableNA}) of $\dot x = A(t) x$ if and only if, for every
    $t_{0} \ge 0$ and every initial condition $x_{0} \in \mathbb{R}^{n}$, the homogeneous state
    response
    \[
      x(t) = \Phi(t, t_{0})\, x_{0}
    \]
    is bounded on $[t_{0}, \infty)$. -/)
  (proof := /-- The operator form is \cref{lem:stableNA-linearVectorField-iff-opNorm}.  An
    operator bound gives the response bound $C\|x_{0}\|$; conversely a family of operators
    bounded at every point of a Banach space is norm-bounded, by the uniform boundedness
    principle. -/)]
theorem stableNA_linearVectorField_iff (hA : Continuous A) :
    StableNA (linearVectorField A) (0 : ℝⁿ) ↔
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x₀ : ℝⁿ, ∃ C : ℝ, ∀ t ≥ t₀,
        ‖stateTransitionCLM A t t₀ x₀‖ ≤ C := by
  rw [stableNA_linearVectorField_iff_opNorm hA]
  constructor
  · intro h t₀ ht₀ x₀
    obtain ⟨C, hC⟩ := h t₀ ht₀
    exact ⟨C * ‖x₀‖, fun t ht => ((stateTransitionCLM A t t₀).le_opNorm x₀).trans
      (mul_le_mul_of_nonneg_right (hC t ht) (norm_nonneg _))⟩
  · intro h t₀ ht₀
    obtain ⟨C, hC⟩ := banach_steinhaus
      (g := fun i : {t : ℝ // t₀ ≤ t} => stateTransitionCLM A i.1 t₀)
      (fun x => by obtain ⟨C, hC⟩ := h t₀ ht₀ x; exact ⟨C, fun i => hC i.1 i.2⟩)
    exact ⟨C, fun t ht => hC ⟨t, ht⟩⟩

/-- Uniform stability is the same bound made independent of the initial time.

Khalil separates uniform stability from stability by the order of the quantifiers on `δ` and
`t₀`; on the linear side that separation is visible as whether the constant `C` bounding
`‖Φ(t, t₀)‖` may depend on `t₀`. -/
@[blueprint "thm:uniformlyStableNA-linearVectorField-iff"
  (title := "Uniform stability of a linear time-varying system")
  (statement := /-- For continuous $A$, the origin is a uniformly stable equilibrium
    (\cref{def:uniformlyStableNA}) of $\dot x = A(t) x$ if and only if there is a single $C$
    with
    \[
      \|\Phi(t, t_{0})\| \le C, \qquad \forall\, t \ge t_{0} \ge 0.
    \] -/)
  (proof := /-- Identical to \cref{lem:stableNA-linearVectorField-iff-opNorm}, with the
    margin $\delta$ and the bound $C$ both carried outside the quantifier on $t_{0}$. -/)]
theorem uniformlyStableNA_linearVectorField_iff (hA : Continuous A) :
    UniformlyStableNA (linearVectorField A) (0 : ℝⁿ) ↔
      ∃ C : ℝ, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ t ≥ t₀, ‖stateTransitionCLM A t t₀‖ ≤ C := by
  constructor
  · intro hS
    obtain ⟨δ, hδ, hstab⟩ := hS 1 one_pos
    refine ⟨2 * 1 / δ, fun t₀ ht₀ t ht => opNorm_stateTransitionCLM_le_of_ball hδ zero_le_one
      fun x hx => ?_⟩
    have htraj := isTrajectoryNA_stateTransitionCLM hA t₀ x
    exact (by simpa using (hstab t₀ ht₀ _ htraj (by simpa using hx) t ht).le :
      ‖stateTransitionCLM A t t₀ x‖ ≤ 1)
  · rintro ⟨C, hC⟩ ε hε
    have hC'0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
    refine ⟨ε / (max C 0 + 1), by positivity, fun t₀ ht₀ φ hφ hφ0 t ht => ?_⟩
    rw [sub_zero] at hφ0 ⊢
    have h1 : ‖φ t‖ ≤ max C 0 * ‖φ t₀‖ :=
      (norm_le_of_isTrajectoryNA hA hφ ht).trans
        (by gcongr; exact (hC t₀ ht₀ t ht).trans (le_max_left _ _))
    have h2 : ‖φ t₀‖ * (max C 0 + 1) < ε :=
      (lt_div_iff₀ (by linarith)).1 hφ0
    nlinarith [norm_nonneg (φ t₀)]

/-! ## Definition 8.1(2): asymptotic stability -/

/-- **Hespanha, Definition 8.1(2).** The system `ẋ = A(t) x` is asymptotically stable — stable,
and `x(t) = Φ(t, t₀) x₀ → 0` for every initial condition — exactly when the origin is
asymptotically stable in the sense of `AsymptoticStableNA`.

The boundedness clause is stated because the textbook states it ("in addition"), not because
it is needed: a continuous response that converges is bounded. -/
@[blueprint "thm:asymptoticStableNA-linearVectorField-iff"
  (title := "Asymptotic stability of a linear time-varying system")
  (statement := /-- Hespanha, Definition 8.1(2).  For continuous $A$, the origin is an
    asymptotically stable equilibrium (\cref{def:asymptoticStableNA}) of $\dot x = A(t) x$ if
    and only if, for every $t_{0} \ge 0$ and every $x_{0} \in \mathbb{R}^{n}$, the response
    $t \mapsto \Phi(t, t_{0}) x_{0}$ is bounded on $[t_{0}, \infty)$ and tends to $0$ as
    $t \to \infty$. -/)
  (proof := /-- The stability conjunct is \cref{thm:stableNA-linearVectorField-iff}.  For
    attractivity: an arbitrary $x_{0}$ is rescaled into the attractivity ball, and the limit
    scales back, since the response is linear in the initial state; conversely every trajectory
    is a response (\cref{thm:isTrajectoryNA-eq-stateTransitionCLM}), so convergence of the
    responses is convergence of the trajectories, from any radius. -/)]
theorem asymptoticStableNA_linearVectorField_iff (hA : Continuous A) :
    AsymptoticStableNA (linearVectorField A) (0 : ℝⁿ) ↔
      (∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x₀ : ℝⁿ, ∃ C : ℝ, ∀ t ≥ t₀,
        ‖stateTransitionCLM A t t₀ x₀‖ ≤ C) ∧
      (∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x₀ : ℝⁿ,
        Tendsto (fun t => stateTransitionCLM A t t₀ x₀) atTop (𝓝 0)) := by
  constructor
  · rintro ⟨hS, hattr⟩
    refine ⟨(stableNA_linearVectorField_iff hA).1 hS, fun t₀ ht₀ x₀ => ?_⟩
    obtain ⟨c, hc, hconv⟩ := hattr t₀ ht₀
    rcases eq_or_ne x₀ 0 with rfl | hx
    · simp only [map_zero]
      exact tendsto_const_nhds
    have hx0 : 0 < ‖x₀‖ := norm_pos_iff.2 hx
    set r : ℝ := c / (2 * ‖x₀‖) with hr
    have hr0 : 0 < r := div_pos hc (by positivity)
    have hnorm : ‖r • x₀‖ = c / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hr]; field_simp
    have htraj := isTrajectoryNA_stateTransitionCLM hA t₀ (r • x₀)
    have hlim := hconv _ htraj (by simpa [hnorm] using (by linarith : c / 2 < c))
    have h2 := hlim.const_smul r⁻¹
    simpa [smul_smul, inv_mul_cancel₀ hr0.ne'] using h2
  · rintro ⟨hbd, hconv⟩
    refine ⟨(stableNA_linearVectorField_iff hA).2 hbd,
      fun t₀ ht₀ => ⟨1, one_pos, fun φ hφ _ => ?_⟩⟩
    refine Filter.Tendsto.congr' ?_ (hconv t₀ ht₀ (φ t₀))
    filter_upwards [eventually_ge_atTop t₀] with t ht
    exact (IsTrajectoryNA.eq_stateTransitionCLM hA hφ ht).symm

/-! ## Definition 8.1(3): exponential stability -/

/-- **Hespanha, Definition 8.1(3)**, in its global form: the response obeys
`‖x(t)‖ ≤ k e^{-γ(t - t₀)} ‖x(t₀)‖` for every initial condition. -/
@[blueprint "thm:globallyExponentiallyStableNA-linearVectorField-iff"
  (title := "Global exponential stability of a linear time-varying system")
  (statement := /-- Hespanha, Definition 8.1(3).  For continuous $A$, the origin is a globally
    exponentially stable equilibrium (\cref{def:globallyExponentiallyStableNA}) of
    $\dot x = A(t)x$ if and only if there are $k, \gamma > 0$ with
    \[
      \|\Phi(t, t_{0})\| \le k\, e^{-\gamma (t - t_{0})},
      \qquad \forall\, t \ge t_{0} \ge 0.
    \] -/)
  (proof := /-- Both directions are the trajectory characterization plus homogeneity: the
    exponential estimate along every trajectory is the operator estimate applied to the initial
    state, and conversely the estimate on any ball scales to the operator estimate. -/)]
theorem globallyExponentiallyStableNA_linearVectorField_iff (hA : Continuous A) :
    GloballyExponentiallyStableNA (linearVectorField A) (0 : ℝⁿ) ↔
      ∃ k > 0, ∃ γ > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ t ≥ t₀,
        ‖stateTransitionCLM A t t₀‖ ≤ k * Real.exp (-γ * (t - t₀)) := by
  constructor
  · rintro ⟨k, hk, γ, hγ, hbd⟩
    refine ⟨k, hk, γ, hγ, fun t₀ ht₀ t ht => opNorm_stateTransitionCLM_le_of_ball_mul
      (c := 1) one_pos (mul_nonneg hk.le (Real.exp_pos _).le) fun x _ => ?_⟩
    have h1 : ‖stateTransitionCLM A t t₀ x‖ ≤ k * ‖x‖ * Real.exp (-γ * (t - t₀)) := by
      simpa using hbd t₀ ht₀ _ (isTrajectoryNA_stateTransitionCLM hA t₀ x) t ht
    calc ‖stateTransitionCLM A t t₀ x‖ ≤ k * ‖x‖ * Real.exp (-γ * (t - t₀)) := h1
      _ = k * Real.exp (-γ * (t - t₀)) * ‖x‖ := by ring
  · rintro ⟨k, hk, γ, hγ, hbd⟩
    refine ⟨k, hk, γ, hγ, fun t₀ ht₀ φ hφ t ht => ?_⟩
    rw [sub_zero, sub_zero]
    calc ‖φ t‖ ≤ ‖stateTransitionCLM A t t₀‖ * ‖φ t₀‖ := norm_le_of_isTrajectoryNA hA hφ ht
      _ ≤ k * Real.exp (-γ * (t - t₀)) * ‖φ t₀‖ := by
          gcongr; exact hbd t₀ ht₀ t ht
      _ = k * ‖φ t₀‖ * Real.exp (-γ * (t - t₀)) := by ring

/-- **Hespanha, Definition 8.1(3)**, in its local form. The right-hand side is the same as in
`globallyExponentiallyStableNA_linearVectorField_iff`: the radius `c` of the local definition
carries no information for a linear system. -/
@[blueprint "thm:exponentiallyStableNA-linearVectorField-iff"
  (title := "Exponential stability of a linear time-varying system")
  (statement := /-- For continuous $A$, the origin is an exponentially stable equilibrium
    (\cref{def:exponentiallyStableNA}) of $\dot x = A(t)x$ if and only if there are
    $k, \gamma > 0$ with
    \[
      \|\Phi(t, t_{0})\| \le k\, e^{-\gamma (t - t_{0})},
      \qquad \forall\, t \ge t_{0} \ge 0.
    \]
    The condition is the one in
    \cref{thm:globallyExponentiallyStableNA-linearVectorField-iff}: the radius in the local
    definition carries no information here. -/)
  (proof := /-- As in the global case; the radius $c$ of the local definition is absorbed by
    the scaling argument, and $c = 1$ serves in the converse. -/)]
theorem exponentiallyStableNA_linearVectorField_iff (hA : Continuous A) :
    ExponentiallyStableNA (linearVectorField A) (0 : ℝⁿ) ↔
      ∃ k > 0, ∃ γ > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ t ≥ t₀,
        ‖stateTransitionCLM A t t₀‖ ≤ k * Real.exp (-γ * (t - t₀)) := by
  constructor
  · rintro ⟨c, hc, k, hk, γ, hγ, hbd⟩
    refine ⟨k, hk, γ, hγ, fun t₀ ht₀ t ht => opNorm_stateTransitionCLM_le_of_ball_mul
      hc (mul_nonneg hk.le (Real.exp_pos _).le) fun x hx => ?_⟩
    have h1 : ‖stateTransitionCLM A t t₀ x‖ ≤ k * ‖x‖ * Real.exp (-γ * (t - t₀)) := by
      simpa using hbd t₀ ht₀ _ (isTrajectoryNA_stateTransitionCLM hA t₀ x)
        (by simpa using hx) t ht
    calc ‖stateTransitionCLM A t t₀ x‖ ≤ k * ‖x‖ * Real.exp (-γ * (t - t₀)) := h1
      _ = k * Real.exp (-γ * (t - t₀)) * ‖x‖ := by ring
  · rintro ⟨k, hk, γ, hγ, hbd⟩
    refine ⟨1, one_pos, k, hk, γ, hγ, fun t₀ ht₀ φ hφ _ t ht => ?_⟩
    rw [sub_zero, sub_zero]
    calc ‖φ t‖ ≤ ‖stateTransitionCLM A t t₀‖ * ‖φ t₀‖ := norm_le_of_isTrajectoryNA hA hφ ht
      _ ≤ k * Real.exp (-γ * (t - t₀)) * ‖φ t₀‖ := by
          gcongr; exact hbd t₀ ht₀ t ht
      _ = k * ‖φ t₀‖ * Real.exp (-γ * (t - t₀)) := by ring

/-- For a linear system, exponential stability is automatically global.

A linear system has no nontrivial region of attraction: the two definitions differ only by a
radius, and the response is homogeneous, so the radius scales away. -/
@[blueprint "cor:exponentiallyStableNA-iff-globallyExponentiallyStableNA"
  (title := "Local exponential stability is global, for a linear system")
  (latexEnv := "lemma")
  (statement := /-- For continuous $A$, the origin of $\dot x = A(t)x$ is exponentially stable
    (\cref{def:exponentiallyStableNA}) if and only if it is globally exponentially stable
    (\cref{def:globallyExponentiallyStableNA}). -/)
  (proof := /-- Both are equivalent to the same operator estimate,
    \cref{thm:exponentiallyStableNA-linearVectorField-iff} and
    \cref{thm:globallyExponentiallyStableNA-linearVectorField-iff}. -/)]
theorem exponentiallyStableNA_iff_globallyExponentiallyStableNA (hA : Continuous A) :
    ExponentiallyStableNA (linearVectorField A) (0 : ℝⁿ) ↔
      GloballyExponentiallyStableNA (linearVectorField A) (0 : ℝⁿ) :=
  (exponentiallyStableNA_linearVectorField_iff hA).trans
    (globallyExponentiallyStableNA_linearVectorField_iff hA).symm

/-! ## Definition 8.1(4): instability -/

/-- **Hespanha, Definition 8.1(4).** The system is unstable when it is not marginally stable:
some initial condition has an unbounded homogeneous response. -/
@[blueprint "thm:unstableNA-linearVectorField-iff"
  (title := "Instability of a linear time-varying system")
  (statement := /-- Hespanha, Definition 8.1(4).  For continuous $A$, the origin of
    $\dot x = A(t)x$ is unstable (\cref{def:unstableNA}) if and only if there are
    $t_{0} \ge 0$ and $x_{0} \in \mathbb{R}^{n}$ whose homogeneous response
    $t \mapsto \Phi(t, t_{0}) x_{0}$ is unbounded on $[t_{0}, \infty)$. -/)
  (proof := /-- The negation of \cref{thm:stableNA-linearVectorField-iff}. -/)]
theorem unstableNA_linearVectorField_iff (hA : Continuous A) :
    UnstableNA (linearVectorField A) (0 : ℝⁿ) ↔
      ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∃ x₀ : ℝⁿ, ∀ C : ℝ, ∃ t ≥ t₀,
        C < ‖stateTransitionCLM A t t₀ x₀‖ := by
  rw [UnstableNA, stableNA_linearVectorField_iff hA]
  push Not
  rfl

end LinearSystems

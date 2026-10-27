import LeanForControl.ODEs.PeanoBaker
import LeanForControl.LinearSystems.Solutions.DefsCtsLTV
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Architect

/-!
# Continuous-time solutions of linear time-varying systems

The solution theory of `ẋ = A(t) x + B(t) u(t)`, read on the system object `ContinuousLTV`:
Theorem 5.1 (the homogeneous response `Φ(t, t₀) x₀` is the unique trajectory from `x₀`) and
Theorem 5.2 (variation of constants: the forced response is the unique trajectory under the
input `u`).

The analysis is the Banach-algebra theory of `PeanoBaker.lean`, at the algebra of operators on
the state space; this file applies it to states. Uniqueness is the integrating
factor: along a trajectory, `Φ(t₀, r) x(r)` has derivative `Φ(t₀, r) B(r) u(r)`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5.
-/

namespace LinearSystems

open Matrix MeasureTheory

namespace ContinuousLTV

variable {E U Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [CompleteSpace E] in
@[simp] lemma stateTransition_self (s : ContinuousLTV E U Y) (t : ℝ) (x : E) :
    s.stateTransition t t x = x := by
  simp [stateTransition, stateTransitionMatrix_self]

/-- **The state transition operator solves `Φ̇ = A Φ`**, at every time, read on the system. -/
lemma hasDerivAt_stateTransition (s : ContinuousLTV E U Y) (hA : Continuous s.A) (t t₀ : ℝ) :
    HasDerivAt (fun t => s.stateTransition t t₀)
      (s.A t * s.stateTransition t t₀) t :=
  hasDerivAt_stateTransitionMatrix hA t t₀

/-- **The derivative in the initial time**, read on the system:
`∂Φ(t, τ)/∂τ = -Φ(t, τ) A(τ)`. -/
lemma hasDerivAt_stateTransition_snd (s : ContinuousLTV E U Y) (hA : Continuous s.A)
    (t τ : ℝ) :
    HasDerivAt (fun σ => s.stateTransition t σ)
      (-(s.stateTransition t τ * s.A τ)) τ :=
  hasDerivAt_stateTransitionMatrix_snd hA t τ

/-- **The semigroup property**, on states: `Φ(t, σ) Φ(σ, τ) x = Φ(t, τ) x`, for all times in any
order. -/
@[blueprint "thm:continuousLTV-stateTransition-comp"
  (title := "Semigroup property of the state transition operator")
  (statement := /-- For $A$ continuous, $\Phi(t, \sigma)\,\Phi(\sigma, \tau)\,x = \Phi(t, \tau)\,x$
    for all $t, \sigma, \tau$ and every state $x$. -/)
  (proof := /-- \cref{thm:stateTransitionMatrix-mul} in the algebra of operators. -/)]
lemma stateTransition_comp (s : ContinuousLTV E U Y) (hA : Continuous s.A) (t σ τ : ℝ)
    (x : E) :
    s.stateTransition t σ (s.stateTransition σ τ x) = s.stateTransition t τ x := by
  rw [stateTransition, stateTransition, stateTransition,
    ← stateTransitionMatrix_mul hA t σ τ]
  rfl

/-- The semigroup property as a product of operators: `Φ(t, σ) Φ(σ, τ) = Φ(t, τ)`. -/
lemma stateTransition_mul (s : ContinuousLTV E U Y) (hA : Continuous s.A) (t σ τ : ℝ) :
    s.stateTransition t σ * s.stateTransition σ τ = s.stateTransition t τ :=
  ContinuousLinearMap.ext (s.stateTransition_comp hA t σ τ)

/-- The state transition operator is continuous in the current time. -/
lemma continuous_stateTransition (s : ContinuousLTV E U Y) (hA : Continuous s.A) (t₀ : ℝ) :
    Continuous fun t => s.stateTransition t t₀ :=
  continuous_iff_continuousAt.2 fun t => (s.hasDerivAt_stateTransition hA t t₀).continuousAt

/-- The state transition operator is continuous in the initial time. -/
lemma continuous_stateTransition_snd (s : ContinuousLTV E U Y) (hA : Continuous s.A) (t : ℝ) :
    Continuous fun τ => s.stateTransition t τ :=
  continuous_iff_continuousAt.2 fun τ => (s.hasDerivAt_stateTransition_snd hA t τ).continuousAt

/-- The homogeneous response is a trajectory of the system under zero input, at every time.

No hypothesis on `B` appears: the forcing term is switched off, so only `A` is involved.
Hespanha's Definition 8.1 is stated about this map, so this is the form in which the solution
theory reaches the stability theory. -/
@[blueprint "thm:isTrajectory-homogeneousResponse"
  (title := "The homogeneous response is a trajectory")
  (statement := /-- For a continuous-time linear system with continuous $A$, the homogeneous
    response $t \mapsto \Phi(t, t_0)\,x_0$ from any state $x_0$ at any time $t_0$ is a
    trajectory (\cref{def:continuousLTV-isTrajectory}) under zero input.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, Theorem 5.1. -/)
  (proof := /-- Apply \cref{thm:hasDerivAt-stateTransitionMatrix} to the fixed state $x_0$. -/)]
theorem isTrajectory_homogeneousResponse (s : ContinuousLTV E U Y)
    (hA : Continuous s.A) (t₀ : ℝ) (x₀ : E) :
    s.IsTrajectory 0 (fun t => s.stateTransition t t₀ x₀) := fun t => by
  simpa using (s.hasDerivAt_stateTransition hA t t₀).clm_apply (hasDerivAt_const t x₀)

/-- The homogeneous response is a trajectory of the unforced system on the forward ray, the
interval the stability predicates quantify over. -/
@[blueprint "thm:isTrajectoryOn-homogeneousResponse"
  (title := "The homogeneous response is a trajectory on the forward ray")
  (statement := /-- The homogeneous response $t \mapsto \Phi(t, t_0)\,x_0$ is a trajectory of
    the unforced system (\cref{def:continuousLTV-isTrajectoryOn}) on $[t_{0}, \infty)$. -/)
  (proof := /-- \cref{thm:isTrajectory-homogeneousResponse}, restricted to the ray by
    \cref{lem:continuousSystem-isTrajectory-isTrajectoryOn}. -/)]
theorem isTrajectoryOn_homogeneousResponse (s : ContinuousLTV E U Y)
    (hA : Continuous s.A) (t₀ : ℝ) (x₀ : E) :
    s.IsTrajectoryOn 0 (fun t => s.stateTransition t t₀ x₀) (Set.Ici t₀) :=
  (isTrajectory_homogeneousResponse s hA t₀ x₀).isTrajectoryOn _

/-- Every trajectory of the unforced system is its own homogeneous response.

The integrating factor: along a trajectory `x`, `Φ(t₀, r) x(r)` has derivative
`-Φ(t₀, r) A(r) x(r) + Φ(t₀, r) A(r) x(r) = 0`, so it is constant, equal to `x(t₀)`; apply
`Φ(t, t₀)`. -/
@[blueprint "thm:eq-homogeneousResponse-of-isTrajectoryOn"
  (title := "Trajectories of the unforced system are homogeneous responses")
  (statement := /-- Let $s$ have continuous $A$ and let $\varphi$ be a trajectory of the
    unforced system on $[t_{0}, t_{1}]$ (\cref{def:continuousLTV-isTrajectoryOn}).  Then
    $\varphi(t) = \Phi(t, t_{0})\,\varphi(t_{0})$ for every $t \in [t_{0}, t_{1}]$
    (\cref{def:continuousLTV-stateTransition}).

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, Theorem 5.1. -/)
  (proof := /-- $r \mapsto \Phi(t_0, r)\,\varphi(r)$ has derivative
    $-\Phi(t_0, r) A(r) \varphi(r) + \Phi(t_0, r) A(r) \varphi(r) = 0$
    (\cref{thm:hasDerivAt-stateTransitionMatrix-snd}), so it is constant on $[t_0, t_1]$, equal
    to $\varphi(t_0)$.  Apply $\Phi(t, t_0)$ and use
    \cref{thm:continuousLTV-stateTransition-comp}. -/)]
theorem eq_homogeneousResponse_of_isTrajectoryOn (s : ContinuousLTV E U Y)
    (hA : Continuous s.A) {x : ℝ → E} {t₀ t₁ : ℝ}
    (hx : s.IsTrajectoryOn 0 x (Set.Icc t₀ t₁)) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    x t = s.stateTransition t t₀ (x t₀) := by
  have hd : ∀ r ∈ Set.Icc t₀ t₁,
      HasDerivWithinAt (fun r => s.stateTransition t₀ r (x r)) 0 (Set.Icc t₀ t₁) r := by
    intro r hr
    convert (s.hasDerivAt_stateTransition_snd hA t₀ r).hasDerivWithinAt.clm_apply (hx r hr)
      using 1
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_mul', Function.comp_apply,
      ContinuousSystem.vectorField_apply, Pi.zero_apply, toContinuousSystem_F, map_zero, add_zero]
    rw [eq_comm, neg_add_eq_zero]
  have h_const : s.stateTransition t₀ t (x t) = x t₀ := by
    simpa using constant_of_has_deriv_right_zero (fun r hr => (hd r hr).continuousWithinAt)
      (fun r hr => (hd r (Set.Ico_subset_Icc_self hr)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hr)) t ht
  rw [← h_const, stateTransition_comp s hA, stateTransition_self]

/-- **The unforced system of an LTV system is forward complete.**  Every trajectory segment is
the restriction of a homogeneous response, which is a trajectory for all time. -/
@[blueprint "thm:continuousLTV-isForwardComplete-zeroInput"
  (title := "Linear systems are forward complete")
  (statement := /-- If $A$ is continuous, the unforced system
    (\cref{def:continuousSystem-zeroInput}) of \cref{def:continuousLTV-toContinuousSystem} is
    forward complete (\cref{def:continuousSystem-isForwardComplete}). -/)
  (proof := /-- A trajectory on $[t_0, t_1]$ agrees there with the homogeneous response from its
    initial state (\cref{thm:eq-homogeneousResponse-of-isTrajectoryOn}), which is a trajectory
    on $[t_0, \infty)$ (\cref{thm:isTrajectoryOn-homogeneousResponse}). -/)]
theorem isForwardComplete_zeroInput (s : ContinuousLTV E U Y) (hA : Continuous s.A) :
    s.toContinuousSystem.zeroInput.IsForwardComplete (fun _ => ()) :=
  fun t₀ _ x _ hx _ => ⟨fun t => s.stateTransition t t₀ (x t₀),
    isTrajectoryOn_homogeneousResponse s hA t₀ (x t₀),
    fun _ ht => (eq_homogeneousResponse_of_isTrajectoryOn s hA hx ht).symm⟩

/-- **The unforced system of an LTV system has unique solutions**: two trajectories on a segment
that agree at its start are both the homogeneous response from that state. -/
@[blueprint "thm:continuousLTV-hasUniqueSolutions-zero"
  (title := "Linear systems have unique solutions")
  (statement := /-- If $A$ is continuous, the system of \cref{def:continuousLTV-toContinuousSystem}
    has unique solutions (\cref{def:continuousSystem-hasUniqueSolutions}) under zero input. -/)
  (proof := /-- Both trajectories are the homogeneous response from their common initial state
    (\cref{thm:eq-homogeneousResponse-of-isTrajectoryOn}). -/)]
theorem hasUniqueSolutions_zero (s : ContinuousLTV E U Y) (hA : Continuous s.A) :
    s.toContinuousSystem.HasUniqueSolutions 0 := fun _ _ x y hx hy h₀ _ ht => by
  rw [eq_homogeneousResponse_of_isTrajectoryOn s hA hx ht,
    eq_homogeneousResponse_of_isTrajectoryOn s hA hy ht, h₀]

/-- **The state transition map of a linear system is its state transition operator**: under zero
input, the general state transition map `φ(t; t₀, x₀)` of `s`
(`ContinuousSystem.stateTransitionMap`) is `Φ(t, t₀) x₀`, for `t ≥ t₀`.

The general theory of continuous-time systems therefore applies to linear systems with no
translation layer. -/
@[blueprint "thm:continuousLTV-stateTransitionMap-zero"
  (title := "The state transition map of a linear system")
  (statement := /-- If $A$ is continuous, then under zero input the state transition map
    (\cref{def:continuousSystem-stateTransitionMap}) of the system of
    \cref{def:continuousLTV-toContinuousSystem} is
    \[
      \varphi(t; t_0, x_0) = \Phi(t, t_0)\,x_0, \qquad t \ge t_0,
    \]
    with $\Phi$ the state transition operator (\cref{def:continuousLTV-stateTransition}). -/)
  (proof := /-- The homogeneous response is a trajectory on $[t_0, t]$
    (\cref{thm:isTrajectoryOn-homogeneousResponse}) and solutions are unique
    (\cref{thm:continuousLTV-hasUniqueSolutions-zero}), so it is given by the state transition
    map (\cref{lem:continuousSystem-eq-stateTransitionMap}). -/)]
theorem stateTransitionMap_zero (s : ContinuousLTV E U Y) (hA : Continuous s.A) {t₀ t : ℝ}
    (ht : t₀ ≤ t) (x₀ : E) :
    s.toContinuousSystem.stateTransitionMap 0 t t₀ x₀ = s.stateTransition t t₀ x₀ := by
  have h := ContinuousSystem.eq_stateTransitionMap (hasUniqueSolutions_zero s hA)
    (IsIntegralCurveOn.mono (isTrajectoryOn_homogeneousResponse s hA t₀ x₀)
      Set.Icc_subset_Ici_self) t ⟨ht, le_rfl⟩
  rw [h, stateTransition_self]

/-! ## The forced response -/

omit [CompleteSpace E] in
@[simp] lemma forcedResponse_self (s : ContinuousLTV E U Y) (u : ℝ → U)
    (t₀ : ℝ) (x₀ : E) : s.forcedResponse u t₀ x₀ t₀ = x₀ := by
  simp [forcedResponse]

/-- **The forced response is a trajectory**, at every time (Hespanha, Theorem 5.2).

Write `x(t) = Φ(t, t₀) w(t)` with `w(t) = x₀ + ∫ τ in t₀..t, Φ(t₀, τ) B(τ) u(τ) dτ`, using the
semigroup property under the integral. Then the product rule gives
`ẋ = A(t) Φ(t, t₀) w(t) + Φ(t, t₀) Φ(t₀, t) B(t) u(t) = A(t) x(t) + B(t) u(t)`. -/
@[blueprint "thm:isTrajectory-forcedResponse"
  (title := "The forced response is a trajectory")
  (statement := /-- Let $s$ be a continuous-time linear system with continuous coefficients
    $A$ and $B$, and let $u$ be a continuous input.  Then the forced response
    (\cref{def:forcedResponse}) from any state $x_0$ at any time $t_0$ is a trajectory of $s$
    (\cref{def:continuousLTV-isTrajectory}): it satisfies the state equation at every
    $t \in \mathbb{R}$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, Theorem 5.2.
  -/)
  (proof := /-- By the semigroup property (\cref{thm:continuousLTV-stateTransition-comp}),
    $x(t) = \Phi(t, t_0)\,w(t)$ with
    $w(t) = x_0 + \int_{t_0}^{t} \Phi(t_0, \tau) B(\tau) u(\tau)\,d\tau$.  Differentiate the
    product: $\Phi(\cdot, t_0)$ by \cref{thm:hasDerivAt-stateTransitionMatrix}, and $w$ by the
    fundamental theorem of calculus. -/)]
theorem isTrajectory_forcedResponse (s : ContinuousLTV E U Y) (hA : Continuous s.A)
    (hB : Continuous s.B) {u : ℝ → U} (hu : Continuous u) (t₀ : ℝ)
    (x₀ : E) :
    s.IsTrajectory u (s.forcedResponse u t₀ x₀) := by
  set g : ℝ → E := fun τ => s.B τ (u τ)
  have hg : Continuous g := hB.clm_apply hu
  have hΦg : Continuous fun τ => s.stateTransition t₀ τ (g τ) :=
    (s.continuous_stateTransition_snd hA t₀).clm_apply hg
  have h_eq : s.forcedResponse u t₀ x₀ =
      fun t => s.stateTransition t t₀ (x₀ + ∫ τ in t₀..t, s.stateTransition t₀ τ (g τ)) := by
    funext t
    rw [map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hΦg.intervalIntegrable _ _)]
    simp only [forcedResponse, stateTransition_comp s hA, g]
  rw [h_eq]
  intro t
  convert (s.hasDerivAt_stateTransition hA t t₀).clm_apply
    ((hasDerivAt_const t x₀).add (hΦg.integral_hasStrictDerivAt t₀ t).hasDerivAt) using 1
  simp [stateTransition_comp s hA, g]

/-- **Every trajectory under the input `u` is the forced response** from its initial state
(Hespanha, Theorem 5.2, uniqueness).

The difference of a trajectory and the forced response is a trajectory of the unforced system
that starts at `0`, hence is `0` (`eq_homogeneousResponse_of_isTrajectoryOn`). -/
@[blueprint "thm:eq-forcedResponse-of-isTrajectoryOn"
  (title := "Trajectories are forced responses")
  (statement := /-- Let $A$, $B$ and $u$ be continuous and let $x$ be a trajectory of $s$ under
    $u$ on $[t_0, t_1]$ (\cref{def:continuousLTV-isTrajectoryOn}).  Then $x$ is the forced
    response (\cref{def:forcedResponse}) from $x(t_0)$ there.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, Theorem 5.2. -/)
  (proof := /-- $x$ minus the forced response is a trajectory of the unforced system
    (\cref{thm:isTrajectory-forcedResponse}) starting at $0$, so it is
    $\Phi(t, t_0)\,0 = 0$ (\cref{thm:eq-homogeneousResponse-of-isTrajectoryOn}). -/)]
theorem eq_forcedResponse_of_isTrajectoryOn (s : ContinuousLTV E U Y) (hA : Continuous s.A)
    (hB : Continuous s.B) {u : ℝ → U} (hu : Continuous u)
    {x : ℝ → E} {t₀ t₁ : ℝ} (hx : s.IsTrajectoryOn u x (Set.Icc t₀ t₁)) {t : ℝ}
    (ht : t ∈ Set.Icc t₀ t₁) : x t = s.forcedResponse u t₀ (x t₀) t := by
  have hd : s.IsTrajectoryOn 0 (fun r => x r - s.forcedResponse u t₀ (x t₀) r) (Set.Icc t₀ t₁) :=
    fun r hr => by
      convert (hx r hr).sub
        (isTrajectory_forcedResponse s hA hB hu t₀ (x t₀) r).hasDerivWithinAt using 1
      simp
  have h := eq_homogeneousResponse_of_isTrajectoryOn s hA hd ht
  rw [forcedResponse_self, sub_self, map_zero] at h
  exact sub_eq_zero.1 h

end ContinuousLTV

end LinearSystems

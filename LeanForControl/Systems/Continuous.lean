import LeanForControl.Analysis.DiniDeriv
import LeanForControl.Analysis.LieDerivative
import LeanForControl.Analysis.IntegralCurves
import LeanForControl.ODEs.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Architect

/-!
# `Systems.Continuous` — the general continuous-time system

The most general continuous-time system the library considers,

* `ContinuousSystem E U Y` — `ẋ = F(t, x, u)`, `y = h(t, x, u)`, with `t ∈ ℝ`,

with state space `E`, input space `U` and output space `Y`.  The linear systems of
`LinearSystems.Continuous` are special cases.  Its discrete-time counterpart is
`DiscreteSystem` in `Systems.Discrete`, which carries the same API under the same names.

## Special cases

Each special case is a constructor building the general object from the special data, together
with a predicate recognising it inside a general system and a lemma relating the two:

* **Time invariance** — `t` is dropped: `timeInvariant f h` builds `F(t, x, u) = f(x, u)`, and
  `IsTimeInvariant` says `F` and `h` do not depend on time.
* **Autonomy** — `u` is dropped: `autonomous f h` builds a system with input space `Unit`, and
  `IsAutonomous` says `F` and `h` do not depend on the input.

The two combine: `timeInvariant` applied to input-free data gives `ẋ = f(x)`.

"Autonomous" here means *without input*, the control-theory convention.  Much of the
dynamical-systems literature, including Khalil, uses it for *time-invariant* instead.

## Trajectories

There are two trajectory predicates, for two kinds of input.

* **`IsTrajectoryOn s u x I`** is the derivative form, Mathlib's `IsIntegralCurveOn`:
  `ẋ(t) = F(t, x(t), u(t))` for every `t ∈ I`, the derivative taken *within* `I`.  It is the
  form the Lyapunov machinery works with, and the natural one for continuous inputs.  Two
  caveats: at an isolated point of `I` the derivative within `I` is unconstrained, so `I` should
  be a nondegenerate segment `[t₀, t₁]` or a ray `[t₀, ∞)`; and `x` must be differentiable
  everywhere on `I`, which excludes the solutions produced by discontinuous inputs (under a step
  input, `ẋ = u` has a corner).
* **`IsCaratheodoryTrajectoryOn s u x I`** is the integral form: between any `a ≤ b` in `I`,
  `x(b) - x(a) = ∫ₐᵇ F(τ, x(τ), u(τ)) dτ`.  It needs `E` complete but not `x` differentiable, so it
  admits piecewise-constant, sampled-data, bang-bang and merely measurable inputs.  Input-driven
  notions such as input-to-state stability are stated with it.

When `τ ↦ F(τ, x(τ), u(τ))` is continuous the two agree on segments and on rays
(`isCaratheodoryTrajectoryOn_iff_isTrajectoryOn`), via the
integral-solution bridge `isIntegralSolution_iff_isIntegralCurveOn`.  Neither handles
discontinuity in the *state*, such as discontinuous feedback, which needs Filippov solutions.

## Why separate continuous- and discrete-time objects

The same reasons as for `ContinuousLTV` and `DiscreteLTV`: the data is the same
shape, but its reading is not.  A continuous trajectory is an integral curve and needs a normed
space; a discrete one is a recursion and needs nothing.  A change of coordinates picks up a
time-derivative term in continuous time and none in discrete time.  Separate files also keep the
analysis imports out of discrete-time developments, and leave room for further classes, such as
hybrid systems, as files of their own.

## Conventions

* The structure carries no typeclasses: structure on `E`, `U`, `Y` goes on the operations that
  need it.
* The API lives in the namespace `ContinuousSystem`, so dot notation resolves.
-/

/-- A continuous-time system: the data `(F, h)` of

    ẋ(t) = F(t, x(t), u(t)),    y(t) = h(t, x(t), u(t))

with states in `E`, inputs in `U` and outputs in `Y`.  The structure is only the data. -/
@[blueprint "def:continuousSystem"
  (title := "Continuous-time system")
  (statement := /-- A \emph{continuous-time system} with state space $E$, input space $U$ and
    output space $Y$ is the data of two maps
    \[
      F : \mathbb{R} \times E \times U \to E, \qquad h : \mathbb{R} \times E \times U \to Y,
    \]
    to be read as $\dot x = F(t, x, u)$, $y = h(t, x, u)$.  The structure is only the data. -/)]
structure ContinuousSystem (E U Y : Type*) where
  /-- State equation: `ẋ = F(t, x, u)`. -/
  F : ℝ → E → U → E
  /-- Output equation: `y = h(t, x, u)`. -/
  h : ℝ → E → U → Y

namespace ContinuousSystem

variable {E U Y : Type*}

/-- The time-invariant system `ẋ = f(x, u)`, `y = g(x, u)`. -/
@[blueprint "def:continuousSystem-timeInvariant"
  (title := "Time-invariant continuous-time system")
  (statement := /-- The continuous-time system $\dot x = f(x, u)$, $y = g(x, u)$, whose
    equations do not depend on time. -/)]
def timeInvariant (f : E → U → E) (g : E → U → Y) : ContinuousSystem E U Y where
  F := fun _ => f
  h := fun _ => g

@[simp] lemma timeInvariant_F (f : E → U → E) (g : E → U → Y) (t : ℝ) :
    (timeInvariant f g).F t = f := rfl

@[simp] lemma timeInvariant_h (f : E → U → E) (g : E → U → Y) (t : ℝ) :
    (timeInvariant f g).h t = g := rfl

/-- The system is *time-invariant*: its equations take the same form at every time. -/
@[blueprint "def:continuousSystem-isTimeInvariant"
  (title := "Time invariance, continuous-time system")
  (statement := /-- A continuous-time system is \emph{time-invariant} when $F(t, \cdot, \cdot)$
    and $h(t, \cdot, \cdot)$ are the same for every $t$. -/)]
def IsTimeInvariant (s : ContinuousSystem E U Y) : Prop :=
  ∀ t t' : ℝ, s.F t = s.F t' ∧ s.h t = s.h t'

/-- A system built by `timeInvariant` is time-invariant. -/
@[blueprint "lem:continuousSystem-isTimeInvariant-timeInvariant"
  (title := "Time-invariant continuous-time systems are time-invariant")
  (latexEnv := "lemma")
  (statement := /-- The system of \cref{def:continuousSystem-timeInvariant} is time-invariant
    (\cref{def:continuousSystem-isTimeInvariant}). -/)]
theorem isTimeInvariant_timeInvariant (f : E → U → E) (g : E → U → Y) :
    (timeInvariant f g).IsTimeInvariant :=
  fun _ _ => ⟨rfl, rfl⟩

/-- A time-invariant system is built by `timeInvariant`. -/
@[blueprint "lem:continuousSystem-isTimeInvariant-exists-eq"
  (title := "Time-invariant continuous-time systems come from time-free data")
  (latexEnv := "lemma")
  (statement := /-- A time-invariant continuous-time system
    (\cref{def:continuousSystem-isTimeInvariant}) is $\operatorname{timeInvariant} f\,g$ for some
    $f$ and $g$.  The converse of \cref{lem:continuousSystem-isTimeInvariant-timeInvariant}. -/)
  (proof := /-- Read $f$ and $g$ off at $t = 0$; time invariance says every other time agrees with
    it. -/)]
theorem IsTimeInvariant.exists_eq {s : ContinuousSystem E U Y} (hs : s.IsTimeInvariant) :
    ∃ (f : E → U → E) (g : E → U → Y), s = timeInvariant f g := by
  refine ⟨s.F 0, s.h 0, ?_⟩
  obtain ⟨sF, sh⟩ := s
  simp only [timeInvariant, mk.injEq]
  exact ⟨funext fun t => (hs t 0).1, funext fun t => (hs t 0).2⟩

/-- The autonomous (input-free) system `ẋ = f(t, x)`, `y = g(t, x)`, with input space `Unit`. -/
@[blueprint "def:continuousSystem-autonomous"
  (title := "Autonomous continuous-time system")
  (statement := /-- The continuous-time system $\dot x = f(t, x)$, $y = g(t, x)$, which has no
    input: its input space is the one-point type. -/)]
def autonomous (f : ℝ → E → E) (g : ℝ → E → Y) : ContinuousSystem E Unit Y where
  F := fun t x _ => f t x
  h := fun t x _ => g t x

@[simp] lemma autonomous_F (f : ℝ → E → E) (g : ℝ → E → Y) (t : ℝ) (x : E) (u : Unit) :
    (autonomous f g).F t x u = f t x := rfl

@[simp] lemma autonomous_h (f : ℝ → E → E) (g : ℝ → E → Y) (t : ℝ) (x : E) (u : Unit) :
    (autonomous f g).h t x u = g t x := rfl

/-- The system is *autonomous*: its equations do not depend on the input. -/
@[blueprint "def:continuousSystem-isAutonomous"
  (title := "Autonomy, continuous-time system")
  (statement := /-- A continuous-time system is \emph{autonomous} when $F(t, x, u)$ and
    $h(t, x, u)$ do not depend on $u$. -/)]
def IsAutonomous (s : ContinuousSystem E U Y) : Prop :=
  ∀ (t : ℝ) (x : E) (u u' : U), s.F t x u = s.F t x u' ∧ s.h t x u = s.h t x u'

/-- A system built by `autonomous` is autonomous. -/
@[blueprint "lem:continuousSystem-isAutonomous-autonomous"
  (title := "Autonomous continuous-time systems are autonomous")
  (latexEnv := "lemma")
  (statement := /-- The system of \cref{def:continuousSystem-autonomous} is autonomous
    (\cref{def:continuousSystem-isAutonomous}). -/)]
theorem isAutonomous_autonomous (f : ℝ → E → E) (g : ℝ → E → Y) :
    (autonomous f g).IsAutonomous :=
  fun _ _ _ _ => ⟨rfl, rfl⟩

/-- An autonomous system is input-free data in disguise: its equations are those of some `f` and
`g` that do not take an input.  It equals `autonomous f g` only up to the input space, which is
`U` rather than `Unit`. -/
@[blueprint "lem:continuousSystem-isAutonomous-exists"
  (title := "Autonomous continuous-time systems come from input-free data")
  (latexEnv := "lemma")
  (statement := /-- If a continuous-time system is autonomous
    (\cref{def:continuousSystem-isAutonomous}) and its input space is nonempty, there are
    $f$ and $g$ with $F(t, x, u) = f(t, x)$ and $h(t, x, u) = g(t, x)$ for every input $u$. -/)
  (proof := /-- Fix any input $u_0$ and read $f$ and $g$ off at it. -/)]
theorem IsAutonomous.exists_eq [Nonempty U] {s : ContinuousSystem E U Y} (hs : s.IsAutonomous) :
    ∃ (f : ℝ → E → E) (g : ℝ → E → Y), ∀ t x u, s.F t x u = f t x ∧ s.h t x u = g t x := by
  obtain ⟨u₀⟩ := ‹Nonempty U›
  exact ⟨fun t x => s.F t x u₀, fun t x => s.h t x u₀, fun t x u => hs t x u u₀⟩

/-! ### Semantics -/

/-- The right-hand side of the state equation under the input signal `u`,
`(t, x) ↦ F(t, x, u(t))`: a time-dependent vector field on the state space, the shape the ODE
machinery consumes. -/
@[blueprint "def:continuousSystem-vectorField"
  (title := "State equation of a continuous-time system")
  (statement := /-- Under an input signal $u : \mathbb{R} \to U$, the right-hand side of the
    state equation is the time-dependent vector field $(t, x) \mapsto F(t, x, u(t))$. -/)]
def vectorField (s : ContinuousSystem E U Y) (u : ℝ → U) : ℝ → E → E :=
  fun t x => s.F t x (u t)

/-- The output equation under the input signal `u`, `(t, x) ↦ h(t, x, u(t))`. -/
@[blueprint "def:continuousSystem-outputMap"
  (title := "Output equation of a continuous-time system")
  (statement := /-- Under an input signal $u$, the output equation is
    $(t, x) \mapsto h(t, x, u(t))$.  An instantaneous relation: no derivative appears. -/)]
def outputMap (s : ContinuousSystem E U Y) (u : ℝ → U) : ℝ → E → Y :=
  fun t x => s.h t x (u t)

@[simp] lemma vectorField_apply (s : ContinuousSystem E U Y) (u : ℝ → U) (t : ℝ) (x : E) :
    s.vectorField u t x = s.F t x (u t) := rfl

@[simp] lemma outputMap_apply (s : ContinuousSystem E U Y) (u : ℝ → U) (t : ℝ) (x : E) :
    s.outputMap u t x = s.h t x (u t) := rfl

section Trajectory

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `x` is a trajectory of `s` under the input `u` on the set `I`: `ẋ(t) = F(t, x(t), u(t))`
for every `t ∈ I`, the derivative taken within `I`.

Stated on a set rather than on all of `ℝ`, because a map can satisfy the equation on an
interval without being defined for all time.  Which set — a segment `[t₀, t₁]` or a ray
`[t₀, ∞)` — is chosen by the notions built on this one, not here.  The output is
`s.outputMap u t (x t)`; it is not part of this predicate, because the output equation
constrains nothing about `x`. -/
@[blueprint "def:continuousSystem-isTrajectoryOn"
  (title := "Trajectory of a continuous-time system")
  (statement := /-- A map $x : \mathbb{R} \to E$ is a \emph{trajectory} of $s$ under the input
    $u$ on a set $I \subseteq \mathbb{R}$ when
    \[
      \dot x(t) = F(t, x(t), u(t)), \qquad \forall\, t \in I,
    \]
    the derivative being taken within $I$.  Stated on a set: a map can satisfy the equation on
    an interval without being defined for all time. -/)]
def IsTrajectoryOn (s : ContinuousSystem E U Y) (u : ℝ → U) (x : ℝ → E) (I : Set ℝ) : Prop :=
  IsIntegralCurveOn x (s.vectorField u) I

/-- `x` is a trajectory of `s` under the input `u` for all time. -/
@[blueprint "def:continuousSystem-isTrajectory"
  (title := "Trajectory for all time of a continuous-time system")
  (statement := /-- A trajectory (\cref{def:continuousSystem-isTrajectoryOn}) defined on all of
    $\mathbb{R}$. -/)]
def IsTrajectory (s : ContinuousSystem E U Y) (u : ℝ → U) (x : ℝ → E) : Prop :=
  IsIntegralCurve x (s.vectorField u)

@[blueprint "lem:continuousSystem-isTrajectoryOn-univ"
  (title := "Trajectories of a continuous-time system on the whole line")
  (latexEnv := "lemma")
  (statement := /-- \cref{def:continuousSystem-isTrajectoryOn} at $I = \mathbb{R}$ is
    \cref{def:continuousSystem-isTrajectory}. -/)]
lemma isTrajectoryOn_univ {s : ContinuousSystem E U Y} {u : ℝ → U} {x : ℝ → E} :
    s.IsTrajectoryOn u x Set.univ ↔ s.IsTrajectory u x :=
  isIntegralCurveOn_univ

@[blueprint "lem:continuousSystem-isTrajectory-isTrajectoryOn"
  (title := "Restriction of a trajectory of a continuous-time system")
  (latexEnv := "lemma")
  (statement := /-- A trajectory for all time is a trajectory on every set. -/)]
lemma IsTrajectory.isTrajectoryOn {s : ContinuousSystem E U Y} {u : ℝ → U} {x : ℝ → E}
    (h : s.IsTrajectory u x) (I : Set ℝ) : s.IsTrajectoryOn u x I :=
  IsIntegralCurve.isIntegralCurveOn h I

/-- `x` is a **right trajectory** of `s` under the input `u` on `I`: continuous on `I`, with right
derivative `ẋ(t⁺) = F(t, x(t), u(t))` at every `t ∈ I` (taken within `I ∩ [t, ∞)`).

This is the solution concept for piecewise continuous inputs, taken right-continuous: between
switching times the input is continuous and the solution classical, and at a switching time the
solution has a corner — no two-sided derivative — but its right derivative uses the input's new
value.  Sample-and-hold, step and switching signals are of this kind.  Every trajectory is a right
trajectory (`IsTrajectoryOn.isRightTrajectoryOn`), and the Lyapunov comparison arguments only use
right derivatives, so they hold along right trajectories unchanged. -/
@[blueprint "def:continuousSystem-isRightTrajectoryOn"
  (title := "Right trajectory of a continuous-time system")
  (statement := /-- A map $x : \mathbb{R} \to E$ is a \emph{right trajectory} of $s$ under the
    input $u$ on $I \subseteq \mathbb{R}$ when it is continuous on $I$ and has right derivative
    \[
      \dot x(t^+) = F(t, x(t), u(t)), \qquad \forall\, t \in I,
    \]
    taken within $I \cap [t, \infty)$.  It is the solution concept for piecewise continuous,
    right-continuous inputs: at a switching time the solution has a corner, but its right
    derivative is given by the new value of the input.  Every trajectory
    (\cref{def:continuousSystem-isTrajectoryOn}) is one. -/)]
def IsRightTrajectoryOn (s : ContinuousSystem E U Y) (u : ℝ → U) (x : ℝ → E) (I : Set ℝ) :
    Prop :=
  ContinuousOn x I ∧ ∀ t ∈ I, HasDerivWithinAt x (s.vectorField u t (x t)) (I ∩ Set.Ici t) t

/-- Every trajectory is a right trajectory. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-isRightTrajectoryOn"
  (title := "Trajectories are right trajectories")
  (latexEnv := "lemma")
  (statement := /-- A trajectory on $I$ (\cref{def:continuousSystem-isTrajectoryOn}) is a right
    trajectory on $I$ (\cref{def:continuousSystem-isRightTrajectoryOn}). -/)]
lemma IsTrajectoryOn.isRightTrajectoryOn {s : ContinuousSystem E U Y} {u : ℝ → U} {x : ℝ → E}
    {I : Set ℝ} (h : s.IsTrajectoryOn u x I) : s.IsRightTrajectoryOn u x I :=
  ⟨IsIntegralCurveOn.continuousOn h, fun t ht => (h t ht).mono Set.inter_subset_left⟩

/-- A right trajectory on `I` is one on every subset of `I`. -/
lemma IsRightTrajectoryOn.mono {s : ContinuousSystem E U Y} {u : ℝ → U} {x : ℝ → E}
    {I J : Set ℝ} (h : s.IsRightTrajectoryOn u x I) (hJI : J ⊆ I) :
    s.IsRightTrajectoryOn u x J :=
  ⟨h.1.mono hJI, fun t ht => (h.2 t (hJI ht)).mono (Set.inter_subset_inter_left _ hJI)⟩

/-- On a segment, a right trajectory has right derivative `F(t, x(t), u(t))` at every `t` before
the right end, within `[t, ∞)`. -/
lemma IsRightTrajectoryOn.hasDerivWithinAt_Ici {s : ContinuousSystem E U Y} {u : ℝ → U}
    {x : ℝ → E} {t₀ t₁ : ℝ} (h : s.IsRightTrajectoryOn u x (Set.Icc t₀ t₁)) {t : ℝ}
    (ht : t ∈ Set.Ico t₀ t₁) : HasDerivWithinAt x (s.vectorField u t (x t)) (Set.Ici t) t :=
  (h.2 t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (Filter.inter_mem (Icc_mem_nhdsGE_of_mem ht) self_mem_nhdsWithin)

/-! ### The derivative of a function along the system -/

/-- The derivative of `V(t, x)` along the system at the input value `u`,
`∂V/∂t + ∂V/∂x · F(t, x, u)`: the rate of change of `V` along a trajectory through `x` at time
`t` while the input takes the value `u`.  It is the Lie derivative (`_root_.lieDerivative`) of
`V` along the field `F(·, ·, u)`, so the lemmas of `Analysis.LieDerivative` apply to it
directly: a trajectory is an integral curve of `s.vectorField`.  Input-free notions such as
Lyapunov stability use `u = ()`; input-to-state notions use a general `u`. -/
@[blueprint "def:continuousSystem-lieDerivative"
  (title := "Derivative along the system")
  (statement := /-- For $V : \mathbb{R} \times E \to \mathbb{R}$ and an input value $u \in U$,
    the \emph{derivative of $V$ along the system} $\dot x = F(t, x, u)$ is
    \[
      \dot V(t, x, u) = \frac{\partial V}{\partial t}(t, x)
        + \frac{\partial V}{\partial x}(t, x)\, F(t, x, u),
    \]
    the Lie derivative of $V$ along the field $F(\cdot, \cdot, u)$ (\cref{def:lieDerivative}).
    -/)]
noncomputable def lieDerivative (s : ContinuousSystem E U Y) (V : ℝ → E → ℝ) (t : ℝ) (x : E)
    (u : U) : ℝ :=
  _root_.lieDerivative V (fun t x => s.F t x u) t x

/-! ### Well-posedness -/

/-- Every solution segment starting at time `t₀` in the set `S` extends to a solution on
`[t₀, ∞)`: such solutions do not escape in finite time.

Forward completeness is kept apart from the notions that need it.  Statements about limits as
`t → ∞` quantify over solutions on `[t₀, ∞)`, and without it a solution that escapes in finite
time would be silently left out of them. -/
@[blueprint "def:continuousSystem-isForwardCompleteOn"
  (title := "Forward completeness from a set")
  (statement := /-- A continuous-time system is \emph{forward complete} from a set $S$ at time
    $t_0$ under the input $u$ when every trajectory on a segment $[t_0, t_1]$
    (\cref{def:continuousSystem-isTrajectoryOn}) with $x(t_0) \in S$ agrees on that segment with
    a trajectory on $[t_0, \infty)$. -/)]
def IsForwardCompleteOn (s : ContinuousSystem E U Y) (u : ℝ → U) (t₀ : ℝ) (S : Set E) : Prop :=
  ∀ (t₁ : ℝ) (x : ℝ → E), t₀ ≤ t₁ → s.IsTrajectoryOn u x (Set.Icc t₀ t₁) → x t₀ ∈ S →
    ∃ y : ℝ → E, s.IsTrajectoryOn u y (Set.Ici t₀) ∧ Set.EqOn y x (Set.Icc t₀ t₁)

/-- Every solution segment, from any initial time and state, extends to a solution on
`[t₀, ∞)`. -/
@[blueprint "def:continuousSystem-isForwardComplete"
  (title := "Forward completeness")
  (statement := /-- A continuous-time system is \emph{forward complete} under the input $u$ when
    it is forward complete (\cref{def:continuousSystem-isForwardCompleteOn}) from every state at
    every initial time. -/)]
def IsForwardComplete (s : ContinuousSystem E U Y) (u : ℝ → U) : Prop :=
  ∀ t₀ : ℝ, s.IsForwardCompleteOn u t₀ Set.univ

/-- Solutions are *unique* forward in time: two solution segments on `[t₀, t₁]` that agree at
`t₀` agree on the whole segment.

Kept apart from the stability notions, which quantify over every solution and so need no
uniqueness: theorems that use it assume it. -/
@[blueprint "def:continuousSystem-hasUniqueSolutions"
  (title := "Uniqueness of solutions")
  (statement := /-- A continuous-time system has \emph{unique solutions} under the input $u$
    when any two trajectories on a segment $[t_0, t_1]$
    (\cref{def:continuousSystem-isTrajectoryOn}) that agree at $t_0$ agree on all of
    $[t_0, t_1]$. -/)]
def HasUniqueSolutions (s : ContinuousSystem E U Y) (u : ℝ → U) : Prop :=
  ∀ (t₀ t₁ : ℝ) (x y : ℝ → E), s.IsTrajectoryOn u x (Set.Icc t₀ t₁) →
    s.IsTrajectoryOn u y (Set.Icc t₀ t₁) → x t₀ = y t₀ → Set.EqOn x y (Set.Icc t₀ t₁)

/-- **Lipschitz right-hand sides have unique solutions.**  If `x ↦ F(t, x, u(t))` is
`K`-Lipschitz for every `t`, solutions are unique forward in time. -/
@[blueprint "thm:continuousSystem-hasUniqueSolutions-of-lipschitz"
  (title := "Lipschitz systems have unique solutions")
  (statement := /-- If $x \mapsto F(t, x, u(t))$ is $K$-Lipschitz for every $t$, the system has
    unique solutions under $u$ (\cref{def:continuousSystem-hasUniqueSolutions}). -/)
  (proof := /-- Grönwall's inequality, in the form of Mathlib's
    \texttt{ODE\_solution\_unique\_of\_mem\_Icc\_right}: a derivative within $[t_0, t_1]$ at a point
    of $[t_0, t_1)$ is a right derivative there. -/)]
theorem hasUniqueSolutions_of_lipschitz {s : ContinuousSystem E U Y} {u : ℝ → U} {K : NNReal}
    (hL : ∀ t, LipschitzWith K (s.vectorField u t)) : s.HasUniqueSolutions u := by
  intro t₀ t₁ x y hx hy h₀
  -- a derivative within the segment, at a point other than its right end, is a right derivative
  have h_right : ∀ {z : ℝ → E}, s.IsTrajectoryOn u z (Set.Icc t₀ t₁) → ∀ t ∈ Set.Ico t₀ t₁,
      HasDerivWithinAt z (s.vectorField u t (z t)) (Set.Ici t) t := fun hz t ht =>
    (hz t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => Set.univ)
    (fun t _ => (hL t).lipschitzOnWith) (fun t ht => (hx t ht).continuousWithinAt) (h_right hx)
    (fun _ _ => Set.mem_univ _) (fun t ht => (hy t ht).continuousWithinAt) (h_right hy)
    (fun _ _ => Set.mem_univ _) h₀

/-- **Globally Lipschitz systems are forward complete.**  If `(t, x) ↦ F(t, x, u(t))` is
continuous and `K`-Lipschitz in `x` uniformly in `t`, every trajectory segment extends to
`[t₀, ∞)`.

Global Lipschitz is what rules out escape in finite time here; a local Lipschitz condition
alone does not (`ẋ = x²`). -/
@[blueprint "thm:continuousSystem-isForwardComplete-of-lipschitz"
  (title := "Globally Lipschitz systems are forward complete")
  (statement := /-- If $(t, x) \mapsto F(t, x, u(t))$ is continuous and $K$-Lipschitz in $x$
    uniformly in $t$, the system is forward complete under $u$
    (\cref{def:continuousSystem-isForwardComplete}). -/)
  (proof := /-- From the endpoint $x(t_0)$ of a segment, Picard--Lindel\"of gives a solution on
    $[t_0, \infty)$ (\cref{thm:exists-isIntegralCurveOn-Ici}), which agrees with the segment by
    uniqueness (\cref{thm:continuousSystem-hasUniqueSolutions-of-lipschitz}). -/)]
theorem isForwardComplete_of_lipschitz [CompleteSpace E] {s : ContinuousSystem E U Y}
    {u : ℝ → U} {K : NNReal} (hF : Continuous (Function.uncurry (s.vectorField u)))
    (hL : ∀ t, LipschitzWith K (s.vectorField u t)) : s.IsForwardComplete u := by
  intro t₀ t₁ x ht hx _
  obtain ⟨y, hy₀, hy, -⟩ := exists_isIntegralCurveOn_Ici hF hL t₀ (x t₀)
  exact ⟨y, hy, hasUniqueSolutions_of_lipschitz hL t₀ t₁ y x
    (IsIntegralCurveOn.mono hy Set.Icc_subset_Ici_self) hx hy₀⟩

/-- **Exponential bounds on the distance of a trajectory to a point** (Khalil, Exercise 3.17(b)):
if `‖F(t, x(t), u(t))‖ ≤ L ‖x(t) - x_c‖` along a trajectory on `[t₀, t₁]`, then
`‖x(t₀) - x_c‖ e^{-L(t - t₀)} ≤ ‖x(t) - x_c‖ ≤ ‖x(t₀) - x_c‖ e^{L(t - t₀)}` there.  For a field
`L`-Lipschitz in the state with an equilibrium at `x_c`, the hypothesis holds everywhere.

The bound is only needed along the trajectory, and the state space is any normed space. -/
@[blueprint "thm:continuousSystem-isTrajectoryOn-norm-exp-bounds"
  (title := "Exponential bounds on a trajectory")
  (statement := /-- If $x$ is a trajectory on $[t_0, t_1]$
    (\cref{def:continuousSystem-isTrajectoryOn}) with
    $\|F(t, x(t), u(t))\| \le L\|x(t) - x_c\|$ for $t \in [t_0, t_1)$, then for every
    $t \in [t_0, t_1]$
    \[
      \|x(t_0) - x_c\|\,e^{-L(t - t_0)} \le \|x(t) - x_c\| \le \|x(t_0) - x_c\|\,e^{L(t - t_0)}.
    \]

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Exercise 3.17(b). -/)
  (proof := /-- $D^{+}\|x - x_c\| \le \|\dot x\| \le L\|x - x_c\|$ and
    $D^{+}(-\|x - x_c\|) \le \|\dot x\| \le (-L)(-\|x - x_c\|)$
    (\cref{lem:diniDerivRight-le-norm-of-hasDerivWithinAt}); apply Gr\"onwall
    (\cref{thm:le-mul-exp-of-diniDerivRight-le}) to each. -/)]
theorem IsTrajectoryOn.norm_exp_bounds {s : ContinuousSystem E U Y} {u : ℝ → U} {x : ℝ → E}
    {x_c : E} {t₀ t₁ L : ℝ} (hx : s.IsTrajectoryOn u x (Set.Icc t₀ t₁))
    (hL : ∀ t ∈ Set.Ico t₀ t₁, ‖s.vectorField u t (x t)‖ ≤ L * ‖x t - x_c‖) {t : ℝ}
    (ht : t ∈ Set.Icc t₀ t₁) :
    ‖x t₀ - x_c‖ * Real.exp (-L * (t - t₀)) ≤ ‖x t - x_c‖ ∧
      ‖x t - x_c‖ ≤ ‖x t₀ - x_c‖ * Real.exp (L * (t - t₀)) := by
  have hx_cont : ContinuousOn x (Set.Icc t₀ t₁) := IsIntegralCurveOn.continuousOn hx
  -- At a point of `[t₀, t₁)`, a derivative within the segment is a right derivative.
  have hx_right : ∀ r ∈ Set.Ico t₀ t₁,
      HasDerivWithinAt x (s.vectorField u r (x r)) (Set.Ici r) r := fun r hr =>
    (hx r (Set.Ico_subset_Icc_self hr)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hr)
  have hd_cont : ContinuousOn (fun r => ‖x r - x_c‖) (Set.Icc t₀ t₁) :=
    (hx_cont.sub continuousOn_const).norm
  -- `‖x - x_c‖` changes by at most `‖x q - x r‖`.
  have h_change : ∀ q r, ‖x q - x_c‖ - ‖x r - x_c‖ ≤ ‖x q - x r‖ := fun q r => by
    simpa using norm_sub_norm_le (x q - x_c) (x r - x_c)
  refine ⟨?_, le_mul_exp_of_diniDerivRight_le hd_cont (fun r hr =>
    (diniDerivRight_le_norm_of_hasDerivWithinAt (hx_right r hr) fun q => h_change q r).trans
      (EReal.coe_le_coe_iff.2 (hL r hr))) t ht⟩
  have h := le_mul_exp_of_diniDerivRight_le (v := fun r => -‖x r - x_c‖) (K := -L) hd_cont.neg
    (fun r hr => (diniDerivRight_le_norm_of_hasDerivWithinAt (hx_right r hr) fun q => by
      linarith [h_change r q, norm_sub_rev (x r) (x q)]).trans
        (EReal.coe_le_coe_iff.2 (by linarith [hL r hr]))) t ht
  linarith

/-- **No equilibrium is reached in finite time.**  For a field that is Lipschitz in the state, a
trajectory on `[t₀, t₁]` that is at an equilibrium at time `t₁` was there all along: solutions are
unique backward in time too. -/
@[blueprint "thm:continuousSystem-isTrajectoryOn-eqOn-of-equilibrium"
  (title := "Equilibria are not reached in finite time")
  (statement := /-- If the state equation is Lipschitz in the state, uniformly in time, and a
    trajectory on $[t_0, t_1]$ satisfies $F(t, x(t_1), u(t)) = 0$ for all $t$, then
    $x(t) = x(t_1)$ for every $t \in [t_0, t_1]$. -/)
  (proof := /-- $x$ and the constant curve at $x(t_1)$
    (\cref{lem:isIntegralCurveOn-const}) are two solutions agreeing at $t_1$; backward
    uniqueness (Gr\"onwall) makes them equal. -/)]
theorem IsTrajectoryOn.eqOn_of_equilibrium {s : ContinuousSystem E U Y} {u : ℝ → U}
    {K : NNReal} (hL : ∀ t, LipschitzWith K (s.vectorField u t)) {x : ℝ → E} {t₀ t₁ : ℝ}
    (hx : s.IsTrajectoryOn u x (Set.Icc t₀ t₁)) (h_eq : ∀ t, s.vectorField u t (x t₁) = 0) :
    Set.EqOn x (fun _ => x t₁) (Set.Icc t₀ t₁) :=
  ODE_solution_unique_of_mem_Icc_left (s := fun _ => Set.univ)
    (fun t _ => (hL t).lipschitzOnWith) (IsIntegralCurveOn.continuousOn hx)
    (fun t ht => (hx t (Set.Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE_of_mem ht))
    (fun _ _ => Set.mem_univ _) continuousOn_const
    (fun t _ => (isIntegralCurveOn_const (s := Set.univ) fun r _ => h_eq r) t
      (Set.mem_univ _) |>.mono (Set.subset_univ _))
    (fun _ _ => Set.mem_univ _) rfl

/-! ### The state transition map -/

/-- The **existence interval** of the trajectory from `x₀` at time `t₀`: the times `t ≥ t₀` up to
which a trajectory from `x₀` exists, that is, the maximal interval of existence `[t₀, T)`. -/
@[blueprint "def:continuousSystem-existenceInterval"
  (title := "Existence interval")
  (statement := /-- The \emph{existence interval} of the trajectory of $s$ under $u$ from $x_0$
    at time $t_0$ is the set of $t \ge t_0$ for which a trajectory on $[t_0, t]$
    (\cref{def:continuousSystem-isTrajectoryOn}) with $x(t_0) = x_0$ exists: the maximal interval
    of existence. -/)]
def existenceInterval (s : ContinuousSystem E U Y) (u : ℝ → U) (t₀ : ℝ) (x₀ : E) : Set ℝ :=
  {t | t₀ ≤ t ∧ ∃ x : ℝ → E, x t₀ = x₀ ∧ s.IsTrajectoryOn u x (Set.Icc t₀ t)}

open scoped Classical in
/-- The **state transition map** `φ(t; t₀, x₀)`: the value at `t` of a trajectory from `x₀` at
time `t₀` that exists up to `t`, and `x₀` outside the existence interval (before `t₀`, or past a
finite escape time).

It is meant for systems with unique solutions (`HasUniqueSolutions`), which the results about its
trajectories assume.  Without uniqueness the trajectory is chosen separately for each `t`, so
`t ↦ φ(t; t₀, x₀)` may splice different solutions and need not be a trajectory; there the honest
object is the set of solutions from `x₀`, which is how the stability definitions are stated. -/
@[blueprint "def:continuousSystem-stateTransitionMap"
  (title := "State transition map")
  (statement := /-- The \emph{state transition map} $\varphi(t; t_0, x_0)$ of $s$ under $u$ is
    the value at time $t$ of a trajectory from $x_0$ at time $t_0$, for $t$ in the existence
    interval (\cref{def:continuousSystem-existenceInterval}); with unique solutions
    (\cref{def:continuousSystem-hasUniqueSolutions}) it does not depend on the trajectory chosen.
    Outside the existence interval it is $x_0$, by convention. -/)]
noncomputable def stateTransitionMap (s : ContinuousSystem E U Y) (u : ℝ → U)
    (t t₀ : ℝ) (x₀ : E) : E :=
  if h : t ∈ s.existenceInterval u t₀ x₀ then h.2.choose t else x₀

variable {s : ContinuousSystem E U Y} {u : ℝ → U}

/-- The initial time is in the existence interval: a trajectory on `[t₀, t₀]` is trivial. -/
lemma mem_existenceInterval_self (t₀ : ℝ) (x₀ : E) : t₀ ∈ s.existenceInterval u t₀ x₀ :=
  ⟨le_rfl, fun _ => x₀, rfl,
    fun _ _ => HasFDerivWithinAt.of_subsingleton (Set.subsingleton_Icc_of_ge le_rfl)⟩

/-- The existence interval is an interval: with `t`, it contains every time between `t₀` and
`t`. -/
lemma mem_existenceInterval_of_le {t₀ t τ : ℝ} {x₀ : E} (ht : t ∈ s.existenceInterval u t₀ x₀)
    (h₀ : t₀ ≤ τ) (h₁ : τ ≤ t) : τ ∈ s.existenceInterval u t₀ x₀ :=
  ⟨h₀, ht.2.choose, ht.2.choose_spec.1,
    IsIntegralCurveOn.mono ht.2.choose_spec.2 (Set.Icc_subset_Icc_right h₁)⟩

/-- `φ(t₀; t₀, x₀) = x₀`. -/
@[simp]
lemma stateTransitionMap_self (t₀ : ℝ) (x₀ : E) : s.stateTransitionMap u t₀ t₀ x₀ = x₀ := by
  have h := mem_existenceInterval_self (s := s) (u := u) t₀ x₀
  rw [stateTransitionMap, dif_pos h]
  exact h.2.choose_spec.1

/-- **Forward completeness means global existence**: if every trajectory extends to `[t₀, ∞)`,
the existence interval is all of `[t₀, ∞)`. -/
@[blueprint "lem:continuousSystem-existenceInterval-eq-Ici"
  (title := "Existence intervals of a forward complete system")
  (latexEnv := "lemma")
  (statement := /-- If $s$ is forward complete under $u$
    (\cref{def:continuousSystem-isForwardComplete}), the existence interval
    (\cref{def:continuousSystem-existenceInterval}) from every $(t_0, x_0)$ is $[t_0, \infty)$. -/)
  (proof := /-- The trajectory on $[t_0, t_0]$ is trivial; forward completeness extends it to
    $[t_0, \infty)$. -/)]
lemma existenceInterval_eq_Ici (hfc : s.IsForwardComplete u) (t₀ : ℝ) (x₀ : E) :
    s.existenceInterval u t₀ x₀ = Set.Ici t₀ := by
  refine Set.Subset.antisymm (fun t ht => ht.1) fun t ht => ⟨ht, ?_⟩
  obtain ⟨y, hy, hy_eq⟩ := hfc t₀ t₀ (fun _ => x₀) le_rfl
    (fun _ _ => HasFDerivWithinAt.of_subsingleton (Set.subsingleton_Icc_of_ge le_rfl))
    (Set.mem_univ _)
  exact ⟨y, hy_eq ⟨le_rfl, le_rfl⟩, IsIntegralCurveOn.mono hy Set.Icc_subset_Ici_self⟩

/-- **Every trajectory is given by the state transition map**: with unique solutions, a
trajectory on `[t₀, t₁]` is `t ↦ φ(t; t₀, x(t₀))` there. -/
@[blueprint "lem:continuousSystem-eq-stateTransitionMap"
  (title := "Trajectories are given by the state transition map")
  (latexEnv := "lemma")
  (statement := /-- If $s$ has unique solutions under $u$
    (\cref{def:continuousSystem-hasUniqueSolutions}), every trajectory $x$ on $[t_0, t_1]$
    satisfies $x(t) = \varphi(t; t_0, x(t_0))$ there
    (\cref{def:continuousSystem-stateTransitionMap}). -/)
  (proof := /-- $x$ itself witnesses that $t$ is in the existence interval, and the trajectory
    chosen by $\varphi$ agrees with $x$ on $[t_0, t]$ by uniqueness. -/)]
lemma eq_stateTransitionMap (hu : s.HasUniqueSolutions u) {t₀ t₁ : ℝ} {x : ℝ → E}
    (hx : s.IsTrajectoryOn u x (Set.Icc t₀ t₁)) :
    ∀ t ∈ Set.Icc t₀ t₁, x t = s.stateTransitionMap u t t₀ (x t₀) := by
  intro t ht
  have hx_t : s.IsTrajectoryOn u x (Set.Icc t₀ t) :=
    IsIntegralCurveOn.mono hx (Set.Icc_subset_Icc_right ht.2)
  have hmem : t ∈ s.existenceInterval u t₀ (x t₀) := ⟨ht.1, x, rfl, hx_t⟩
  rw [stateTransitionMap, dif_pos hmem]
  obtain ⟨hy₀, hy⟩ := hmem.2.choose_spec
  exact (hu t₀ t _ x hy hx_t hy₀ ⟨ht.1, le_rfl⟩).symm

/-- **The state transition map is a trajectory**: with unique solutions,
`t ↦ φ(t; t₀, x₀)` is a trajectory on the existence interval. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-stateTransitionMap"
  (title := "The state transition map is a trajectory")
  (latexEnv := "lemma")
  (statement := /-- If $s$ has unique solutions under $u$
    (\cref{def:continuousSystem-hasUniqueSolutions}), $t \mapsto \varphi(t; t_0, x_0)$
    (\cref{def:continuousSystem-stateTransitionMap}) is a trajectory on the existence interval
    (\cref{def:continuousSystem-existenceInterval}). -/)
  (proof := /-- Near each time $t$ of the existence interval, $\varphi$ agrees with a trajectory on
    a segment $[t_0, t']$ containing a neighbourhood of $t$ in the interval
    (\cref{lem:continuousSystem-eq-stateTransitionMap}), so it has that trajectory's
    derivative. -/)]
lemma isTrajectoryOn_stateTransitionMap (hu : s.HasUniqueSolutions u) (t₀ : ℝ) (x₀ : E) :
    s.IsTrajectoryOn u (fun t => s.stateTransitionMap u t t₀ x₀)
      (s.existenceInterval u t₀ x₀) := by
  intro t ht
  -- A segment `[t₀, t']` of the existence interval containing a neighbourhood of `t` in it.
  obtain ⟨t', ht', htt', h_nhds⟩ : ∃ t' ∈ s.existenceInterval u t₀ x₀, t ≤ t' ∧
      Set.Icc t₀ t' ∈ nhdsWithin t (s.existenceInterval u t₀ x₀) := by
    by_cases h : ∃ t' ∈ s.existenceInterval u t₀ x₀, t < t'
    · obtain ⟨t', ht', htt'⟩ := h
      exact ⟨t', ht', htt'.le, mem_nhdsWithin.2 ⟨Set.Iio t', isOpen_Iio, htt',
        fun τ hτ => ⟨hτ.2.1, hτ.1.le⟩⟩⟩
    · simp only [not_exists, not_and, not_lt] at h
      exact ⟨t, ht, le_rfl, Filter.mem_of_superset self_mem_nhdsWithin
        fun τ hτ => ⟨hτ.1, h τ hτ⟩⟩
  -- There `φ` is a trajectory `x` from `x₀`.
  obtain ⟨x, hx₀, hx⟩ := ht'.2
  have h_eq := eq_stateTransitionMap hu hx
  rw [hx₀] at h_eq
  have htI : t ∈ Set.Icc t₀ t' := ⟨ht.1, htt'⟩
  have h_ev : (fun τ => s.stateTransitionMap u τ t₀ x₀) =ᶠ[nhdsWithin t
      (s.existenceInterval u t₀ x₀)] x := by
    filter_upwards [h_nhds] with τ hτ using (h_eq τ hτ).symm
  have hd := ((hx t htI).mono_of_mem_nhdsWithin h_nhds).congr_of_eventuallyEq h_ev
    (h_eq t htI).symm
  rwa [h_eq t htI] at hd

/-- With forward completeness and unique solutions, `t ↦ φ(t; t₀, x₀)` is a trajectory on
`[t₀, ∞)`. -/
lemma isTrajectoryOn_stateTransitionMap_Ici (hfc : s.IsForwardComplete u)
    (hu : s.HasUniqueSolutions u) (t₀ : ℝ) (x₀ : E) :
    s.IsTrajectoryOn u (fun t => s.stateTransitionMap u t t₀ x₀) (Set.Ici t₀) := by
  simpa [existenceInterval_eq_Ici hfc] using isTrajectoryOn_stateTransitionMap hu t₀ x₀

/-- **The semigroup property**: `φ(t; τ, φ(τ; t₀, x₀)) = φ(t; t₀, x₀)` for `t₀ ≤ τ ≤ t` in the
existence interval.  The state transition matrix satisfies the linear case,
`Φ(t, τ) Φ(τ, t₀) = Φ(t, t₀)`. -/
@[blueprint "lem:continuousSystem-stateTransitionMap-semigroup"
  (title := "The semigroup property")
  (latexEnv := "lemma")
  (statement := /-- If $s$ has unique solutions under $u$
    (\cref{def:continuousSystem-hasUniqueSolutions}), then for $t_0 \le \tau \le t$ with $t$ in
    the existence interval from $(t_0, x_0)$,
    \[
      \varphi(t; \tau, \varphi(\tau; t_0, x_0)) = \varphi(t; t_0, x_0).
    \] -/)
  (proof := /-- $\varphi(\cdot; t_0, x_0)$ is a trajectory on $[\tau, t]$
    (\cref{lem:continuousSystem-isTrajectoryOn-stateTransitionMap}), so it is given by $\varphi$
    from $(\tau, \varphi(\tau; t_0, x_0))$ (\cref{lem:continuousSystem-eq-stateTransitionMap}).
    -/)]
lemma stateTransitionMap_semigroup (hu : s.HasUniqueSolutions u) {t₀ τ t : ℝ} {x₀ : E}
    (hτ : t₀ ≤ τ) (hτt : τ ≤ t) (ht : t ∈ s.existenceInterval u t₀ x₀) :
    s.stateTransitionMap u t τ (s.stateTransitionMap u τ t₀ x₀) =
      s.stateTransitionMap u t t₀ x₀ := by
  have hy : s.IsTrajectoryOn u (fun r => s.stateTransitionMap u r t₀ x₀) (Set.Icc τ t) :=
    IsIntegralCurveOn.mono (isTrajectoryOn_stateTransitionMap hu t₀ x₀)
      fun r hr => mem_existenceInterval_of_le ht (hτ.trans hr.1) hr.2
  exact (eq_stateTransitionMap hu hy t ⟨hτt, le_rfl⟩).symm

/-- **An equilibrium stays put**: if `F(t, x_eq, u(t)) = 0` for all `t`, then
`φ(t; t₀, x_eq) = x_eq` for `t ≥ t₀`. -/
lemma stateTransitionMap_of_equilibrium (hu : s.HasUniqueSolutions u) {x_eq : E}
    (h_eq : ∀ t, s.vectorField u t x_eq = 0) {t₀ t : ℝ} (ht : t₀ ≤ t) :
    s.stateTransitionMap u t t₀ x_eq = x_eq :=
  (eq_stateTransitionMap hu (isIntegralCurveOn_const fun r _ => h_eq r) t ⟨ht, le_rfl⟩).symm

/-- **Solutions separate at most exponentially in the initial state**: for a field `L`-Lipschitz
in the state, uniformly in time, `‖φ(t; t₀, x₀) - φ(t; t₀, y₀)‖ ≤ ‖x₀ - y₀‖ e^{L(t - t₀)}`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 3.4, without perturbation. -/
@[blueprint "thm:continuousSystem-dist-stateTransitionMap-le"
  (title := "Lipschitz dependence on the initial state")
  (statement := /-- If the system is forward complete under $u$
    (\cref{def:continuousSystem-isForwardComplete}) and $x \mapsto F(t, x, u(t))$ is
    $L$-Lipschitz for every $t$, then for $t \ge t_0$
    \[
      \|\varphi(t; t_0, x_0) - \varphi(t; t_0, y_0)\| \le \|x_0 - y_0\|\, e^{L(t - t_0)}
    \]
    (\cref{def:continuousSystem-stateTransitionMap}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 3.4, without
    perturbation. -/)
  (proof := /-- Both maps are trajectories on $[t_0, \infty)$
    (\cref{thm:continuousSystem-hasUniqueSolutions-of-lipschitz}); apply Gr\"onwall's inequality
    to their difference on $[t_0, t]$. -/)]
theorem dist_stateTransitionMap_le (hfc : s.IsForwardComplete u) {L : NNReal}
    (hL : ∀ t, LipschitzWith L (s.vectorField u t)) {t₀ t : ℝ} (ht : t₀ ≤ t) (x₀ y₀ : E) :
    dist (s.stateTransitionMap u t t₀ x₀) (s.stateTransitionMap u t t₀ y₀) ≤
      dist x₀ y₀ * Real.exp (L * (t - t₀)) := by
  have hu := hasUniqueSolutions_of_lipschitz hL
  simpa using dist_le_of_isIntegralCurveOn_Icc hL
    (IsIntegralCurveOn.mono (isTrajectoryOn_stateTransitionMap_Ici hfc hu t₀ x₀)
      Set.Icc_subset_Ici_self)
    (IsIntegralCurveOn.mono (isTrajectoryOn_stateTransitionMap_Ici hfc hu t₀ y₀)
      Set.Icc_subset_Ici_self) t ⟨ht, le_rfl⟩

/-- **Solutions depend Lipschitz-continuously on the initial time and state**: for a field
`L`-Lipschitz in the state and bounded by `B`, the solutions from `(t₀, x₀)` and `(t₀', x₀')`,
compared after the same elapsed time `σ`, differ by at most `(2B + 1) e^{Lσ}` times the distance
between the initial data.  Run the earlier one to the later initial time (speed `B`), then apply
`dist_stateTransitionMap_le`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Section 3.2. -/
@[blueprint "thm:continuousSystem-norm-stateTransitionMap-sub-le"
  (title := "Lipschitz dependence on the initial time and state")
  (statement := /-- If the system is forward complete under $u$
    (\cref{def:continuousSystem-isForwardComplete}), and $x \mapsto F(t, x, u(t))$ is
    $L$-Lipschitz and bounded by $B$ for every $t$, then for $\sigma \ge 0$
    \[
      \|\varphi(t_0 + \sigma; t_0, x_0) - \varphi(t_0' + \sigma; t_0', x_0')\|
        \le (2B + 1)\,e^{L\sigma}\,\|(t_0, x_0) - (t_0', x_0')\|
    \]
    (\cref{def:continuousSystem-stateTransitionMap}), the norm on $\mathbb{R} \times E$ being the
    maximum.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Section 3.2. -/)
  (proof := /-- Say $t_0 \le t_0'$.  The first solution moves at most $B|t_0 - t_0'|$ between
    the two initial times and between the two final times; from $t_0'$ on, the two solutions
    separate at most like $e^{L\sigma}$
    (\cref{thm:continuousSystem-dist-stateTransitionMap-le}). -/)]
theorem norm_stateTransitionMap_sub_le (hfc : s.IsForwardComplete u) {L : NNReal}
    (hL : ∀ t, LipschitzWith L (s.vectorField u t)) {B : ℝ}
    (hB : ∀ t y, ‖s.vectorField u t y‖ ≤ B) (z z' : ℝ × E) {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖s.stateTransitionMap u (z.1 + σ) z.1 z.2 - s.stateTransitionMap u (z'.1 + σ) z'.1 z'.2‖ ≤
      (2 * B + 1) * Real.exp (L * σ) * dist z z' := by
  have hu := hasUniqueSolutions_of_lipschitz hL
  let φ : ℝ × E → ℝ → E := fun p τ => s.stateTransitionMap u τ p.1 p.2
  have hφ0 : ∀ p, φ p p.1 = p.2 := fun p => stateTransitionMap_self p.1 p.2
  have hφ : ∀ p, IsIntegralCurveOn (φ p) (s.vectorField u) (Set.Ici p.1) := fun p =>
    isTrajectoryOn_stateTransitionMap_Ici hfc hu p.1 p.2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 z.2)
  have h_exp : 1 ≤ Real.exp (L * σ) := Real.one_le_exp (by positivity)
  -- The case where `z` starts first.
  have h_one : ∀ z z' : ℝ × E, z.1 ≤ z'.1 →
      ‖φ z (z.1 + σ) - φ z' (z'.1 + σ)‖ ≤ (2 * B + 1) * Real.exp (L * σ) * dist z z' := by
    intro z z' h
    set d := dist z z'
    have hdt : z'.1 - z.1 ≤ d := by
      have := le_max_left (dist z.1 z'.1) (dist z.2 z'.2)
      rw [← Prod.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)] at this
      exact this
    have hdx : ‖z.2 - z'.2‖ ≤ d := by
      rw [← dist_eq_norm]
      exact (le_max_right _ _).trans_eq Prod.dist_eq.symm
    have hd : 0 ≤ d := dist_nonneg
    -- `φ z` runs from `z.1` to `z'.1` at speed `B`.
    have h_speed : ∀ σ' τ, z.1 ≤ σ' → z.1 ≤ τ → ‖φ z τ - φ z σ'‖ ≤ B * |τ - σ'| :=
      fun σ' τ h₁ h₂ => (hφ z).norm_sub_le (convex_Ici _) (fun _ _ => hB _ _) h₁ h₂
    have h_gron : ‖φ z (z'.1 + σ) - φ z' (z'.1 + σ)‖ ≤
        ‖φ z z'.1 - z'.2‖ * Real.exp (L * σ) := by
      have h := dist_le_of_isIntegralCurveOn_Icc hL
        ((hφ z).mono (Set.Icc_subset_Ici_iff (by linarith) |>.2 h))
        ((hφ z').mono Set.Icc_subset_Ici_self) (z'.1 + σ) ⟨by linarith, le_rfl⟩
      rwa [dist_eq_norm, dist_eq_norm, hφ0 z', add_sub_cancel_left] at h
    calc ‖φ z (z.1 + σ) - φ z' (z'.1 + σ)‖
        ≤ ‖φ z (z.1 + σ) - φ z (z'.1 + σ)‖ + ‖φ z (z'.1 + σ) - φ z' (z'.1 + σ)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ B * d + (B * d + d) * Real.exp (L * σ) := by
          gcongr
          · calc ‖φ z (z.1 + σ) - φ z (z'.1 + σ)‖
                ≤ B * |z.1 + σ - (z'.1 + σ)| := h_speed _ _ (by linarith) (by linarith)
              _ ≤ B * d := by
                  gcongr
                  rw [abs_le]; constructor <;> linarith
          · refine h_gron.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
            calc ‖φ z z'.1 - z'.2‖
                ≤ ‖φ z z'.1 - z.2‖ + ‖z.2 - z'.2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
              _ ≤ B * d + d := by
                  gcongr
                  calc ‖φ z z'.1 - z.2‖
                      = ‖φ z z'.1 - φ z z.1‖ := by rw [hφ0 z]
                    _ ≤ B * |z'.1 - z.1| := h_speed _ _ le_rfl h
                    _ ≤ B * d := by gcongr; rw [abs_of_nonneg (by linarith)]; exact hdt
      _ ≤ (2 * B + 1) * Real.exp (L * σ) * d := by nlinarith [mul_nonneg hB0 hd]
  rcases le_total z.1 z'.1 with h | h
  · exact h_one z z' h
  · rw [norm_sub_rev, dist_comm]
    exact h_one z' z h

/-! ### Invariance -/

/-- `S` is **forward invariant** (positively invariant) under the input `u`: every trajectory
segment that starts in `S` stays in `S` for as long as it is defined.  This is for the one input
signal `u`; robust and controlled invariance quantify over `u`.

Stated on segments `[t₀, t₁]` and for every initial time, so it constrains solutions that escape
in finite time up to their escape, and it makes sense for time-varying systems. -/
@[blueprint "def:continuousSystem-isForwardInvariant"
  (title := "Forward invariant set")
  (statement := /-- A set $S \subseteq E$ is \emph{forward invariant} (or positively invariant)
    for $s$ under the input $u$ when every trajectory on a segment $[t_0, t_1]$
    (\cref{def:continuousSystem-isTrajectoryOn}) that starts in $S$ stays in $S$:
    \[
      x(t_0) \in S \;\Rightarrow\; x(t) \in S \quad \forall\, t \in [t_0, t_1].
    \] -/)]
def IsForwardInvariant (s : ContinuousSystem E U Y) (u : ℝ → U) (S : Set E) : Prop :=
  ∀ (t₀ t₁ : ℝ) (x : ℝ → E), s.IsTrajectoryOn u x (Set.Icc t₀ t₁) → x t₀ ∈ S →
    ∀ t ∈ Set.Icc t₀ t₁, x t ∈ S

end Trajectory

/-! ### Holding the input constant -/

section ConstInput

/-- The system with its input **held at `u₀`**: the autonomous system `ẋ = F(t, x, u₀)`,
`y = h(t, x, u₀)`.  With `u₀ = 0` this is the unforced system (`zeroInput`); a general `u₀` is
the operating point of a system whose equilibrium is not at the zero input. -/
@[blueprint "def:continuousSystem-constInput"
  (title := "The system with its input held constant")
  (statement := /-- For $u_0$ in the input space, the autonomous system
    (\cref{def:continuousSystem-autonomous}) $\dot x = F(t, x, u_0)$, $y = h(t, x, u_0)$ obtained
    by holding the input at $u_0$. -/)]
def constInput (s : ContinuousSystem E U Y) (u₀ : U) : ContinuousSystem E Unit Y :=
  autonomous (fun t x => s.F t x u₀) (fun t x => s.h t x u₀)

@[simp] lemma constInput_F (s : ContinuousSystem E U Y) (u₀ : U) (t : ℝ) (x : E) (v : Unit) :
    (s.constInput u₀).F t x v = s.F t x u₀ := rfl

@[simp] lemma constInput_h (s : ContinuousSystem E U Y) (u₀ : U) (t : ℝ) (x : E) (v : Unit) :
    (s.constInput u₀).h t x v = s.h t x u₀ := rfl

/-- The system with its input held constant is autonomous. -/
lemma isAutonomous_constInput (s : ContinuousSystem E U Y) (u₀ : U) :
    (s.constInput u₀).IsAutonomous :=
  isAutonomous_autonomous _ _

/-- The trajectories of the system with its input held at `u₀` are those of the system under the
constant input `u₀`. -/
lemma constInput_isTrajectoryOn_iff [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ContinuousSystem E U Y) (u₀ : U) {x : ℝ → E} {I : Set ℝ} :
    (s.constInput u₀).IsTrajectoryOn (fun _ => ()) x I ↔ s.IsTrajectoryOn (fun _ => u₀) x I :=
  Iff.rfl

variable [Zero U]

/-- The *unforced* system: the input held at `0` (`constInput`), as an autonomous system
`ẋ = F(t, x, 0)`, `y = h(t, x, 0)`.  Stability of a system with input is stability of this system;
input–output notions such as input-to-state stability are stated on the system itself. -/
@[blueprint "def:continuousSystem-zeroInput"
  (title := "The unforced system")
  (statement := /-- The system with its input held at $0$
    (\cref{def:continuousSystem-constInput}): $\dot x = F(t, x, 0)$, $y = h(t, x, 0)$.
    Stability of a system with input means stability of this system. -/)]
def zeroInput (s : ContinuousSystem E U Y) : ContinuousSystem E Unit Y :=
  s.constInput 0

@[simp] lemma zeroInput_F (s : ContinuousSystem E U Y) (t : ℝ) (x : E) (v : Unit) :
    s.zeroInput.F t x v = s.F t x 0 := rfl

@[simp] lemma zeroInput_h (s : ContinuousSystem E U Y) (t : ℝ) (x : E) (v : Unit) :
    s.zeroInput.h t x v = s.h t x 0 := rfl

/-- The unforced system is autonomous. -/
lemma isAutonomous_zeroInput (s : ContinuousSystem E U Y) : s.zeroInput.IsAutonomous :=
  isAutonomous_constInput s 0

/-- The trajectories of the unforced system are those of the system under the zero input. -/
@[blueprint "lem:continuousSystem-zeroInput-isTrajectoryOn-iff"
  (title := "Trajectories of the unforced system")
  (latexEnv := "lemma")
  (statement := /-- A map is a trajectory of the unforced system
    (\cref{def:continuousSystem-zeroInput}) on $I$ exactly when it is a trajectory of $s$ under
    the zero input on $I$. -/)]
lemma zeroInput_isTrajectoryOn_iff [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ContinuousSystem E U Y) {x : ℝ → E} {I : Set ℝ} :
    s.zeroInput.IsTrajectoryOn (fun _ => ()) x I ↔ s.IsTrajectoryOn 0 x I :=
  Iff.rfl

end ConstInput

/-! ### Cascades -/

section Cascade

variable {E₂ Y₂ W : Type*}

/-- The **cascade** of `s₁`, driven by the state of `s₂`, with `s₂`, driven by the external input:
`ẋ₁ = F₁(t, x₁, x₂)`, `ẋ₂ = F₂(t, x₂, w)`, with output `(h₁(t, x₁, x₂), h₂(t, x₂, w))`.  With
`W = Unit` this is the cascade of `s₁` with an autonomous system. -/
@[blueprint "def:continuousSystem-cascade"
  (title := "Cascade of continuous-time systems")
  (statement := /-- For a system $s_1$ whose input space is the state space of a system $s_2$
    with input $w$, the \emph{cascade} is the system on pairs $(x_1, x_2)$ with input $w$
    \[
      \dot x_1 = F_1(t, x_1, x_2), \qquad \dot x_2 = F_2(t, x_2, w),
    \]
    with output $(h_1(t, x_1, x_2), h_2(t, x_2, w))$: the state of $s_2$ drives $s_1$. -/)]
def cascade (s₁ : ContinuousSystem E E₂ Y) (s₂ : ContinuousSystem E₂ W Y₂) :
    ContinuousSystem (E × E₂) W (Y × Y₂) where
  F t x w := (s₁.F t x.1 x.2, s₂.F t x.2 w)
  h t x w := (s₁.h t x.1 x.2, s₂.h t x.2 w)

/-- A trajectory of the cascade is a pair of trajectories: of `s₁` under the input `x₂`, and of
`s₂` under the external input. -/
@[blueprint "lem:continuousSystem-cascade-isTrajectoryOn-iff"
  (title := "Trajectories of a cascade")
  (latexEnv := "lemma")
  (statement := /-- A map $(x_1, x_2)$ is a trajectory of the cascade
    (\cref{def:continuousSystem-cascade}) under the input $w$ on $I$ exactly when $x_1$ is a
    trajectory of $s_1$ under the input $x_2$ on $I$ and $x_2$ is a trajectory of $s_2$ under
    $w$ on $I$. -/)]
lemma cascade_isTrajectoryOn_iff [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E₂]
    [NormedSpace ℝ E₂] {s₁ : ContinuousSystem E E₂ Y} {s₂ : ContinuousSystem E₂ W Y₂}
    {u : ℝ → W} {x : ℝ → E × E₂} {I : Set ℝ} :
    (cascade s₁ s₂).IsTrajectoryOn u x I ↔
      s₁.IsTrajectoryOn (fun τ => (x τ).2) (fun τ => (x τ).1) I ∧
        s₂.IsTrajectoryOn u (fun τ => (x τ).2) I := by
  constructor
  · intro hx
    exact ⟨fun t ht =>
        (ContinuousLinearMap.fst ℝ E E₂).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht),
      fun t ht => (ContinuousLinearMap.snd ℝ E E₂).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)⟩
  · rintro ⟨h₁, h₂⟩ t ht
    exact (h₁ t ht).prodMk (h₂ t ht)

/-- A right trajectory of the cascade is a pair of right trajectories, as for trajectories
(`cascade_isTrajectoryOn_iff`). -/
@[blueprint "lem:continuousSystem-cascade-isRightTrajectoryOn-iff"
  (title := "Right trajectories of a cascade")
  (latexEnv := "lemma")
  (statement := /-- A map $(x_1, x_2)$ is a right trajectory of the cascade
    (\cref{def:continuousSystem-isRightTrajectoryOn}, \cref{def:continuousSystem-cascade})
    under $w$ on $I$ exactly when $x_1$ is a right trajectory of $s_1$ under the input $x_2$ and
    $x_2$ is a right trajectory of $s_2$ under $w$, on $I$. -/)]
lemma cascade_isRightTrajectoryOn_iff [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {s₁ : ContinuousSystem E E₂ Y}
    {s₂ : ContinuousSystem E₂ W Y₂} {u : ℝ → W} {x : ℝ → E × E₂} {I : Set ℝ} :
    (cascade s₁ s₂).IsRightTrajectoryOn u x I ↔
      s₁.IsRightTrajectoryOn (fun τ => (x τ).2) (fun τ => (x τ).1) I ∧
        s₂.IsRightTrajectoryOn u (fun τ => (x τ).2) I := by
  constructor
  · rintro ⟨hc, hx⟩
    exact ⟨⟨continuous_fst.comp_continuousOn hc, fun t ht =>
        (ContinuousLinearMap.fst ℝ E E₂).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)⟩,
      ⟨continuous_snd.comp_continuousOn hc, fun t ht =>
        (ContinuousLinearMap.snd ℝ E E₂).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)⟩⟩
  · rintro ⟨⟨hc₁, h₁⟩, ⟨hc₂, h₂⟩⟩
    exact ⟨hc₁.prodMk hc₂, fun t ht => (h₁ t ht).prodMk (h₂ t ht)⟩

end Cascade

/-! ### Carathéodory trajectories -/

section Caratheodory

open MeasureTheory Set Topology

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `x` is a *Carathéodory trajectory* of `s` under the input `u` on the set `I`: between any two
times `a ≤ b` in `I`, the map `τ ↦ F(τ, x(τ), u(τ))` is integrable and
`x(b) - x(a) = ∫ₐᵇ F(τ, x(τ), u(τ)) dτ`.

This is the integral form of `IsTrajectoryOn`.  It does not ask `x` to be differentiable, so it
admits the solutions produced by discontinuous inputs (piecewise-constant, sampled-data, bang-bang,
or merely measurable and bounded), which have corners where the input jumps and are not classical
trajectories.  Input-driven notions such as input-to-state stability need this form.  When
`τ ↦ F(τ, x(τ), u(τ))` is continuous the two notions agree on every interval
(`isCaratheodoryTrajectoryOn_iff_isTrajectoryOn`).

Because the equation links every pair of points of `I`, there is no vacuity at isolated points: on
`{0, 1}` it ties `x 1` to `x 0`, and on a singleton it says nothing, which is correct.

Completeness of `E` is required: without it the Bochner integral is `0` by convention, and the
definition would silently say that `x` is constant. -/
@[blueprint "def:continuousSystem-isCaratheodoryTrajectoryOn"
  (title := "Carathéodory trajectory of a continuous-time system")
  (statement := /-- A map $x : \mathbb{R} \to E$, with $E$ a Banach space, is a
    \emph{Carathéodory trajectory} of $s$ under the input $u$ on a set $I \subseteq \mathbb{R}$
    when, for all $a \le b$ in $I$, the map $\tau \mapsto F(\tau, x(\tau), u(\tau))$ is integrable
    on $[a, b]$ and
    \[
      x(b) - x(a) = \int_{a}^{b} F(\tau, x(\tau), u(\tau))\,\mathrm{d}\tau .
    \]
    Unlike \cref{def:continuousSystem-isTrajectoryOn} it does not require $x$ to be
    differentiable, so it admits the solutions produced by discontinuous or merely measurable
    inputs, which input-to-state stability quantifies over. -/)]
def IsCaratheodoryTrajectoryOn (s : ContinuousSystem E U Y) (u : ℝ → U) (x : ℝ → E)
    (I : Set ℝ) : Prop :=
  ∀ a ∈ I, ∀ b ∈ I, a ≤ b →
    IntervalIntegrable (fun τ => s.vectorField u τ (x τ)) volume a b ∧
      x b - x a = ∫ τ in a..b, s.vectorField u τ (x τ)

/-- `x` is a Carathéodory trajectory of `s` under the input `u` for all time. -/
@[blueprint "def:continuousSystem-isCaratheodoryTrajectory"
  (title := "Carathéodory trajectory for all time")
  (statement := /-- A Carathéodory trajectory
    (\cref{def:continuousSystem-isCaratheodoryTrajectoryOn}) on all of $\mathbb{R}$. -/)]
def IsCaratheodoryTrajectory (s : ContinuousSystem E U Y) (u : ℝ → U) (x : ℝ → E) : Prop :=
  s.IsCaratheodoryTrajectoryOn u x univ

omit [CompleteSpace E] in
@[blueprint "lem:continuousSystem-isCaratheodoryTrajectory-isCaratheodoryTrajectoryOn"
  (title := "Restriction of a Carathéodory trajectory")
  (latexEnv := "lemma")
  (statement := /-- A Carathéodory trajectory on $I$ is one on every subset of $I$; in
    particular one for all time is one on every set. -/)]
lemma IsCaratheodoryTrajectoryOn.mono {s : ContinuousSystem E U Y} {u : ℝ → U} {x : ℝ → E}
    {I J : Set ℝ} (h : s.IsCaratheodoryTrajectoryOn u x I) (hJI : J ⊆ I) :
    s.IsCaratheodoryTrajectoryOn u x J :=
  fun a ha b hb hab => h a (hJI ha) b (hJI hb) hab

/-- **On a segment, the integral and derivative forms agree** when `τ ↦ F(τ, x(τ), u(τ))` is
continuous there. -/
@[blueprint "thm:continuousSystem-isCaratheodoryTrajectoryOn-Icc-iff"
  (title := "Carathéodory and classical trajectories agree on a segment")
  (statement := /-- Let $t_0 \le t_1$ and let $\tau \mapsto F(\tau, x(\tau), u(\tau))$ be
    continuous on $[t_0, t_1]$.  Then $x$ is a Carathéodory trajectory on $[t_0, t_1]$
    (\cref{def:continuousSystem-isCaratheodoryTrajectoryOn}) if and only if it is a trajectory
    there (\cref{def:continuousSystem-isTrajectoryOn}). -/)
  (proof := /-- Both are equivalent to the integral equation anchored at $t_0$
    (\cref{def:isIntegralSolution}), by \cref{lem:isIntegralSolution-iff-isIntegralCurveOn}.  The
    anchored equation gives the equation between any $a \le b$ by subtracting its values at $b$
    and $a$. -/)]
theorem isCaratheodoryTrajectoryOn_Icc_iff {s : ContinuousSystem E U Y} {u : ℝ → U}
    {x : ℝ → E} {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
    (hg : ContinuousOn (fun τ => s.vectorField u τ (x τ)) (Icc t₀ t₁)) :
    s.IsCaratheodoryTrajectoryOn u x (Icc t₀ t₁) ↔ s.IsTrajectoryOn u x (Icc t₀ t₁) := by
  have h_uIcc : uIcc t₀ t₁ = Icc t₀ t₁ := uIcc_of_le hle
  have hg' : ContinuousOn (fun τ => s.vectorField u τ (x τ)) (uIcc t₀ t₁) := h_uIcc ▸ hg
  -- integrable between any two points of the segment, by continuity
  have h_int : ∀ a ∈ Icc t₀ t₁, ∀ b ∈ Icc t₀ t₁,
      IntervalIntegrable (fun τ => s.vectorField u τ (x τ)) volume a b := fun a ha b hb =>
    (hg.mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  constructor
  · -- integral form ⇒ anchored integral equation ⇒ integral curve
    intro h
    have h_sol : IsIntegralSolution t₀ t₁ x (x t₀) (s.vectorField u) := fun t ht => by
      rw [h_uIcc] at ht
      have h_eq := (h t₀ (left_mem_Icc.2 hle) t ht ht.1).2
      refine ⟨h_int t₀ (left_mem_Icc.2 hle) t ht, ?_⟩
      rw [← h_eq]
      abel
    have h_curve := (isIntegralSolution_iff_isIntegralCurveOn hg').1 h_sol
    rwa [h_uIcc] at h_curve
  · -- integral curve ⇒ anchored integral equation ⇒ equation between any `a ≤ b`
    intro h a ha b hb _
    have h_sol := (isIntegralSolution_iff_isIntegralCurveOn hg').2 (by rwa [h_uIcc])
    refine ⟨h_int a ha b hb, ?_⟩
    rw [(h_sol b (h_uIcc ▸ hb)).2, (h_sol a (h_uIcc ▸ ha)).2, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (h_int t₀ (left_mem_Icc.2 hle) b hb)
        (h_int t₀ (left_mem_Icc.2 hle) a ha)]

/-- **On any interval, the integral and derivative forms agree** when `τ ↦ F(τ, x(τ), u(τ))` is
continuous there.

The interval may be closed, open, half-open, a ray, all of `ℝ`, or a single point.
Order-connectedness is exactly what is needed: the integral form integrates along `[a, b] ⊆ I`,
while the derivative form only looks near each point, and on a set with a gap the two differ. -/
@[blueprint "thm:continuousSystem-isCaratheodoryTrajectoryOn-iff"
  (title := "Carathéodory and classical trajectories agree on an interval")
  (statement := /-- Let $I \subseteq \mathbb{R}$ be an interval (order-connected) and let
    $\tau \mapsto F(\tau, x(\tau), u(\tau))$ be continuous on $I$.  Then $x$ is a Carathéodory
    trajectory on $I$ (\cref{def:continuousSystem-isCaratheodoryTrajectoryOn}) if and only if it is
    a trajectory there (\cref{def:continuousSystem-isTrajectoryOn}).

    Order-connectedness cannot be dropped: on $\{0\} \cup [1, 2]$ the integral form relates $x(1)$
    to $x(0)$, the derivative form does not. -/)
  (proof := /-- Both notions reduce to closed segments inside $I$, where they agree by
    \cref{thm:continuousSystem-isCaratheodoryTrajectoryOn-Icc-iff}.  For the integral form, the
    equation between $a \le b$ only involves $[a, b] \subseteq I$.  For the derivative form, at
    $t \in I$ choose $a \le t \le b$ in $I$, taking $a < t$ if $I$ has a point left of $t$ and
    $a = t$ otherwise, and likewise for $b$.  Then $[a, b] \subseteq I$ agrees with $I$ near $t$,
    so a derivative within $[a, b]$ at $t$ is one within $I$. -/)]
theorem isCaratheodoryTrajectoryOn_iff_isTrajectoryOn {s : ContinuousSystem E U Y} {u : ℝ → U}
    {x : ℝ → E} {I : Set ℝ} (hI : I.OrdConnected)
    (hg : ContinuousOn (fun τ => s.vectorField u τ (x τ)) I) :
    s.IsCaratheodoryTrajectoryOn u x I ↔ s.IsTrajectoryOn u x I := by
  constructor
  · -- at each `t ∈ I`, pass to a closed segment `[a, b] ⊆ I` that agrees with `I` near `t`
    intro h t ht
    -- a left end `a ≤ t` in `I`, below which `I` has no points near `t`
    obtain ⟨a, ha, hat, h_lower⟩ : ∃ a ∈ I, a ≤ t ∧ ∀ᶠ τ in 𝓝[I] t, a ≤ τ := by
      by_cases hL : ∃ a ∈ I, a < t
      · obtain ⟨a, ha, hlt⟩ := hL
        exact ⟨a, ha, hlt.le,
          ((eventually_gt_nhds hlt).filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le⟩
      · push Not at hL
        exact ⟨t, ht, le_rfl, eventually_nhdsWithin_of_forall hL⟩
    -- a right end `b ≥ t` in `I`, above which `I` has no points near `t`
    obtain ⟨b, hb, htb, h_upper⟩ : ∃ b ∈ I, t ≤ b ∧ ∀ᶠ τ in 𝓝[I] t, τ ≤ b := by
      by_cases hR : ∃ b ∈ I, t < b
      · obtain ⟨b, hb, hlt⟩ := hR
        exact ⟨b, hb, hlt.le,
          ((eventually_lt_nhds hlt).filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le⟩
      · push Not at hR
        exact ⟨t, ht, le_rfl, eventually_nhdsWithin_of_forall hR⟩
    have h_sub : Icc a b ⊆ I := hI.out ha hb
    have h_near : Icc a b ∈ 𝓝[I] t := (h_lower.and h_upper).mono fun _ h => h
    -- on the segment the trajectory is classical, and the segment is `I` near `t`
    have h_seg := (isCaratheodoryTrajectoryOn_Icc_iff (hat.trans htb) (hg.mono h_sub)).1
      (h.mono h_sub)
    exact (h_seg t ⟨hat, htb⟩).mono_of_mem_nhdsWithin h_near
  · -- the equation between `a ≤ b` only involves the segment `[a, b] ⊆ I`
    intro h a ha b hb hab
    have h_sub : Icc a b ⊆ I := hI.out ha hb
    have h_seg := (isCaratheodoryTrajectoryOn_Icc_iff hab (hg.mono h_sub)).2
      (IsIntegralCurveOn.mono h h_sub)
    exact h_seg a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab

end Caratheodory

end ContinuousSystem

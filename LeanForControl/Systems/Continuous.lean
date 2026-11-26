import LeanForControl.Analysis.AbsolutelyContinuous
import LeanForControl.Analysis.LieDerivative
import LeanForControl.Analysis.IntegralCurves
import LeanForControl.ODEs.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
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

A trajectory is a solution in the sense of Carathéodory.  **`IsTrajectoryOn s u x I`** says that
for every segment `[a, b] ⊆ I`, `τ ↦ F(τ, x(τ), u(τ))` is integrable on it and
`x(b) - x(a) = ∫ₐᵇ F(τ, x(τ), u(τ)) dτ`.  It needs `E` complete but not `x` differentiable, so it
admits the solutions produced by piecewise-constant, sampled-data, bang-bang and merely measurable
inputs, which have corners where the input jumps.  A trajectory is continuous on an interval and
has derivative `F(t, x(t), u(t))` almost everywhere.

The classical notion is Mathlib's `IsIntegralCurveOn x (s.vectorField u) I`.  A classical
solution along which the field is integrable on every segment of `I` is a trajectory
(`isTrajectoryOn_of_isIntegralCurveOn`), and on an interval a trajectory along which the field is
continuous is classical (`IsTrajectoryOn.isIntegralCurveOn`).  On an interval the two notions
therefore agree when the field is continuous along `x` (`isTrajectoryOn_iff_isIntegralCurveOn`),
in particular when it is jointly continuous
(`isTrajectoryOn_iff_isIntegralCurveOn_of_continuous`).  On a segment, a trajectory is exactly an
integral solution (`isTrajectoryOn_Icc_iff_isIntegralSolution`), so the integral-form tools of
`Analysis.IntegralCurves` and `ODEs.ODE_properties` (re-anchoring, time reflection, Grönwall) apply
to trajectories with no continuity assumption.  Neither notion handles discontinuity in the
*state*, such as discontinuous feedback, which needs Filippov solutions.

A trajectory is absolutely continuous on the segments of its set
(`IsTrajectoryOn.absolutelyContinuousOnInterval`), and a function `V(t, x)` has derivative
`s.lieDerivative V t (x t) (u t)` along it at almost every time at which `V` is differentiable
(`IsTrajectoryOn.ae_hasDerivAt_lieDerivative`).  The Lyapunov arguments built on this, for `V`
locally Lipschitz near the graph of the trajectory — integrated bound, monotonicity, level bound,
exponential decay — are `IsTrajectoryOn.sub_le_integral_of_lieDerivative_le` and its neighbours;
`IsTrajectoryOn.sub_le_integral_of_fderiv_le` and `IsTrajectoryOn.antitoneOn_of_fderiv_nonpos` are
the forms for a time-invariant `V(x)`.

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

open MeasureTheory Set Topology
open scoped Pointwise

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `x` is a trajectory of `s` under the input `u` on the set `I`: on every segment `[a, b] ⊆ I`,
the map `τ ↦ F(τ, x(τ), u(τ))` is integrable and
`x(b) - x(a) = ∫ₐᵇ F(τ, x(τ), u(τ)) dτ`.  This is the Carathéodory notion of solution.

It does not ask `x` to be differentiable, so it admits the solutions produced by discontinuous
inputs (piecewise-constant, sampled-data, bang-bang, or merely measurable and bounded), which have
corners where the input jumps.  A trajectory is continuous on an interval
(`IsTrajectoryOn.continuousOn`) and has derivative `F(t, x(t), u(t))` at almost every time
(`IsTrajectoryOn.ae_hasDerivAt`).  When `τ ↦ F(τ, x(τ), u(τ))` is continuous it is exactly a
classical solution, Mathlib's `IsIntegralCurveOn` (`isTrajectoryOn_iff_isIntegralCurveOn`).

Stated on a set rather than on all of `ℝ`, because a map can satisfy the equation on an interval
without being defined for all time.  Only segments inside `I` are used, so the predicate depends
only on `x` on `I`: on an interval it links every two of its times, and on a set with gaps it says
that `x` is a trajectory on each piece separately, with no relation across a gap.  The output is
`s.outputMap u t (x t)`; it is not part of this predicate, because the output equation constrains
nothing about `x`.

Integrability is part of the definition, and `E` is complete: without completeness the Bochner
integral is `0` by convention, and the definition would silently say that `x` is constant. -/
@[blueprint "def:continuousSystem-isTrajectoryOn"
  (title := "Trajectory of a continuous-time system")
  (statement := /-- A map $x : \mathbb{R} \to E$, with $E$ a Banach space, is a
    \emph{trajectory} of $s$ under the input $u$ on a set $I \subseteq \mathbb{R}$ when, for every
    segment $[a, b] \subseteq I$, the map $\tau \mapsto F(\tau, x(\tau), u(\tau))$ is
    integrable on $[a, b]$ and
    \[
      x(b) - x(a) = \int_{a}^{b} F(\tau, x(\tau), u(\tau))\,\mathrm{d}\tau .
    \]
    This is the Carath\'eodory notion of solution: $x$ need not be differentiable, so it admits
    the solutions produced by discontinuous or merely measurable inputs.  Stated on a set: a map
    can satisfy the equation on an interval without being defined for all time.  Integrability is
    part of the definition, and completeness of $E$ is what makes the integral meaningful. -/),
  -- `CompleteSpace E` is unused in the body on purpose: see the docstring
  nolint unusedArguments]
def IsTrajectoryOn [CompleteSpace E] (s : ContinuousSystem E U Y) (u : ℝ → U) (x : ℝ → E)
    (I : Set ℝ) : Prop :=
  ∀ a b, a ≤ b → Icc a b ⊆ I →
    IntervalIntegrable (fun τ => s.vectorField u τ (x τ)) volume a b ∧
      x b - x a = ∫ τ in a..b, s.vectorField u τ (x τ)

variable [CompleteSpace E]

/-- `x` is a trajectory of `s` under the input `u` for all time. -/
@[blueprint "def:continuousSystem-isTrajectory"
  (title := "Trajectory for all time of a continuous-time system")
  (statement := /-- A trajectory (\cref{def:continuousSystem-isTrajectoryOn}) defined on all of
    $\mathbb{R}$. -/)]
def IsTrajectory (s : ContinuousSystem E U Y) (u : ℝ → U) (x : ℝ → E) : Prop :=
  s.IsTrajectoryOn u x univ

@[blueprint "lem:continuousSystem-isTrajectoryOn-univ"
  (title := "Trajectories of a continuous-time system on the whole line")
  (latexEnv := "lemma")
  (statement := /-- \cref{def:continuousSystem-isTrajectoryOn} at $I = \mathbb{R}$ is
    \cref{def:continuousSystem-isTrajectory}. -/)]
lemma isTrajectoryOn_univ {s : ContinuousSystem E U Y} {u : ℝ → U} {x : ℝ → E} :
    s.IsTrajectoryOn u x Set.univ ↔ s.IsTrajectory u x :=
  Iff.rfl

variable {s : ContinuousSystem E U Y} {u : ℝ → U} {x y : ℝ → E} {I J : Set ℝ}

/-- A trajectory on `I` is one on every subset of `I`. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-mono"
  (title := "Restriction of a trajectory")
  (latexEnv := "lemma")
  (statement := /-- A trajectory on $I$ (\cref{def:continuousSystem-isTrajectoryOn}) is one on
    every subset of $I$. -/)]
lemma IsTrajectoryOn.mono (h : s.IsTrajectoryOn u x I) (hJI : J ⊆ I) : s.IsTrajectoryOn u x J :=
  fun a b hab hJ => h a b hab (hJ.trans hJI)

@[blueprint "lem:continuousSystem-isTrajectory-isTrajectoryOn"
  (title := "Restriction of a trajectory of a continuous-time system")
  (latexEnv := "lemma")
  (statement := /-- A trajectory for all time is a trajectory on every set. -/)]
lemma IsTrajectory.isTrajectoryOn (h : s.IsTrajectory u x) (I : Set ℝ) : s.IsTrajectoryOn u x I :=
  IsTrajectoryOn.mono h (subset_univ I)

/-- On a set with at most one point every map is a trajectory: the equation only relates a time to
itself.  In particular every map is a trajectory on `[t, t]`. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-of-subsingleton"
  (title := "Trajectories on a single point")
  (latexEnv := "lemma")
  (statement := /-- Every map is a trajectory (\cref{def:continuousSystem-isTrajectoryOn}) on a
    set with at most one point, for instance on $[t, t]$. -/)]
lemma isTrajectoryOn_of_subsingleton (hI : I.Subsingleton) : s.IsTrajectoryOn u x I := by
  intro a b hab hJ
  obtain rfl := hI (hJ (left_mem_Icc.2 hab)) (hJ (right_mem_Icc.2 hab))
  simp

/-- **On a segment, a trajectory is an integral solution**, anchored at its own initial value:
the equation between any two times is the equation from the left end, re-anchored.  No continuity
is needed, so the integral-form tools of `Analysis.IntegralCurves` (re-anchoring, time reflection,
continuous dependence) apply to trajectories directly. -/
@[blueprint "thm:continuousSystem-isTrajectoryOn-Icc-iff-isIntegralSolution"
  (title := "Trajectories on a segment are integral solutions")
  (statement := /-- For $t_0 \le t_1$, $x$ is a trajectory on $[t_0, t_1]$
    (\cref{def:continuousSystem-isTrajectoryOn}) if and only if it is an integral solution of
    $\dot x = F(t, x, u(t))$ on $[t_0, t_1]$ with initial value $x(t_0)$
    (\cref{def:isIntegralSolution}). -/)
  (proof := /-- The equation between $t_0$ and $t$ is a special case.  Conversely, re-anchoring
    the integral solution at $a$ (\cref{lem:isIntegralSolution-reanchor}) gives the equation
    between $a$ and $b$. -/)]
theorem isTrajectoryOn_Icc_iff_isIntegralSolution {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁) :
    s.IsTrajectoryOn u x (Icc t₀ t₁) ↔ IsIntegralSolution t₀ t₁ x (x t₀) (s.vectorField u) := by
  constructor
  · intro h t ht
    rw [uIcc_of_le hle] at ht
    obtain ⟨h_int, h_eq⟩ := h t₀ t ht.1 (Icc_subset_Icc_right ht.2)
    exact ⟨h_int, by rw [← h_eq]; abel⟩
  · intro h a b hab hJ
    rw [← uIcc_of_le hle] at hJ
    obtain ⟨h_int, h_eq⟩ := h.reanchor (hJ (left_mem_Icc.2 hab)) (hJ (right_mem_Icc.2 hab)) b
      right_mem_uIcc
    exact ⟨h_int, by rw [h_eq]; abel⟩

/-- A trajectory is continuous on an interval. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-continuousOn"
  (title := "Trajectories are continuous")
  (latexEnv := "lemma")
  (statement := /-- A trajectory (\cref{def:continuousSystem-isTrajectoryOn}) on an interval $I$
    is continuous on $I$. -/)
  (proof := /-- Near $t \in I$, $I$ agrees with a segment $[a, b] \subseteq I$
    (\cref{lem:exists-Icc-mem-nhdsWithin}), on which $x$ is an integral solution
    (\cref{thm:continuousSystem-isTrajectoryOn-Icc-iff-isIntegralSolution}), hence continuous
    (\cref{lem:isIntegralSolution-continuousOn}). -/)]
lemma IsTrajectoryOn.continuousOn (h : s.IsTrajectoryOn u x I) (hI : I.OrdConnected) :
    ContinuousOn x I := by
  intro t ht
  obtain ⟨a, ha, b, hb, hab, h_near⟩ := exists_Icc_mem_nhdsWithin ht
  have h_sol := (isTrajectoryOn_Icc_iff_isIntegralSolution (hab.1.trans hab.2)).1
    (h.mono (hI.out ha hb))
  have h_cont := h_sol.continuousOn
  rw [uIcc_of_le (hab.1.trans hab.2)] at h_cont
  exact (h_cont t hab).mono_of_mem_nhdsWithin h_near

/-- **A trajectory has derivative `F(t, x(t), u(t))` at almost every time** of the interior of its
set.  This is the sense in which a trajectory solves `ẋ = F(t, x, u)`. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-ae-hasDerivAt"
  (title := "Trajectories solve the equation almost everywhere")
  (latexEnv := "lemma")
  (statement := /-- If $x$ is a trajectory on $I$ (\cref{def:continuousSystem-isTrajectoryOn}),
    then for almost every $t$ in the interior of $I$, $x$ is differentiable at $t$ with
    $\dot x(t) = F(t, x(t), u(t))$. -/)
  (proof := /-- On a segment $[a, b] \subseteq I$, $x$ is $x(a)$ plus a primitive of an integrable
    function, which has that function as derivative almost everywhere
    (\cref{lem:ae-hasDerivAt-of-sub-eq-integral}).  This passes to the interior of $I$
    (\cref{lem:ae-mem-interior-imp-of-forall-Icc-subset}). -/)]
lemma IsTrajectoryOn.ae_hasDerivAt (h : s.IsTrajectoryOn u x I) :
    ∀ᵐ t, t ∈ interior I → HasDerivAt x (s.vectorField u t (x t)) t :=
  ae_mem_interior_imp_of_forall_Icc_subset fun a b hab hI =>
    ae_hasDerivAt_of_sub_eq_integral (h a b hab.le hI).1 fun t ht =>
      (h a t (uIcc_of_le hab.le ▸ ht).1
        ((Icc_subset_Icc_right (uIcc_of_le hab.le ▸ ht).2).trans hI)).2

/-- **Trajectories are absolutely continuous** on every segment of the set on which they are
trajectories. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-absolutelyContinuousOnInterval"
  (title := "Trajectories are absolutely continuous")
  (latexEnv := "lemma")
  (statement := /-- If $x$ is a trajectory on $I$ (\cref{def:continuousSystem-isTrajectoryOn})
    and the segment between $a$ and $b$ is contained in $I$, then $x$ is absolutely continuous
    on that segment. -/)
  (proof := /-- On that segment $x$ is $x(a)$ plus the primitive of the integrable function
    $\tau \mapsto F(\tau, x(\tau), u(\tau))$
    (\cref{lem:absolutelyContinuousOnInterval-of-sub-eq-integral}). -/)]
lemma IsTrajectoryOn.absolutelyContinuousOnInterval {a b : ℝ} (h : s.IsTrajectoryOn u x I)
    (hI : uIcc a b ⊆ I) : AbsolutelyContinuousOnInterval x a b := by
  wlog hab : a ≤ b generalizing a b
  · exact (this (uIcc_comm a b ▸ hI) (le_of_not_ge hab)).symm
  rw [uIcc_of_le hab] at hI
  exact absolutelyContinuousOnInterval_of_sub_eq_integral (h a b hab hI).1 fun t ht =>
    (h a t (uIcc_of_le hab ▸ ht).1 ((Icc_subset_Icc_right (uIcc_of_le hab ▸ ht).2).trans hI)).2

/-- Trajectories are determined by their values on `I`: a map agreeing on `I` with a trajectory on
`I` is one. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-congr"
  (title := "Maps agreeing with a trajectory")
  (latexEnv := "lemma")
  (statement := /-- If $x$ is a trajectory on $I$
    (\cref{def:continuousSystem-isTrajectoryOn}) and $y = x$ on $I$, then $y$ is a trajectory on
    $I$. -/)]
lemma IsTrajectoryOn.congr (h : s.IsTrajectoryOn u x I) (hxy : EqOn x y I) :
    s.IsTrajectoryOn u y I := by
  intro a b hab hJ
  have h_eq : EqOn (fun τ => s.vectorField u τ (x τ)) (fun τ => s.vectorField u τ (y τ))
      (uIcc a b) := fun τ hτ => by
    simp only [hxy (hJ (uIcc_of_le hab ▸ hτ))]
  obtain ⟨h_int, h_eq'⟩ := h a b hab hJ
  exact ⟨h_int.congr fun τ hτ => h_eq (uIoc_subset_uIcc hτ), by
    rw [← hxy (hJ (left_mem_Icc.2 hab)), ← hxy (hJ (right_mem_Icc.2 hab)), h_eq',
      intervalIntegral.integral_congr h_eq]⟩

/-- A trajectory only sees the field along itself: if the field of `s'` under `u'` agrees with the
field of `s` under `u` along `x` on `I`, a trajectory of `s` under `u` on `I` is one of `s'` under
`u'`.  The two systems may have different input and output spaces. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-congr-vectorField"
  (title := "Systems whose fields agree along a trajectory")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be a trajectory of $s$ under $u$ on $I$
    (\cref{def:continuousSystem-isTrajectoryOn}).  If
    $F(\tau, x(\tau), u(\tau)) = F'(\tau, x(\tau), u'(\tau))$ for every $\tau \in I$, then $x$
    is a trajectory of $s'$ under $u'$ on $I$. -/)
  (proof := /-- The two integrands agree on every segment contained in $I$. -/)]
lemma IsTrajectoryOn.congr_vectorField {U' Y' : Type*} {s' : ContinuousSystem E U' Y'}
    {u' : ℝ → U'} (h : s.IsTrajectoryOn u x I)
    (hF : ∀ τ ∈ I, s.vectorField u τ (x τ) = s'.vectorField u' τ (x τ)) :
    s'.IsTrajectoryOn u' x I := by
  intro a b hab hJ
  have h_eq : EqOn (fun τ => s.vectorField u τ (x τ)) (fun τ => s'.vectorField u' τ (x τ))
      (uIcc a b) := fun τ hτ => hF τ (hJ (uIcc_of_le hab ▸ hτ))
  obtain ⟨h_int, h_eq'⟩ := h a b hab hJ
  exact ⟨h_int.congr fun τ hτ => h_eq (uIoc_subset_uIcc hτ), by
    rw [h_eq', intervalIntegral.integral_congr h_eq]⟩

/-- **Gluing.** Trajectories on `[a, b]` and on `[b, c]` make one on `[a, c]`. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-glue-Icc"
  (title := "Gluing trajectories")
  (latexEnv := "lemma")
  (statement := /-- If $x$ is a trajectory (\cref{def:continuousSystem-isTrajectoryOn}) on
    $[a, b]$ and on $[b, c]$, it is a trajectory on $[a, c]$. -/)
  (proof := /-- For $p \le b \le q$, add the equations on $[p, b]$ and $[b, q]$; the integrals
    over adjacent intervals add up. -/)]
lemma IsTrajectoryOn.glue_Icc {a b c : ℝ} (h₁ : s.IsTrajectoryOn u x (Icc a b))
    (h₂ : s.IsTrajectoryOn u x (Icc b c)) : s.IsTrajectoryOn u x (Icc a c) := by
  intro p q hpq hJ
  have hp := hJ (left_mem_Icc.2 hpq)
  have hq := hJ (right_mem_Icc.2 hpq)
  rcases le_total q b with hqb | hbq
  · exact h₁ p q hpq (Icc_subset_Icc hp.1 hqb)
  rcases le_total b p with hbp | hpb
  · exact h₂ p q hpq (Icc_subset_Icc hbp hq.2)
  obtain ⟨hi₁, he₁⟩ := h₁ p b hpb (Icc_subset_Icc hp.1 le_rfl)
  obtain ⟨hi₂, he₂⟩ := h₂ b q hbq (Icc_subset_Icc le_rfl hq.2)
  refine ⟨hi₁.trans hi₂, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂, ← he₁, ← he₂]
  abel

/-- A trajectory on `[t₀, ∞)` is one on every segment `[t₀, t]`, and conversely. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-Ici-iff"
  (title := "Trajectories on a ray")
  (latexEnv := "lemma")
  (statement := /-- $x$ is a trajectory on $[t_0, \infty)$
    (\cref{def:continuousSystem-isTrajectoryOn}) if and only if it is one on $[t_0, t]$ for
    every $t$. -/)]
lemma isTrajectoryOn_Ici_iff {t₀ : ℝ} :
    s.IsTrajectoryOn u x (Ici t₀) ↔ ∀ t, s.IsTrajectoryOn u x (Icc t₀ t) :=
  ⟨fun h _ => h.mono Icc_subset_Ici_self,
    fun h a b hab hJ => h b a b hab (Icc_subset_Icc (hJ (left_mem_Icc.2 hab)) le_rfl)⟩

/-- **Time invariance.** If the state equation does not depend on time, shifting a trajectory and
its input in time gives a trajectory on the shifted set.  This holds in particular for a
time-invariant system (`IsTimeInvariant`), whose output equation is constrained as well. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-comp-add"
  (title := "Time shift of a trajectory")
  (latexEnv := "lemma")
  (statement := /-- If $F(t, \cdot, \cdot)$ is the same for every $t$ (as for a time-invariant
    system, \cref{def:continuousSystem-isTimeInvariant}) and $x$ is a trajectory under $u$ on
    $I$ (\cref{def:continuousSystem-isTrajectoryOn}), then $t \mapsto x(t + d)$ is a trajectory
    under $t \mapsto u(t + d)$ on $I - d$. -/)
  (proof := /-- Substitute $\tau \mapsto \tau + d$ in the integral; the equation is the same at
    $\tau$ and $\tau + d$. -/)]
lemma IsTrajectoryOn.comp_add (hs : ∀ t t', s.F t = s.F t') (h : s.IsTrajectoryOn u x I) (d : ℝ) :
    s.IsTrajectoryOn (fun t => u (t + d)) (fun t => x (t + d)) (-d +ᵥ I) := by
  intro a b hab hJ
  obtain ⟨h_int, h_eq⟩ := h (a + d) (b + d) (by linarith) fun τ hτ => by
    have := hJ (show τ - d ∈ Icc a b from ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)
    rwa [mem_neg_vadd_set_iff, vadd_eq_add, add_sub_cancel] at this
  have h_fun : (fun τ => s.vectorField (fun t => u (t + d)) τ (x (τ + d))) =
      fun τ => s.vectorField u (τ + d) (x (τ + d)) := by
    funext τ
    simp only [vectorField_apply, hs τ (τ + d)]
  rw [h_fun, intervalIntegral.integral_comp_add_right (fun τ => s.vectorField u τ (x τ))]
  refine ⟨?_, h_eq⟩
  simpa using h_int.comp_add_right d

/-- **Change of coordinates.**  An affine map `x ↦ c + e x`, with `e` linear and continuous, that
carries the field of `s` under `u` to the field of `s'` under `u'` carries the trajectories of `s`
to trajectories of `s'`. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-semiconj"
  (title := "Trajectories under a change of coordinates")
  (latexEnv := "lemma")
  (statement := /-- Let $e : E \to E'$ be a bounded linear map and $c \in E'$ with
    $F'(t, c + e\,x, u'(t)) = e\,F(t, x, u(t))$ for all $t$ and $x$.  If $x$ is a trajectory of
    $s$ under $u$ on $I$ (\cref{def:continuousSystem-isTrajectoryOn}), then
    $t \mapsto c + e\,x(t)$ is a trajectory of $s'$ under $u'$ on $I$. -/)
  (proof := /-- A bounded linear map commutes with the integral. -/)]
lemma IsTrajectoryOn.semiconj {E' U' Y' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [CompleteSpace E'] {s' : ContinuousSystem E' U' Y'} {u' : ℝ → U'} (e : E →L[ℝ] E') (c : E')
    (he : ∀ t x, s'.F t (c + e x) (u' t) = e (s.F t x (u t))) (h : s.IsTrajectoryOn u x I) :
    s'.IsTrajectoryOn u' (fun t => c + e (x t)) I := fun a b hab hJ => by
  obtain ⟨h_int, h_eq⟩ := h a b hab hJ
  simp only [vectorField_apply, he] at h_int h_eq ⊢
  refine ⟨⟨e.integrable_comp h_int.1, e.integrable_comp h_int.2⟩, ?_⟩
  rw [e.intervalIntegral_comp_comm h_int, ← h_eq, map_sub]
  abel

/-- **An equilibrium is a constant trajectory**: if `F(t, p, u(t)) = 0` for all `t`, the constant
map at `p` is a trajectory on every set. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-const"
  (title := "Constant trajectories at equilibria")
  (latexEnv := "lemma")
  (statement := /-- If $F(t, p, u(t)) = 0$ for every $t$, the constant map $t \mapsto p$ is a
    trajectory (\cref{def:continuousSystem-isTrajectoryOn}) on every set. -/)]
lemma isTrajectoryOn_const {p : E} (h : ∀ t, s.vectorField u t p = 0) :
    s.IsTrajectoryOn u (fun _ => p) I := fun _ _ _ _ => by
  simp only [h, sub_self, intervalIntegral.integral_zero]
  exact ⟨intervalIntegrable_const, trivial⟩

/-- **Bounded speed**: along a trajectory whose field is bounded by `B` on `[a, b]`, the state moves
at most `B (b - a)` between `a` and `b`. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-norm-sub-le"
  (title := "Trajectories of a bounded field move at bounded speed")
  (latexEnv := "lemma")
  (statement := /-- If $x$ is a trajectory on $I$ (\cref{def:continuousSystem-isTrajectoryOn}),
    $[a, b] \subseteq I$ and $\|F(\tau, x(\tau), u(\tau))\| \le B$ for $\tau \in [a, b]$, then
    $\|x(b) - x(a)\| \le B\,(b - a)$. -/)]
lemma IsTrajectoryOn.norm_sub_le (h : s.IsTrajectoryOn u x I) {a b B : ℝ} (hab : a ≤ b)
    (hJ : Icc a b ⊆ I) (hB : ∀ τ ∈ Icc a b, ‖s.vectorField u τ (x τ)‖ ≤ B) :
    ‖x b - x a‖ ≤ B * (b - a) := by
  rw [(h a b hab hJ).2]
  exact intervalIntegral.norm_integral_le_const_mul hab hB

/-! ### Classical solutions -/

/-- **Classical solutions are trajectories**: an integral curve of
`(t, x) ↦ F(t, x, u(t))` along which the field is integrable is a trajectory.  Integrability holds
in particular when the field is continuous along `x` (`isTrajectoryOn_iff_isIntegralCurveOn`). -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-of-isIntegralCurveOn"
  (title := "Classical solutions are trajectories")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be differentiable within $I$ with
    $\dot x(t) = F(t, x(t), u(t))$ for $t \in I$, and $\tau \mapsto F(\tau, x(\tau), u(\tau))$
    integrable on every $[a, b] \subseteq I$.  Then $x$ is a trajectory on $I$
    (\cref{def:continuousSystem-isTrajectoryOn}). -/)
  (proof := /-- On $[a, b] \subseteq I$, $x$ is continuous with derivative
    $F(t, x(t), u(t))$ at every interior point, so the fundamental theorem of calculus gives the
    integral equation. -/)]
lemma isTrajectoryOn_of_isIntegralCurveOn (h : IsIntegralCurveOn x (s.vectorField u) I)
    (h_int : ∀ a b, a ≤ b → Icc a b ⊆ I →
      IntervalIntegrable (fun τ => s.vectorField u τ (x τ)) volume a b) :
    s.IsTrajectoryOn u x I := by
  intro a b hab hab'
  refine ⟨h_int a b hab hab', (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (h.continuousOn.mono hab') (fun t ht => ?_) (h_int a b hab hab')).symm⟩
  exact (h t (hab' (Ioo_subset_Icc_self ht))).mono_of_mem_nhdsWithin
    (nhdsWithin_le_nhds (Filter.mem_of_superset (Icc_mem_nhds ht.1 ht.2) hab'))

/-- **Trajectories with a continuous field are classical solutions**: on an interval, if
`τ ↦ F(τ, x(τ), u(τ))` is continuous, a trajectory is differentiable within the interval with
`ẋ(t) = F(t, x(t), u(t))`. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-isIntegralCurveOn"
  (title := "Trajectories with a continuous field are classical")
  (latexEnv := "lemma")
  (statement := /-- Let $I$ be an interval, $x$ a trajectory on $I$
    (\cref{def:continuousSystem-isTrajectoryOn}), and $\tau \mapsto F(\tau, x(\tau), u(\tau))$
    continuous on $I$.  Then $x$ is differentiable within $I$, with
    $\dot x(t) = F(t, x(t), u(t))$ for every $t \in I$. -/)
  (proof := /-- Near $t \in I$, $I$ agrees with a segment $[a, b] \subseteq I$
    (\cref{lem:exists-Icc-mem-nhdsWithin}).  There $x$ is an integral solution
    (\cref{thm:continuousSystem-isTrajectoryOn-Icc-iff-isIntegralSolution}) with continuous
    integrand, hence differentiable (\cref{lem:isIntegralSolution-iff-isIntegralCurveOn-Icc}). -/)]
lemma IsTrajectoryOn.isIntegralCurveOn (h : s.IsTrajectoryOn u x I) (hI : I.OrdConnected)
    (hg : ContinuousOn (fun τ => s.vectorField u τ (x τ)) I) :
    IsIntegralCurveOn x (s.vectorField u) I := by
  intro t ht
  obtain ⟨a, ha, b, hb, hab, h_near⟩ := exists_Icc_mem_nhdsWithin ht
  have h_seg := (isIntegralSolution_iff_isIntegralCurveOn_Icc (hab.1.trans hab.2)
    (hg.mono (hI.out ha hb))).1
    ((isTrajectoryOn_Icc_iff_isIntegralSolution (hab.1.trans hab.2)).1 (h.mono (hI.out ha hb)))
  exact (h_seg t hab).mono_of_mem_nhdsWithin h_near

/-- **On an interval, trajectories and classical solutions agree** when `τ ↦ F(τ, x(τ), u(τ))` is
continuous there.

The interval may be closed, open, half-open, a ray, all of `ℝ`, or a single point.
Order-connectedness is what the proof needs: the integral form only sees segments inside `I`,
while the derivative form looks near each point, and on a set containing no segment, such as the
rationals, the integral form says nothing and the derivative form does not. -/
@[blueprint "thm:continuousSystem-isTrajectoryOn-iff-isIntegralCurveOn"
  (title := "Trajectories and classical solutions agree for continuous fields")
  (statement := /-- Let $I \subseteq \mathbb{R}$ be an interval (order-connected) and let
    $\tau \mapsto F(\tau, x(\tau), u(\tau))$ be continuous on $I$.  Then $x$ is a trajectory on
    $I$ (\cref{def:continuousSystem-isTrajectoryOn}) if and only if it is differentiable within
    $I$ with $\dot x(t) = F(t, x(t), u(t))$ for every $t \in I$.

    Order-connectedness cannot be dropped: on $\mathbb{Q}$, which contains no segment, every map
    is a trajectory, but not every map is differentiable within $\mathbb{Q}$. -/)
  (proof := /-- \cref{lem:continuousSystem-isTrajectoryOn-isIntegralCurveOn} and
    \cref{lem:continuousSystem-isTrajectoryOn-of-isIntegralCurveOn}; a continuous function is
    integrable on every segment. -/)]
theorem isTrajectoryOn_iff_isIntegralCurveOn (hI : I.OrdConnected)
    (hg : ContinuousOn (fun τ => s.vectorField u τ (x τ)) I) :
    s.IsTrajectoryOn u x I ↔ IsIntegralCurveOn x (s.vectorField u) I :=
  ⟨fun h => h.isIntegralCurveOn hI hg, fun h => isTrajectoryOn_of_isIntegralCurveOn h
    fun _ _ hab hJ => (hg.mono hJ).intervalIntegrable_of_Icc hab⟩

/-- **For a continuous field, trajectories on an interval are the classical solutions**: if
`(t, x) ↦ F(t, x, u(t))` is jointly continuous, the field is continuous along every trajectory and
along every classical solution, so `isTrajectoryOn_iff_isIntegralCurveOn` needs no hypothesis on
`x`. -/
@[blueprint "thm:continuousSystem-isTrajectoryOn-iff-isIntegralCurveOn-of-continuous"
  (title := "Trajectories of a continuous field are the classical solutions")
  (statement := /-- Let $I \subseteq \mathbb{R}$ be an interval and let
    $(t, x) \mapsto F(t, x, u(t))$ be continuous.  Then $x$ is a trajectory on $I$
    (\cref{def:continuousSystem-isTrajectoryOn}) if and only if it is differentiable within $I$
    with $\dot x(t) = F(t, x(t), u(t))$ for every $t \in I$. -/)
  (proof := /-- A trajectory is continuous on $I$
    (\cref{lem:continuousSystem-isTrajectoryOn-continuousOn}), and so is a classical solution; in
    both cases $\tau \mapsto F(\tau, x(\tau), u(\tau))$ is continuous on $I$, and
    \cref{thm:continuousSystem-isTrajectoryOn-iff-isIntegralCurveOn} applies. -/)]
theorem isTrajectoryOn_iff_isIntegralCurveOn_of_continuous
    (hF : Continuous (Function.uncurry (s.vectorField u))) (hI : I.OrdConnected) :
    s.IsTrajectoryOn u x I ↔ IsIntegralCurveOn x (s.vectorField u) I :=
  ⟨fun h => (isTrajectoryOn_iff_isIntegralCurveOn hI
      (hF.comp_continuousOn (continuousOn_id.prodMk (h.continuousOn hI)))).1 h,
    fun h => (isTrajectoryOn_iff_isIntegralCurveOn hI
      (hF.comp_continuousOn (continuousOn_id.prodMk h.continuousOn))).2 h⟩

/-! ### The derivative of a function along the system -/

/-- The derivative of `V(t, x)` along the system at the input value `u`,
`∂V/∂t + ∂V/∂x · F(t, x, u)`: the rate of change of `V` along a trajectory through `x` at time
`t` while the input takes the value `u`.  It is the Lie derivative (`_root_.lieDerivative`) of
`V` along the field `F(·, ·, u)`, so the lemmas of `Analysis.LieDerivative` apply to it
directly: where the field is continuous along it, a trajectory is an integral curve of
`s.vectorField` (`IsTrajectoryOn.isIntegralCurveOn`).  Input-free notions such as
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

/-! ### Functions along trajectories

A trajectory is absolutely continuous, so a function `V(t, x)` that is locally Lipschitz on a set
containing its graph is absolutely continuous along it, with derivative the derivative along the
system `s.lieDerivative V t (x t) (u t)` at almost every time where `V` is differentiable.  The
consequences below are the Lyapunov arguments along trajectories: an almost-everywhere
bound on the derivative along the system integrates to a bound on the increment of `V`, to
monotonicity, to a level bound and to exponential decay.  They hold with no continuity of the
field in time, so they cover discontinuous and merely measurable inputs. -/

section AlongTrajectory

variable {V : ℝ → E → ℝ} {S : Set (ℝ × E)} {a b : ℝ}

/-- **Chain rule along a trajectory**: at almost every time of the interior of `I` at which `V`
is differentiable along the trajectory, `t ↦ V(t, x(t))` has derivative
`s.lieDerivative V t (x t) (u t)`. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-ae-hasDerivAt-lieDerivative"
  (title := "Chain rule along a trajectory")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be a trajectory on $I$ (\cref{def:continuousSystem-isTrajectoryOn}).
    Then for almost every $t$ in the interior of $I$, if $V$ is differentiable at $(t, x(t))$,
    \[
      \frac{d}{dt}\, V(t, x(t)) = \dot V(t, x(t), u(t))
    \]
    (\cref{def:continuousSystem-lieDerivative}). -/)
  (proof := /-- At almost every such $t$, $\dot x(t) = F(t, x(t), u(t))$
    (\cref{lem:continuousSystem-isTrajectoryOn-ae-hasDerivAt}); apply the chain rule. -/)]
lemma IsTrajectoryOn.ae_hasDerivAt_lieDerivative (h : s.IsTrajectoryOn u x I) :
    ∀ᵐ t, t ∈ interior I → DifferentiableAt ℝ (Function.uncurry V) (t, x t) →
      HasDerivAt (fun τ => V τ (x τ)) (s.lieDerivative V t (x t) (u t)) t := by
  filter_upwards [h.ae_hasDerivAt] with t ht hmem hV
  exact hasDerivWithinAt_univ.mp ((ht hmem).hasDerivWithinAt.hasDerivWithinAt_lieDerivative hV)

/-- **Derivative along a trajectory**: on a segment, at almost every time at which `V` is
differentiable along the trajectory, the derivative of `t ↦ V(t, x(t))` is
`s.lieDerivative V t (x t) (u t)`.  The form of the chain rule that the bounds below consume. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-ae-deriv-eq-lieDerivative"
  (title := "Derivative along a trajectory on a segment")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be a trajectory on $[a, b]$
    (\cref{def:continuousSystem-isTrajectoryOn}) and $V$ differentiable at $(t, x(t))$ for almost
    every $t \in (a, b)$.  Then for almost every $t \in (a, b)$ the derivative of
    $\tau \mapsto V(\tau, x(\tau))$ at $t$ is $\dot V(t, x(t), u(t))$
    (\cref{def:continuousSystem-lieDerivative}). -/)
  (proof := /-- \cref{lem:continuousSystem-isTrajectoryOn-ae-hasDerivAt-lieDerivative}; the
    interior of $[a, b]$ is $(a, b)$. -/)]
lemma IsTrajectoryOn.ae_deriv_eq_lieDerivative (hx : s.IsTrajectoryOn u x (Icc a b))
    (hVd : ∀ᵐ t, t ∈ Ioo a b → DifferentiableAt ℝ (Function.uncurry V) (t, x t)) :
    ∀ᵐ t, t ∈ Ioo a b → deriv (fun τ => V τ (x τ)) t = s.lieDerivative V t (x t) (u t) := by
  filter_upwards [hx.ae_hasDerivAt_lieDerivative (V := V), hVd] with t ht hVt hmem
  exact (ht (by rwa [interior_Icc]) (hVt hmem)).deriv

/-- A function `V(t, x)` locally Lipschitz on a set containing the graph of a trajectory on
`[a, b]` is absolutely continuous along it. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-absolutelyContinuousOnInterval-comp"
  (title := "Locally Lipschitz functions along a trajectory")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be a trajectory on $[a, b]$
    (\cref{def:continuousSystem-isTrajectoryOn}), $a \le b$, and $V$ locally Lipschitz on a set
    containing $\{(t, x(t)) : t \in [a, b]\}$.  Then $t \mapsto V(t, x(t))$ is absolutely
    continuous on $[a, b]$. -/)
  (proof := /-- The graph $t \mapsto (t, x(t))$ is absolutely continuous
    (\cref{lem:continuousSystem-isTrajectoryOn-absolutelyContinuousOnInterval},
    \cref{lem:absolutelyContinuousOnInterval-graph}); apply
    \cref{lem:locallyLipschitzOn-comp-absolutelyContinuousOnInterval}. -/)]
lemma IsTrajectoryOn.absolutelyContinuousOnInterval_comp (hx : s.IsTrajectoryOn u x (Icc a b))
    (hab : a ≤ b) (hV : LocallyLipschitzOn S (Function.uncurry V))
    (hxS : ∀ t ∈ Icc a b, (t, x t) ∈ S) :
    AbsolutelyContinuousOnInterval (fun t => V t (x t)) a b :=
  hV.comp_absolutelyContinuousOnInterval (γ := fun t => (t, x t)) (by rwa [uIcc_of_le hab])
    (hx.absolutelyContinuousOnInterval (uIcc_of_le hab).subset).graph

/-- **Integrated Lyapunov inequality along a trajectory.**  If the derivative along the system is
at most `h t` at almost every time of `(a, b)`, then `V` increases by at most `∫ₐᵇ h`. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-sub-le-integral-of-lieDerivative-le"
  (title := "Integrated Lyapunov inequality along a trajectory")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be a trajectory on $[a, b]$
    (\cref{def:continuousSystem-isTrajectoryOn}), $a \le b$, and $V$ locally Lipschitz on a set
    containing $\{(t, x(t)) : t \in [a, b]\}$ and differentiable at $(t, x(t))$ for
    almost every $t \in (a, b)$.  If $\dot V(t, x(t), u(t)) \le h(t)$
    (\cref{def:continuousSystem-lieDerivative}) for almost every $t \in (a, b)$, with $h$
    integrable, then
    \[
      V(b, x(b)) - V(a, x(a)) \le \int_a^b h(t)\,\mathrm{d}t.
    \] -/)
  (proof := /-- $t \mapsto V(t, x(t))$ is absolutely continuous
    (\cref{lem:continuousSystem-isTrajectoryOn-absolutelyContinuousOnInterval-comp}) with
    derivative $\dot V(t, x(t), u(t))$ almost everywhere
    (\cref{lem:continuousSystem-isTrajectoryOn-ae-deriv-eq-lieDerivative}); apply
    \cref{lem:absolutelyContinuousOnInterval-sub-le-integral-of-deriv-le}. -/)]
lemma IsTrajectoryOn.sub_le_integral_of_lieDerivative_le (hx : s.IsTrajectoryOn u x (Icc a b))
    (hab : a ≤ b) (hV : LocallyLipschitzOn S (Function.uncurry V))
    (hxS : ∀ t ∈ Icc a b, (t, x t) ∈ S)
    (hVd : ∀ᵐ t, t ∈ Ioo a b → DifferentiableAt ℝ (Function.uncurry V) (t, x t)) {h : ℝ → ℝ}
    (hh : IntervalIntegrable h volume a b)
    (h_le : ∀ᵐ t, t ∈ Ioo a b → s.lieDerivative V t (x t) (u t) ≤ h t) :
    V b (x b) - V a (x a) ≤ ∫ t in a..b, h t := by
  refine (hx.absolutelyContinuousOnInterval_comp hab hV hxS).sub_le_integral_of_deriv_le hab hh ?_
  filter_upwards [hx.ae_deriv_eq_lieDerivative hVd, h_le] with t ht hle hmem
  exact (ht hmem).trans_le (hle hmem)

/-- **Nonpositive derivative along a trajectory**: if the derivative along the system is
nonpositive at almost every time of `(a, b)`, then `V` does not increase along the trajectory on
`[a, b]`. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-antitoneOn-of-lieDerivative-nonpos"
  (title := "Nonpositive derivative along a trajectory")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be a trajectory on $[a, b]$
    (\cref{def:continuousSystem-isTrajectoryOn}) and $V$ locally Lipschitz on a set containing
    $\{(t, x(t)) : t \in [a, b]\}$ and differentiable at $(t, x(t))$ for almost every
    $t \in (a, b)$.  If
    $\dot V(t, x(t), u(t)) \le 0$ (\cref{def:continuousSystem-lieDerivative}) for almost every
    $t \in (a, b)$, then $t \mapsto V(t, x(t))$ is nonincreasing on $[a, b]$. -/)
  (proof := /-- As in
    \cref{lem:continuousSystem-isTrajectoryOn-sub-le-integral-of-lieDerivative-le},
    with \cref{lem:absolutelyContinuousOnInterval-antitoneOn-of-deriv-nonpos}. -/)]
lemma IsTrajectoryOn.antitoneOn_of_lieDerivative_nonpos (hx : s.IsTrajectoryOn u x (Icc a b))
    (hV : LocallyLipschitzOn S (Function.uncurry V)) (hxS : ∀ t ∈ Icc a b, (t, x t) ∈ S)
    (hVd : ∀ᵐ t, t ∈ Ioo a b → DifferentiableAt ℝ (Function.uncurry V) (t, x t))
    (h_nonpos : ∀ᵐ t, t ∈ Ioo a b → s.lieDerivative V t (x t) (u t) ≤ 0) :
    AntitoneOn (fun t => V t (x t)) (Icc a b) := by
  rcases lt_or_ge b a with hba | hab
  · exact fun _ hs _ _ _ => absurd (hs.1.trans hs.2) (not_le.2 hba)
  refine (hx.absolutelyContinuousOnInterval_comp hab hV hxS).antitoneOn_of_deriv_nonpos ?_
  filter_upwards [hx.ae_deriv_eq_lieDerivative hVd, h_nonpos] with t ht hle hmem
  exact (ht hmem).trans_le (hle hmem)

/-- **Level form**: if the derivative along the system is nonpositive at almost every time of
`(a, b)` at which `V` exceeds the level `η`, then `V` never exceeds `max (V a (x a)) η` along the
trajectory on `[a, b]`. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-le-max-of-lieDerivative-nonpos"
  (title := "Nonpositive derivative above a level, along a trajectory")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be a trajectory on $[a, b]$
    (\cref{def:continuousSystem-isTrajectoryOn}) and $V$ locally Lipschitz on a set containing
    $\{(t, x(t)) : t \in [a, b]\}$ and differentiable at $(t, x(t))$ for almost every
    $t \in (a, b)$.  If
    $\dot V(t, x(t), u(t)) \le 0$ (\cref{def:continuousSystem-lieDerivative}) for almost every
    $t \in (a, b)$ with $V(t, x(t)) > \eta$, then
    $V(t, x(t)) \le \max\{V(a, x(a)), \eta\}$ for all $t \in [a, b]$. -/)
  (proof := /-- As in
    \cref{lem:continuousSystem-isTrajectoryOn-sub-le-integral-of-lieDerivative-le},
    with \cref{lem:absolutelyContinuousOnInterval-le-max-of-deriv-nonpos}. -/)]
lemma IsTrajectoryOn.le_max_of_lieDerivative_nonpos (hx : s.IsTrajectoryOn u x (Icc a b))
    (hV : LocallyLipschitzOn S (Function.uncurry V)) (hxS : ∀ t ∈ Icc a b, (t, x t) ∈ S)
    (hVd : ∀ᵐ t, t ∈ Ioo a b → DifferentiableAt ℝ (Function.uncurry V) (t, x t)) {η : ℝ}
    (h_dec : ∀ᵐ t, t ∈ Ioo a b → η < V t (x t) → s.lieDerivative V t (x t) (u t) ≤ 0) :
    ∀ t ∈ Icc a b, V t (x t) ≤ max (V a (x a)) η := by
  intro t ht
  refine (hx.absolutelyContinuousOnInterval_comp (ht.1.trans ht.2) hV hxS
    ).le_max_of_deriv_nonpos ?_ t ht
  filter_upwards [hx.ae_deriv_eq_lieDerivative hVd, h_dec] with t ht hle hmem hη
  exact (ht hmem).trans_le (hle hmem hη)

/-- **Exponential decay along a trajectory**: if the derivative along the system is at most
`-c V` at almost every time of `(a, b)`, then `V(t, x(t)) ≤ V(a, x(a)) e^{-c(t - a)}` on
`[a, b]`.  With `c < 0` this is a growth bound. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-le-mul-exp-of-lieDerivative-le"
  (title := "Exponential bound along a trajectory")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be a trajectory on $[a, b]$
    (\cref{def:continuousSystem-isTrajectoryOn}), $V$ locally Lipschitz on a set containing
    $\{(t, x(t)) : t \in [a, b]\}$ and differentiable at $(t, x(t))$ for almost every
    $t \in (a, b)$, and $c \in \mathbb{R}$.  If $\dot V(t, x(t), u(t)) \le -c\, V(t, x(t))$
    (\cref{def:continuousSystem-lieDerivative}) for almost every $t \in (a, b)$, then
    $V(t, x(t)) \le V(a, x(a))\, e^{-c(t - a)}$ for all $t \in [a, b]$. -/)
  (proof := /-- As in
    \cref{lem:continuousSystem-isTrajectoryOn-sub-le-integral-of-lieDerivative-le},
    with \cref{lem:absolutelyContinuousOnInterval-le-mul-exp-of-deriv-le}. -/)]
lemma IsTrajectoryOn.le_mul_exp_of_lieDerivative_le (hx : s.IsTrajectoryOn u x (Icc a b))
    (hV : LocallyLipschitzOn S (Function.uncurry V)) (hxS : ∀ t ∈ Icc a b, (t, x t) ∈ S)
    (hVd : ∀ᵐ t, t ∈ Ioo a b → DifferentiableAt ℝ (Function.uncurry V) (t, x t)) {c : ℝ}
    (h_rate : ∀ᵐ t, t ∈ Ioo a b → s.lieDerivative V t (x t) (u t) ≤ -c * V t (x t)) :
    ∀ t ∈ Icc a b, V t (x t) ≤ V a (x a) * Real.exp (-c * (t - a)) := by
  intro t ht
  refine (hx.absolutelyContinuousOnInterval_comp (ht.1.trans ht.2) hV hxS
    ).le_mul_exp_of_deriv_le ?_ t ht
  filter_upwards [hx.ae_deriv_eq_lieDerivative hVd, h_rate] with t ht hle hmem
  exact (ht hmem).trans_le (hle hmem)

/-- **Integrated Lyapunov inequality, time-invariant form.**  For `V : E → ℝ` locally Lipschitz on
a set containing the trajectory, a bound `DV(x(t)) F(t, x(t), u(t)) ≤ h t` at almost every time of
`(a, b)` integrates to `V(x(b)) - V(x(a)) ≤ ∫ₐᵇ h`. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-sub-le-integral-of-fderiv-le"
  (title := "Integrated Lyapunov inequality, time-invariant function")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be a trajectory on $[a, b]$
    (\cref{def:continuousSystem-isTrajectoryOn}), $a \le b$, with values in $D$ on $[a, b]$, and
    $V : E \to \mathbb{R}$ locally Lipschitz on $D$ and differentiable at $x(t)$ for almost every
    $t \in (a, b)$.  If $DV(x(t))\, F(t, x(t), u(t)) \le h(t)$ for almost every $t \in (a, b)$,
    with $h$ integrable, then
    \[
      V(x(b)) - V(x(a)) \le \int_a^b h(t)\,\mathrm{d}t.
    \] -/)
  (proof := /-- \cref{lem:continuousSystem-isTrajectoryOn-sub-le-integral-of-lieDerivative-le}
    for $(t, x) \mapsto V(x)$, which is locally Lipschitz
    (\cref{lem:locallyLipschitzOn-comp-snd}) and whose derivative along the system is
    $DV(x)\, F(t, x, u)$ (\cref{lem:lieDerivative-const}). -/)]
lemma IsTrajectoryOn.sub_le_integral_of_fderiv_le {V : E → ℝ} {D : Set E}
    (hx : s.IsTrajectoryOn u x (Icc a b)) (hab : a ≤ b) (hV : LocallyLipschitzOn D V)
    (hxD : ∀ t ∈ Icc a b, x t ∈ D) (hVd : ∀ᵐ t, t ∈ Ioo a b → DifferentiableAt ℝ V (x t))
    {h : ℝ → ℝ} (hh : IntervalIntegrable h volume a b)
    (h_le : ∀ᵐ t, t ∈ Ioo a b → fderiv ℝ V (x t) (s.vectorField u t (x t)) ≤ h t) :
    V (x b) - V (x a) ≤ ∫ t in a..b, h t :=
  hx.sub_le_integral_of_lieDerivative_le (V := fun _ => V) hab hV.comp_snd hxD
    (hVd.mono fun t ht hmem => (ht hmem).comp (t, x t) differentiableAt_snd) hh (by
      filter_upwards [hVd, h_le] with t hVt hle hmem
      exact (lieDerivative_const (hVt hmem)).trans_le (hle hmem))

/-- **Nonpositive derivative along a trajectory, time-invariant form.**  For `V : E → ℝ` locally
Lipschitz on a set containing the trajectory, if `DV(x(t)) F(t, x(t), u(t)) ≤ 0` at almost every
time of `(a, b)`, then `V` does not increase along the trajectory on `[a, b]`. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-antitoneOn-of-fderiv-nonpos"
  (title := "Nonpositive derivative along a trajectory, time-invariant function")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be a trajectory on $[a, b]$
    (\cref{def:continuousSystem-isTrajectoryOn}) with values in $D$ on $[a, b]$, and
    $V : E \to \mathbb{R}$ locally Lipschitz on $D$ and differentiable at $x(t)$ for almost every
    $t \in (a, b)$.  If $DV(x(t))\, F(t, x(t), u(t)) \le 0$ for almost every $t \in (a, b)$,
    then $t \mapsto V(x(t))$ is nonincreasing on $[a, b]$. -/)
  (proof := /-- \cref{lem:continuousSystem-isTrajectoryOn-antitoneOn-of-lieDerivative-nonpos}
    for $(t, x) \mapsto V(x)$, as in
    \cref{lem:continuousSystem-isTrajectoryOn-sub-le-integral-of-fderiv-le}. -/)]
lemma IsTrajectoryOn.antitoneOn_of_fderiv_nonpos {V : E → ℝ} {D : Set E}
    (hx : s.IsTrajectoryOn u x (Icc a b)) (hV : LocallyLipschitzOn D V)
    (hxD : ∀ t ∈ Icc a b, x t ∈ D) (hVd : ∀ᵐ t, t ∈ Ioo a b → DifferentiableAt ℝ V (x t))
    (h_nonpos : ∀ᵐ t, t ∈ Ioo a b → fderiv ℝ V (x t) (s.vectorField u t (x t)) ≤ 0) :
    AntitoneOn (fun t => V (x t)) (Icc a b) :=
  hx.antitoneOn_of_lieDerivative_nonpos (V := fun _ => V) hV.comp_snd hxD
    (hVd.mono fun t ht hmem => (ht hmem).comp (t, x t) differentiableAt_snd) (by
      filter_upwards [hVd, h_nonpos] with t hVt hle hmem
      exact (lieDerivative_const (hVt hmem)).trans_le (hle hmem))

end AlongTrajectory

/-! ### Well-posedness

Solutions here are trajectories in the sense of Carathéodory (`IsTrajectoryOn`), so existence,
uniqueness and completeness are statements about absolutely continuous solutions, classical or
not. -/

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
uniqueness: theorems that use it assume it.  Uniqueness is among all trajectories, classical or
not: for a continuous field, a classical solution is then unique among all trajectories. -/
@[blueprint "def:continuousSystem-hasUniqueSolutions"
  (title := "Uniqueness of solutions")
  (statement := /-- A continuous-time system has \emph{unique solutions} under the input $u$
    when any two trajectories on a segment $[t_0, t_1]$
    (\cref{def:continuousSystem-isTrajectoryOn}) that agree at $t_0$ agree on all of
    $[t_0, t_1]$. -/)]
def HasUniqueSolutions (s : ContinuousSystem E U Y) (u : ℝ → U) : Prop :=
  ∀ (t₀ t₁ : ℝ) (x y : ℝ → E), s.IsTrajectoryOn u x (Set.Icc t₀ t₁) →
    s.IsTrajectoryOn u y (Set.Icc t₀ t₁) → x t₀ = y t₀ → Set.EqOn x y (Set.Icc t₀ t₁)

/-- **Grönwall separation of trajectories.**  If `x ↦ F(t, x, u(t))` is `K`-Lipschitz for every
`t ∈ (t₀, t₁)`, two trajectories on `[t₀, t₁]` separate at most exponentially:
`‖x(t) - y(t)‖ ≤ ‖x(t₀) - y(t₀)‖ e^{K(t - t₀)}`.  No regularity in time is assumed.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), continuous dependence on initial conditions, in
the unperturbed case. -/
@[blueprint "thm:continuousSystem-isTrajectoryOn-dist-le-mul-exp"
  (title := "Grönwall separation of trajectories")
  (statement := /-- If $x \mapsto F(t, x, u(t))$ is $K$-Lipschitz for every $t \in (t_0, t_1)$
    and $x, y$ are trajectories on $[t_0, t_1]$ (\cref{def:continuousSystem-isTrajectoryOn}), then
    \[
      \|x(t) - y(t)\| \le \|x(t_0) - y(t_0)\|\,e^{K(t - t_0)} \qquad \forall\, t \in [t_0, t_1].
    \]

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), continuous dependence on initial
    conditions, in the unperturbed case. -/)
  (proof := /-- Both are integral solutions on $[t_0, t]$
    (\cref{thm:continuousSystem-isTrajectoryOn-Icc-iff-isIntegralSolution}), and the Lipschitz
    bound is the hypothesis of \cref{thm:isIntegralSolution-norm-sub-le-mul-exp}. -/)]
theorem IsTrajectoryOn.dist_le_mul_exp {K : NNReal} {t₀ t₁ : ℝ}
    (hx : s.IsTrajectoryOn u x (Icc t₀ t₁)) (hy : s.IsTrajectoryOn u y (Icc t₀ t₁))
    (hL : ∀ t ∈ Ioo t₀ t₁, LipschitzWith K (s.vectorField u t)) :
    ∀ t ∈ Icc t₀ t₁, dist (x t) (y t) ≤ dist (x t₀) (y t₀) * Real.exp (K * (t - t₀)) := by
  intro t ht
  have hle := ht.1.trans ht.2
  simpa only [dist_eq_norm] using IsIntegralSolution.norm_sub_le_mul_exp K.coe_nonneg hle
    ((isTrajectoryOn_Icc_iff_isIntegralSolution hle).1 hx)
    ((isTrajectoryOn_Icc_iff_isIntegralSolution hle).1 hy)
    (fun r hr => (hL r hr).norm_sub_le _ _) t ht

/-- **Lipschitz right-hand sides have unique solutions.**  If `x ↦ F(t, x, u(t))` is
`K`-Lipschitz for every `t`, solutions are unique forward in time.  No regularity in time is
assumed. -/
@[blueprint "thm:continuousSystem-hasUniqueSolutions-of-lipschitz"
  (title := "Lipschitz systems have unique solutions")
  (statement := /-- If $x \mapsto F(t, x, u(t))$ is $K$-Lipschitz for every $t$, the system has
    unique solutions under $u$ (\cref{def:continuousSystem-hasUniqueSolutions}). -/)
  (proof := /-- Two trajectories agreeing at $t_0$ are at distance at most
    $0 \cdot e^{K(t - t_0)}$ (\cref{thm:continuousSystem-isTrajectoryOn-dist-le-mul-exp}). -/)]
theorem hasUniqueSolutions_of_lipschitz {K : NNReal}
    (hL : ∀ t, LipschitzWith K (s.vectorField u t)) : s.HasUniqueSolutions u := by
  intro t₀ t₁ x y hx hy h₀ t ht
  exact dist_le_zero.mp (by simpa [h₀] using hx.dist_le_mul_exp hy (fun t _ => hL t) t ht)

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
  (proof := /-- From the endpoint $x(t_0)$ of a segment, Picard--Lindel\"of gives a classical
    solution on $[t_0, \infty)$ (\cref{thm:exists-isIntegralCurveOn-Ici}), which is a trajectory
    (\cref{thm:continuousSystem-isTrajectoryOn-iff-isIntegralCurveOn-of-continuous}) and agrees
    with the segment by uniqueness
    (\cref{thm:continuousSystem-hasUniqueSolutions-of-lipschitz}). -/)]
theorem isForwardComplete_of_lipschitz {K : NNReal}
    (hF : Continuous (Function.uncurry (s.vectorField u)))
    (hL : ∀ t, LipschitzWith K (s.vectorField u t)) : s.IsForwardComplete u := by
  intro t₀ t₁ x _ hx _
  obtain ⟨y, hy₀, hy, -⟩ := exists_isIntegralCurveOn_Ici hF hL t₀ (x t₀)
  have hy' : s.IsTrajectoryOn u y (Ici t₀) :=
    (isTrajectoryOn_iff_isIntegralCurveOn_of_continuous hF ordConnected_Ici).2 hy
  exact ⟨y, hy', hasUniqueSolutions_of_lipschitz hL t₀ t₁ y x (hy'.mono Icc_subset_Ici_self) hx
    hy₀⟩

/-- **Exponential bounds on the distance of a trajectory to a point**: if
`‖F(t, x(t), u(t))‖ ≤ L ‖x(t) - x_c‖` at almost every time of a trajectory on `[t₀, t₁]`, then
`‖x(t₀) - x_c‖ e^{-L(t - t₀)} ≤ ‖x(t) - x_c‖ ≤ ‖x(t₀) - x_c‖ e^{L(t - t₀)}` there.  For a field
`L`-Lipschitz in the state with an equilibrium at `x_c`, the hypothesis holds everywhere.

The bound is only needed along the trajectory, and the state space is any Banach space.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), the exercise on exponential bounds for the
solutions of a system with a Lipschitz right-hand side. -/
@[blueprint "thm:continuousSystem-isTrajectoryOn-norm-exp-bounds"
  (title := "Exponential bounds on a trajectory")
  (statement := /-- If $x$ is a trajectory on $[t_0, t_1]$
    (\cref{def:continuousSystem-isTrajectoryOn}) with
    $\|F(t, x(t), u(t))\| \le L\|x(t) - x_c\|$ for almost every $t \in (t_0, t_1)$, then for
    every $t \in [t_0, t_1]$
    \[
      \|x(t_0) - x_c\|\,e^{-L(t - t_0)} \le \|x(t) - x_c\| \le \|x(t_0) - x_c\|\,e^{L(t - t_0)}.
    \]

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), the exercise on exponential bounds for
    the solutions of a system with a Lipschitz right-hand side. -/)
  (proof := /-- $v(t) = \|x(t) - x_c\|$ is absolutely continuous
    (\cref{lem:continuousSystem-isTrajectoryOn-absolutelyContinuousOnInterval},
    \cref{lem:absolutelyContinuousOnInterval-norm}), and at almost every $t$,
    $|v'(t)| \le \|\dot x(t)\| = \|F(t, x(t), u(t))\| \le L\, v(t)$
    (\cref{lem:hasDerivAt-abs-le-norm-of-norm},
    \cref{lem:continuousSystem-isTrajectoryOn-ae-hasDerivAt}).  Apply
    \cref{lem:absolutelyContinuousOnInterval-le-mul-exp-of-deriv-le} to $v$ and to $-v$. -/)]
theorem IsTrajectoryOn.norm_exp_bounds {x_c : E} {t₀ t₁ L : ℝ}
    (hx : s.IsTrajectoryOn u x (Icc t₀ t₁))
    (hL : ∀ᵐ t, t ∈ Ioo t₀ t₁ → ‖s.vectorField u t (x t)‖ ≤ L * ‖x t - x_c‖) {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) :
    ‖x t₀ - x_c‖ * Real.exp (-L * (t - t₀)) ≤ ‖x t - x_c‖ ∧
      ‖x t - x_c‖ ≤ ‖x t₀ - x_c‖ * Real.exp (L * (t - t₀)) := by
  have hle := ht.1.trans ht.2
  have hv : AbsolutelyContinuousOnInterval (fun r => ‖x r - x_c‖) t₀ t₁ :=
    ((IsometryEquiv.subRight x_c).isometry.lipschitzWith.comp_absolutelyContinuousOnInterval
      (hx.absolutelyContinuousOnInterval (uIcc_of_le hle).subset)).norm
  -- almost everywhere, `|v'| ≤ ‖ẋ‖ ≤ L v`
  have hv' : ∀ᵐ r, r ∈ Ioo t₀ t₁ → |deriv (fun r => ‖x r - x_c‖) r| ≤ L * ‖x r - x_c‖ := by
    filter_upwards [hx.ae_hasDerivAt, hv.ae_differentiableAt, hL] with r hr hvr hLr hmem
    exact (((hr (by rwa [interior_Icc])).sub_const x_c).abs_le_norm_of_norm
      (hvr (Icc_subset_uIcc (Ioo_subset_Icc_self hmem))).hasDerivAt).trans (hLr hmem)
  have h_up := hv.le_mul_exp_of_deriv_le (c := -L) (hv'.mono fun r hr hmem => by
    rw [neg_neg]; exact (le_abs_self _).trans (hr hmem)) t ht
  have h_down := hv.neg.le_mul_exp_of_deriv_le (c := L) (hv'.mono fun r hr hmem => by
    rw [deriv.neg, Pi.neg_apply]; linarith [neg_abs_le (deriv (fun r => ‖x r - x_c‖) r), hr hmem])
    t ht
  rw [neg_neg] at h_up
  simp only [Pi.neg_apply, neg_mul, neg_le_neg_iff] at h_down
  exact ⟨by rwa [neg_mul], h_up⟩

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

/-- The initial time is in the existence interval: a trajectory on `[t₀, t₀]` is trivial. -/
@[blueprint "lem:continuousSystem-mem-existenceInterval-self"
  (title := "The initial time is in the existence interval")
  (latexEnv := "lemma")
  (statement := /-- $t_0$ is in the existence interval from $(t_0, x_0)$
    (\cref{def:continuousSystem-existenceInterval}). -/)
  (proof := /-- Every map is a trajectory on $[t_0, t_0]$
    (\cref{lem:continuousSystem-isTrajectoryOn-of-subsingleton}). -/)]
lemma mem_existenceInterval_self (t₀ : ℝ) (x₀ : E) : t₀ ∈ s.existenceInterval u t₀ x₀ :=
  ⟨le_rfl, fun _ => x₀, rfl, isTrajectoryOn_of_subsingleton (Set.subsingleton_Icc_of_ge le_rfl)⟩

/-- The existence interval is an interval: with `t`, it contains every time between `t₀` and
`t`. -/
@[blueprint "lem:continuousSystem-mem-existenceInterval-of-le"
  (title := "The existence interval is an interval")
  (latexEnv := "lemma")
  (statement := /-- If $t$ is in the existence interval from $(t_0, x_0)$
    (\cref{def:continuousSystem-existenceInterval}) and $t_0 \le \tau \le t$, then $\tau$ is in
    it. -/)
  (proof := /-- Restrict a trajectory on $[t_0, t]$ to $[t_0, \tau]$
    (\cref{lem:continuousSystem-isTrajectoryOn-mono}). -/)]
lemma mem_existenceInterval_of_le {t₀ t τ : ℝ} {x₀ : E} (ht : t ∈ s.existenceInterval u t₀ x₀)
    (h₀ : t₀ ≤ τ) (h₁ : τ ≤ t) : τ ∈ s.existenceInterval u t₀ x₀ :=
  ⟨h₀, ht.2.choose, ht.2.choose_spec.1, ht.2.choose_spec.2.mono (Set.Icc_subset_Icc_right h₁)⟩

/-- `φ(t₀; t₀, x₀) = x₀`. -/
@[blueprint "lem:continuousSystem-stateTransitionMap-self"
  (title := "The state transition map at the initial time")
  (latexEnv := "lemma")
  (statement := /-- $\varphi(t_0; t_0, x_0) = x_0$
    (\cref{def:continuousSystem-stateTransitionMap}). -/)
  (proof := /-- $t_0$ is in the existence interval
    (\cref{lem:continuousSystem-mem-existenceInterval-self}), and the trajectory chosen there
    starts at $x_0$. -/),
  simp]
lemma stateTransitionMap_self (t₀ : ℝ) (x₀ : E) : s.stateTransitionMap u t₀ t₀ x₀ = x₀ := by
  have h := mem_existenceInterval_self (s := s) (u := u) t₀ x₀
  rw [stateTransitionMap, dite_eq_left h]
  exact h.2.choose_spec.1

/-- **Forward completeness means global existence**: if every trajectory extends to `[t₀, ∞)`,
the existence interval is all of `[t₀, ∞)`. -/
@[blueprint "lem:continuousSystem-existenceInterval-eq-Ici"
  (title := "Existence intervals of a forward complete system")
  (latexEnv := "lemma")
  (statement := /-- If $s$ is forward complete under $u$
    (\cref{def:continuousSystem-isForwardComplete}), the existence interval
    (\cref{def:continuousSystem-existenceInterval}) from every $(t_0, x_0)$ is $[t_0, \infty)$. -/)
  (proof := /-- Every map is a trajectory on $[t_0, t_0]$; forward completeness extends it to
    $[t_0, \infty)$. -/)]
lemma existenceInterval_eq_Ici (hfc : s.IsForwardComplete u) (t₀ : ℝ) (x₀ : E) :
    s.existenceInterval u t₀ x₀ = Set.Ici t₀ := by
  refine Set.Subset.antisymm (fun t ht => ht.1) fun t ht => ⟨ht, ?_⟩
  obtain ⟨y, hy, hy_eq⟩ := hfc t₀ t₀ (fun _ => x₀) le_rfl
    (isTrajectoryOn_of_subsingleton (Set.subsingleton_Icc_of_ge le_rfl)) (Set.mem_univ _)
  exact ⟨y, hy_eq ⟨le_rfl, le_rfl⟩, hy.mono Set.Icc_subset_Ici_self⟩

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
  have hx_t : s.IsTrajectoryOn u x (Set.Icc t₀ t) := hx.mono (Set.Icc_subset_Icc_right ht.2)
  have hmem : t ∈ s.existenceInterval u t₀ (x t₀) := ⟨ht.1, x, rfl, hx_t⟩
  rw [stateTransitionMap, dite_eq_left hmem]
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
  (proof := /-- For a segment $[a, b]$ contained in the existence interval, $\varphi$ agrees on
    $[t_0, b]$ with a trajectory from $x_0$ (\cref{lem:continuousSystem-eq-stateTransitionMap}),
    so it satisfies the equation between $a$ and $b$
    (\cref{lem:continuousSystem-isTrajectoryOn-congr}). -/)]
lemma isTrajectoryOn_stateTransitionMap (hu : s.HasUniqueSolutions u) (t₀ : ℝ) (x₀ : E) :
    s.IsTrajectoryOn u (fun t => s.stateTransitionMap u t t₀ x₀)
      (s.existenceInterval u t₀ x₀) := by
  intro a b hab hJ
  have ha := hJ (left_mem_Icc.2 hab)
  have hb := hJ (right_mem_Icc.2 hab)
  -- On `[t₀, b]`, `φ` is a trajectory `x` from `x₀`.
  obtain ⟨x, hx₀, hx⟩ := hb.2
  have h_eq := eq_stateTransitionMap hu hx
  rw [hx₀] at h_eq
  exact (hx.congr fun τ hτ => h_eq τ hτ) a b hab (Icc_subset_Icc_left ha.1)

/-- With forward completeness and unique solutions, `t ↦ φ(t; t₀, x₀)` is a trajectory on
`[t₀, ∞)`. -/
@[blueprint "lem:continuousSystem-isTrajectoryOn-stateTransitionMap-Ici"
  (title := "The state transition map of a forward complete system is a trajectory")
  (latexEnv := "lemma")
  (statement := /-- If $s$ is forward complete (\cref{def:continuousSystem-isForwardComplete})
    and has unique solutions (\cref{def:continuousSystem-hasUniqueSolutions}) under $u$, then
    $t \mapsto \varphi(t; t_0, x_0)$ (\cref{def:continuousSystem-stateTransitionMap}) is a
    trajectory on $[t_0, \infty)$. -/)
  (proof := /-- \cref{lem:continuousSystem-isTrajectoryOn-stateTransitionMap}; the existence
    interval is $[t_0, \infty)$ (\cref{lem:continuousSystem-existenceInterval-eq-Ici}). -/)]
lemma isTrajectoryOn_stateTransitionMap_Ici (hfc : s.IsForwardComplete u)
    (hu : s.HasUniqueSolutions u) (t₀ : ℝ) (x₀ : E) :
    s.IsTrajectoryOn u (fun t => s.stateTransitionMap u t t₀ x₀) (Set.Ici t₀) := by
  simpa [existenceInterval_eq_Ici hfc] using isTrajectoryOn_stateTransitionMap hu t₀ x₀

/-- **For a continuous field, the state transition map is a classical solution**: with forward
completeness, unique solutions and `(t, x) ↦ F(t, x, u(t))` jointly continuous,
`t ↦ φ(t; t₀, x₀)` is differentiable within `[t₀, ∞)` with derivative
`F(t, φ(t; t₀, x₀), u(t))`. -/
@[blueprint "lem:continuousSystem-isIntegralCurveOn-stateTransitionMap-Ici"
  (title := "The state transition map of a continuous field is a classical solution")
  (latexEnv := "lemma")
  (statement := /-- Let $s$ be forward complete under $u$
    (\cref{def:continuousSystem-isForwardComplete}) with unique solutions
    (\cref{def:continuousSystem-hasUniqueSolutions}), and let $(t, x) \mapsto F(t, x, u(t))$ be
    continuous.  Then $t \mapsto \varphi(t; t_0, x_0)$
    (\cref{def:continuousSystem-stateTransitionMap}) is differentiable within $[t_0, \infty)$,
    with derivative $F(t, \varphi(t; t_0, x_0), u(t))$ at every $t \ge t_0$. -/)
  (proof := /-- It is a trajectory on $[t_0, \infty)$
    (\cref{lem:continuousSystem-isTrajectoryOn-stateTransitionMap},
    \cref{lem:continuousSystem-existenceInterval-eq-Ici}), and trajectories of a continuous field
    on an interval are classical solutions
    (\cref{thm:continuousSystem-isTrajectoryOn-iff-isIntegralCurveOn-of-continuous}). -/)]
lemma isIntegralCurveOn_stateTransitionMap_Ici
    (hF : Continuous (Function.uncurry (s.vectorField u))) (hfc : s.IsForwardComplete u)
    (hu : s.HasUniqueSolutions u) (t₀ : ℝ) (x₀ : E) :
    IsIntegralCurveOn (fun t => s.stateTransitionMap u t t₀ x₀) (s.vectorField u) (Set.Ici t₀) :=
  (isTrajectoryOn_iff_isIntegralCurveOn_of_continuous hF Set.ordConnected_Ici).1
    (isTrajectoryOn_stateTransitionMap_Ici hfc hu t₀ x₀)

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
    (isTrajectoryOn_stateTransitionMap hu t₀ x₀).mono
      fun r hr => mem_existenceInterval_of_le ht (hτ.trans hr.1) hr.2
  exact (eq_stateTransitionMap hu hy t ⟨hτt, le_rfl⟩).symm

/-- **An equilibrium stays put**: if `F(t, x_eq, u(t)) = 0` for all `t`, then
`φ(t; t₀, x_eq) = x_eq` for `t ≥ t₀`. -/
@[blueprint "lem:continuousSystem-stateTransitionMap-of-equilibrium"
  (title := "The state transition map at an equilibrium")
  (latexEnv := "lemma")
  (statement := /-- If $s$ has unique solutions under $u$
    (\cref{def:continuousSystem-hasUniqueSolutions}) and $F(t, x_{\mathrm{eq}}, u(t)) = 0$ for
    every $t$, then $\varphi(t; t_0, x_{\mathrm{eq}}) = x_{\mathrm{eq}}$ for $t \ge t_0$
    (\cref{def:continuousSystem-stateTransitionMap}). -/)
  (proof := /-- The constant map is a trajectory (\cref{lem:continuousSystem-isTrajectoryOn-const}),
    so it is given by $\varphi$ (\cref{lem:continuousSystem-eq-stateTransitionMap}). -/)]
lemma stateTransitionMap_of_equilibrium (hu : s.HasUniqueSolutions u) {x_eq : E}
    (h_eq : ∀ t, s.vectorField u t x_eq = 0) {t₀ t : ℝ} (ht : t₀ ≤ t) :
    s.stateTransitionMap u t t₀ x_eq = x_eq :=
  (eq_stateTransitionMap hu (isTrajectoryOn_const h_eq) t ⟨ht, le_rfl⟩).symm

/-- **Solutions separate at most exponentially in the initial state**: for a field `L`-Lipschitz
in the state, uniformly in time, `‖φ(t; t₀, x₀) - φ(t; t₀, y₀)‖ ≤ ‖x₀ - y₀‖ e^{L(t - t₀)}`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), continuous dependence on initial conditions,
without perturbation. -/
@[blueprint "thm:continuousSystem-dist-stateTransitionMap-le"
  (title := "Lipschitz dependence on the initial state")
  (statement := /-- If the system is forward complete under $u$
    (\cref{def:continuousSystem-isForwardComplete}) and $x \mapsto F(t, x, u(t))$ is
    $L$-Lipschitz for every $t$, then for $t \ge t_0$
    \[
      \|\varphi(t; t_0, x_0) - \varphi(t; t_0, y_0)\| \le \|x_0 - y_0\|\, e^{L(t - t_0)}
    \]
    (\cref{def:continuousSystem-stateTransitionMap}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), continuous dependence on initial
    conditions, without perturbation. -/)
  (proof := /-- Both maps are trajectories on $[t_0, \infty)$
    (\cref{thm:continuousSystem-hasUniqueSolutions-of-lipschitz}); apply Gr\"onwall separation
    (\cref{thm:continuousSystem-isTrajectoryOn-dist-le-mul-exp}) on $[t_0, t]$. -/)]
theorem dist_stateTransitionMap_le (hfc : s.IsForwardComplete u) {L : NNReal}
    (hL : ∀ t, LipschitzWith L (s.vectorField u t)) {t₀ t : ℝ} (ht : t₀ ≤ t) (x₀ y₀ : E) :
    dist (s.stateTransitionMap u t t₀ x₀) (s.stateTransitionMap u t t₀ y₀) ≤
      dist x₀ y₀ * Real.exp (L * (t - t₀)) := by
  have hu := hasUniqueSolutions_of_lipschitz hL
  simpa using IsTrajectoryOn.dist_le_mul_exp
    ((isTrajectoryOn_stateTransitionMap_Ici hfc hu t₀ x₀).mono Set.Icc_subset_Ici_self)
    ((isTrajectoryOn_stateTransitionMap_Ici hfc hu t₀ y₀).mono Set.Icc_subset_Ici_self)
    (fun t _ => hL t) t ⟨ht, le_rfl⟩

/-- **Solutions depend Lipschitz-continuously on the initial time and state**: for a field
`L`-Lipschitz in the state and bounded by `B`, the solutions from `(t₀, x₀)` and `(t₀', x₀')`,
compared after the same elapsed time `σ`, differ by at most `(2B + 1) e^{Lσ}` times the distance
between the initial data.  Run the earlier one to the later initial time (speed `B`), then apply
`dist_stateTransitionMap_le`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), continuous dependence on initial conditions
and parameters. -/
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

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), continuous dependence on initial
    conditions and parameters. -/)
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
  have hφ : ∀ p, s.IsTrajectoryOn u (φ p) (Set.Ici p.1) := fun p =>
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
    have h_speed : ∀ a b, z.1 ≤ a → a ≤ b → ‖φ z b - φ z a‖ ≤ B * (b - a) :=
      fun a b h₁ h₂ => (hφ z).norm_sub_le h₂ (fun _ hτ => h₁.trans hτ.1) fun _ _ => hB _ _
    have h_gron : ‖φ z (z'.1 + σ) - φ z' (z'.1 + σ)‖ ≤
        ‖φ z z'.1 - z'.2‖ * Real.exp (L * σ) := by
      have h := IsTrajectoryOn.dist_le_mul_exp
        ((hφ z).mono (Set.Icc_subset_Ici_iff (by linarith) |>.2 h))
        ((hφ z').mono Set.Icc_subset_Ici_self) (fun t _ => hL t) (z'.1 + σ) ⟨by linarith, le_rfl⟩
      rwa [dist_eq_norm, dist_eq_norm, hφ0 z', add_sub_cancel_left] at h
    calc ‖φ z (z.1 + σ) - φ z' (z'.1 + σ)‖
        ≤ ‖φ z (z.1 + σ) - φ z (z'.1 + σ)‖ + ‖φ z (z'.1 + σ) - φ z' (z'.1 + σ)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ B * d + (B * d + d) * Real.exp (L * σ) := by
          gcongr
          · calc ‖φ z (z.1 + σ) - φ z (z'.1 + σ)‖
                = ‖φ z (z'.1 + σ) - φ z (z.1 + σ)‖ := norm_sub_rev _ _
              _ ≤ B * (z'.1 + σ - (z.1 + σ)) := h_speed _ _ (by linarith) (by linarith)
              _ ≤ B * d := by gcongr; linarith
          · refine h_gron.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
            calc ‖φ z z'.1 - z'.2‖
                ≤ ‖φ z z'.1 - z.2‖ + ‖z.2 - z'.2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
              _ ≤ B * d + d := by
                  gcongr
                  calc ‖φ z z'.1 - z.2‖
                      = ‖φ z z'.1 - φ z z.1‖ := by rw [hφ0 z]
                    _ ≤ B * (z'.1 - z.1) := h_speed _ _ le_rfl h
                    _ ≤ B * d := by gcongr
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
@[blueprint "lem:continuousSystem-isAutonomous-constInput"
  (title := "The system with its input held constant is autonomous")
  (latexEnv := "lemma")
  (statement := /-- The system of \cref{def:continuousSystem-constInput} is autonomous
    (\cref{def:continuousSystem-isAutonomous}). -/)]
lemma isAutonomous_constInput (s : ContinuousSystem E U Y) (u₀ : U) :
    (s.constInput u₀).IsAutonomous :=
  isAutonomous_autonomous _ _

/-- The trajectories of the system with its input held at `u₀` are those of the system under the
constant input `u₀`. -/
@[blueprint "lem:continuousSystem-constInput-isTrajectoryOn-iff"
  (title := "Trajectories of the system with its input held constant")
  (latexEnv := "lemma")
  (statement := /-- A map is a trajectory of the system with its input held at $u_0$
    (\cref{def:continuousSystem-constInput}) on $I$ exactly when it is a trajectory of $s$ under
    the constant input $u_0$ on $I$. -/)]
lemma constInput_isTrajectoryOn_iff [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
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
@[blueprint "lem:continuousSystem-isAutonomous-zeroInput"
  (title := "The unforced system is autonomous")
  (latexEnv := "lemma")
  (statement := /-- The unforced system (\cref{def:continuousSystem-zeroInput}) is autonomous
    (\cref{def:continuousSystem-isAutonomous}). -/)]
lemma isAutonomous_zeroInput (s : ContinuousSystem E U Y) : s.zeroInput.IsAutonomous :=
  isAutonomous_constInput s 0

/-- The trajectories of the unforced system are those of the system under the zero input. -/
@[blueprint "lem:continuousSystem-zeroInput-isTrajectoryOn-iff"
  (title := "Trajectories of the unforced system")
  (latexEnv := "lemma")
  (statement := /-- A map is a trajectory of the unforced system
    (\cref{def:continuousSystem-zeroInput}) on $I$ exactly when it is a trajectory of $s$ under
    the zero input on $I$. -/)]
lemma zeroInput_isTrajectoryOn_iff [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
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
lemma cascade_isTrajectoryOn_iff [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂] {s₁ : ContinuousSystem E E₂ Y}
    {s₂ : ContinuousSystem E₂ W Y₂} {u : ℝ → W} {x : ℝ → E × E₂} {I : Set ℝ} :
    (cascade s₁ s₂).IsTrajectoryOn u x I ↔
      s₁.IsTrajectoryOn (fun τ => (x τ).2) (fun τ => (x τ).1) I ∧
        s₂.IsTrajectoryOn u (fun τ => (x τ).2) I := by
  constructor
  · intro hx
    -- the integral of a pair is the pair of integrals
    refine ⟨fun a b hab hJ => ?_, fun a b hab hJ => ?_⟩ <;>
      obtain ⟨h_int, h_eq⟩ := hx a b hab hJ
    · have h_int₁ := (ContinuousLinearMap.fst ℝ E E₂).integrable_comp h_int.1
      have h_int₁' := (ContinuousLinearMap.fst ℝ E E₂).integrable_comp h_int.2
      refine ⟨⟨h_int₁, h_int₁'⟩, ?_⟩
      exact (congrArg Prod.fst h_eq).trans
        ((ContinuousLinearMap.fst ℝ E E₂).intervalIntegral_comp_comm h_int).symm
    · have h_int₂ := (ContinuousLinearMap.snd ℝ E E₂).integrable_comp h_int.1
      have h_int₂' := (ContinuousLinearMap.snd ℝ E E₂).integrable_comp h_int.2
      refine ⟨⟨h_int₂, h_int₂'⟩, ?_⟩
      exact (congrArg Prod.snd h_eq).trans
        ((ContinuousLinearMap.snd ℝ E E₂).intervalIntegral_comp_comm h_int).symm
  · rintro ⟨h₁, h₂⟩ a b hab hJ
    obtain ⟨hi₁, he₁⟩ := h₁ a b hab hJ
    obtain ⟨hi₂, he₂⟩ := h₂ a b hab hJ
    have h_int : IntervalIntegrable (fun τ => (cascade s₁ s₂).vectorField u τ (x τ))
        MeasureTheory.volume a b :=
      ⟨hi₁.1.prodMk hi₂.1, hi₁.2.prodMk hi₂.2⟩
    refine ⟨h_int, Prod.ext ?_ ?_⟩
    · exact he₁.trans ((ContinuousLinearMap.fst ℝ E E₂).intervalIntegral_comp_comm h_int)
    · exact he₂.trans ((ContinuousLinearMap.snd ℝ E E₂).intervalIntegral_comp_comm h_int)

end Cascade

end ContinuousSystem

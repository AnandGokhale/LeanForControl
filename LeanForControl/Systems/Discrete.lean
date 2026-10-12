import Mathlib.Data.Set.Basic
import Architect

/-!
# `Systems.Discrete` — the general discrete-time system

The most general discrete-time system the library considers,

* `DiscreteSystem E U Y` — `x⁺ = F(k, x, u)`, `y = h(k, x, u)`, with `k ∈ ℕ`,

with state space `E`, input space `U` and output space `Y`.  The linear systems of
`LinearSystems.Discrete` are special cases.

This is the discrete-time counterpart of `ContinuousSystem` in `Systems.Continuous`, which
explains the design: why the two time domains are separate objects, how the special cases
(time invariance drops `k`, autonomy drops `u`) are constructors with matching predicates, and
that "autonomous" means *without input*.  The API here carries the same names.

## Trajectories

`IsTrajectoryOn s u x I` is the recursion `x(k+1) = F(k, x(k), u(k))` for every `k ∈ I`.
Membership constrains the step *out of* `k`, so `I = Set.Ici k₀` is the forward recursion from
`k₀`, and the horizon `[k₀, k₁]` corresponds to `I = Set.Ico k₀ k₁`.  Unlike continuous time
there is no derivative, so neither the choice of `I` nor regularity of the input raises any
subtlety, and nothing beyond the bare types is needed.
-/

/-- A discrete-time system: the data `(F, h)` of

    x(k+1) = F(k, x(k), u(k)),    y(k) = h(k, x(k), u(k))

with states in `E`, inputs in `U` and outputs in `Y`.  The structure is only the data. -/
@[blueprint "def:discreteSystem"
  (title := "Discrete-time system")
  (statement := /-- A \emph{discrete-time system} with state space $E$, input space $U$ and output
    space $Y$ is the data of two maps
    \[
      F : \mathbb{N} \times E \times U \to E, \qquad h : \mathbb{N} \times E \times U \to Y,
    \]
    to be read as $x^{+} = F(k, x, u)$, $y = h(k, x, u)$.  The same data as
    \cref{def:continuousSystem} with time in $\mathbb{N}$; what differs is the reading, a shift
    rather than a derivative. -/)]
structure DiscreteSystem (E U Y : Type*) where
  /-- State equation: `x⁺ = F(k, x, u)`. -/
  F : ℕ → E → U → E
  /-- Output equation: `y = h(k, x, u)`. -/
  h : ℕ → E → U → Y

namespace DiscreteSystem

variable {E U Y : Type*}

/-- The time-invariant system `x⁺ = f(x, u)`, `y = g(x, u)`. -/
@[blueprint "def:discreteSystem-timeInvariant"
  (title := "Time-invariant discrete-time system")
  (statement := /-- The discrete-time system $x^{+} = f(x, u)$, $y = g(x, u)$, whose equations do
    not depend on time. -/)]
def timeInvariant (f : E → U → E) (g : E → U → Y) : DiscreteSystem E U Y where
  F := fun _ => f
  h := fun _ => g

@[simp] lemma timeInvariant_F (f : E → U → E) (g : E → U → Y) (k : ℕ) :
    (timeInvariant f g).F k = f := rfl

@[simp] lemma timeInvariant_h (f : E → U → E) (g : E → U → Y) (k : ℕ) :
    (timeInvariant f g).h k = g := rfl

/-- The system is *time-invariant*: its equations take the same form at every time. -/
@[blueprint "def:discreteSystem-isTimeInvariant"
  (title := "Time invariance, discrete-time system")
  (statement := /-- A discrete-time system is \emph{time-invariant} when $F(k, \cdot, \cdot)$ and
    $h(k, \cdot, \cdot)$ are the same for every $k$. -/)]
def IsTimeInvariant (s : DiscreteSystem E U Y) : Prop :=
  ∀ k k' : ℕ, s.F k = s.F k' ∧ s.h k = s.h k'

/-- A system built by `timeInvariant` is time-invariant. -/
@[blueprint "lem:discreteSystem-isTimeInvariant-timeInvariant"
  (title := "Time-invariant discrete-time systems are time-invariant")
  (latexEnv := "lemma")
  (statement := /-- The system of \cref{def:discreteSystem-timeInvariant} is time-invariant
    (\cref{def:discreteSystem-isTimeInvariant}). -/)]
theorem isTimeInvariant_timeInvariant (f : E → U → E) (g : E → U → Y) :
    (timeInvariant f g).IsTimeInvariant :=
  fun _ _ => ⟨rfl, rfl⟩

/-- A time-invariant system is built by `timeInvariant`. -/
@[blueprint "lem:discreteSystem-isTimeInvariant-exists-eq"
  (title := "Time-invariant discrete-time systems come from time-free data")
  (latexEnv := "lemma")
  (statement := /-- A time-invariant discrete-time system
    (\cref{def:discreteSystem-isTimeInvariant}) is $\operatorname{timeInvariant} f\,g$ for some $f$
    and $g$.  The converse of \cref{lem:discreteSystem-isTimeInvariant-timeInvariant}. -/)
  (proof := /-- Read $f$ and $g$ off at $k = 0$; time invariance says every other time agrees with
    it. -/)]
theorem IsTimeInvariant.exists_eq {s : DiscreteSystem E U Y} (hs : s.IsTimeInvariant) :
    ∃ (f : E → U → E) (g : E → U → Y), s = timeInvariant f g := by
  refine ⟨s.F 0, s.h 0, ?_⟩
  obtain ⟨sF, sh⟩ := s
  simp only [timeInvariant, mk.injEq]
  exact ⟨funext fun k => (hs k 0).1, funext fun k => (hs k 0).2⟩

/-- The autonomous (input-free) system `x⁺ = f(k, x)`, `y = g(k, x)`, with input space `Unit`. -/
@[blueprint "def:discreteSystem-autonomous"
  (title := "Autonomous discrete-time system")
  (statement := /-- The discrete-time system $x^{+} = f(k, x)$, $y = g(k, x)$, which has no input:
    its input space is the one-point type. -/)]
def autonomous (f : ℕ → E → E) (g : ℕ → E → Y) : DiscreteSystem E Unit Y where
  F := fun k x _ => f k x
  h := fun k x _ => g k x

@[simp] lemma autonomous_F (f : ℕ → E → E) (g : ℕ → E → Y) (k : ℕ) (x : E) (u : Unit) :
    (autonomous f g).F k x u = f k x := rfl

@[simp] lemma autonomous_h (f : ℕ → E → E) (g : ℕ → E → Y) (k : ℕ) (x : E) (u : Unit) :
    (autonomous f g).h k x u = g k x := rfl

/-- The system is *autonomous*: its equations do not depend on the input. -/
@[blueprint "def:discreteSystem-isAutonomous"
  (title := "Autonomy, discrete-time system")
  (statement := /-- A discrete-time system is \emph{autonomous} when $F(k, x, u)$ and $h(k, x, u)$
    do not depend on $u$. -/)]
def IsAutonomous (s : DiscreteSystem E U Y) : Prop :=
  ∀ (k : ℕ) (x : E) (u u' : U), s.F k x u = s.F k x u' ∧ s.h k x u = s.h k x u'

/-- A system built by `autonomous` is autonomous. -/
@[blueprint "lem:discreteSystem-isAutonomous-autonomous"
  (title := "Autonomous discrete-time systems are autonomous")
  (latexEnv := "lemma")
  (statement := /-- The system of \cref{def:discreteSystem-autonomous} is autonomous
    (\cref{def:discreteSystem-isAutonomous}). -/)]
theorem isAutonomous_autonomous (f : ℕ → E → E) (g : ℕ → E → Y) :
    (autonomous f g).IsAutonomous :=
  fun _ _ _ _ => ⟨rfl, rfl⟩

/-- An autonomous system is input-free data in disguise: its equations are those of some `f` and
`g` that do not take an input.  It equals `autonomous f g` only up to the input space, which is
`U` rather than `Unit`. -/
@[blueprint "lem:discreteSystem-isAutonomous-exists"
  (title := "Autonomous discrete-time systems come from input-free data")
  (latexEnv := "lemma")
  (statement := /-- If a discrete-time system is autonomous
    (\cref{def:discreteSystem-isAutonomous}) and its input space is nonempty, there are $f$ and
    $g$ with $F(k, x, u) = f(k, x)$ and $h(k, x, u) = g(k, x)$ for every input $u$. -/)
  (proof := /-- Fix any input $u_0$ and read $f$ and $g$ off at it. -/)]
theorem IsAutonomous.exists_eq [Nonempty U] {s : DiscreteSystem E U Y} (hs : s.IsAutonomous) :
    ∃ (f : ℕ → E → E) (g : ℕ → E → Y), ∀ k x u, s.F k x u = f k x ∧ s.h k x u = g k x := by
  obtain ⟨u₀⟩ := ‹Nonempty U›
  exact ⟨fun k x => s.F k x u₀, fun k x => s.h k x u₀, fun k x u => hs k x u u₀⟩

/-! ### Semantics -/

/-- The right-hand side of the state equation under the input sequence `u`,
`(k, x) ↦ F(k, x, u(k))`: the next-state map at each time. -/
@[blueprint "def:discreteSystem-vectorField"
  (title := "State equation of a discrete-time system")
  (statement := /-- Under an input sequence $u : \mathbb{N} \to U$, the right-hand side of the
    state equation is the time-dependent next-state map $(k, x) \mapsto F(k, x, u(k))$.  The same
    expression as \cref{def:continuousSystem-vectorField}; what differs is what a trajectory does
    with it, a shift rather than a derivative. -/)]
def vectorField (s : DiscreteSystem E U Y) (u : ℕ → U) : ℕ → E → E :=
  fun k x => s.F k x (u k)

/-- The output equation under the input sequence `u`, `(k, x) ↦ h(k, x, u(k))`. -/
@[blueprint "def:discreteSystem-outputMap"
  (title := "Output equation of a discrete-time system")
  (statement := /-- Under an input sequence $u$, the output equation is
    $(k, x) \mapsto h(k, x, u(k))$. -/)]
def outputMap (s : DiscreteSystem E U Y) (u : ℕ → U) : ℕ → E → Y :=
  fun k x => s.h k x (u k)

@[simp] lemma vectorField_apply (s : DiscreteSystem E U Y) (u : ℕ → U) (k : ℕ) (x : E) :
    s.vectorField u k x = s.F k x (u k) := rfl

@[simp] lemma outputMap_apply (s : DiscreteSystem E U Y) (u : ℕ → U) (k : ℕ) (x : E) :
    s.outputMap u k x = s.h k x (u k) := rfl

/-- `x` is a trajectory of `s` under the input `u` on the set `I`:
`x(k+1) = F(k, x(k), u(k))` for every `k ∈ I`.

Membership constrains the step *out of* `k`, so `I = Set.Ici k₀` is the forward recursion from
`k₀`, and a trajectory over the horizon `[k₀, k₁]` is one on `Set.Ico k₀ k₁`. -/
@[blueprint "def:discreteSystem-isTrajectoryOn"
  (title := "Trajectory of a discrete-time system")
  (statement := /-- A sequence $x : \mathbb{N} \to E$ is a \emph{trajectory} of $s$ under the
    input $u$ on a set $I \subseteq \mathbb{N}$ when
    \[
      x(k+1) = F(k, x(k), u(k)), \qquad \forall\, k \in I.
    \]
    Membership constrains the step \emph{out of} $k$, so $I = [k_0, \infty)$ is the forward
    recursion from $k_0$, and the horizon $[k_0, k_1]$ corresponds to $I = [k_0, k_1)$. -/)]
def IsTrajectoryOn (s : DiscreteSystem E U Y) (u : ℕ → U) (x : ℕ → E) (I : Set ℕ) : Prop :=
  ∀ k ∈ I, x (k + 1) = s.vectorField u k (x k)

/-- `x` is a trajectory of `s` under the input `u` at every time. -/
@[blueprint "def:discreteSystem-isTrajectory"
  (title := "Trajectory for all time of a discrete-time system")
  (statement := /-- A trajectory (\cref{def:discreteSystem-isTrajectoryOn}) satisfying the
    recursion at every $k \in \mathbb{N}$. -/)]
def IsTrajectory (s : DiscreteSystem E U Y) (u : ℕ → U) (x : ℕ → E) : Prop :=
  ∀ k : ℕ, x (k + 1) = s.vectorField u k (x k)

@[blueprint "lem:discreteSystem-isTrajectoryOn-univ"
  (title := "Trajectories of a discrete-time system on the whole domain")
  (latexEnv := "lemma")
  (statement := /-- \cref{def:discreteSystem-isTrajectoryOn} at $I = \mathbb{N}$ is
    \cref{def:discreteSystem-isTrajectory}. -/)]
lemma isTrajectoryOn_univ {s : DiscreteSystem E U Y} {u : ℕ → U} {x : ℕ → E} :
    s.IsTrajectoryOn u x Set.univ ↔ s.IsTrajectory u x :=
  ⟨fun h k => h k (Set.mem_univ k), fun h k _ => h k⟩

@[blueprint "lem:discreteSystem-isTrajectory-isTrajectoryOn"
  (title := "Restriction of a trajectory of a discrete-time system")
  (latexEnv := "lemma")
  (statement := /-- A trajectory at every time is a trajectory on every set. -/)]
lemma IsTrajectory.isTrajectoryOn {s : DiscreteSystem E U Y} {u : ℕ → U} {x : ℕ → E}
    (h : s.IsTrajectory u x) (I : Set ℕ) : s.IsTrajectoryOn u x I :=
  fun k _ => h k

end DiscreteSystem

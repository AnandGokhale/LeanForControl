import Mathlib.Analysis.ODE.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Architect

/-!
# `LinearSystems.DefsSystem` — the linear system object

The `(A, B, C, D)` data of a linear system, and the equations that data satisfies.

* `LinearSystem T X U Y 𝕜` — the coefficients, as functions on a time domain `T`.
* `vectorField`, `outputMap` — the right-hand sides `A x + B u` and `C x + D u`, shared by
  both readings of the state equation.
* `IsTrajectoryOn`, `IsTrajectory` — the continuous-time reading, `ẋ = A x + B u`.
* `IsDiscreteTrajectory` — the discrete-time reading, `x(k+1) = A x + B u`.
* `const`, `IsTimeInvariant` — time-invariant systems are the constant systems of a given time
  domain, not a type of their own.

## Conventions

* States, inputs and outputs are indexed by abstract `Fintype`s rather than `Fin n`, so that
  the state space of an interconnection is `X₁ ⊕ X₂` definitionally.
* The structure carries no typeclasses: `Fintype`, `DecidableEq` and ring structure on `𝕜` go
  on the operations that need them.
* The namespace is `LinearSystem`, singular, matching the type. Dot notation resolves in the
  namespace named by the type, so this is required rather than stylistic.
-/

universe u

/-- A linear system: the coefficient data `(A, B, C, D)` of

* `ẋ(t) = A(t) x(t) + B(t) u(t)`, `y(t) = C(t) x(t) + D(t) u(t)` in continuous time, or
* `x(k+1) = A(k) x(k) + B(k) u(k)`, `y(k) = C(k) x(k) + D(k) u(k)` in discrete time,

with states indexed by `X`, inputs by `U`, outputs by `Y`, and coefficients in `𝕜`.

This is *data*, not dynamics. The two displays above are how the data gets read, and neither
reading is recorded here — that is the semantics layer's job, and until it says so there is no
sense in which this object is continuous-time or discrete-time. It is why the time domain `T`
is an arbitrary type, acquiring order, measure or derivative structure only where semantics
are attached.

Linear time-invariant systems are the constant systems of a given time domain (`const`,
`IsTimeInvariant`) rather than a type of their own, so that every theorem proved here applies
to them unchanged.

The structure requires no typeclasses — `Matrix X X 𝕜` is a function type. `Fintype`,
`DecidableEq` and any ring structure on `𝕜` belong on the individual operations that need
them, not on the object. -/
@[blueprint "def:linearSystem"
  (title := "Linear system")
  (statement := /-- A \emph{linear system} on a time domain $T$, with states indexed by $X$,
    inputs by $U$, outputs by $Y$ and coefficients in $\mathbb{K}$, is the data of four
    matrix-valued maps
    \[
      A : T \to \mathbb{K}^{X \times X}, \quad
      B : T \to \mathbb{K}^{X \times U}, \quad
      C : T \to \mathbb{K}^{Y \times X}, \quad
      D : T \to \mathbb{K}^{Y \times U}.
    \]
    This is data, not dynamics: the equations these coefficients satisfy are
    \cref{def:linearSystem-vectorField} and \cref{def:linearSystem-outputMap}, and which of
    the two readings of the state equation is meant --- $\dot x = Ax + Bu$
    (\cref{def:linearSystem-isTrajectoryOn}) or $x(k+1) = Ax + Bu$
    (\cref{def:linearSystem-isDiscreteTrajectory}) --- is not recorded in the data. -/)]
structure LinearSystem (T : Type u) (X U Y 𝕜 : Type*) where
  /-- State matrix. -/
  A : T → Matrix X X 𝕜
  /-- Input matrix. -/
  B : T → Matrix X U 𝕜
  /-- Output matrix. -/
  C : T → Matrix Y X 𝕜
  /-- Feedthrough matrix. -/
  D : T → Matrix Y U 𝕜

namespace LinearSystem

open Matrix

variable {T : Type u} {X U Y 𝕜 : Type*}

/-- The system with constant coefficients `A`, `B`, `C`, `D` — a linear time-invariant system,
read on the time domain `T`. -/
@[blueprint "def:linearSystem-const"
  (title := "Constant system")
  (statement := /-- The system whose coefficients $A$, $B$, $C$, $D$ do not depend on time.
    Linear time-invariant systems are the constant systems of a given time domain rather than
    a type of their own, so that every result about \cref{def:linearSystem} applies to them
    unchanged. -/)]
def const (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) : LinearSystem T X U Y 𝕜 where
  A := fun _ => A
  B := fun _ => B
  C := fun _ => C
  D := fun _ => D

@[simp] lemma const_A (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) (t : T) : (const A B C D : LinearSystem T X U Y 𝕜).A t = A := rfl

@[simp] lemma const_B (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) (t : T) : (const A B C D : LinearSystem T X U Y 𝕜).B t = B := rfl

@[simp] lemma const_C (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) (t : T) : (const A B C D : LinearSystem T X U Y 𝕜).C t = C := rfl

@[simp] lemma const_D (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) (t : T) : (const A B C D : LinearSystem T X U Y 𝕜).D t = D := rfl

/-- The system is *time-invariant*: every coefficient is constant in time. -/
@[blueprint "def:linearSystem-isTimeInvariant"
  (title := "Time invariance")
  (statement := /-- A system is \emph{time-invariant} when each of its four coefficients takes
    the same value at every pair of times. -/)]
def IsTimeInvariant (s : LinearSystem T X U Y 𝕜) : Prop :=
  ∀ t t' : T, s.A t = s.A t' ∧ s.B t = s.B t' ∧ s.C t = s.C t' ∧ s.D t = s.D t'

/-- A constant system is time-invariant. -/
@[blueprint "lem:linearSystem-isTimeInvariant-const"
  (title := "Constant systems are time-invariant")
  (latexEnv := "lemma")
  (statement := /-- A constant system (\cref{def:linearSystem-const}) is time-invariant
    (\cref{def:linearSystem-isTimeInvariant}). -/)]
theorem isTimeInvariant_const (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) : (const A B C D : LinearSystem T X U Y 𝕜).IsTimeInvariant :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- A time-invariant system is a constant system.

The converse of `isTimeInvariant_const`, and the reason `IsTimeInvariant` is stated as
constancy rather than as `∃ A B C D, s = const A B C D`: the predicate is checkable at a pair
of times, and this lemma recovers the existential once a time is available to read the
coefficients off at. -/
@[blueprint "lem:linearSystem-exists-eq-const"
  (title := "Time-invariant systems are constant")
  (latexEnv := "lemma")
  (statement := /-- A time-invariant system on a nonempty time domain is a constant system:
    there are $A$, $B$, $C$, $D$ with $s = \operatorname{const} A\,B\,C\,D$.  The converse of
    \cref{lem:linearSystem-isTimeInvariant-const}. -/)
  (proof := /-- Read the coefficients off at any time of the domain; time invariance says
    every other time agrees with it. -/)]
theorem exists_eq_const [Nonempty T] {s : LinearSystem T X U Y 𝕜} (h : s.IsTimeInvariant) :
    ∃ (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜) (D : Matrix Y U 𝕜),
      s = const A B C D := by
  obtain ⟨t₀⟩ := ‹Nonempty T›
  refine ⟨s.A t₀, s.B t₀, s.C t₀, s.D t₀, ?_⟩
  obtain ⟨sA, sB, sC, sD⟩ := s
  simp only [const, mk.injEq]
  refine ⟨funext fun t => ?_, funext fun t => ?_, funext fun t => ?_, funext fun t => ?_⟩
  exacts [(h t t₀).1, (h t t₀).2.1, (h t t₀).2.2.1, (h t t₀).2.2.2]

/-! ## What the coefficients mean

The state and output right-hand sides, and the two readings of the state equation. Together
with the structure above, these are the definition of the system: the structure supplies the
coefficients and these supply the equations. -/

section Semantics

variable [Fintype X] [Fintype U] [NonUnitalNonAssocSemiring 𝕜]

/-- The right-hand side of the state equation, `(t, z) ↦ A(t) z + B(t) u(t)`, as a
time-dependent vector field on the state space.

Shared by both readings: continuous time asks that `ẋ(t)` equal this, discrete time asks that
`x(k+1)` equal it. It is stated as a function of a state *value* `z` rather than of the
trajectory, because that is the shape the ODE machinery consumes. -/
@[blueprint "def:linearSystem-vectorField"
  (title := "State equation")
  (statement := /-- The right-hand side of the state equation, as a time-dependent vector
    field on the state space:
    \[
      (t, z) \mapsto A(t)\,z + B(t)\,u(t).
    \]
    Both readings of the state equation are built from this one map: continuous time asks that
    $\dot x(t)$ equal it, discrete time that $x(k+1)$ equal it.  It is a function of a state
    \emph{value} rather than of a trajectory, which is the shape the ODE machinery
    consumes. -/)]
def vectorField (s : LinearSystem T X U Y 𝕜) (u : T → U → 𝕜) : T → (X → 𝕜) → (X → 𝕜) :=
  fun t z => s.A t *ᵥ z + s.B t *ᵥ u t

/-- The output equation, `(t, z) ↦ C(t) z + D(t) u(t)`.

Unlike the state equation this is the same sentence in continuous and discrete time — it is
an instantaneous relation, with no derivative and no shift — so it is stated once, for an
arbitrary time domain. -/
@[blueprint "def:linearSystem-outputMap"
  (title := "Output equation")
  (statement := /-- The output equation,
    \[
      (t, z) \mapsto C(t)\,z + D(t)\,u(t).
    \]
    Unlike the state equation this is the same sentence in continuous and in discrete time ---
    an instantaneous relation, with no derivative and no shift --- so it is stated once, for an
    arbitrary time domain. -/)]
def outputMap (s : LinearSystem T X U Y 𝕜) (u : T → U → 𝕜) : T → (X → 𝕜) → (Y → 𝕜) :=
  fun t z => s.C t *ᵥ z + s.D t *ᵥ u t

@[simp] lemma vectorField_apply (s : LinearSystem T X U Y 𝕜) (u : T → U → 𝕜) (t : T)
    (z : X → 𝕜) : s.vectorField u t z = s.A t *ᵥ z + s.B t *ᵥ u t := rfl

@[simp] lemma outputMap_apply (s : LinearSystem T X U Y 𝕜) (u : T → U → 𝕜) (t : T)
    (z : X → 𝕜) : s.outputMap u t z = s.C t *ᵥ z + s.D t *ᵥ u t := rfl

end Semantics

section Continuous

variable [Fintype X] [Fintype U]

/-- **The continuous-time reading.** `x` is a trajectory of `s` under the input `u` on the set
`I` when

    ẋ(t) = A(t) x(t) + B(t) u(t)    for every `t ∈ I`.

Stated on a set rather than on all of `ℝ` for the same reason the nonlinear track does: a
function can satisfy the equation on an interval without being defined for all time, and a
definition should not presuppose otherwise. `IsTrajectory` below is the global case.

The accompanying output is `s.outputMap u t (x t)`; it is not part of this predicate, because
the output equation constrains nothing about `x`. -/
@[blueprint "def:linearSystem-isTrajectoryOn"
  (title := "Trajectory, continuous time")
  (statement := /-- The \emph{continuous-time reading} of the state equation.  A map $x$ is a
    trajectory of $s$ under the input $u$ on a set $I \subseteq \mathbb{R}$ when
    \[
      \dot x(t) = A(t)\,x(t) + B(t)\,u(t), \qquad \forall\, t \in I.
    \]
    Stated on a set rather than on all of $\mathbb{R}$: a map can satisfy the equation on an
    interval without being defined for all time, and the definition should not presuppose
    otherwise.  The accompanying output is \cref{def:linearSystem-outputMap} evaluated along
    $x$; it is not part of this predicate, because the output equation constrains nothing
    about $x$. -/)]
def IsTrajectoryOn (s : LinearSystem ℝ X U Y ℝ) (u : ℝ → U → ℝ) (x : ℝ → X → ℝ)
    (I : Set ℝ) : Prop :=
  IsIntegralCurveOn x (s.vectorField u) I

/-- `x` is a trajectory of `s` under the input `u` for all time. -/
@[blueprint "def:linearSystem-isTrajectory"
  (title := "Trajectory for all time")
  (statement := /-- A trajectory (\cref{def:linearSystem-isTrajectoryOn}) defined on all of
    $\mathbb{R}$. -/)]
def IsTrajectory (s : LinearSystem ℝ X U Y ℝ) (u : ℝ → U → ℝ) (x : ℝ → X → ℝ) : Prop :=
  IsIntegralCurve x (s.vectorField u)

@[blueprint "lem:linearSystem-isTrajectoryOn-univ"
  (title := "Trajectories on the whole line")
  (latexEnv := "lemma")
  (statement := /-- A trajectory on $\mathbb{R}$ itself is exactly a trajectory for all time:
    \cref{def:linearSystem-isTrajectoryOn} at $I = \mathbb{R}$ is
    \cref{def:linearSystem-isTrajectory}. -/)]
lemma isTrajectoryOn_univ {s : LinearSystem ℝ X U Y ℝ} {u : ℝ → U → ℝ} {x : ℝ → X → ℝ} :
    s.IsTrajectoryOn u x Set.univ ↔ s.IsTrajectory u x :=
  isIntegralCurveOn_univ

@[blueprint "lem:linearSystem-isTrajectory-isTrajectoryOn"
  (title := "Restriction of a trajectory")
  (latexEnv := "lemma")
  (statement := /-- A trajectory for all time (\cref{def:linearSystem-isTrajectory}) is a
    trajectory on every set. -/)]
lemma IsTrajectory.isTrajectoryOn {s : LinearSystem ℝ X U Y ℝ} {u : ℝ → U → ℝ}
    {x : ℝ → X → ℝ} (h : s.IsTrajectory u x) (I : Set ℝ) : s.IsTrajectoryOn u x I :=
  IsIntegralCurve.isIntegralCurveOn h I

end Continuous

section Discrete

variable [Fintype X] [Fintype U] [NonUnitalNonAssocSemiring 𝕜]

/-- **The discrete-time reading.** `x` is a trajectory of `s` under the input `u` when

    x(k+1) = A(k) x(k) + B(k) u(k)    for every `k`.

No set parameter here, unlike `IsTrajectoryOn`: the relation constrains a *pair* of times, so
restricting it to a set would raise the question of what happens at the boundary. Adding a
horizon is better done when something needs one.

The accompanying output is `s.outputMap u k (x k)`. -/
@[blueprint "def:linearSystem-isDiscreteTrajectory"
  (title := "Trajectory, discrete time")
  (statement := /-- The \emph{discrete-time reading} of the state equation.  A map $x$ is a
    trajectory of $s$ under the input $u$ when
    \[
      x(k+1) = A(k)\,x(k) + B(k)\,u(k), \qquad \forall\, k \in \mathbb{Z}.
    \]
    There is no set parameter here, unlike \cref{def:linearSystem-isTrajectoryOn}: the relation
    constrains a \emph{pair} of times, so restricting it to a set would raise the question of
    what happens at the boundary.  A horizon is better added when something needs one. -/)]
def IsDiscreteTrajectory (s : LinearSystem ℤ X U Y 𝕜) (u : ℤ → U → 𝕜) (x : ℤ → X → 𝕜) : Prop :=
  ∀ k : ℤ, x (k + 1) = s.vectorField u k (x k)

end Discrete

end LinearSystem

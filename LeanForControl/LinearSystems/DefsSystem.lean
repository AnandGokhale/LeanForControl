import Mathlib.Analysis.ODE.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Architect

/-!
# `LinearSystems.DefsSystem` — the linear system objects

The `(A, B, C, D)` data of a linear system, and the equations that data satisfies. There are
two objects, one per time domain:

* `ContinuousLinearSystem X U Y 𝕜` — coefficients on `ℝ`, read as `ẋ = A x + B u`.
* `DiscreteLinearSystem X U Y 𝕜` — coefficients on `ℕ`, read as `x(k+1) = A x + B u`.

Each carries the same API under the same names — `timeInvariant`, `IsTimeInvariant`, `vectorField`,
`outputMap`, `IsTrajectoryOn`, `IsTrajectory` — disambiguated by the type rather than by a
prefix.

## Why two objects rather than one parameterized by the time domain

A single record `LinearSystem T X U Y 𝕜` would share the memoryless algebra, but the two
readings of the state equation are not variants of one notion: a continuous trajectory is an
integral curve, a discrete one is a recursion. They differ in shape, in the scalar structure
they need, and in what a similarity transform does to them — `T⁻¹AT − T⁻¹Ṫ` against
`T(k+1)⁻¹A(k)T(k)`. Sharing a namespace would force one of the two to carry a `disc` prefix,
which is the tax `Solutions/` already pays (`discStateTransitionMatrix` and friends).

The price is that the memoryless operations are written twice. Today that is twelve one-line
declarations; the ones with real content that will also be duplicated are `dual`, `reindex`,
`directSum` and `wire`.

## Conventions

* States, inputs and outputs are indexed by abstract `Fintype`s rather than `Fin n`, so that
  the state space of an interconnection is `X₁ ⊕ X₂` definitionally.
* The structures carry no typeclasses: `Fintype`, `DecidableEq` and ring structure on `𝕜` go
  on the operations that need them.
* The namespace is `LinearSystems`, with each structure's API in a nested namespace named for
  it. Dot notation resolves in the namespace named by the type, so the nesting is required
  rather than stylistic.
-/

namespace LinearSystems

open Matrix

/-- A continuous-time linear system: the coefficient data `(A, B, C, D)` of

    ẋ(t) = A(t) x(t) + B(t) u(t),    y(t) = C(t) x(t) + D(t) u(t)

with states indexed by `X`, inputs by `U`, outputs by `Y`, and coefficients in `𝕜`.

The structure is the data; the equations above are `vectorField`, `outputMap` and
`IsTrajectoryOn`. It requires no typeclasses — `Matrix X X 𝕜` is a function type. -/
@[blueprint "def:ctsLinearSystem"
  (title := "Continuous-time linear system")
  (statement := /-- A \emph{continuous-time linear system} with states indexed by $X$, inputs
    by $U$, outputs by $Y$ and coefficients in $\mathbb{K}$ is the data of four matrix-valued
    maps on $\mathbb{R}$,
    \[
      A : \mathbb{R} \to \mathbb{K}^{X \times X}, \quad
      B : \mathbb{R} \to \mathbb{K}^{X \times U}, \quad
      C : \mathbb{R} \to \mathbb{K}^{Y \times X}, \quad
      D : \mathbb{R} \to \mathbb{K}^{Y \times U},
    \]
    to be read as $\dot x = A(t)x + B(t)u$, $y = C(t)x + D(t)u$.  The reading itself is
    \cref{def:ctsLinearSystem-vectorField}, \cref{def:ctsLinearSystem-outputMap} and
    \cref{def:ctsLinearSystem-isTrajectoryOn}; the structure is only the data. -/)]
structure ContinuousLinearSystem (X U Y 𝕜 : Type*) where
  /-- State matrix. -/
  A : ℝ → Matrix X X 𝕜
  /-- Input matrix. -/
  B : ℝ → Matrix X U 𝕜
  /-- Output matrix. -/
  C : ℝ → Matrix Y X 𝕜
  /-- Feedthrough matrix. -/
  D : ℝ → Matrix Y U 𝕜

/-- A discrete-time linear system: the coefficient data `(A, B, C, D)` of

    x(k+1) = A(k) x(k) + B(k) u(k),    y(k) = C(k) x(k) + D(k) u(k)

on the time domain `ℕ`, matching the convention of `Solutions/DiscLTV.lean`. -/
@[blueprint "def:discLinearSystem"
  (title := "Discrete-time linear system")
  (statement := /-- A \emph{discrete-time linear system} is the same data as
    \cref{def:ctsLinearSystem} with the coefficients indexed by $\mathbb{N}$ instead of
    $\mathbb{R}$, to be read as $x(k+1) = A(k)x(k) + B(k)u(k)$, $y(k) = C(k)x(k) + D(k)u(k)$.

    The forward time domain $\mathbb{N}$ rather than $\mathbb{Z}$ matches the discrete solution
    theory, whose state transition matrix is an ordered product over $[t_0, t)$. -/)]
structure DiscreteLinearSystem (X U Y 𝕜 : Type*) where
  /-- State matrix. -/
  A : ℕ → Matrix X X 𝕜
  /-- Input matrix. -/
  B : ℕ → Matrix X U 𝕜
  /-- Output matrix. -/
  C : ℕ → Matrix Y X 𝕜
  /-- Feedthrough matrix. -/
  D : ℕ → Matrix Y U 𝕜

namespace ContinuousLinearSystem

variable {X U Y 𝕜 : Type*}

/-- The linear time-invariant system with coefficients `A`, `B`, `C`, `D`, which do not
vary with time. -/
@[blueprint "def:ctsLinearSystem-timeInvariant"
  (title := "Time-invariant continuous-time system")
  (statement := /-- The continuous-time system whose coefficients do not depend on time.
    Linear time-invariant systems are the constant systems rather than a type of their own, so
    that every result about \cref{def:ctsLinearSystem} applies to them unchanged. -/)]
def timeInvariant (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) : ContinuousLinearSystem X U Y 𝕜 where
  A := fun _ => A
  B := fun _ => B
  C := fun _ => C
  D := fun _ => D

@[simp] lemma timeInvariant_A (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) (t : ℝ) : (timeInvariant A B C D).A t = A := rfl

@[simp] lemma timeInvariant_B (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) (t : ℝ) : (timeInvariant A B C D).B t = B := rfl

@[simp] lemma timeInvariant_C (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) (t : ℝ) : (timeInvariant A B C D).C t = C := rfl

@[simp] lemma timeInvariant_D (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) (t : ℝ) : (timeInvariant A B C D).D t = D := rfl

/-- The system is *time-invariant*: every coefficient is constant in time. -/
@[blueprint "def:ctsLinearSystem-isTimeInvariant"
  (title := "Time invariance, continuous time")
  (statement := /-- A continuous-time system is \emph{time-invariant} when each of its four
    coefficients takes the same value at every pair of times. -/)]
def IsTimeInvariant (s : ContinuousLinearSystem X U Y 𝕜) : Prop :=
  ∀ t t' : ℝ, s.A t = s.A t' ∧ s.B t = s.B t' ∧ s.C t = s.C t' ∧ s.D t = s.D t'

/-- A constant system is time-invariant. -/
@[blueprint "lem:ctsLinearSystem-isTimeInvariant-timeInvariant"
  (title := "Time-invariant continuous-time systems are time-invariant")
  (latexEnv := "lemma")
  (statement := /-- A constant system (\cref{def:ctsLinearSystem-timeInvariant}) is time-invariant
    (\cref{def:ctsLinearSystem-isTimeInvariant}). -/)]
theorem isTimeInvariant_timeInvariant (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) : (timeInvariant A B C D).IsTimeInvariant :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- A time-invariant system is a constant system. -/
@[blueprint "lem:ctsLinearSystem-exists-eq"
  (title := "Time-invariant systems come from constant coefficients")
  (latexEnv := "lemma")
  (statement := /-- A time-invariant continuous-time system is a constant system: there are
    $A$, $B$, $C$, $D$ with $s = \operatorname{const} A\,B\,C\,D$.  The converse of
    \cref{lem:ctsLinearSystem-isTimeInvariant-timeInvariant}. -/)
  (proof := /-- Read the coefficients off at $t = 0$; time invariance says every other time
    agrees with it. -/)]
theorem IsTimeInvariant.exists_eq {s : ContinuousLinearSystem X U Y 𝕜} (h : s.IsTimeInvariant) :
    ∃ (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜) (D : Matrix Y U 𝕜),
      s = timeInvariant A B C D := by
  refine ⟨s.A 0, s.B 0, s.C 0, s.D 0, ?_⟩
  obtain ⟨sA, sB, sC, sD⟩ := s
  simp only [timeInvariant, mk.injEq]
  refine ⟨funext fun t => ?_, funext fun t => ?_, funext fun t => ?_, funext fun t => ?_⟩
  exacts [(h t 0).1, (h t 0).2.1, (h t 0).2.2.1, (h t 0).2.2.2]

section Semantics

variable [Fintype X] [Fintype U] [NonUnitalNonAssocSemiring 𝕜]

/-- The right-hand side of the state equation, `(t, z) ↦ A(t) z + B(t) u(t)`. -/
@[blueprint "def:ctsLinearSystem-vectorField"
  (title := "State equation, continuous time")
  (statement := /-- The right-hand side of the state equation, as a time-dependent vector
    field on the state space:
    \[
      (t, z) \mapsto A(t)\,z + B(t)\,u(t).
    \]
    It is a function of a state \emph{value} rather than of a trajectory, which is the shape
    the ODE machinery consumes. -/)]
def vectorField (s : ContinuousLinearSystem X U Y 𝕜) (u : ℝ → U → 𝕜) :
    ℝ → (X → 𝕜) → (X → 𝕜) :=
  fun t z => s.A t *ᵥ z + s.B t *ᵥ u t

/-- The output equation, `(t, z) ↦ C(t) z + D(t) u(t)`. -/
@[blueprint "def:ctsLinearSystem-outputMap"
  (title := "Output equation, continuous time")
  (statement := /-- The output equation,
    $(t, z) \mapsto C(t)\,z + D(t)\,u(t)$.  An instantaneous relation: no derivative
    appears, which is why it is the same sentence here as in discrete time
    (\cref{def:discLinearSystem-outputMap}). -/)]
def outputMap (s : ContinuousLinearSystem X U Y 𝕜) (u : ℝ → U → 𝕜) :
    ℝ → (X → 𝕜) → (Y → 𝕜) :=
  fun t z => s.C t *ᵥ z + s.D t *ᵥ u t

@[simp] lemma vectorField_apply (s : ContinuousLinearSystem X U Y 𝕜) (u : ℝ → U → 𝕜) (t : ℝ)
    (z : X → 𝕜) : s.vectorField u t z = s.A t *ᵥ z + s.B t *ᵥ u t := rfl

@[simp] lemma outputMap_apply (s : ContinuousLinearSystem X U Y 𝕜) (u : ℝ → U → 𝕜) (t : ℝ)
    (z : X → 𝕜) : s.outputMap u t z = s.C t *ᵥ z + s.D t *ᵥ u t := rfl

/-- With the input switched off the state equation is `ẋ = A(t) x`: the input term vanishes.

This is what lets a statement about the unforced system be written on the system object rather
than on its state matrix alone. -/
@[simp, blueprint "lem:ctsLinearSystem-vectorField-zero-input"
  (title := "The unforced state equation")
  (latexEnv := "lemma")
  (statement := /-- At zero input the state equation (\cref{def:ctsLinearSystem-vectorField})
    reduces to $(t, z) \mapsto A(t)\,z$. -/)]
lemma vectorField_zero_input (s : ContinuousLinearSystem X U Y 𝕜) :
    s.vectorField (0 : ℝ → U → 𝕜) = fun t z => s.A t *ᵥ z := by
  funext t z; simp [vectorField]

/-- At the origin the state equation contributes only the input term. In particular the origin
is an equilibrium of the unforced system: `s.vectorField 0 t 0 = 0`. -/
@[blueprint "lem:ctsLinearSystem-vectorField-apply-zero"
  (title := "The state equation at the origin")
  (latexEnv := "lemma")
  (statement := /-- At $z = 0$ the state equation
    (\cref{def:ctsLinearSystem-vectorField}) contributes only the input term,
    $A(t)\,0 + B(t)u(t) = B(t)u(t)$.  With the input switched off the origin is
    therefore an equilibrium of the system. -/)]
lemma vectorField_apply_zero (s : ContinuousLinearSystem X U Y 𝕜) (u : ℝ → U → 𝕜) (t : ℝ) :
    s.vectorField u t 0 = s.B t *ᵥ u t := by
  simp [vectorField]

end Semantics

section Trajectory

variable [Fintype X] [Fintype U]

/-- `x` is a trajectory of `s` under the input `u` on the set `I`:

    ẋ(t) = A(t) x(t) + B(t) u(t)    for every `t ∈ I`.

Stated on a set rather than on all of `ℝ`, because a map can satisfy the equation on an
interval without being defined for all time. The accompanying output is `s.outputMap u t (x t)`;
it is not part of this predicate, because the output equation constrains nothing about `x`. -/
@[blueprint "def:ctsLinearSystem-isTrajectoryOn"
  (title := "Trajectory, continuous time")
  (statement := /-- A map $x$ is a \emph{trajectory} of $s$ under the input $u$ on a set
    $I \subseteq \mathbb{R}$ when
    \[
      \dot x(t) = A(t)\,x(t) + B(t)\,u(t), \qquad \forall\, t \in I.
    \]
    Stated on a set rather than on all of $\mathbb{R}$: a map can satisfy the equation on an
    interval without being defined for all time, and the definition should not presuppose
    otherwise. -/)]
def IsTrajectoryOn (s : ContinuousLinearSystem X U Y ℝ) (u : ℝ → U → ℝ) (x : ℝ → X → ℝ)
    (I : Set ℝ) : Prop :=
  IsIntegralCurveOn x (s.vectorField u) I

/-- `x` is a trajectory of `s` under the input `u` for all time. -/
@[blueprint "def:ctsLinearSystem-isTrajectory"
  (title := "Trajectory for all time, continuous time")
  (statement := /-- A trajectory (\cref{def:ctsLinearSystem-isTrajectoryOn}) defined on all of
    $\mathbb{R}$. -/)]
def IsTrajectory (s : ContinuousLinearSystem X U Y ℝ) (u : ℝ → U → ℝ) (x : ℝ → X → ℝ) : Prop :=
  IsIntegralCurve x (s.vectorField u)

@[blueprint "lem:ctsLinearSystem-isTrajectoryOn-univ"
  (title := "Trajectories on the whole line")
  (latexEnv := "lemma")
  (statement := /-- \cref{def:ctsLinearSystem-isTrajectoryOn} at $I = \mathbb{R}$ is
    \cref{def:ctsLinearSystem-isTrajectory}. -/)]
lemma isTrajectoryOn_univ {s : ContinuousLinearSystem X U Y ℝ} {u : ℝ → U → ℝ}
    {x : ℝ → X → ℝ} : s.IsTrajectoryOn u x Set.univ ↔ s.IsTrajectory u x :=
  isIntegralCurveOn_univ

@[blueprint "lem:ctsLinearSystem-isTrajectory-isTrajectoryOn"
  (title := "Restriction of a trajectory")
  (latexEnv := "lemma")
  (statement := /-- A trajectory for all time is a trajectory on every set. -/)]
lemma IsTrajectory.isTrajectoryOn {s : ContinuousLinearSystem X U Y ℝ} {u : ℝ → U → ℝ}
    {x : ℝ → X → ℝ} (h : s.IsTrajectory u x) (I : Set ℝ) : s.IsTrajectoryOn u x I :=
  IsIntegralCurve.isIntegralCurveOn h I

end Trajectory

end ContinuousLinearSystem

namespace DiscreteLinearSystem

variable {X U Y 𝕜 : Type*}

/-- The linear time-invariant system with coefficients `A`, `B`, `C`, `D`, which do not
vary with time. -/
@[blueprint "def:discLinearSystem-timeInvariant"
  (title := "Time-invariant discrete-time system")
  (statement := /-- The discrete-time system whose coefficients do not depend on time. -/)]
def timeInvariant (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) : DiscreteLinearSystem X U Y 𝕜 where
  A := fun _ => A
  B := fun _ => B
  C := fun _ => C
  D := fun _ => D

@[simp] lemma timeInvariant_A (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) (k : ℕ) : (timeInvariant A B C D).A k = A := rfl

@[simp] lemma timeInvariant_B (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) (k : ℕ) : (timeInvariant A B C D).B k = B := rfl

@[simp] lemma timeInvariant_C (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) (k : ℕ) : (timeInvariant A B C D).C k = C := rfl

@[simp] lemma timeInvariant_D (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) (k : ℕ) : (timeInvariant A B C D).D k = D := rfl

/-- The system is *time-invariant*: every coefficient is constant in time. -/
@[blueprint "def:discLinearSystem-isTimeInvariant"
  (title := "Time invariance, discrete time")
  (statement := /-- A discrete-time system is \emph{time-invariant} when each of its four
    coefficients takes the same value at every pair of times. -/)]
def IsTimeInvariant (s : DiscreteLinearSystem X U Y 𝕜) : Prop :=
  ∀ k k' : ℕ, s.A k = s.A k' ∧ s.B k = s.B k' ∧ s.C k = s.C k' ∧ s.D k = s.D k'

/-- A constant system is time-invariant. -/
@[blueprint "lem:discLinearSystem-isTimeInvariant-timeInvariant"
  (title := "Time-invariant discrete-time systems are time-invariant")
  (latexEnv := "lemma")
  (statement := /-- A constant system (\cref{def:discLinearSystem-timeInvariant}) is time-invariant
    (\cref{def:discLinearSystem-isTimeInvariant}). -/)]
theorem isTimeInvariant_timeInvariant (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜)
    (D : Matrix Y U 𝕜) : (timeInvariant A B C D).IsTimeInvariant :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- A time-invariant system is a constant system. -/
@[blueprint "lem:discLinearSystem-exists-eq"
  (title := "Time-invariant systems come from constant coefficients")
  (latexEnv := "lemma")
  (statement := /-- A time-invariant discrete-time system is a constant system.  The converse
    of \cref{lem:discLinearSystem-isTimeInvariant-timeInvariant}. -/)
  (proof := /-- Read the coefficients off at $k = 0$. -/)]
theorem IsTimeInvariant.exists_eq {s : DiscreteLinearSystem X U Y 𝕜} (h : s.IsTimeInvariant) :
    ∃ (A : Matrix X X 𝕜) (B : Matrix X U 𝕜) (C : Matrix Y X 𝕜) (D : Matrix Y U 𝕜),
      s = timeInvariant A B C D := by
  refine ⟨s.A 0, s.B 0, s.C 0, s.D 0, ?_⟩
  obtain ⟨sA, sB, sC, sD⟩ := s
  simp only [timeInvariant, mk.injEq]
  refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩
  exacts [(h k 0).1, (h k 0).2.1, (h k 0).2.2.1, (h k 0).2.2.2]

section Semantics

variable [Fintype X] [Fintype U] [NonUnitalNonAssocSemiring 𝕜]

/-- The right-hand side of the state equation, `(k, z) ↦ A(k) z + B(k) u(k)`. -/
@[blueprint "def:discLinearSystem-vectorField"
  (title := "State equation, discrete time")
  (statement := /-- The right-hand side of the state equation,
    $(k, z) \mapsto A(k)\,z + B(k)\,u(k)$.  The same expression as
    \cref{def:ctsLinearSystem-vectorField}; what differs is what the trajectory is asked to do
    with it --- here a shift rather than a derivative. -/)]
def vectorField (s : DiscreteLinearSystem X U Y 𝕜) (u : ℕ → U → 𝕜) :
    ℕ → (X → 𝕜) → (X → 𝕜) :=
  fun k z => s.A k *ᵥ z + s.B k *ᵥ u k

/-- The output equation, `(k, z) ↦ C(k) z + D(k) u(k)`. -/
@[blueprint "def:discLinearSystem-outputMap"
  (title := "Output equation, discrete time")
  (statement := /-- The output equation,
    $(k, z) \mapsto C(k)\,z + D(k)\,u(k)$. -/)]
def outputMap (s : DiscreteLinearSystem X U Y 𝕜) (u : ℕ → U → 𝕜) :
    ℕ → (X → 𝕜) → (Y → 𝕜) :=
  fun k z => s.C k *ᵥ z + s.D k *ᵥ u k

@[simp] lemma vectorField_apply (s : DiscreteLinearSystem X U Y 𝕜) (u : ℕ → U → 𝕜) (k : ℕ)
    (z : X → 𝕜) : s.vectorField u k z = s.A k *ᵥ z + s.B k *ᵥ u k := rfl

@[simp] lemma outputMap_apply (s : DiscreteLinearSystem X U Y 𝕜) (u : ℕ → U → 𝕜) (k : ℕ)
    (z : X → 𝕜) : s.outputMap u k z = s.C k *ᵥ z + s.D k *ᵥ u k := rfl

/-- With the input switched off the state equation is `x(k+1) = A(k) x(k)`. -/
@[simp, blueprint "lem:discLinearSystem-vectorField-zero-input"
  (title := "The unforced state equation, discrete time")
  (latexEnv := "lemma")
  (statement := /-- At zero input the state equation (\cref{def:discLinearSystem-vectorField})
    reduces to $(k, z) \mapsto A(k)\,z$. -/)]
lemma vectorField_zero_input (s : DiscreteLinearSystem X U Y 𝕜) :
    s.vectorField (0 : ℕ → U → 𝕜) = fun k z => s.A k *ᵥ z := by
  funext k z; simp [vectorField]

/-- At the origin the state equation contributes only the input term. In particular the origin
is an equilibrium of the unforced system: `s.vectorField 0 k 0 = 0`. -/
@[blueprint "lem:discLinearSystem-vectorField-apply-zero"
  (title := "The state equation at the origin")
  (latexEnv := "lemma")
  (statement := /-- At $z = 0$ the state equation
    (\cref{def:discLinearSystem-vectorField}) contributes only the input term,
    $A(k)\,0 + B(k)u(k) = B(k)u(k)$.  With the input switched off the origin is
    therefore an equilibrium of the system. -/)]
lemma vectorField_apply_zero (s : DiscreteLinearSystem X U Y 𝕜) (u : ℕ → U → 𝕜) (k : ℕ) :
    s.vectorField u k 0 = s.B k *ᵥ u k := by
  simp [vectorField]

/-- `x` is a trajectory of `s` under the input `u` on the set `I`:

    x(k+1) = A(k) x(k) + B(k) u(k)    for every `k ∈ I`.

A trajectory here is a *sequence* satisfying a recursion, not an integral curve — which is why
this is a separate object from `ContinuousLinearSystem` rather than the same one at a different
time domain. Membership constrains the step *out of* `k`, so `I = Set.Ici t₀` is the forward
recursion from `t₀`. -/
@[blueprint "def:discLinearSystem-isTrajectoryOn"
  (title := "Trajectory, discrete time")
  (statement := /-- A sequence $x$ is a \emph{trajectory} of $s$ under the input $u$ on a set
    $I \subseteq \mathbb{N}$ when
    \[
      x(k+1) = A(k)\,x(k) + B(k)\,u(k), \qquad \forall\, k \in I.
    \]
    Membership constrains the step \emph{out of} $k$, so $I = [t_0, \infty)$ is the forward
    recursion from $t_0$.  A discrete trajectory is a sequence satisfying a recursion, not an
    integral curve (\cref{def:ctsLinearSystem-isTrajectoryOn}); the two notions share a shape
    only superficially. -/)]
def IsTrajectoryOn (s : DiscreteLinearSystem X U Y 𝕜) (u : ℕ → U → 𝕜) (x : ℕ → X → 𝕜)
    (I : Set ℕ) : Prop :=
  ∀ k ∈ I, x (k + 1) = s.vectorField u k (x k)

/-- `x` is a trajectory of `s` under the input `u` at every time. -/
@[blueprint "def:discLinearSystem-isTrajectory"
  (title := "Trajectory for all time, discrete time")
  (statement := /-- A trajectory (\cref{def:discLinearSystem-isTrajectoryOn}) satisfying the
    recursion at every $k \in \mathbb{N}$. -/)]
def IsTrajectory (s : DiscreteLinearSystem X U Y 𝕜) (u : ℕ → U → 𝕜) (x : ℕ → X → 𝕜) : Prop :=
  ∀ k : ℕ, x (k + 1) = s.vectorField u k (x k)

@[blueprint "lem:discLinearSystem-isTrajectoryOn-univ"
  (title := "Discrete trajectories on the whole domain")
  (latexEnv := "lemma")
  (statement := /-- \cref{def:discLinearSystem-isTrajectoryOn} at $I = \mathbb{N}$ is
    \cref{def:discLinearSystem-isTrajectory}. -/)]
lemma isTrajectoryOn_univ {s : DiscreteLinearSystem X U Y 𝕜} {u : ℕ → U → 𝕜} {x : ℕ → X → 𝕜} :
    s.IsTrajectoryOn u x Set.univ ↔ s.IsTrajectory u x :=
  ⟨fun h k => h k (Set.mem_univ k), fun h k _ => h k⟩

@[blueprint "lem:discLinearSystem-isTrajectory-isTrajectoryOn"
  (title := "Restriction of a discrete trajectory")
  (latexEnv := "lemma")
  (statement := /-- A trajectory at every time is a trajectory on every set. -/)]
lemma IsTrajectory.isTrajectoryOn {s : DiscreteLinearSystem X U Y 𝕜} {u : ℕ → U → 𝕜}
    {x : ℕ → X → 𝕜} (h : s.IsTrajectory u x) (I : Set ℕ) : s.IsTrajectoryOn u x I :=
  fun k _ => h k

end Semantics

end DiscreteLinearSystem

end LinearSystems

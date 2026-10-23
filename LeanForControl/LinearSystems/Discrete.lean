import LeanForControl.Systems.Discrete
import Mathlib.Data.Matrix.Mul
import Architect

/-!
# `LinearSystems.Discrete` — discrete-time linear systems

The discrete-time counterpart of `LinearSystems.Continuous`: linear systems as a special case of
the general discrete-time system `DiscreteSystem` of `Systems.Discrete`, with state equation
`x(k+1) = A(k) x(k) + B(k) u(k)` and output equation `y(k) = C(k) x(k) + D(k) u(k)`.

* `DiscreteLTV X U Y 𝕜` — time-varying coefficients `A(k)`, `B(k)`, `C(k)`, `D(k)`;
* `DiscreteLTI X U Y 𝕜` — constant coefficients `A`, `B`, `C`, `D`.

As in continuous time, each is constructor data: `DiscreteLTV.toDiscreteSystem` builds the general
system, `DiscreteLTI.toLTV` the time-varying one, and the semantics are defined through
`toDiscreteSystem`.  The time domain is `ℕ`, matching the discrete solution theory, whose state
transition matrix is an ordered product over `[t₀, t)`.  Trajectories need no derivative, so they
are stated over any `𝕜`.
-/

namespace LinearSystems

open Matrix

/-! ## Linear time-varying systems -/

/-- A discrete-time linear time-varying system: the coefficient data `(A, B, C, D)` of

    x(k+1) = A(k) x(k) + B(k) u(k),    y(k) = C(k) x(k) + D(k) u(k)

on the time domain `ℕ`.  The structure is only the data; the system it describes is
`toDiscreteSystem`. -/
@[blueprint "def:discreteLTV"
  (title := "Discrete-time linear time-varying system")
  (statement := /-- A \emph{discrete-time linear time-varying (LTV) system} is the same data as
    \cref{def:continuousLTV} with the coefficients indexed by $\mathbb{N}$ instead of
    $\mathbb{R}$, describing the discrete-time system (\cref{def:discreteSystem})
    $x(k+1) = A(k)x(k) + B(k)u(k)$, $y(k) = C(k)x(k) + D(k)u(k)$
    (\cref{def:discreteLTV-toDiscreteSystem}).

    The forward time domain $\mathbb{N}$ rather than $\mathbb{Z}$ matches the discrete solution
    theory, whose state transition matrix is an ordered product over $[t_0, t)$. -/)]
structure DiscreteLTV (X U Y 𝕜 : Type*) where
  /-- State matrix. -/
  A : ℕ → Matrix X X 𝕜
  /-- Input matrix. -/
  B : ℕ → Matrix X U 𝕜
  /-- Output matrix. -/
  C : ℕ → Matrix Y X 𝕜
  /-- Feedthrough matrix. -/
  D : ℕ → Matrix Y U 𝕜

namespace DiscreteLTV

variable {X U Y 𝕜 : Type*}

/-- The system is *time-invariant*: every coefficient is constant in time. -/
@[blueprint "def:discreteLTV-isTimeInvariant"
  (title := "Time invariance of a discrete-time LTV system")
  (statement := /-- A discrete-time LTV system is \emph{time-invariant} when each of its four
    coefficients takes the same value at every pair of times. -/)]
def IsTimeInvariant (s : DiscreteLTV X U Y 𝕜) : Prop :=
  ∀ k k' : ℕ, s.A k = s.A k' ∧ s.B k = s.B k' ∧ s.C k = s.C k' ∧ s.D k = s.D k'

section Semantics

variable [Fintype X] [Fintype U] [NonUnitalNonAssocSemiring 𝕜]

/-- The general system a discrete-time LTV system describes:
`x⁺ = A(k) x + B(k) u`, `y = C(k) x + D(k) u`. -/
@[blueprint "def:discreteLTV-toDiscreteSystem"
  (title := "The system of a discrete-time LTV system")
  (statement := /-- The discrete-time system (\cref{def:discreteSystem}) with
    $F(k, x, u) = A(k)x + B(k)u$ and $h(k, x, u) = C(k)x + D(k)u$. -/)]
def toDiscreteSystem (s : DiscreteLTV X U Y 𝕜) : DiscreteSystem (X → 𝕜) (U → 𝕜) (Y → 𝕜) where
  F k x v := s.A k *ᵥ x + s.B k *ᵥ v
  h k x v := s.C k *ᵥ x + s.D k *ᵥ v

@[simp] lemma toDiscreteSystem_F (s : DiscreteLTV X U Y 𝕜) (k : ℕ) (x : X → 𝕜) (v : U → 𝕜) :
    s.toDiscreteSystem.F k x v = s.A k *ᵥ x + s.B k *ᵥ v := rfl

@[simp] lemma toDiscreteSystem_h (s : DiscreteLTV X U Y 𝕜) (k : ℕ) (x : X → 𝕜) (v : U → 𝕜) :
    s.toDiscreteSystem.h k x v = s.C k *ᵥ x + s.D k *ᵥ v := rfl

/-- The right-hand side of the state equation, `(k, z) ↦ A(k) z + B(k) u(k)`: the next-state
map of `toDiscreteSystem` under the input `u`. -/
@[blueprint "def:discreteLTV-vectorField"
  (title := "State equation of a discrete-time LTV system")
  (statement := /-- The right-hand side of the state equation,
    $(k, z) \mapsto A(k)\,z + B(k)\,u(k)$: the next-state map
    (\cref{def:discreteSystem-vectorField}) of \cref{def:discreteLTV-toDiscreteSystem}. -/)]
abbrev vectorField (s : DiscreteLTV X U Y 𝕜) (u : ℕ → U → 𝕜) : ℕ → (X → 𝕜) → (X → 𝕜) :=
  s.toDiscreteSystem.vectorField u

/-- The output equation, `(k, z) ↦ C(k) z + D(k) u(k)`. -/
@[blueprint "def:discreteLTV-outputMap"
  (title := "Output equation of a discrete-time LTV system")
  (statement := /-- The output equation, $(k, z) \mapsto C(k)\,z + D(k)\,u(k)$: the output map
    (\cref{def:discreteSystem-outputMap}) of \cref{def:discreteLTV-toDiscreteSystem}. -/)]
abbrev outputMap (s : DiscreteLTV X U Y 𝕜) (u : ℕ → U → 𝕜) : ℕ → (X → 𝕜) → (Y → 𝕜) :=
  s.toDiscreteSystem.outputMap u

@[simp] lemma vectorField_apply (s : DiscreteLTV X U Y 𝕜) (u : ℕ → U → 𝕜) (k : ℕ)
    (z : X → 𝕜) : s.vectorField u k z = s.A k *ᵥ z + s.B k *ᵥ u k := rfl

@[simp] lemma outputMap_apply (s : DiscreteLTV X U Y 𝕜) (u : ℕ → U → 𝕜) (k : ℕ)
    (z : X → 𝕜) : s.outputMap u k z = s.C k *ᵥ z + s.D k *ᵥ u k := rfl

/-- With the input switched off the state equation is `x(k+1) = A(k) x(k)`. -/
@[simp, blueprint "lem:discreteLTV-vectorField-zero-input"
  (title := "The unforced state equation of a discrete-time LTV system")
  (latexEnv := "lemma")
  (statement := /-- At zero input the state equation (\cref{def:discreteLTV-vectorField})
    reduces to $(k, z) \mapsto A(k)\,z$. -/)]
lemma vectorField_zero_input (s : DiscreteLTV X U Y 𝕜) :
    s.vectorField (0 : ℕ → U → 𝕜) = fun k z => s.A k *ᵥ z := by
  funext k z; simp

/-- At the origin the state equation contributes only the input term. In particular the origin
is an equilibrium of the unforced system: `s.vectorField 0 k 0 = 0`. -/
@[blueprint "lem:discreteLTV-vectorField-apply-zero"
  (title := "The state equation of a discrete-time LTV system at the origin")
  (latexEnv := "lemma")
  (statement := /-- At $z = 0$ the state equation (\cref{def:discreteLTV-vectorField})
    contributes only the input term, $A(k)\,0 + B(k)u(k) = B(k)u(k)$.  With the input switched
    off the origin is therefore an equilibrium of the system. -/)]
lemma vectorField_apply_zero (s : DiscreteLTV X U Y 𝕜) (u : ℕ → U → 𝕜) (k : ℕ) :
    s.vectorField u k 0 = s.B k *ᵥ u k := by
  simp

/-- A time-invariant LTV system describes a time-invariant system. -/
@[blueprint "lem:discreteLTV-isTimeInvariant-toDiscreteSystem"
  (title := "Time-invariant discrete-time LTV systems are time-invariant systems")
  (latexEnv := "lemma")
  (statement := /-- If a discrete-time LTV system is time-invariant
    (\cref{def:discreteLTV-isTimeInvariant}), so is the system it describes
    (\cref{def:discreteSystem-isTimeInvariant}). -/)]
lemma IsTimeInvariant.toDiscreteSystem {s : DiscreteLTV X U Y 𝕜} (hs : s.IsTimeInvariant) :
    s.toDiscreteSystem.IsTimeInvariant := fun k k' => by
  obtain ⟨hA, hB, hC, hD⟩ := hs k k'
  refine ⟨funext fun x => funext fun v => ?_, funext fun x => funext fun v => ?_⟩
  · simp [hA, hB]
  · simp [hC, hD]

/-- `x` is a trajectory of `s` under the input `u` on the set `I`: a trajectory
(`DiscreteSystem.IsTrajectoryOn`) of the system `s` describes,
`x(k+1) = A(k) x(k) + B(k) u(k)` for every `k ∈ I`. -/
@[blueprint "def:discreteLTV-isTrajectoryOn"
  (title := "Trajectory of a discrete-time LTV system")
  (statement := /-- A sequence $x$ is a \emph{trajectory} of $s$ under the input $u$ on a set
    $I \subseteq \mathbb{N}$ when it is a trajectory (\cref{def:discreteSystem-isTrajectoryOn})
    of \cref{def:discreteLTV-toDiscreteSystem}:
    \[
      x(k+1) = A(k)\,x(k) + B(k)\,u(k), \qquad \forall\, k \in I.
    \] -/)]
abbrev IsTrajectoryOn (s : DiscreteLTV X U Y 𝕜) (u : ℕ → U → 𝕜) (x : ℕ → X → 𝕜)
    (I : Set ℕ) : Prop :=
  s.toDiscreteSystem.IsTrajectoryOn u x I

/-- `x` is a trajectory of `s` under the input `u` at every time. -/
@[blueprint "def:discreteLTV-isTrajectory"
  (title := "Trajectory for all time of a discrete-time LTV system")
  (statement := /-- A trajectory (\cref{def:discreteSystem-isTrajectory}) for all time of
    \cref{def:discreteLTV-toDiscreteSystem}. -/)]
abbrev IsTrajectory (s : DiscreteLTV X U Y 𝕜) (u : ℕ → U → 𝕜) (x : ℕ → X → 𝕜) : Prop :=
  s.toDiscreteSystem.IsTrajectory u x

end Semantics

end DiscreteLTV

/-! ## Linear time-invariant systems -/

/-- A discrete-time linear time-invariant system: the constant coefficient data `(A, B, C, D)` of

    x(k+1) = A x(k) + B u(k),    y(k) = C x(k) + D u(k). -/
@[blueprint "def:discreteLTI"
  (title := "Discrete-time linear time-invariant system")
  (statement := /-- A \emph{discrete-time linear time-invariant (LTI) system} is the data of four
    matrices $A$, $B$, $C$, $D$, describing the discrete-time LTV system
    (\cref{def:discreteLTV}) with these constant coefficients, $x(k+1) = Ax(k) + Bu(k)$,
    $y(k) = Cx(k) + Du(k)$. -/)]
structure DiscreteLTI (X U Y 𝕜 : Type*) where
  /-- State matrix. -/
  A : Matrix X X 𝕜
  /-- Input matrix. -/
  B : Matrix X U 𝕜
  /-- Output matrix. -/
  C : Matrix Y X 𝕜
  /-- Feedthrough matrix. -/
  D : Matrix Y U 𝕜

namespace DiscreteLTI

variable {X U Y 𝕜 : Type*}

/-- The discrete-time LTV system with the constant coefficients of an LTI system. -/
@[blueprint "def:discreteLTI-toLTV"
  (title := "The LTV system of a discrete-time LTI system")
  (statement := /-- The discrete-time LTV system (\cref{def:discreteLTV}) whose coefficients are
    the constant maps $k \mapsto A$, $k \mapsto B$, $k \mapsto C$, $k \mapsto D$. -/)]
def toLTV (sys : DiscreteLTI X U Y 𝕜) : DiscreteLTV X U Y 𝕜 where
  A := fun _ => sys.A
  B := fun _ => sys.B
  C := fun _ => sys.C
  D := fun _ => sys.D

@[simp] lemma toLTV_A (sys : DiscreteLTI X U Y 𝕜) (k : ℕ) : sys.toLTV.A k = sys.A := rfl
@[simp] lemma toLTV_B (sys : DiscreteLTI X U Y 𝕜) (k : ℕ) : sys.toLTV.B k = sys.B := rfl
@[simp] lemma toLTV_C (sys : DiscreteLTI X U Y 𝕜) (k : ℕ) : sys.toLTV.C k = sys.C := rfl
@[simp] lemma toLTV_D (sys : DiscreteLTI X U Y 𝕜) (k : ℕ) : sys.toLTV.D k = sys.D := rfl

/-- The LTV system of an LTI system is time-invariant. -/
@[blueprint "lem:discreteLTI-isTimeInvariant-toLTV"
  (title := "Discrete-time LTI systems are time-invariant LTV systems")
  (latexEnv := "lemma")
  (statement := /-- The LTV system of a discrete-time LTI system
    (\cref{def:discreteLTI-toLTV}) is time-invariant (\cref{def:discreteLTV-isTimeInvariant}). -/)]
theorem isTimeInvariant_toLTV (sys : DiscreteLTI X U Y 𝕜) : sys.toLTV.IsTimeInvariant :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- A time-invariant discrete-time LTV system is the LTV system of an LTI system. -/
@[blueprint "lem:discreteLTV-isTimeInvariant-exists-eq"
  (title := "Time-invariant discrete-time LTV systems come from LTI systems")
  (latexEnv := "lemma")
  (statement := /-- A time-invariant discrete-time LTV system
    (\cref{def:discreteLTV-isTimeInvariant}) is the LTV system of some LTI system.  The converse
    of \cref{lem:discreteLTI-isTimeInvariant-toLTV}. -/)
  (proof := /-- Read the coefficients off at $k = 0$. -/)]
theorem _root_.LinearSystems.DiscreteLTV.IsTimeInvariant.exists_eq
    {s : DiscreteLTV X U Y 𝕜} (h : s.IsTimeInvariant) :
    ∃ sys : DiscreteLTI X U Y 𝕜, s = sys.toLTV := by
  refine ⟨⟨s.A 0, s.B 0, s.C 0, s.D 0⟩, ?_⟩
  obtain ⟨sA, sB, sC, sD⟩ := s
  simp only [toLTV, DiscreteLTV.mk.injEq]
  refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩
  exacts [(h k 0).1, (h k 0).2.1, (h k 0).2.2.1, (h k 0).2.2.2]

section Semantics

variable [Fintype X] [Fintype U] [NonUnitalNonAssocSemiring 𝕜]

/-- The general system a discrete-time LTI system describes: `x⁺ = A x + B u`, `y = C x + D u`. -/
@[blueprint "def:discreteLTI-toDiscreteSystem"
  (title := "The system of a discrete-time LTI system")
  (statement := /-- The discrete-time system (\cref{def:discreteSystem}) of the LTV system of
    $s$ (\cref{def:discreteLTV-toDiscreteSystem}, \cref{def:discreteLTI-toLTV}). -/)]
abbrev toDiscreteSystem (sys : DiscreteLTI X U Y 𝕜) : DiscreteSystem (X → 𝕜) (U → 𝕜) (Y → 𝕜) :=
  sys.toLTV.toDiscreteSystem

/-- **LTI is linear and time-invariant.**  The system of a discrete-time LTI system is the
time-invariant system with next-state map `A x + B u` and output map `C x + D u`. -/
@[blueprint "lem:discreteLTI-toDiscreteSystem-eq-timeInvariant"
  (title := "A discrete-time LTI system is a linear time-invariant system")
  (latexEnv := "lemma")
  (statement := /-- The system of a discrete-time LTI system
    (\cref{def:discreteLTI-toDiscreteSystem}) is the time-invariant system
    (\cref{def:discreteSystem-timeInvariant}) with $f(x, u) = Ax + Bu$ and $g(x, u) = Cx + Du$:
    the two routes from the LTI data to a general system agree. -/)]
theorem toDiscreteSystem_eq_timeInvariant (sys : DiscreteLTI X U Y 𝕜) :
    sys.toDiscreteSystem = DiscreteSystem.timeInvariant (fun x v => sys.A *ᵥ x + sys.B *ᵥ v)
      (fun x v => sys.C *ᵥ x + sys.D *ᵥ v) :=
  rfl

/-- The right-hand side of the state equation, `(k, z) ↦ A z + B u(k)`. -/
abbrev vectorField (sys : DiscreteLTI X U Y 𝕜) (u : ℕ → U → 𝕜) : ℕ → (X → 𝕜) → (X → 𝕜) :=
  sys.toLTV.vectorField u

/-- The output equation, `(k, z) ↦ C z + D u(k)`. -/
abbrev outputMap (sys : DiscreteLTI X U Y 𝕜) (u : ℕ → U → 𝕜) : ℕ → (X → 𝕜) → (Y → 𝕜) :=
  sys.toLTV.outputMap u

/-- `x` is a trajectory of the LTI system `sys` under the input `u` on the set `I`. -/
abbrev IsTrajectoryOn (sys : DiscreteLTI X U Y 𝕜) (u : ℕ → U → 𝕜) (x : ℕ → X → 𝕜)
    (I : Set ℕ) : Prop :=
  sys.toLTV.IsTrajectoryOn u x I

/-- `x` is a trajectory of the LTI system `sys` under the input `u` at every time. -/
abbrev IsTrajectory (sys : DiscreteLTI X U Y 𝕜) (u : ℕ → U → 𝕜) (x : ℕ → X → 𝕜) : Prop :=
  sys.toLTV.IsTrajectory u x

end Semantics

end DiscreteLTI

end LinearSystems

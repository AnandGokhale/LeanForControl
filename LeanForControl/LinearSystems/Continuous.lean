import LeanForControl.Systems.Continuous
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Architect

/-!
# `LinearSystems.Continuous` — continuous-time linear systems

Linear systems are a special case of the general continuous-time system `ContinuousSystem` of
`Systems.Continuous`: the system whose state equation is `ẋ = A(t) x + B(t) u` and whose output
equation is `y = C(t) x + D(t) u`.  Two objects carry the coefficient data:

* `ContinuousLTV E U Y` — time-varying operator coefficients `A(t)`, `B(t)`, `C(t)`, `D(t)`;
* `ContinuousLTI X U Y 𝕜` — constant matrix coefficients `A`, `B`, `C`, `D`.

Each is the data of a constructor rather than a separate notion of system:
`ContinuousLTV.toContinuousSystem` builds the general system, and `ContinuousLTI.toLTV` builds the
time-varying one with constant coefficients.  The semantics — `vectorField`, `outputMap`,
`IsTrajectoryOn`, `IsCaratheodoryTrajectoryOn` — are *defined through* `toContinuousSystem`, so
every result about general systems applies to linear ones unchanged.  The two routes from an LTI
system to the general object agree definitionally with `ContinuousSystem.timeInvariant`
(`ContinuousLTI.toContinuousSystem_eq_timeInvariant`).

The discrete-time counterparts are in `LinearSystems.Discrete`.  The design of the general objects
— separate continuous- and discrete-time objects, special cases as constructors with matching
predicates — is explained in `Systems.Continuous`.

## Conventions

* An LTV system has states, inputs and outputs in real normed spaces and continuous linear maps
  as coefficients; an inner product enters only where a theorem needs one (Lyapunov).
* An LTI system keeps matrix coefficients, indexed by abstract `Fintype`s rather than `Fin n`
  (the spectral theory is about matrices); its LTV system reads them as operators on Euclidean
  space.
-/

namespace LinearSystems

open Matrix

/-! ## Linear time-varying systems -/

/-- A continuous-time linear time-varying system: the coefficient data `(A, B, C, D)` of

    ẋ(t) = A(t) x(t) + B(t) u(t),    y(t) = C(t) x(t) + D(t) u(t)

with states in a normed space `E`, inputs in `U` and outputs in `Y`; the coefficients are
continuous linear maps.

The structure is only the data; the system it describes is `toContinuousSystem`. -/
@[blueprint "def:continuousLTV"
  (title := "Continuous-time linear time-varying system")
  (statement := /-- A \emph{continuous-time linear time-varying (LTV) system} with state space
    $E$, input space $U$ and output space $Y$ (real normed spaces) is the data of four maps on
    $\mathbb{R}$ into continuous linear maps,
    \[
      A : \mathbb{R} \to (E \to_L E), \quad
      B : \mathbb{R} \to (U \to_L E), \quad
      C : \mathbb{R} \to (E \to_L Y), \quad
      D : \mathbb{R} \to (U \to_L Y),
    \]
    describing the continuous-time system (\cref{def:continuousSystem})
    $\dot x = A(t)x + B(t)u$, $y = C(t)x + D(t)u$
    (\cref{def:continuousLTV-toContinuousSystem}). -/)]
structure ContinuousLTV (E U Y : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Y] [NormedSpace ℝ Y] where
  /-- State operator. -/
  A : ℝ → E →L[ℝ] E
  /-- Input operator. -/
  B : ℝ → U →L[ℝ] E
  /-- Output operator. -/
  C : ℝ → E →L[ℝ] Y
  /-- Feedthrough operator. -/
  D : ℝ → U →L[ℝ] Y

namespace ContinuousLTV

variable {E U Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup U]
  [NormedSpace ℝ U] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The system is *time-invariant*: every coefficient is constant in time. -/
@[blueprint "def:continuousLTV-isTimeInvariant"
  (title := "Time invariance of an LTV system")
  (statement := /-- A continuous-time LTV system is \emph{time-invariant} when each of its
    four coefficients takes the same value at every pair of times. -/)]
def IsTimeInvariant (s : ContinuousLTV E U Y) : Prop :=
  ∀ t t' : ℝ, s.A t = s.A t' ∧ s.B t = s.B t' ∧ s.C t = s.C t' ∧ s.D t = s.D t'

section Semantics

/-- The general system an LTV system describes: `ẋ = A(t) x + B(t) u`, `y = C(t) x + D(t) u`. -/
@[blueprint "def:continuousLTV-toContinuousSystem"
  (title := "The system of an LTV system")
  (statement := /-- The continuous-time system (\cref{def:continuousSystem}) on $E$, $U$, $Y$
    with $F(t, x, u) = A(t)x + B(t)u$ and $h(t, x, u) = C(t)x + D(t)u$. -/)]
def toContinuousSystem (s : ContinuousLTV E U Y) : ContinuousSystem E U Y where
  F t x v := s.A t x + s.B t v
  h t x v := s.C t x + s.D t v

@[simp] lemma toContinuousSystem_F (s : ContinuousLTV E U Y) (t : ℝ) (x : E) (v : U) :
    s.toContinuousSystem.F t x v = s.A t x + s.B t v := rfl

@[simp] lemma toContinuousSystem_h (s : ContinuousLTV E U Y) (t : ℝ) (x : E) (v : U) :
    s.toContinuousSystem.h t x v = s.C t x + s.D t v := rfl

/-- The right-hand side of the state equation, `(t, z) ↦ A(t) z + B(t) u(t)`: the vector field
of `toContinuousSystem` under the input `u`. -/
@[blueprint "def:continuousLTV-vectorField"
  (title := "State equation of an LTV system")
  (statement := /-- The right-hand side of the state equation,
    $(t, z) \mapsto A(t)\,z + B(t)\,u(t)$: the vector field
    (\cref{def:continuousSystem-vectorField}) of \cref{def:continuousLTV-toContinuousSystem}. -/)]
abbrev vectorField (s : ContinuousLTV E U Y) (u : ℝ → U) : ℝ → E → E :=
  s.toContinuousSystem.vectorField u

/-- The output equation, `(t, z) ↦ C(t) z + D(t) u(t)`: the output map of `toContinuousSystem`
under the input `u`. -/
@[blueprint "def:continuousLTV-outputMap"
  (title := "Output equation of an LTV system")
  (statement := /-- The output equation, $(t, z) \mapsto C(t)\,z + D(t)\,u(t)$: the output map
    (\cref{def:continuousSystem-outputMap}) of \cref{def:continuousLTV-toContinuousSystem}. -/)]
abbrev outputMap (s : ContinuousLTV E U Y) (u : ℝ → U) : ℝ → E → Y :=
  s.toContinuousSystem.outputMap u

@[simp] lemma vectorField_apply (s : ContinuousLTV E U Y) (u : ℝ → U) (t : ℝ) (z : E) :
    s.vectorField u t z = s.A t z + s.B t (u t) := rfl

@[simp] lemma outputMap_apply (s : ContinuousLTV E U Y) (u : ℝ → U) (t : ℝ) (z : E) :
    s.outputMap u t z = s.C t z + s.D t (u t) := rfl

/-- With the input switched off the state equation is `ẋ = A(t) x`: the input term vanishes. -/
@[simp, blueprint "lem:continuousLTV-vectorField-zero-input"
  (title := "The unforced state equation of an LTV system")
  (latexEnv := "lemma")
  (statement := /-- At zero input the state equation (\cref{def:continuousLTV-vectorField})
    reduces to $(t, z) \mapsto A(t)\,z$. -/)]
lemma vectorField_zero_input (s : ContinuousLTV E U Y) :
    s.vectorField (0 : ℝ → U) = fun t z => s.A t z := by
  funext t z; simp

/-- At the origin the state equation contributes only the input term. In particular the origin
is an equilibrium of the unforced system: `s.vectorField 0 t 0 = 0`. -/
@[blueprint "lem:continuousLTV-vectorField-apply-zero"
  (title := "The state equation of an LTV system at the origin")
  (latexEnv := "lemma")
  (statement := /-- At $z = 0$ the state equation (\cref{def:continuousLTV-vectorField})
    contributes only the input term, $A(t)\,0 + B(t)u(t) = B(t)u(t)$.  With the input switched
    off the origin is therefore an equilibrium of the system. -/)]
lemma vectorField_apply_zero (s : ContinuousLTV E U Y) (u : ℝ → U) (t : ℝ) :
    s.vectorField u t 0 = s.B t (u t) := by
  simp

/-- A time-invariant LTV system describes a time-invariant system. -/
@[blueprint "lem:continuousLTV-isTimeInvariant-toContinuousSystem"
  (title := "Time-invariant LTV systems are time-invariant systems")
  (latexEnv := "lemma")
  (statement := /-- If an LTV system is time-invariant (\cref{def:continuousLTV-isTimeInvariant}),
    so is the system it describes (\cref{def:continuousSystem-isTimeInvariant}). -/)]
lemma IsTimeInvariant.toContinuousSystem {s : ContinuousLTV E U Y} (hs : s.IsTimeInvariant) :
    s.toContinuousSystem.IsTimeInvariant := fun t t' => by
  obtain ⟨hA, hB, hC, hD⟩ := hs t t'
  refine ⟨funext fun x => funext fun v => ?_, funext fun x => funext fun v => ?_⟩
  · simp [hA, hB]
  · simp [hC, hD]

end Semantics

section Trajectory

/-- `x` is a trajectory of `s` under the input `u` on the set `I`: a trajectory
(`ContinuousSystem.IsTrajectoryOn`) of the system `s` describes,
`ẋ(t) = A(t) x(t) + B(t) u(t)` for every `t ∈ I`. -/
@[blueprint "def:continuousLTV-isTrajectoryOn"
  (title := "Trajectory of an LTV system")
  (statement := /-- A map $x$ is a \emph{trajectory} of $s$ under the input $u$ on a set
    $I \subseteq \mathbb{R}$ when it is a trajectory (\cref{def:continuousSystem-isTrajectoryOn})
    of \cref{def:continuousLTV-toContinuousSystem}:
    \[
      \dot x(t) = A(t)\,x(t) + B(t)\,u(t), \qquad \forall\, t \in I.
    \] -/)]
abbrev IsTrajectoryOn (s : ContinuousLTV E U Y) (u : ℝ → U) (x : ℝ → E) (I : Set ℝ) : Prop :=
  s.toContinuousSystem.IsTrajectoryOn u x I

/-- `x` is a trajectory of `s` under the input `u` for all time. -/
@[blueprint "def:continuousLTV-isTrajectory"
  (title := "Trajectory for all time of an LTV system")
  (statement := /-- A trajectory (\cref{def:continuousSystem-isTrajectory}) for all time of
    \cref{def:continuousLTV-toContinuousSystem}. -/)]
abbrev IsTrajectory (s : ContinuousLTV E U Y) (u : ℝ → U) (x : ℝ → E) : Prop :=
  s.toContinuousSystem.IsTrajectory u x

/-- An LTV trajectory is an integral curve of the LTV vector field, by definition. -/
lemma isTrajectoryOn_iff {s : ContinuousLTV E U Y} {u : ℝ → U} {x : ℝ → E} {I : Set ℝ} :
    s.IsTrajectoryOn u x I ↔ IsIntegralCurveOn x (s.vectorField u) I :=
  Iff.rfl

/-- An LTV trajectory for all time is an integral curve of the LTV vector field, by
definition. -/
lemma isTrajectory_iff {s : ContinuousLTV E U Y} {u : ℝ → U} {x : ℝ → E} :
    s.IsTrajectory u x ↔ IsIntegralCurve x (s.vectorField u) :=
  Iff.rfl

/-- `x` is a Carathéodory trajectory of `s` under the input `u` on the set `I`: the integral
form, which admits discontinuous inputs. -/
@[blueprint "def:continuousLTV-isCaratheodoryTrajectoryOn"
  (title := "Carathéodory trajectory of an LTV system")
  (statement := /-- A Carathéodory trajectory
    (\cref{def:continuousSystem-isCaratheodoryTrajectoryOn}) of
    \cref{def:continuousLTV-toContinuousSystem}. -/)]
abbrev IsCaratheodoryTrajectoryOn (s : ContinuousLTV E U Y) (u : ℝ → U) (x : ℝ → E)
    (I : Set ℝ) : Prop :=
  s.toContinuousSystem.IsCaratheodoryTrajectoryOn u x I

end Trajectory

end ContinuousLTV

/-! ## Linear time-invariant systems -/

/-- A continuous-time linear time-invariant system: the constant coefficient data `(A, B, C, D)`
of

    ẋ(t) = A x(t) + B u(t),    y(t) = C x(t) + D u(t).

The structure is only the data; the time-varying system it describes is `toLTV`, and the general
system `toContinuousSystem`. -/
@[blueprint "def:continuousLTI"
  (title := "Continuous-time linear time-invariant system")
  (statement := /-- A \emph{continuous-time linear time-invariant (LTI) system} is the data of
    four matrices $A \in \mathbb{K}^{X \times X}$, $B \in \mathbb{K}^{X \times U}$,
    $C \in \mathbb{K}^{Y \times X}$, $D \in \mathbb{K}^{Y \times U}$, describing the LTV system
    (\cref{def:continuousLTV}) with these constant coefficients, $\dot x = Ax + Bu$,
    $y = Cx + Du$. -/)]
structure ContinuousLTI (X U Y 𝕜 : Type*) where
  /-- State matrix. -/
  A : Matrix X X 𝕜
  /-- Input matrix. -/
  B : Matrix X U 𝕜
  /-- Output matrix. -/
  C : Matrix Y X 𝕜
  /-- Feedthrough matrix. -/
  D : Matrix Y U 𝕜

namespace ContinuousLTI

variable {X U Y 𝕜 : Type*}

section Semantics

variable [Fintype X] [Fintype U] [Fintype Y] [DecidableEq X] [DecidableEq U]

/-- The LTV system with the constant coefficients of a real LTI system, the matrices read as
operators on Euclidean spaces. -/
@[blueprint "def:continuousLTI-toLTV"
  (title := "The LTV system of an LTI system")
  (statement := /-- The LTV system (\cref{def:continuousLTV}) on $\mathbb{R}^X$, $\mathbb{R}^U$,
    $\mathbb{R}^Y$ whose coefficients are the constant maps $t \mapsto A$, $t \mapsto B$,
    $t \mapsto C$, $t \mapsto D$, the matrices acting on Euclidean vectors. -/)]
noncomputable def toLTV (sys : ContinuousLTI X U Y ℝ) :
    ContinuousLTV (EuclideanSpace ℝ X) (EuclideanSpace ℝ U) (EuclideanSpace ℝ Y) where
  A := fun _ => toEuclideanCLM (n := X) (𝕜 := ℝ) sys.A
  B := fun _ => LinearMap.toContinuousLinearMap (toEuclideanLin sys.B)
  C := fun _ => LinearMap.toContinuousLinearMap (toEuclideanLin sys.C)
  D := fun _ => LinearMap.toContinuousLinearMap (toEuclideanLin sys.D)

@[simp] lemma toLTV_A (sys : ContinuousLTI X U Y ℝ) (t : ℝ) :
    sys.toLTV.A t = toEuclideanCLM (n := X) (𝕜 := ℝ) sys.A := rfl

/-- The LTV system of an LTI system is time-invariant. -/
@[blueprint "lem:continuousLTI-isTimeInvariant-toLTV"
  (title := "LTI systems are time-invariant LTV systems")
  (latexEnv := "lemma")
  (statement := /-- The LTV system of an LTI system (\cref{def:continuousLTI-toLTV}) is
    time-invariant (\cref{def:continuousLTV-isTimeInvariant}). -/)]
theorem isTimeInvariant_toLTV (sys : ContinuousLTI X U Y ℝ) : sys.toLTV.IsTimeInvariant :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- The general system a real LTI system describes: `ẋ = A x + B u`, `y = C x + D u`, on
Euclidean spaces. -/
@[blueprint "def:continuousLTI-toContinuousSystem"
  (title := "The system of an LTI system")
  (statement := /-- The continuous-time system (\cref{def:continuousSystem}) of the LTV system
    of $s$ (\cref{def:continuousLTV-toContinuousSystem}, \cref{def:continuousLTI-toLTV}). -/)]
noncomputable abbrev toContinuousSystem (sys : ContinuousLTI X U Y ℝ) :
    ContinuousSystem (EuclideanSpace ℝ X) (EuclideanSpace ℝ U) (EuclideanSpace ℝ Y) :=
  sys.toLTV.toContinuousSystem

/-- **LTI is linear and time-invariant.**  The system of an LTI system, reached through its LTV
system, is the time-invariant system with state equation `A x + B u` and output equation
`C x + D u`. -/
@[blueprint "lem:continuousLTI-toContinuousSystem-eq-timeInvariant"
  (title := "An LTI system is a linear time-invariant system")
  (latexEnv := "lemma")
  (statement := /-- The system of an LTI system (\cref{def:continuousLTI-toContinuousSystem}) is
    the time-invariant system (\cref{def:continuousSystem-timeInvariant}) with
    $f(x, u) = Ax + Bu$ and $g(x, u) = Cx + Du$: the two routes from the LTI data to a general
    system agree. -/)]
theorem toContinuousSystem_eq_timeInvariant (sys : ContinuousLTI X U Y ℝ) :
    sys.toContinuousSystem = ContinuousSystem.timeInvariant
      (fun x v => toEuclideanLin sys.A x + toEuclideanLin sys.B v)
      (fun x v => toEuclideanLin sys.C x + toEuclideanLin sys.D v) :=
  rfl

/-- The right-hand side of the state equation, `(t, z) ↦ A z + B u(t)`. -/
noncomputable abbrev vectorField (sys : ContinuousLTI X U Y ℝ) (u : ℝ → EuclideanSpace ℝ U) :
    ℝ → EuclideanSpace ℝ X → EuclideanSpace ℝ X :=
  sys.toLTV.vectorField u

/-- The output equation, `(t, z) ↦ C z + D u(t)`. -/
noncomputable abbrev outputMap (sys : ContinuousLTI X U Y ℝ) (u : ℝ → EuclideanSpace ℝ U) :
    ℝ → EuclideanSpace ℝ X → EuclideanSpace ℝ Y :=
  sys.toLTV.outputMap u

end Semantics

section Trajectory

variable [Fintype X] [Fintype U] [Fintype Y] [DecidableEq X] [DecidableEq U]

/-- `x` is a trajectory of the LTI system `sys` under the input `u` on the set `I`. -/
abbrev IsTrajectoryOn (sys : ContinuousLTI X U Y ℝ) (u : ℝ → EuclideanSpace ℝ U)
    (x : ℝ → EuclideanSpace ℝ X) (I : Set ℝ) : Prop :=
  sys.toLTV.IsTrajectoryOn u x I

/-- `x` is a trajectory of the LTI system `sys` under the input `u` for all time. -/
abbrev IsTrajectory (sys : ContinuousLTI X U Y ℝ) (u : ℝ → EuclideanSpace ℝ U)
    (x : ℝ → EuclideanSpace ℝ X) : Prop :=
  sys.toLTV.IsTrajectory u x

end Trajectory

end ContinuousLTI

end LinearSystems

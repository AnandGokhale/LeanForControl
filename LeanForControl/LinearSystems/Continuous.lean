import LeanForControl.Systems.Continuous
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Architect

/-!
# `LinearSystems.Continuous` — continuous-time linear systems

Linear systems are a special case of the general continuous-time system `ContinuousSystem` of
`Systems.Continuous`: the system whose state equation is `ẋ = A(t) x + B(t) u` and whose output
equation is `y = C(t) x + D(t) u`.  Two objects carry the coefficient data:

* `ContinuousLTV X U Y 𝕜` — time-varying coefficients `A(t)`, `B(t)`, `C(t)`, `D(t)`;
* `ContinuousLTI X U Y 𝕜` — constant coefficients `A`, `B`, `C`, `D`.

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

* States, inputs and outputs are indexed by abstract `Fintype`s rather than `Fin n`, so that
  the state space of an interconnection is `X₁ ⊕ X₂` definitionally.
* The structures carry no typeclasses: `Fintype`, `DecidableEq` and ring structure on `𝕜` go
  on the operations that need them.
* Trajectories are real: they need the derivative, so they are stated for `𝕜 = ℝ`.
-/

namespace LinearSystems

open Matrix

/-! ## Linear time-varying systems -/

/-- A continuous-time linear time-varying system: the coefficient data `(A, B, C, D)` of

    ẋ(t) = A(t) x(t) + B(t) u(t),    y(t) = C(t) x(t) + D(t) u(t)

with states indexed by `X`, inputs by `U`, outputs by `Y`, and coefficients in `𝕜`.

The structure is only the data; the system it describes is `toContinuousSystem`. -/
@[blueprint "def:continuousLTV"
  (title := "Continuous-time linear time-varying system")
  (statement := /-- A \emph{continuous-time linear time-varying (LTV) system} with states
    indexed by $X$, inputs by $U$, outputs by $Y$ and coefficients in $\mathbb{K}$ is the data
    of four matrix-valued maps on $\mathbb{R}$,
    \[
      A : \mathbb{R} \to \mathbb{K}^{X \times X}, \quad
      B : \mathbb{R} \to \mathbb{K}^{X \times U}, \quad
      C : \mathbb{R} \to \mathbb{K}^{Y \times X}, \quad
      D : \mathbb{R} \to \mathbb{K}^{Y \times U},
    \]
    describing the continuous-time system (\cref{def:continuousSystem})
    $\dot x = A(t)x + B(t)u$, $y = C(t)x + D(t)u$
    (\cref{def:continuousLTV-toContinuousSystem}). -/)]
structure ContinuousLTV (X U Y 𝕜 : Type*) where
  /-- State matrix. -/
  A : ℝ → Matrix X X 𝕜
  /-- Input matrix. -/
  B : ℝ → Matrix X U 𝕜
  /-- Output matrix. -/
  C : ℝ → Matrix Y X 𝕜
  /-- Feedthrough matrix. -/
  D : ℝ → Matrix Y U 𝕜

namespace ContinuousLTV

variable {X U Y 𝕜 : Type*}

/-- The system is *time-invariant*: every coefficient is constant in time. -/
@[blueprint "def:continuousLTV-isTimeInvariant"
  (title := "Time invariance of an LTV system")
  (statement := /-- A continuous-time LTV system is \emph{time-invariant} when each of its
    four coefficients takes the same value at every pair of times. -/)]
def IsTimeInvariant (s : ContinuousLTV X U Y 𝕜) : Prop :=
  ∀ t t' : ℝ, s.A t = s.A t' ∧ s.B t = s.B t' ∧ s.C t = s.C t' ∧ s.D t = s.D t'

section Semantics

variable [Fintype X] [Fintype U] [DecidableEq X] [DecidableEq U]

/-- The general system a real LTV system describes: `ẋ = A(t) x + B(t) u`, `y = C(t) x + D(t) u`,
on Euclidean state, input and output spaces.  The matrices act through their Euclidean linear
maps (`Matrix.toEuclideanLin`), so the matrix norm that matches the state norm is the `L²`
operator norm. -/
@[blueprint "def:continuousLTV-toContinuousSystem"
  (title := "The system of an LTV system")
  (statement := /-- The continuous-time system (\cref{def:continuousSystem}) on the Euclidean
    spaces $\mathbb{R}^X$, $\mathbb{R}^U$, $\mathbb{R}^Y$ with $F(t, x, u) = A(t)x + B(t)u$ and
    $h(t, x, u) = C(t)x + D(t)u$. -/)]
noncomputable def toContinuousSystem (s : ContinuousLTV X U Y ℝ) :
    ContinuousSystem (EuclideanSpace ℝ X) (EuclideanSpace ℝ U) (EuclideanSpace ℝ Y) where
  F t x v := toEuclideanLin (s.A t) x + toEuclideanLin (s.B t) v
  h t x v := toEuclideanLin (s.C t) x + toEuclideanLin (s.D t) v

@[simp] lemma toContinuousSystem_F (s : ContinuousLTV X U Y ℝ) (t : ℝ) (x : EuclideanSpace ℝ X)
    (v : EuclideanSpace ℝ U) :
    s.toContinuousSystem.F t x v = toEuclideanLin (s.A t) x + toEuclideanLin (s.B t) v := rfl

@[simp] lemma toContinuousSystem_h (s : ContinuousLTV X U Y ℝ) (t : ℝ) (x : EuclideanSpace ℝ X)
    (v : EuclideanSpace ℝ U) :
    s.toContinuousSystem.h t x v = toEuclideanLin (s.C t) x + toEuclideanLin (s.D t) v := rfl

/-- The right-hand side of the state equation, `(t, z) ↦ A(t) z + B(t) u(t)`: the vector field
of `toContinuousSystem` under the input `u`. -/
@[blueprint "def:continuousLTV-vectorField"
  (title := "State equation of an LTV system")
  (statement := /-- The right-hand side of the state equation,
    $(t, z) \mapsto A(t)\,z + B(t)\,u(t)$: the vector field
    (\cref{def:continuousSystem-vectorField}) of \cref{def:continuousLTV-toContinuousSystem}. -/)]
noncomputable abbrev vectorField (s : ContinuousLTV X U Y ℝ) (u : ℝ → EuclideanSpace ℝ U) :
    ℝ → EuclideanSpace ℝ X → EuclideanSpace ℝ X :=
  s.toContinuousSystem.vectorField u

/-- The output equation, `(t, z) ↦ C(t) z + D(t) u(t)`: the output map of `toContinuousSystem`
under the input `u`. -/
@[blueprint "def:continuousLTV-outputMap"
  (title := "Output equation of an LTV system")
  (statement := /-- The output equation, $(t, z) \mapsto C(t)\,z + D(t)\,u(t)$: the output map
    (\cref{def:continuousSystem-outputMap}) of \cref{def:continuousLTV-toContinuousSystem}. -/)]
noncomputable abbrev outputMap (s : ContinuousLTV X U Y ℝ) (u : ℝ → EuclideanSpace ℝ U) :
    ℝ → EuclideanSpace ℝ X → EuclideanSpace ℝ Y :=
  s.toContinuousSystem.outputMap u

@[simp] lemma vectorField_apply (s : ContinuousLTV X U Y ℝ) (u : ℝ → EuclideanSpace ℝ U) (t : ℝ)
    (z : EuclideanSpace ℝ X) :
    s.vectorField u t z = toEuclideanLin (s.A t) z + toEuclideanLin (s.B t) (u t) := rfl

@[simp] lemma outputMap_apply (s : ContinuousLTV X U Y ℝ) (u : ℝ → EuclideanSpace ℝ U) (t : ℝ)
    (z : EuclideanSpace ℝ X) :
    s.outputMap u t z = toEuclideanLin (s.C t) z + toEuclideanLin (s.D t) (u t) := rfl

/-- With the input switched off the state equation is `ẋ = A(t) x`: the input term vanishes. -/
@[simp, blueprint "lem:continuousLTV-vectorField-zero-input"
  (title := "The unforced state equation of an LTV system")
  (latexEnv := "lemma")
  (statement := /-- At zero input the state equation (\cref{def:continuousLTV-vectorField})
    reduces to $(t, z) \mapsto A(t)\,z$. -/)]
lemma vectorField_zero_input (s : ContinuousLTV X U Y ℝ) :
    s.vectorField (0 : ℝ → EuclideanSpace ℝ U) = fun t z => toEuclideanLin (s.A t) z := by
  funext t z; simp

/-- At the origin the state equation contributes only the input term. In particular the origin
is an equilibrium of the unforced system: `s.vectorField 0 t 0 = 0`. -/
@[blueprint "lem:continuousLTV-vectorField-apply-zero"
  (title := "The state equation of an LTV system at the origin")
  (latexEnv := "lemma")
  (statement := /-- At $z = 0$ the state equation (\cref{def:continuousLTV-vectorField})
    contributes only the input term, $A(t)\,0 + B(t)u(t) = B(t)u(t)$.  With the input switched
    off the origin is therefore an equilibrium of the system. -/)]
lemma vectorField_apply_zero (s : ContinuousLTV X U Y ℝ) (u : ℝ → EuclideanSpace ℝ U) (t : ℝ) :
    s.vectorField u t 0 = toEuclideanLin (s.B t) (u t) := by
  simp

/-- A time-invariant LTV system describes a time-invariant system. -/
@[blueprint "lem:continuousLTV-isTimeInvariant-toContinuousSystem"
  (title := "Time-invariant LTV systems are time-invariant systems")
  (latexEnv := "lemma")
  (statement := /-- If an LTV system is time-invariant (\cref{def:continuousLTV-isTimeInvariant}),
    so is the system it describes (\cref{def:continuousSystem-isTimeInvariant}). -/)]
lemma IsTimeInvariant.toContinuousSystem {s : ContinuousLTV X U Y ℝ} (hs : s.IsTimeInvariant) :
    s.toContinuousSystem.IsTimeInvariant := fun t t' => by
  obtain ⟨hA, hB, hC, hD⟩ := hs t t'
  refine ⟨funext fun x => funext fun v => ?_, funext fun x => funext fun v => ?_⟩
  · simp [hA, hB]
  · simp [hC, hD]

end Semantics

section Trajectory

variable [Fintype X] [Fintype U] [DecidableEq X] [DecidableEq U]

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
abbrev IsTrajectoryOn (s : ContinuousLTV X U Y ℝ) (u : ℝ → EuclideanSpace ℝ U)
    (x : ℝ → EuclideanSpace ℝ X) (I : Set ℝ) : Prop :=
  s.toContinuousSystem.IsTrajectoryOn u x I

/-- `x` is a trajectory of `s` under the input `u` for all time. -/
@[blueprint "def:continuousLTV-isTrajectory"
  (title := "Trajectory for all time of an LTV system")
  (statement := /-- A trajectory (\cref{def:continuousSystem-isTrajectory}) for all time of
    \cref{def:continuousLTV-toContinuousSystem}. -/)]
abbrev IsTrajectory (s : ContinuousLTV X U Y ℝ) (u : ℝ → EuclideanSpace ℝ U)
    (x : ℝ → EuclideanSpace ℝ X) : Prop :=
  s.toContinuousSystem.IsTrajectory u x

/-- An LTV trajectory is an integral curve of the LTV vector field, by definition. -/
lemma isTrajectoryOn_iff {s : ContinuousLTV X U Y ℝ} {u : ℝ → EuclideanSpace ℝ U}
    {x : ℝ → EuclideanSpace ℝ X} {I : Set ℝ} :
    s.IsTrajectoryOn u x I ↔ IsIntegralCurveOn x (s.vectorField u) I :=
  Iff.rfl

/-- An LTV trajectory for all time is an integral curve of the LTV vector field, by
definition. -/
lemma isTrajectory_iff {s : ContinuousLTV X U Y ℝ} {u : ℝ → EuclideanSpace ℝ U}
    {x : ℝ → EuclideanSpace ℝ X} : s.IsTrajectory u x ↔ IsIntegralCurve x (s.vectorField u) :=
  Iff.rfl

/-- **Coordinates of a trajectory.**  `x` is a trajectory of the Euclidean system exactly when
its coordinate vector `ofLp ∘ x` solves the matrix equation `ż = A(t) z + B(t) u(t)`.  The solution
theory is proved for that matrix equation; this transports it to the system. -/
@[blueprint "lem:continuousLTV-isTrajectoryOn-iff-ofLp"
  (title := "Trajectories in coordinates")
  (latexEnv := "lemma")
  (statement := /-- $x$ is a trajectory of $s$ on $I$ (\cref{def:continuousLTV-isTrajectoryOn})
    if and only if its coordinate vector solves $\dot z = A(t) z + B(t) u(t)$ on $I$. -/)]
lemma isTrajectoryOn_iff_ofLp {s : ContinuousLTV X U Y ℝ} {u : ℝ → EuclideanSpace ℝ U}
    {x : ℝ → EuclideanSpace ℝ X} {I : Set ℝ} :
    s.IsTrajectoryOn u x I ↔
      IsIntegralCurveOn (fun t => (x t).ofLp) (fun t z => s.A t *ᵥ z + s.B t *ᵥ (u t).ofLp) I := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : X => ℝ)
  constructor
  · intro hx t ht
    simpa [e, Function.comp_def] using
      (e : EuclideanSpace ℝ X →L[ℝ] (X → ℝ)).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)
  · intro hx t ht
    simpa [e, Function.comp_def] using
      (e.symm : (X → ℝ) →L[ℝ] EuclideanSpace ℝ X).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)

/-- `x` is a Carathéodory trajectory of `s` under the input `u` on the set `I`: the integral
form, which admits discontinuous inputs. -/
@[blueprint "def:continuousLTV-isCaratheodoryTrajectoryOn"
  (title := "Carathéodory trajectory of an LTV system")
  (statement := /-- A Carathéodory trajectory
    (\cref{def:continuousSystem-isCaratheodoryTrajectoryOn}) of
    \cref{def:continuousLTV-toContinuousSystem}. -/)]
abbrev IsCaratheodoryTrajectoryOn (s : ContinuousLTV X U Y ℝ) (u : ℝ → EuclideanSpace ℝ U)
    (x : ℝ → EuclideanSpace ℝ X) (I : Set ℝ) : Prop :=
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

/-- The LTV system with the constant coefficients of an LTI system. -/
@[blueprint "def:continuousLTI-toLTV"
  (title := "The LTV system of an LTI system")
  (statement := /-- The LTV system (\cref{def:continuousLTV}) whose coefficients are the
    constant maps $t \mapsto A$, $t \mapsto B$, $t \mapsto C$, $t \mapsto D$. -/)]
def toLTV (sys : ContinuousLTI X U Y 𝕜) : ContinuousLTV X U Y 𝕜 where
  A := fun _ => sys.A
  B := fun _ => sys.B
  C := fun _ => sys.C
  D := fun _ => sys.D

@[simp] lemma toLTV_A (sys : ContinuousLTI X U Y 𝕜) (t : ℝ) : sys.toLTV.A t = sys.A := rfl
@[simp] lemma toLTV_B (sys : ContinuousLTI X U Y 𝕜) (t : ℝ) : sys.toLTV.B t = sys.B := rfl
@[simp] lemma toLTV_C (sys : ContinuousLTI X U Y 𝕜) (t : ℝ) : sys.toLTV.C t = sys.C := rfl
@[simp] lemma toLTV_D (sys : ContinuousLTI X U Y 𝕜) (t : ℝ) : sys.toLTV.D t = sys.D := rfl

/-- The LTV system of an LTI system is time-invariant. -/
@[blueprint "lem:continuousLTI-isTimeInvariant-toLTV"
  (title := "LTI systems are time-invariant LTV systems")
  (latexEnv := "lemma")
  (statement := /-- The LTV system of an LTI system (\cref{def:continuousLTI-toLTV}) is
    time-invariant (\cref{def:continuousLTV-isTimeInvariant}). -/)]
theorem isTimeInvariant_toLTV (sys : ContinuousLTI X U Y 𝕜) : sys.toLTV.IsTimeInvariant :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- A time-invariant LTV system is the LTV system of an LTI system. -/
@[blueprint "lem:continuousLTV-isTimeInvariant-exists-eq"
  (title := "Time-invariant LTV systems come from LTI systems")
  (latexEnv := "lemma")
  (statement := /-- A time-invariant LTV system (\cref{def:continuousLTV-isTimeInvariant}) is
    the LTV system of some LTI system.  The converse of
    \cref{lem:continuousLTI-isTimeInvariant-toLTV}. -/)
  (proof := /-- Read the coefficients off at $t = 0$; time invariance says every other time
    agrees with it. -/)]
theorem _root_.LinearSystems.ContinuousLTV.IsTimeInvariant.exists_eq
    {s : ContinuousLTV X U Y 𝕜} (h : s.IsTimeInvariant) :
    ∃ sys : ContinuousLTI X U Y 𝕜, s = sys.toLTV := by
  refine ⟨⟨s.A 0, s.B 0, s.C 0, s.D 0⟩, ?_⟩
  obtain ⟨sA, sB, sC, sD⟩ := s
  simp only [toLTV, ContinuousLTV.mk.injEq]
  refine ⟨funext fun t => ?_, funext fun t => ?_, funext fun t => ?_, funext fun t => ?_⟩
  exacts [(h t 0).1, (h t 0).2.1, (h t 0).2.2.1, (h t 0).2.2.2]

section Semantics

variable [Fintype X] [Fintype U] [DecidableEq X] [DecidableEq U]

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

variable [Fintype X] [Fintype U] [DecidableEq X] [DecidableEq U]

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

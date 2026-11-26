import LeanForControl.Analysis.PositiveDefinite
import LeanForControl.Stability.Continuous.Defs
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Architect

/-!
# `Stability.Continuous.LyapunovFunctions` — Lyapunov certificates

Lyapunov functions for stability and a Chetaev certificate for instability, on input-free
continuous-time systems `ẋ = f(t, x)` as `ContinuousSystem E Unit Y`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lyapunov's theorems for time-varying systems
(uniform, uniformly asymptotic and exponential stability).

## Named by what they certify

| Certificate                       | Certifies                        |
|-----------------------------------|----------------------------------|
| `IsLyapunovFunction`              | `Stable`                         |
| `IsUniformLyapunovFunction`       | `UniformlyStable`                |
| `IsStrictUniformLyapunovFunction` | `UniformlyAsymptoticallyStable`  |
| `IsExponentialLyapunovFunction`   | `LocallyExponentiallyStable`     |
| `IsChetaevFunction`              | `Unstable` for a time-independent state equation |

The Lyapunov functions are time-varying, `V(t, x)`. What separates these certificates is
which bounds hold: a lower bound `W₁(x) ≤ V(t, x)` gives stability, and adding the
upper bound `V(t, x) ≤ W₂(x)` — *decrescence* — is what makes it uniform.

A time-invariant `V(x)` is the special case `V(t, x) = V(x)`.  Positive definite, it is its own
lower and upper bound, so it is a uniform certificate as soon as it decreases along the system
(`IsUniformLyapunovFunction.of_timeInvariant`).  No separate time-invariant definitions are
needed.

The certificates of LaSalle's invariance principle are not here: they rely on invariance of
ω-limit sets, which holds only for time-invariant systems, and live with that theory.

## Conventions

* Lyapunov certificates hold on a neighbourhood `D`; the Chetaev region has `x_eq` on its
  boundary instead. Mathlib's `frontier D` denotes this topological boundary $\partial D$.
* Conditions are imposed for `t ≥ 0`, the initial times of `Stability.Continuous.Defs`.
* The derivative of `V` along the system, `∂V/∂t + ∂V/∂x · f`, is
  `ContinuousSystem.lieDerivative` (`Systems.Continuous`), at the input value `()`.
* Lyapunov functions are required to be locally Lipschitz in `(t, x)` on `t ≥ 0`, `x ∈ D`, in
  addition to differentiable there.  Trajectories are Carathéodory solutions, which are only
  absolutely continuous, so `t ↦ V(t, x(t))` must be absolutely continuous for the sign of `V̇`,
  known almost everywhere, to control it; differentiability at each point does not give that.
  A `C¹` function has both properties (`locallyLipschitzOn_of_contDiffAt`), and the
  `of_timeInvariant_of_contDiffAt` constructors take a `C¹` function of the state directly.
* The Chetaev theorem uses a state-only certificate and a time-independent state equation,
  without an equilibrium or forward-completeness premise.
-/

open Set Filter Topology

namespace ContinuousSystem

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Certificates -/

/-- A **Lyapunov function** on the neighbourhood `D` of `x_eq`: locally Lipschitz and
differentiable on `D`, zero at `x_eq`, bounded below by a positive definite `W₁`, and
nonincreasing along the system.  It certifies stability.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), the uniform stability theorem, with the
lower bound only. -/
@[blueprint "def:continuousSystem-isLyapunovFunction"
  (title := "Lyapunov function")
  (statement := /-- A function $V : \mathbb{R} \times E \to \mathbb{R}$ is a
    \emph{Lyapunov function} on a neighbourhood $D$ of $x_{\mathrm{eq}}$ when, for all $t \ge 0$
    and $x \in D$, $V$ is differentiable at $(t, x)$, $V$ is locally Lipschitz on
    $[0, \infty) \times D$, and
    \[
      V(t, x_{\mathrm{eq}}) = 0, \qquad W_1(x) \le V(t, x), \qquad \dot V(t, x) \le 0,
    \]
    for some $W_1$ positive definite on $D$ (\cref{def:isPositiveDefiniteOn}), with $\dot V$ the
    derivative along the system (\cref{def:continuousSystem-lieDerivative}).  It certifies
    stability (\cref{def:continuousSystem-stable}).  Local Lipschitz continuity makes $V$
    absolutely continuous along the (Carath\'eodory) trajectories
    (\cref{lem:continuousSystem-isLyapunovFunction-absolutelyContinuousOnInterval-comp}); every
    $C^1$ function qualifies (\cref{lem:locallyLipschitzOn-of-contDiffAt}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), the uniform stability theorem. -/)]
structure IsLyapunovFunction (s : ContinuousSystem E Unit Y) (V : ℝ → E → ℝ) (x_eq : E)
    (D : Set E) : Prop where
  /-- The region is a neighbourhood of the equilibrium. -/
  nhds : D ∈ 𝓝 x_eq
  /-- `V` is differentiable in `(t, x)` at every `t ≥ 0` and `x ∈ D`. -/
  differentiableAt : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, DifferentiableAt ℝ (Function.uncurry V) (t, x)
  /-- `V` is locally Lipschitz in `(t, x)` on `t ≥ 0`, `x ∈ D`, so that it is absolutely
  continuous along every trajectory staying in `D`. -/
  locallyLipschitzOn : LocallyLipschitzOn (Ici 0 ×ˢ D) (Function.uncurry V)
  /-- `V` vanishes at the equilibrium. -/
  zero : ∀ t : ℝ, 0 ≤ t → V t x_eq = 0
  /-- `V` is bounded below by a positive definite function. -/
  lower : ∃ W₁ : E → ℝ, IsPositiveDefiniteOn W₁ x_eq D ∧
    ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, W₁ x ≤ V t x
  /-- `V` does not increase along the system. -/
  lie_nonpos : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, s.lieDerivative V t x () ≤ 0

/-- A **uniform Lyapunov function**: a Lyapunov function that is also bounded above by a positive
definite `W₂` (decrescent).  It certifies uniform stability.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), the uniform stability theorem. -/
@[blueprint "def:continuousSystem-isUniformLyapunovFunction"
  (title := "Uniform Lyapunov function")
  (statement := /-- A Lyapunov function (\cref{def:continuousSystem-isLyapunovFunction}) that is
    also \emph{decrescent}: $V(t, x) \le W_2(x)$ for all $t \ge 0$, $x \in D$, for some $W_2$
    positive definite on $D$.  The upper bound is what makes the conclusion uniform: it
    certifies uniform stability (\cref{def:continuousSystem-uniformlyStable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), the uniform stability theorem. -/)]
structure IsUniformLyapunovFunction (s : ContinuousSystem E Unit Y) (V : ℝ → E → ℝ) (x_eq : E)
    (D : Set E) : Prop extends s.IsLyapunovFunction V x_eq D where
  /-- `V` is bounded above by a positive definite function. -/
  upper : ∃ W₂ : E → ℝ, IsPositiveDefiniteOn W₂ x_eq D ∧
    ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, V t x ≤ W₂ x

/-- A **strict uniform Lyapunov function**: a uniform Lyapunov function that decreases along the
system at least as fast as a positive definite `W₃`.  It certifies uniform asymptotic stability.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), the uniform asymptotic stability
theorem. -/
@[blueprint "def:continuousSystem-isStrictUniformLyapunovFunction"
  (title := "Strict uniform Lyapunov function")
  (statement := /-- A uniform Lyapunov function
    (\cref{def:continuousSystem-isUniformLyapunovFunction}) with
    $\dot V(t, x) \le -W_3(x)$ for all $t \ge 0$, $x \in D$, for some $W_3$ positive definite on
    $D$.  It certifies uniform asymptotic stability
    (\cref{def:continuousSystem-uniformlyAsymptoticallyStable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), the uniform asymptotic
    stability theorem. -/)]
structure IsStrictUniformLyapunovFunction (s : ContinuousSystem E Unit Y) (V : ℝ → E → ℝ)
    (x_eq : E) (D : Set E) : Prop extends s.IsUniformLyapunovFunction V x_eq D where
  /-- `V` decreases at least as fast as a positive definite function. -/
  strict : ∃ W₃ : E → ℝ, IsPositiveDefiniteOn W₃ x_eq D ∧
    ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, s.lieDerivative V t x () ≤ -W₃ x

/-- An **exponential Lyapunov function** with exponent `a > 0`: locally Lipschitz and
differentiable, sandwiched between multiples of `‖x - x_eq‖ᵃ`, and decreasing along the system
at least as fast as a multiple of it.  It certifies local exponential stability.

The exponent is a parameter rather than an existential: concrete Lyapunov functions come with a
known one (`a = 2` for quadratic forms and for the converse Lyapunov theorem), and results that
combine `V` with other estimates need it.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), the exponential stability theorem. -/
@[blueprint "def:continuousSystem-isExponentialLyapunovFunction"
  (title := "Exponential Lyapunov function")
  (statement := /-- A function $V : \mathbb{R} \times E \to \mathbb{R}$ is an
    \emph{exponential Lyapunov function} with exponent $a > 0$ on a neighbourhood $D$ of
    $x_{\mathrm{eq}}$ when there are $k_1, k_2, k_3 > 0$ with, for all $t \ge 0$ and $x \in D$,
    $V$ differentiable at $(t, x)$, $V$ locally Lipschitz on $[0, \infty) \times D$ (every $C^1$
    function qualifies, \cref{lem:locallyLipschitzOn-of-contDiffAt}), and
    \[
      k_1 \|x - x_{\mathrm{eq}}\|^{a} \le V(t, x) \le k_2 \|x - x_{\mathrm{eq}}\|^{a},
      \qquad \dot V(t, x) \le -k_3 \|x - x_{\mathrm{eq}}\|^{a}.
    \]
    It certifies local exponential stability
    (\cref{def:continuousSystem-locallyExponentiallyStable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), the exponential stability theorem. -/)]
structure IsExponentialLyapunovFunction (s : ContinuousSystem E Unit Y) (V : ℝ → E → ℝ)
    (x_eq : E) (D : Set E) (a : ℝ) : Prop where
  /-- The region is a neighbourhood of the equilibrium. -/
  nhds : D ∈ 𝓝 x_eq
  /-- `V` is differentiable in `(t, x)` at every `t ≥ 0` and `x ∈ D`. -/
  differentiableAt : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, DifferentiableAt ℝ (Function.uncurry V) (t, x)
  /-- `V` is locally Lipschitz in `(t, x)` on `t ≥ 0`, `x ∈ D`, so that it is absolutely
  continuous along every trajectory staying in `D`. -/
  locallyLipschitzOn : LocallyLipschitzOn (Ici 0 ×ˢ D) (Function.uncurry V)
  /-- The exponent is positive. -/
  exponent_pos : 0 < a
  /-- The power-law sandwich and decay rate. -/
  bounds : ∃ k₁ > 0, ∃ k₂ > 0, ∃ k₃ > 0, ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D,
    k₁ * ‖x - x_eq‖ ^ a ≤ V t x ∧ V t x ≤ k₂ * ‖x - x_eq‖ ^ a ∧
      s.lieDerivative V t x () ≤ -(k₃ * ‖x - x_eq‖ ^ a)

/-! ## Restriction to a smaller region -/

/-- An exponential Lyapunov function on `D` is one on every smaller neighbourhood of `x_eq`. -/
@[blueprint "lem:continuousSystem-isExponentialLyapunovFunction-mono"
  (title := "Restricting an exponential Lyapunov function")
  (latexEnv := "lemma")
  (statement := /-- If $V$ is an exponential Lyapunov function with exponent $a$ on $D$
    (\cref{def:continuousSystem-isExponentialLyapunovFunction}) and $D' \subseteq D$ is a
    neighbourhood of $x_{\mathrm{eq}}$, then $V$ is one on $D'$. -/)]
protected theorem IsExponentialLyapunovFunction.mono {s : ContinuousSystem E Unit Y}
    {V : ℝ → E → ℝ} {x_eq : E} {D D' : Set E} {a : ℝ}
    (hV : s.IsExponentialLyapunovFunction V x_eq D a) (hD' : D' ∈ 𝓝 x_eq) (h : D' ⊆ D) :
    s.IsExponentialLyapunovFunction V x_eq D' a where
  nhds := hD'
  differentiableAt := fun t ht x hx => hV.differentiableAt t ht x (h hx)
  locallyLipschitzOn := hV.locallyLipschitzOn.mono (prod_mono subset_rfl h)
  exponent_pos := hV.exponent_pos
  bounds :=
    let ⟨k₁, hk₁, k₂, hk₂, k₃, hk₃, hb⟩ := hV.bounds
    ⟨k₁, hk₁, k₂, hk₂, k₃, hk₃, fun t ht x hx => hb t ht x (h hx)⟩

/-! ## Certificates along trajectories

The regularity of a certificate is what the tools of `Systems.Continuous` for functions along
trajectories ask for.  These lemmas apply them to a trajectory on `[t₀, t₁]`, `t₀ ≥ 0`, that
stays in the region `D`. -/

section AlongTrajectory

variable [CompleteSpace E] {s : ContinuousSystem E Unit Y} {V : ℝ → E → ℝ} {x_eq : E} {D : Set E}
  {t₀ t₁ : ℝ} {x : ℝ → E}

/-- A Lyapunov function is absolutely continuous along a trajectory that stays in its region. -/
@[blueprint "lem:continuousSystem-isLyapunovFunction-absolutelyContinuousOnInterval-comp"
  (title := "Lyapunov functions are absolutely continuous along trajectories")
  (latexEnv := "lemma")
  (statement := /-- Let $V$ be a Lyapunov function on $D$
    (\cref{def:continuousSystem-isLyapunovFunction}) and $x$ a trajectory on $[t_0, t_1]$
    (\cref{def:continuousSystem-isTrajectoryOn}), $0 \le t_0 \le t_1$, with $x(\tau) \in D$ for
    $\tau \in [t_0, t_1]$.  Then $t \mapsto V(t, x(t))$ is absolutely continuous on
    $[t_0, t_1]$. -/)
  (proof := /-- $V$ is locally Lipschitz on $[0, \infty) \times D$, which contains the graph of
    $x$; apply \cref{lem:continuousSystem-isTrajectoryOn-absolutelyContinuousOnInterval-comp}. -/)]
theorem IsLyapunovFunction.absolutelyContinuousOnInterval_comp
    (hV : s.IsLyapunovFunction V x_eq D) (ht₀ : 0 ≤ t₀)
    (hx : s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁)) (ht : t₀ ≤ t₁)
    (h_in : ∀ τ ∈ Icc t₀ t₁, x τ ∈ D) :
    AbsolutelyContinuousOnInterval (fun t => V t (x t)) t₀ t₁ :=
  hx.absolutelyContinuousOnInterval_comp ht hV.locallyLipschitzOn
    fun τ hτ => ⟨ht₀.trans hτ.1, h_in τ hτ⟩

/-- Along a trajectory that stays in its region, the derivative of a Lyapunov function is, at
almost every time, its derivative along the system. -/
@[blueprint "lem:continuousSystem-isLyapunovFunction-ae-deriv-comp-eq-lieDerivative"
  (title := "Derivative of a Lyapunov function along a trajectory")
  (latexEnv := "lemma")
  (statement := /-- Let $V$ be a Lyapunov function on $D$
    (\cref{def:continuousSystem-isLyapunovFunction}) and $x$ a trajectory on $[t_0, t_1]$
    (\cref{def:continuousSystem-isTrajectoryOn}), $t_0 \ge 0$, with $x(\tau) \in D$ for
    $\tau \in [t_0, t_1]$.  Then for almost every $t \in (t_0, t_1)$ the derivative of
    $\tau \mapsto V(\tau, x(\tau))$ at $t$ is $\dot V(t, x(t))$
    (\cref{def:continuousSystem-lieDerivative}). -/)
  (proof := /-- $V$ is differentiable at every $(t, x(t))$; apply
    \cref{lem:continuousSystem-isTrajectoryOn-ae-deriv-eq-lieDerivative}. -/)]
theorem IsLyapunovFunction.ae_deriv_comp_eq_lieDerivative (hV : s.IsLyapunovFunction V x_eq D)
    (ht₀ : 0 ≤ t₀) (hx : s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁))
    (h_in : ∀ τ ∈ Icc t₀ t₁, x τ ∈ D) :
    ∀ᵐ t, t ∈ Ioo t₀ t₁ → deriv (fun τ => V τ (x τ)) t = s.lieDerivative V t (x t) () :=
  hx.ae_deriv_eq_lieDerivative <| .of_forall fun τ hτ =>
    hV.differentiableAt τ (ht₀.trans hτ.1.le) _ (h_in τ (Ioo_subset_Icc_self hτ))

/-- **A Lyapunov function does not increase along a trajectory** that stays in its region. -/
@[blueprint "lem:continuousSystem-isLyapunovFunction-antitoneOn-comp"
  (title := "Lyapunov functions do not increase along trajectories")
  (latexEnv := "lemma")
  (statement := /-- Let $V$ be a Lyapunov function on $D$
    (\cref{def:continuousSystem-isLyapunovFunction}) and $x$ a trajectory on $[t_0, t_1]$
    (\cref{def:continuousSystem-isTrajectoryOn}), $t_0 \ge 0$, with $x(\tau) \in D$ for
    $\tau \in [t_0, t_1]$.  Then $t \mapsto V(t, x(t))$ is nonincreasing on $[t_0, t_1]$. -/)
  (proof := /-- $\dot V \le 0$ along $x$; apply
    \cref{lem:continuousSystem-isTrajectoryOn-antitoneOn-of-lieDerivative-nonpos}. -/)]
theorem IsLyapunovFunction.antitoneOn_comp (hV : s.IsLyapunovFunction V x_eq D) (ht₀ : 0 ≤ t₀)
    (hx : s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁)) (h_in : ∀ τ ∈ Icc t₀ t₁, x τ ∈ D) :
    AntitoneOn (fun t => V t (x t)) (Icc t₀ t₁) :=
  hx.antitoneOn_of_lieDerivative_nonpos hV.locallyLipschitzOn
    (fun τ hτ => ⟨ht₀.trans hτ.1, h_in τ hτ⟩)
    (.of_forall fun τ hτ =>
      hV.differentiableAt τ (ht₀.trans hτ.1.le) _ (h_in τ (Ioo_subset_Icc_self hτ)))
    (.of_forall fun τ hτ =>
      hV.lie_nonpos τ (ht₀.trans hτ.1.le) _ (h_in τ (Ioo_subset_Icc_self hτ)))

/-- **An exponential Lyapunov function decays exponentially along trajectories** that stay in its
region: `V(t, x(t)) ≤ V(t₀, x(t₀)) e^{-c(t - t₀)}`, with `c = k₃/k₂` for the constants of its
bounds. -/
@[blueprint "lem:continuousSystem-isExponentialLyapunovFunction-exists-comp-le-mul-exp"
  (title := "Exponential Lyapunov functions decay exponentially along trajectories")
  (latexEnv := "lemma")
  (statement := /-- Let $V$ be an exponential Lyapunov function on $D$
    (\cref{def:continuousSystem-isExponentialLyapunovFunction}).  There is $c > 0$ such that
    every trajectory $x$ on a segment $[t_0, t_1]$
    (\cref{def:continuousSystem-isTrajectoryOn}), $t_0 \ge 0$, with $x(\tau) \in D$ for
    $\tau \in [t_0, t_1]$ satisfies
    \[
      V(t, x(t)) \le V(t_0, x(t_0))\, e^{-c(t - t_0)} \qquad \forall\, t \in [t_0, t_1].
    \] -/)
  (proof := /-- With $c = k_3/k_2$, the bounds give $\dot V \le -k_3\|x - x_{\mathrm{eq}}\|^a
    \le -c V$; apply \cref{lem:continuousSystem-isTrajectoryOn-le-mul-exp-of-lieDerivative-le}.
    -/)]
theorem IsExponentialLyapunovFunction.exists_comp_le_mul_exp {a : ℝ}
    (hV : s.IsExponentialLyapunovFunction V x_eq D a) :
    ∃ c > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
      s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → (∀ τ ∈ Icc t₀ t₁, x τ ∈ D) →
        ∀ t ∈ Icc t₀ t₁, V t (x t) ≤ V t₀ (x t₀) * Real.exp (-c * (t - t₀)) := by
  obtain ⟨_, -, k₂, hk₂, k₃, hk₃, hb⟩ := hV.bounds
  refine ⟨k₃ / k₂, div_pos hk₃ hk₂, fun t₀ ht₀ t₁ x hx h_in =>
    hx.le_mul_exp_of_lieDerivative_le hV.locallyLipschitzOn
      (fun τ hτ => ⟨ht₀.trans hτ.1, h_in τ hτ⟩)
      (.of_forall fun τ hτ =>
        hV.differentiableAt τ (ht₀.trans hτ.1.le) _ (h_in τ (Ioo_subset_Icc_self hτ)))
      (.of_forall fun τ hτ => ?_)⟩
  -- `V ≤ k₂ ‖x - x_eq‖ᵃ` turns `V̇ ≤ -k₃ ‖x - x_eq‖ᵃ` into `V̇ ≤ -(k₃/k₂) V`.
  obtain ⟨-, h_up, h_lie⟩ := hb τ (ht₀.trans hτ.1.le) (x τ) (h_in τ (Ioo_subset_Icc_self hτ))
  calc s.lieDerivative V τ (x τ) () ≤ -(k₃ * ‖x τ - x_eq‖ ^ a) := h_lie
    _ = -(k₃ / k₂) * (k₂ * ‖x τ - x_eq‖ ^ a) := by field_simp
    _ ≤ -(k₃ / k₂) * V τ (x τ) :=
      mul_le_mul_of_nonpos_left h_up (neg_nonpos.2 (div_pos hk₃ hk₂).le)

end AlongTrajectory

/-! ## Time-invariant Lyapunov functions -/

/-- **A time-invariant Lyapunov function is a uniform one.**  If `V(x)` is locally Lipschitz and
differentiable on `D`, positive definite on `D`, and does not increase along the system, then
`V(t, x) = V(x)` is a uniform Lyapunov function: `V` is its own lower and upper bound. -/
@[blueprint "lem:continuousSystem-isUniformLyapunovFunction-of-timeInvariant"
  (title := "Time-invariant Lyapunov functions are uniform")
  (latexEnv := "lemma")
  (statement := /-- Let $V : E \to \mathbb{R}$ be positive definite on a neighbourhood $D$ of
    $x_{\mathrm{eq}}$ (\cref{def:isPositiveDefiniteOn}), locally Lipschitz on $D$ and
    differentiable at its points (every $C^1$ function qualifies,
    \cref{lem:continuousSystem-isUniformLyapunovFunction-of-timeInvariant-of-contDiffAt}), with
    $\nabla V(x) \cdot f(t, x) \le 0$ for all $t \ge 0$, $x \in D$.  Then $(t, x) \mapsto V(x)$
    is a uniform Lyapunov function (\cref{def:continuousSystem-isUniformLyapunovFunction}). -/)
  (proof := /-- Take $W_1 = W_2 = V$.  The derivative along the system of a function of $x$ alone
    is its directional derivative along the vector field. -/)]
theorem IsUniformLyapunovFunction.of_timeInvariant {s : ContinuousSystem E Unit Y} {V : E → ℝ}
    {x_eq : E} {D : Set E} (hD : D ∈ 𝓝 x_eq) (hV_diff : ∀ x ∈ D, DifferentiableAt ℝ V x)
    (hV_lip : LocallyLipschitzOn D V) (hV_pos : IsPositiveDefiniteOn V x_eq D)
    (hV_dec : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, fderiv ℝ V x (s.F t x ()) ≤ 0) :
    s.IsUniformLyapunovFunction (fun _ => V) x_eq D where
  nhds := hD
  differentiableAt := fun _ _ x hx => (hV_diff x hx).comp _ differentiableAt_snd
  locallyLipschitzOn := hV_lip.comp_snd.mono fun _ hp => hp.2
  zero := fun _ _ => hV_pos.2.1
  lower := ⟨V, hV_pos, fun _ _ _ _ => le_rfl⟩
  lie_nonpos := fun t ht x hx =>
    (lieDerivative_const (v := fun t x => s.F t x ()) (hV_diff x hx)).trans_le (hV_dec t ht x hx)
  upper := ⟨V, hV_pos, fun _ _ _ _ => le_rfl⟩

/-- **A `C¹` time-invariant Lyapunov function is a uniform one**:
`IsUniformLyapunovFunction.of_timeInvariant` for `V` continuously differentiable at the points of
`D`, where it is then locally Lipschitz. -/
@[blueprint "lem:continuousSystem-isUniformLyapunovFunction-of-timeInvariant-of-contDiffAt"
  (title := "Continuously differentiable time-invariant Lyapunov functions are uniform")
  (latexEnv := "lemma")
  (statement := /-- Let $V : E \to \mathbb{R}$ be positive definite on a neighbourhood $D$ of
    $x_{\mathrm{eq}}$ and $C^1$ at every point of $D$, with
    $\nabla V(x) \cdot f(t, x) \le 0$ for all $t \ge 0$, $x \in D$.  Then $(t, x) \mapsto V(x)$
    is a uniform Lyapunov function (\cref{def:continuousSystem-isUniformLyapunovFunction}). -/)
  (proof := /-- \cref{lem:continuousSystem-isUniformLyapunovFunction-of-timeInvariant}; $V$ is
    locally Lipschitz on $D$ (\cref{lem:locallyLipschitzOn-of-contDiffAt}). -/)]
theorem IsUniformLyapunovFunction.of_timeInvariant_of_contDiffAt {s : ContinuousSystem E Unit Y}
    {V : E → ℝ} {x_eq : E} {D : Set E} (hD : D ∈ 𝓝 x_eq) (hV_c1 : ∀ x ∈ D, ContDiffAt ℝ 1 V x)
    (hV_pos : IsPositiveDefiniteOn V x_eq D)
    (hV_dec : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, fderiv ℝ V x (s.F t x ()) ≤ 0) :
    s.IsUniformLyapunovFunction (fun _ => V) x_eq D :=
  of_timeInvariant hD (fun x hx => (hV_c1 x hx).differentiableAt one_ne_zero)
    (locallyLipschitzOn_of_contDiffAt hV_c1) hV_pos hV_dec

/-- **A strictly decreasing time-invariant Lyapunov function is a strict uniform one.**  If in
addition `∇V · f ≤ -W₃` for a positive definite `W₃`, then `V(t, x) = V(x)` is a strict uniform
Lyapunov function. -/
@[blueprint "lem:continuousSystem-isStrictUniformLyapunovFunction-of-timeInvariant"
  (title := "Strict time-invariant Lyapunov functions are strict uniform")
  (latexEnv := "lemma")
  (statement := /-- Let $V : E \to \mathbb{R}$ be positive definite on a neighbourhood $D$ of
    $x_{\mathrm{eq}}$, locally Lipschitz on $D$ and differentiable at its points, with
    $\nabla V(x) \cdot f(t, x) \le -W_3(x)$ for all
    $t \ge 0$, $x \in D$, for some $W_3$ positive definite on $D$.  Then $(t, x) \mapsto V(x)$ is
    a strict uniform Lyapunov function
    (\cref{def:continuousSystem-isStrictUniformLyapunovFunction}). -/)
  (proof := /-- As for \cref{lem:continuousSystem-isUniformLyapunovFunction-of-timeInvariant};
    $-W_3 \le 0$ gives the non-strict decrease. -/)]
theorem IsStrictUniformLyapunovFunction.of_timeInvariant {s : ContinuousSystem E Unit Y}
    {V : E → ℝ} {x_eq : E} {D : Set E} (hD : D ∈ 𝓝 x_eq)
    (hV_diff : ∀ x ∈ D, DifferentiableAt ℝ V x) (hV_lip : LocallyLipschitzOn D V)
    (hV_pos : IsPositiveDefiniteOn V x_eq D) {W₃ : E → ℝ} (hW₃ : IsPositiveDefiniteOn W₃ x_eq D)
    (hV_dec : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, fderiv ℝ V x (s.F t x ()) ≤ -W₃ x) :
    s.IsStrictUniformLyapunovFunction (fun _ => V) x_eq D where
  toIsUniformLyapunovFunction :=
    IsUniformLyapunovFunction.of_timeInvariant hD hV_diff hV_lip hV_pos fun t ht x hx => by
      linarith [hV_dec t ht x hx, hW₃.nonneg hx]
  strict := ⟨W₃, hW₃, fun t ht x hx =>
    (lieDerivative_const (v := fun t x => s.F t x ()) (hV_diff x hx)).trans_le (hV_dec t ht x hx)⟩

/-- **A strictly decreasing `C¹` time-invariant Lyapunov function is a strict uniform one**:
`IsStrictUniformLyapunovFunction.of_timeInvariant` for `V` continuously differentiable at the
points of `D`, where it is then locally Lipschitz. -/
@[blueprint "lem:continuousSystem-isStrictUniformLyapunovFunction-of-timeInvariant-of-contDiffAt"
  (title := "Continuously differentiable strict time-invariant Lyapunov functions")
  (latexEnv := "lemma")
  (statement := /-- Let $V : E \to \mathbb{R}$ be positive definite on a neighbourhood $D$ of
    $x_{\mathrm{eq}}$ and $C^1$ at every point of $D$, with
    $\nabla V(x) \cdot f(t, x) \le -W_3(x)$ for all $t \ge 0$, $x \in D$, for some $W_3$ positive
    definite on $D$.  Then $(t, x) \mapsto V(x)$ is a strict uniform Lyapunov function
    (\cref{def:continuousSystem-isStrictUniformLyapunovFunction}). -/)
  (proof := /-- \cref{lem:continuousSystem-isStrictUniformLyapunovFunction-of-timeInvariant}; $V$
    is locally Lipschitz on $D$ (\cref{lem:locallyLipschitzOn-of-contDiffAt}). -/)]
theorem IsStrictUniformLyapunovFunction.of_timeInvariant_of_contDiffAt
    {s : ContinuousSystem E Unit Y} {V : E → ℝ} {x_eq : E} {D : Set E} (hD : D ∈ 𝓝 x_eq)
    (hV_c1 : ∀ x ∈ D, ContDiffAt ℝ 1 V x) (hV_pos : IsPositiveDefiniteOn V x_eq D) {W₃ : E → ℝ}
    (hW₃ : IsPositiveDefiniteOn W₃ x_eq D)
    (hV_dec : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, fderiv ℝ V x (s.F t x ()) ≤ -W₃ x) :
    s.IsStrictUniformLyapunovFunction (fun _ => V) x_eq D :=
  of_timeInvariant hD (fun x hx => (hV_c1 x hx).differentiableAt one_ne_zero)
    (locallyLipschitzOn_of_contDiffAt hV_c1) hV_pos hW₃ hV_dec

/-- **For a time-invariant system, strict decrease is enough.**  If the state equation is a
continuous time-invariant field `f` with `f(x_eq) = 0`, and `V(x)` is `C¹`, positive definite on
`D`, with `∇V · f < 0` off `x_eq`, then `V(t, x) = V(x)` is a strict uniform Lyapunov function:
the rate `W₃ = -∇V · f` is itself positive definite.  For a time-varying field this fails, since
`∇V(x) · f(t, x)` may tend to `0` as `t → ∞`. -/
@[blueprint "lem:continuousSystem-isStrictUniformLyapunovFunction-of-timeInvariant-of-neg"
  (title := "Strict decrease suffices for a time-invariant system")
  (latexEnv := "lemma")
  (statement := /-- Let the state equation be $\dot x = f(x)$ with $f$ continuous and
    $f(x_{\mathrm{eq}}) = 0$, and let $V : E \to \mathbb{R}$ be $C^1$ and positive definite on a
    neighbourhood $D$ of $x_{\mathrm{eq}}$ with $\nabla V(x) \cdot f(x) < 0$ for
    $x \in D \setminus \{x_{\mathrm{eq}}\}$.  Then $(t, x) \mapsto V(x)$ is a strict uniform
    Lyapunov function (\cref{def:continuousSystem-isStrictUniformLyapunovFunction}). -/)
  (proof := /-- Take $W_3 = -\nabla V \cdot f$: continuous since $V$ is $C^1$ and $f$ is
    continuous, zero at $x_{\mathrm{eq}}$ since $f(x_{\mathrm{eq}}) = 0$, and positive elsewhere
    on $D$.  Apply
    \cref{lem:continuousSystem-isStrictUniformLyapunovFunction-of-timeInvariant-of-contDiffAt}.
    -/)]
theorem IsStrictUniformLyapunovFunction.of_timeInvariant_of_neg {s : ContinuousSystem E Unit Y}
    {f : E → E} (hF : ∀ t x, s.F t x () = f x) (hf : Continuous f) {V : E → ℝ} {x_eq : E}
    {D : Set E} (hD : D ∈ 𝓝 x_eq) (hV_c1 : ContDiff ℝ 1 V)
    (hV_pos : IsPositiveDefiniteOn V x_eq D) (hf_eq : f x_eq = 0)
    (hV_neg : ∀ x ∈ D, x ≠ x_eq → fderiv ℝ V x (f x) < 0) :
    s.IsStrictUniformLyapunovFunction (fun _ => V) x_eq D :=
  of_timeInvariant_of_contDiffAt hD (fun _ _ => hV_c1.contDiffAt) hV_pos
    (W₃ := fun x => -fderiv ℝ V x (f x))
    ⟨((hV_c1.continuous_fderiv one_ne_zero).clm_apply hf).neg.continuousOn, by simp [hf_eq],
      fun x hx hne => neg_pos.mpr (hV_neg x hx hne)⟩
    fun t _ x _ => by rw [hF, neg_neg]

/-- **A time-invariant exponential Lyapunov function.**  If `V(x)` is locally Lipschitz and
differentiable on `D`, sandwiched between multiples of `‖x - x_eq‖ᵃ`, with `∇V · f` at most a
negative multiple of it, then `V(t, x) = V(x)` is an exponential Lyapunov function. -/
@[blueprint "lem:continuousSystem-isExponentialLyapunovFunction-of-timeInvariant"
  (title := "Time-invariant exponential Lyapunov functions")
  (latexEnv := "lemma")
  (statement := /-- Let $V : E \to \mathbb{R}$ be locally Lipschitz on a neighbourhood $D$ of
    $x_{\mathrm{eq}}$ and differentiable at its points, $a > 0$ and $k_1, k_2, k_3 > 0$ with, for
    all $t \ge 0$ and $x \in D$,
    \[
      k_1 \|x - x_{\mathrm{eq}}\|^{a} \le V(x) \le k_2 \|x - x_{\mathrm{eq}}\|^{a},
      \qquad \nabla V(x) \cdot f(t, x) \le -k_3 \|x - x_{\mathrm{eq}}\|^{a}.
    \]
    Then $(t, x) \mapsto V(x)$ is an exponential Lyapunov function with exponent $a$ on $D$
    (\cref{def:continuousSystem-isExponentialLyapunovFunction}). -/)
  (proof := /-- $(t, x) \mapsto V(x)$ is locally Lipschitz (\cref{lem:locallyLipschitzOn-comp-snd})
    and its derivative along the system is $\nabla V \cdot f$ (\cref{lem:lieDerivative-const}).
    -/)]
theorem IsExponentialLyapunovFunction.of_timeInvariant {s : ContinuousSystem E Unit Y}
    {V : E → ℝ} {x_eq : E} {D : Set E} {a : ℝ} (hD : D ∈ 𝓝 x_eq)
    (hV_diff : ∀ x ∈ D, DifferentiableAt ℝ V x) (hV_lip : LocallyLipschitzOn D V) (ha : 0 < a)
    (h_bounds : ∃ k₁ > 0, ∃ k₂ > 0, ∃ k₃ > 0, ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D,
      k₁ * ‖x - x_eq‖ ^ a ≤ V x ∧ V x ≤ k₂ * ‖x - x_eq‖ ^ a ∧
        fderiv ℝ V x (s.F t x ()) ≤ -(k₃ * ‖x - x_eq‖ ^ a)) :
    s.IsExponentialLyapunovFunction (fun _ => V) x_eq D a where
  nhds := hD
  differentiableAt := fun _ _ x hx => (hV_diff x hx).comp _ differentiableAt_snd
  locallyLipschitzOn := hV_lip.comp_snd.mono fun _ hp => hp.2
  exponent_pos := ha
  bounds :=
    let ⟨k₁, hk₁, k₂, hk₂, k₃, hk₃, hb⟩ := h_bounds
    ⟨k₁, hk₁, k₂, hk₂, k₃, hk₃, fun t ht x hx =>
      ⟨(hb t ht x hx).1, (hb t ht x hx).2.1,
        (lieDerivative_const (v := fun t x => s.F t x ()) (hV_diff x hx)).trans_le
          (hb t ht x hx).2.2⟩⟩

/-- **A `C¹` time-invariant exponential Lyapunov function**:
`IsExponentialLyapunovFunction.of_timeInvariant` for `V` continuously differentiable at the points
of `D`, where it is then locally Lipschitz. -/
@[blueprint "lem:continuousSystem-isExponentialLyapunovFunction-of-timeInvariant-of-contDiffAt"
  (title := "Continuously differentiable time-invariant exponential Lyapunov functions")
  (latexEnv := "lemma")
  (statement := /-- The conclusion of
    \cref{lem:continuousSystem-isExponentialLyapunovFunction-of-timeInvariant} holds for $V$ that
    is $C^1$ at every point of $D$, in place of locally Lipschitz on $D$ and differentiable at
    its points. -/)
  (proof := /-- $V$ is locally Lipschitz on $D$ (\cref{lem:locallyLipschitzOn-of-contDiffAt}).
    -/)]
theorem IsExponentialLyapunovFunction.of_timeInvariant_of_contDiffAt
    {s : ContinuousSystem E Unit Y} {V : E → ℝ} {x_eq : E} {D : Set E} {a : ℝ} (hD : D ∈ 𝓝 x_eq)
    (hV_c1 : ∀ x ∈ D, ContDiffAt ℝ 1 V x) (ha : 0 < a)
    (h_bounds : ∃ k₁ > 0, ∃ k₂ > 0, ∃ k₃ > 0, ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D,
      k₁ * ‖x - x_eq‖ ^ a ≤ V x ∧ V x ≤ k₂ * ‖x - x_eq‖ ^ a ∧
        fderiv ℝ V x (s.F t x ()) ≤ -(k₃ * ‖x - x_eq‖ ^ a)) :
    s.IsExponentialLyapunovFunction (fun _ => V) x_eq D a :=
  of_timeInvariant hD (fun x hx => (hV_c1 x hx).differentiableAt one_ne_zero)
    (locallyLipschitzOn_of_contDiffAt hV_c1) ha h_bounds

/-! ## Chetaev certificate -/

section Chetaev

/-- A globally `C¹` state-only certificate, positive in an open region within a fixed ball,
zero on the region's boundary there, and with strictly positive Lie derivative for `t ≥ 0`.
The base point lies on the boundary. With a time-independent state equation this certifies
instability; neither the region nor the function is assumed globally bounded.

Reference: Khalil, *Nonlinear Systems*, 3rd ed. (Prentice Hall, 2002), Chetaev's theorem,
for the positive-region escape argument. -/
@[blueprint "def:continuousSystem-isChetaevFunction"
  (title := "Chetaev function")
  (statement := /-- Let $s$ be an input-free continuous-time system. A Chetaev certificate
    consists of an open region $D$, a point $x_{\rm eq}\in\partial D$, a radius $\rho>0$,
    and a globally $C^1$ function $V$. For $\|x-x_{\rm eq}\|\le\rho$, $V(x)>0$ in $D$
    and $V(x)=0$ on $\partial D$; in $D$ the derivative $\nabla V(x)\cdot F(t,x,())$
    is strictly positive for every $t\ge0$.

    Reference: Khalil, \emph{Nonlinear Systems}, 3rd ed., Chetaev's theorem. -/)]
structure IsChetaevFunction (s : ContinuousSystem E Unit Y) (V : E → ℝ)
    (x_eq : E) (D : Set E) (ρ : ℝ) : Prop where
  /-- The certificate radius is positive. -/
  hradius : 0 < ρ
  /-- The positive region is open. -/
  hD_open : IsOpen D
  /-- The base point belongs to the region's boundary. -/
  hmem_boundary : x_eq ∈ frontier D
  /-- The certificate is globally continuously differentiable. -/
  hV_c1 : ContDiff ℝ 1 V
  /-- Positivity inside the region and closed certificate ball. -/
  hpos : ∀ x ∈ D, ‖x - x_eq‖ ≤ ρ → 0 < V x
  /-- Vanishing on the region's boundary within the closed ball. -/
  hboundary_zero : ∀ x ∈ frontier D, ‖x - x_eq‖ ≤ ρ → V x = 0
  /-- Strictly positive system Lie derivative in the region and closed ball. -/
  hLie_pos : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, ‖x - x_eq‖ ≤ ρ →
    0 < s.lieDerivative (fun _ ↦ V) t x ()

end Chetaev

end ContinuousSystem

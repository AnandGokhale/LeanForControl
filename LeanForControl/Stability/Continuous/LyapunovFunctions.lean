import LeanForControl.Analysis.PositiveDefinite
import LeanForControl.Stability.Continuous.Defs
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Architect

/-!
# `Stability.Continuous.LyapunovFunctions` — Lyapunov certificates

Lyapunov functions for an equilibrium `x_eq` of an autonomous continuous-time system
`ẋ = f(t, x)`, as a `ContinuousSystem E Unit Y`.  Each is a *certificate*: a function whose
existence implies one of the stability notions of `Stability.Continuous.Defs`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorems 4.8–4.10.

## Named by what they certify

| Certificate                       | Certifies                        |
|-----------------------------------|----------------------------------|
| `IsLyapunovFunction`              | `Stable`                         |
| `IsUniformLyapunovFunction`       | `UniformlyStable`                |
| `IsStrictUniformLyapunovFunction` | `UniformlyAsymptoticallyStable`  |
| `IsExponentialLyapunovFunction`   | `LocallyExponentiallyStable`     |

The functions are time-varying, `V(t, x)`.  What separates the certificates is not whether time
appears but which bounds hold: a lower bound `W₁(x) ≤ V(t, x)` gives stability, and adding the
upper bound `V(t, x) ≤ W₂(x)` — *decrescence* — is what makes it uniform.

A time-invariant `V(x)` is the special case `V(t, x) = V(x)`.  Positive definite, it is its own
lower and upper bound, so it is a uniform certificate as soon as it decreases along the system
(`IsUniformLyapunovFunction.of_timeInvariant`).  No separate time-invariant definitions are
needed.

The certificates of LaSalle's invariance principle are not here: they rely on invariance of
ω-limit sets, which holds only for time-invariant systems, and live with that theory.

## Conventions

* The certificate holds on a neighbourhood `D` of `x_eq`; `D = univ` gives the global versions.
* Conditions are imposed for `t ≥ 0`, the initial times of `Stability.Continuous.Defs`.
* The derivative of `V` along the system, `∂V/∂t + ∂V/∂x · f`, is
  `ContinuousSystem.lieDerivative` (`Systems.Continuous`), at the input value `()`.
-/

open Set Filter Topology

namespace ContinuousSystem

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Certificates -/

/-- A **Lyapunov function** on the neighbourhood `D` of `x_eq`: differentiable, zero at `x_eq`,
bounded below by a positive definite `W₁`, and nonincreasing along the system.  It certifies
stability.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.8, with the lower bound only. -/
@[blueprint "def:continuousSystem-isLyapunovFunction"
  (title := "Lyapunov function")
  (statement := /-- A differentiable $V : \mathbb{R} \times E \to \mathbb{R}$ is a
    \emph{Lyapunov function} on a neighbourhood $D$ of $x_{\mathrm{eq}}$ when, for all $t \ge 0$
    and $x \in D$,
    \[
      V(t, x_{\mathrm{eq}}) = 0, \qquad W_1(x) \le V(t, x), \qquad \dot V(t, x) \le 0,
    \]
    for some $W_1$ positive definite on $D$ (\cref{def:isPositiveDefiniteOn}), with $\dot V$ the
    derivative along the system (\cref{def:continuousSystem-lieDerivative}).  It certifies
    stability (\cref{def:continuousSystem-stable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.8. -/)]
structure IsLyapunovFunction (s : ContinuousSystem E Unit Y) (V : ℝ → E → ℝ) (x_eq : E)
    (D : Set E) : Prop where
  /-- The region is a neighbourhood of the equilibrium. -/
  nhds : D ∈ 𝓝 x_eq
  /-- `V` is differentiable in `(t, x)`. -/
  differentiable : Differentiable ℝ (Function.uncurry V)
  /-- `V` vanishes at the equilibrium. -/
  zero : ∀ t : ℝ, 0 ≤ t → V t x_eq = 0
  /-- `V` is bounded below by a positive definite function. -/
  lower : ∃ W₁ : E → ℝ, IsPositiveDefiniteOn W₁ x_eq D ∧
    ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, W₁ x ≤ V t x
  /-- `V` does not increase along the system. -/
  lie_nonpos : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, s.lieDerivative V t x () ≤ 0

/-- A **uniform Lyapunov function**: a Lyapunov function that is also bounded above by a positive
definite `W₂` (decrescent).  It certifies uniform stability.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.8. -/
@[blueprint "def:continuousSystem-isUniformLyapunovFunction"
  (title := "Uniform Lyapunov function")
  (statement := /-- A Lyapunov function (\cref{def:continuousSystem-isLyapunovFunction}) that is
    also \emph{decrescent}: $V(t, x) \le W_2(x)$ for all $t \ge 0$, $x \in D$, for some $W_2$
    positive definite on $D$.  The upper bound is what makes the conclusion uniform: it
    certifies uniform stability (\cref{def:continuousSystem-uniformlyStable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.8. -/)]
structure IsUniformLyapunovFunction (s : ContinuousSystem E Unit Y) (V : ℝ → E → ℝ) (x_eq : E)
    (D : Set E) : Prop extends s.IsLyapunovFunction V x_eq D where
  /-- `V` is bounded above by a positive definite function. -/
  upper : ∃ W₂ : E → ℝ, IsPositiveDefiniteOn W₂ x_eq D ∧
    ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, V t x ≤ W₂ x

/-- A **strict uniform Lyapunov function**: a uniform Lyapunov function that decreases along the
system at least as fast as a positive definite `W₃`.  It certifies uniform asymptotic stability.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.9. -/
@[blueprint "def:continuousSystem-isStrictUniformLyapunovFunction"
  (title := "Strict uniform Lyapunov function")
  (statement := /-- A uniform Lyapunov function
    (\cref{def:continuousSystem-isUniformLyapunovFunction}) with
    $\dot V(t, x) \le -W_3(x)$ for all $t \ge 0$, $x \in D$, for some $W_3$ positive definite on
    $D$.  It certifies uniform asymptotic stability
    (\cref{def:continuousSystem-uniformlyAsymptoticallyStable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.9. -/)]
structure IsStrictUniformLyapunovFunction (s : ContinuousSystem E Unit Y) (V : ℝ → E → ℝ)
    (x_eq : E) (D : Set E) : Prop extends s.IsUniformLyapunovFunction V x_eq D where
  /-- `V` decreases at least as fast as a positive definite function. -/
  strict : ∃ W₃ : E → ℝ, IsPositiveDefiniteOn W₃ x_eq D ∧
    ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, s.lieDerivative V t x () ≤ -W₃ x

/-- An **exponential Lyapunov function**: sandwiched between multiples of `‖x - x_eq‖ᵃ`, and
decreasing along the system at least as fast as a multiple of it.  It certifies local exponential
stability.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.10. -/
@[blueprint "def:continuousSystem-isExponentialLyapunovFunction"
  (title := "Exponential Lyapunov function")
  (statement := /-- A differentiable $V : \mathbb{R} \times E \to \mathbb{R}$ is an
    \emph{exponential Lyapunov function} on a neighbourhood $D$ of $x_{\mathrm{eq}}$ when there
    are $k_1, k_2, k_3, a > 0$ with, for all $t \ge 0$ and $x \in D$,
    \[
      k_1 \|x - x_{\mathrm{eq}}\|^{a} \le V(t, x) \le k_2 \|x - x_{\mathrm{eq}}\|^{a},
      \qquad \dot V(t, x) \le -k_3 \|x - x_{\mathrm{eq}}\|^{a}.
    \]
    It certifies local exponential stability
    (\cref{def:continuousSystem-locallyExponentiallyStable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.10. -/)]
structure IsExponentialLyapunovFunction (s : ContinuousSystem E Unit Y) (V : ℝ → E → ℝ)
    (x_eq : E) (D : Set E) : Prop where
  /-- The region is a neighbourhood of the equilibrium. -/
  nhds : D ∈ 𝓝 x_eq
  /-- `V` is differentiable in `(t, x)`. -/
  differentiable : Differentiable ℝ (Function.uncurry V)
  /-- The power-law sandwich and decay rate. -/
  bounds : ∃ k₁ > 0, ∃ k₂ > 0, ∃ k₃ > 0, ∃ a > 0, ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D,
    k₁ * ‖x - x_eq‖ ^ a ≤ V t x ∧ V t x ≤ k₂ * ‖x - x_eq‖ ^ a ∧
      s.lieDerivative V t x () ≤ -(k₃ * ‖x - x_eq‖ ^ a)

/-! ## Time-invariant Lyapunov functions -/

/-- **A time-invariant Lyapunov function is a uniform one.**  If `V(x)` is differentiable,
positive definite on `D`, and does not increase along the system, then `V(t, x) = V(x)` is a
uniform Lyapunov function: `V` is its own lower and upper bound. -/
@[blueprint "lem:continuousSystem-isUniformLyapunovFunction-of-timeInvariant"
  (title := "Time-invariant Lyapunov functions are uniform")
  (latexEnv := "lemma")
  (statement := /-- Let $V : E \to \mathbb{R}$ be differentiable and positive definite on a
    neighbourhood $D$ of $x_{\mathrm{eq}}$ (\cref{def:isPositiveDefiniteOn}), with
    $\nabla V(x) \cdot f(t, x) \le 0$ for all $t \ge 0$, $x \in D$.  Then $(t, x) \mapsto V(x)$
    is a uniform Lyapunov function (\cref{def:continuousSystem-isUniformLyapunovFunction}). -/)
  (proof := /-- Take $W_1 = W_2 = V$.  The derivative along the system of a function of $x$ alone
    is its directional derivative along the vector field. -/)]
theorem IsUniformLyapunovFunction.of_timeInvariant {s : ContinuousSystem E Unit Y} {V : E → ℝ}
    {x_eq : E} {D : Set E} (hD : D ∈ 𝓝 x_eq) (hV_diff : Differentiable ℝ V)
    (hV_pos : IsPositiveDefiniteOn V x_eq D)
    (hV_dec : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, fderiv ℝ V x (s.F t x ()) ≤ 0) :
    s.IsUniformLyapunovFunction (fun _ => V) x_eq D where
  nhds := hD
  differentiable := hV_diff.comp differentiable_snd
  zero := fun _ _ => hV_pos.2.1
  lower := ⟨V, hV_pos, fun _ _ _ _ => le_rfl⟩
  lie_nonpos := fun t ht x hx => by
    rw [lieDerivative_const (hV_diff x)]
    exact hV_dec t ht x hx
  upper := ⟨V, hV_pos, fun _ _ _ _ => le_rfl⟩

/-- **A strictly decreasing time-invariant Lyapunov function is a strict uniform one.**  If in
addition `∇V · f ≤ -W₃` for a positive definite `W₃`, then `V(t, x) = V(x)` is a strict uniform
Lyapunov function. -/
@[blueprint "lem:continuousSystem-isStrictUniformLyapunovFunction-of-timeInvariant"
  (title := "Strict time-invariant Lyapunov functions are strict uniform")
  (latexEnv := "lemma")
  (statement := /-- Let $V : E \to \mathbb{R}$ be differentiable and positive definite on a
    neighbourhood $D$ of $x_{\mathrm{eq}}$, with $\nabla V(x) \cdot f(t, x) \le -W_3(x)$ for all
    $t \ge 0$, $x \in D$, for some $W_3$ positive definite on $D$.  Then $(t, x) \mapsto V(x)$ is
    a strict uniform Lyapunov function
    (\cref{def:continuousSystem-isStrictUniformLyapunovFunction}). -/)
  (proof := /-- As for \cref{lem:continuousSystem-isUniformLyapunovFunction-of-timeInvariant};
    $-W_3 \le 0$ gives the non-strict decrease. -/)]
theorem IsStrictUniformLyapunovFunction.of_timeInvariant {s : ContinuousSystem E Unit Y}
    {V : E → ℝ} {x_eq : E} {D : Set E} (hD : D ∈ 𝓝 x_eq) (hV_diff : Differentiable ℝ V)
    (hV_pos : IsPositiveDefiniteOn V x_eq D) {W₃ : E → ℝ} (hW₃ : IsPositiveDefiniteOn W₃ x_eq D)
    (hV_dec : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ D, fderiv ℝ V x (s.F t x ()) ≤ -W₃ x) :
    s.IsStrictUniformLyapunovFunction (fun _ => V) x_eq D where
  toIsUniformLyapunovFunction :=
    IsUniformLyapunovFunction.of_timeInvariant hD hV_diff hV_pos fun t ht x hx => by
      linarith [hV_dec t ht x hx, hW₃.nonneg hx]
  strict := ⟨W₃, hW₃, fun t ht x hx => by
    rw [lieDerivative_const (hV_diff x)]
    exact hV_dec t ht x hx⟩

end ContinuousSystem

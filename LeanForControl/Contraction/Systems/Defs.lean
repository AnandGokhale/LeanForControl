import LeanForControl.Systems.Continuous
import Architect

/-!
# `Contraction.Systems.Defs` — contracting systems

Contraction of a system `ẋ = F(t, x, u(t))` under an input `u` is a property of its trajectories:
the distance between any two of them decays at rate `c`.

| Definition | Meaning |
|---|---|
| `IsContractingOn s u C d c` | `d(x t, y t) ≤ e^{-c(t - t₀)} d(x t₀, y t₀)`, trajectories in `C` |
| `IsInfinitesimallyContractingOn s u C c` | the same, `d(x, y) = ‖x - y‖` |

The rate `c` is any real: `c > 0` is strong contraction, `c = 0` nonexpansiveness.  The distance in
`IsContractingOn` is an argument, not the metric of the state space, which carries the norm used for
derivatives: it can be a norm other than that of `E`, or a Riemannian distance.  A norm other than
that of `E` is also reached by changing the state space to `WeightedNorm R`.

In a norm, contraction is characterized on the vector field by `osL(F(t, ·, u(t))) ≤ -c`; that is a
theorem, not the definition.

Trajectories are right trajectories, so piecewise continuous inputs are included.

Reference: F. Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), Chapter 3.
-/

open Set Real

namespace ContinuousSystem

variable {E U Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Contracting in a distance**: under the input `u`, for every `t₀` and `t₁ > t₀`, any two right
trajectories that stay in `C` on `[t₀, t₁]` satisfy `d(x(t), y(t)) ≤ e^{-c(t - t₀)} d(x(t₀), y(t₀))`
on `[t₀, t₁]`.  The rate `c` is any real; `c > 0` is contraction, `c = 0` nonexpansiveness. -/
@[blueprint "def:continuousSystem-isContractingOn"
  (title := "Contracting system")
  (statement := /-- Let $d$ be a distance on the state space, $C$ a set of states, and
    $c \in \mathbb{R}$.  The system is \emph{contracting with rate $c$ in $d$ on $C$} under the
    input $u$ if, for every $t_0$ and $t_1 > t_0$, any two right trajectories $x, y$
    (\cref{def:continuousSystem-isRightTrajectoryOn}) with values in $C$ on $[t_0, t_1]$ satisfy
    \[ d\bigl(x(t), y(t)\bigr) \le e^{-c (t - t_0)} \, d\bigl(x(t_0), y(t_0)\bigr),
      \qquad t \in [t_0, t_1]. \]
    For $c > 0$ trajectories approach exponentially; for $c = 0$ the system is nonexpansive. -/)]
def IsContractingOn (s : ContinuousSystem E U Y) (u : ℝ → U) (C : Set E) (d : E → E → ℝ)
    (c : ℝ) : Prop :=
  ∀ t₀ : ℝ, ∀ t₁ > t₀, ∀ x y : ℝ → E,
    s.IsRightTrajectoryOn u x (Icc t₀ t₁) → s.IsRightTrajectoryOn u y (Icc t₀ t₁) →
      (∀ t ∈ Icc t₀ t₁, x t ∈ C) → (∀ t ∈ Icc t₀ t₁, y t ∈ C) →
        ∀ t ∈ Icc t₀ t₁, d (x t) (y t) ≤ exp (-c * (t - t₀)) * d (x t₀) (y t₀)

/-- **Infinitesimally contracting**: contracting with rate `c` in the norm of the state space,
`‖x(t) - y(t)‖ ≤ e^{-c(t - t₀)} ‖x(t₀) - y(t₀)‖`.  The book defines it on the vector field,
`osL(F(t, ·, u(t))) ≤ -c`; that condition is a theorem here. -/
@[blueprint "def:continuousSystem-isInfinitesimallyContractingOn"
  (title := "Infinitesimally contracting system")
  (statement := /-- The system is \emph{infinitesimally contracting with rate $c$ on $C$} if it
    is contracting (\cref{def:continuousSystem-isContractingOn}) in the distance
    $d(x, y) = \|x - y\|$ of the norm of the state space.  The book defines it by the
    condition $\operatorname{osL}(F(t, \cdot, u(t))) \le -c$ on the vector field, which
    characterizes it.

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0), Chapter 3. -/)]
abbrev IsInfinitesimallyContractingOn (s : ContinuousSystem E U Y) (u : ℝ → U) (C : Set E)
    (c : ℝ) : Prop :=
  s.IsContractingOn u C (fun x y => ‖x - y‖) c

end ContinuousSystem

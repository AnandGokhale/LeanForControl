import LeanForControl.Contraction.Systems.Defs
import LeanForControl.Contraction.Norms.OneSidedLipschitz
import Architect

/-!
# The contraction bound for one-sided Lipschitz systems

A system whose vector field is one-sided Lipschitz with `-c` on a set `C`, in any norm, is
infinitesimally contracting with rate `c` on `C`:

* `ContinuousSystem.isInfinitesimallyContractingOn_of_oneSidedLipschitz` —
  `osL(F(t, ·, u(t))) ≤ -c` on `C` for all `t` gives `IsInfinitesimallyContractingOn s u C c`;
* `ContinuousSystem.IsInfinitesimallyContractingOn.eqOn` — forward uniqueness: in a contracting
  system, trajectories in `C` from the same point agree.

The distance bound for a time-varying rate `b(t)` is a statement about curves,
`norm_sub_le_exp_integral_of_oneSidedLipschitz` (`Contraction/Norms/OneSidedLipschitz.lean`).

Reference: F. Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), Chapter 3.
-/

open Set Real
open scoped LogNorm

namespace ContinuousSystem

variable {E U Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : ContinuousSystem E U Y} {u : ℝ → U} {C : Set E} {c : ℝ}

/-- **The contraction bound**: if `osL(F(t, ·, u(t))) ≤ -c` on `C` for every `t`, the system is
infinitesimally contracting with rate `c` on `C`. -/
@[blueprint "thm:continuousSystem-isInfinitesimallyContractingOn-of-oneSidedLipschitz"
  (title := "Contraction bound")
  (statement := /-- If the vector field (\cref{def:continuousSystem-vectorField}) satisfies
    $\operatorname{osL}(F(t, \cdot, u(t))) \le -c$ on $C$ (\cref{def:oneSidedLipschitz}) for every
    $t$, the system is infinitesimally contracting with rate $c$ on $C$
    (\cref{def:continuousSystem-isInfinitesimallyContractingOn}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Chapter 3. -/)
  (proof := /-- \cref{thm:norm-sub-le-exp-integral-of-oneSidedLipschitz} with $b = -c$, applied to
    two right trajectories (\cref{def:continuousSystem-isRightTrajectoryOn}). -/)]
theorem isInfinitesimallyContractingOn_of_oneSidedLipschitz
    (hF : ∀ t, osL (s.vectorField u t) on C ≤ ((-c : ℝ) : EReal)) :
    s.IsInfinitesimallyContractingOn u C c := by
  sorry

/-- **Forward uniqueness**: in a system infinitesimally contracting on `C`, two right trajectories
in `C` that start at the same point agree. -/
@[blueprint "thm:continuousSystem-isInfinitesimallyContractingOn-eqOn"
  (title := "Forward uniqueness for contracting systems")
  (statement := /-- If the system is infinitesimally contracting on $C$
    (\cref{def:continuousSystem-isInfinitesimallyContractingOn}), with any rate, and $x, y$ are
    right trajectories on $[t_0, t_1]$ with values in $C$ and $x(t_0) = y(t_0)$, then $x = y$ on
    $[t_0, t_1]$. -/)
  (proof := /-- The contraction estimate bounds $\|x(t) - y(t)\|$ by a multiple of
    $\|x(t_0) - y(t_0)\| = 0$. -/)]
theorem IsInfinitesimallyContractingOn.eqOn (h : s.IsInfinitesimallyContractingOn u C c)
    {x y : ℝ → E} {t₀ t₁ : ℝ}
    (hx : s.IsRightTrajectoryOn u x (Icc t₀ t₁)) (hy : s.IsRightTrajectoryOn u y (Icc t₀ t₁))
    (hxC : ∀ t ∈ Icc t₀ t₁, x t ∈ C) (hyC : ∀ t ∈ Icc t₀ t₁, y t ∈ C) (h₀ : x t₀ = y t₀) :
    EqOn x y (Icc t₀ t₁) := by
  sorry

end ContinuousSystem

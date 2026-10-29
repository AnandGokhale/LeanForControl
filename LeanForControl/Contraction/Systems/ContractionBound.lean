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
  system, trajectories in `C` from the same point agree;
  `ContinuousSystem.IsInfinitesimallyContractingOn.hasUniqueSolutions` — on the whole space, the
  system has unique solutions.

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
  intro t₀ t₁ _ x y hx hy hxC hyC t ht
  -- a derivative within the window, at a point before its right end, is a right derivative
  have hright {z : ℝ → E} (hz : s.IsRightTrajectoryOn u z (Icc t₀ t₁)) (r : ℝ)
      (hr : r ∈ Ico t₀ t₁) : HasDerivWithinAt z (s.vectorField u r (z r)) (Ici r) r :=
    (hz.2 r (Ico_subset_Icc_self hr)).mono_of_mem_nhdsWithin
      (Filter.inter_mem (Icc_mem_nhdsGE_of_mem hr) self_mem_nhdsWithin)
  -- the distance between the curves with the constant rate `b = -c`
  have hb := norm_sub_le_exp_integral_of_oneSidedLipschitz (v := s.vectorField u)
    (b := fun _ => -c) continuous_const (fun r _ => hF r) hx.1 (hright hx) hy.1 (hright hy)
    (fun r hr => hxC r (Ico_subset_Icc_self hr)) (fun r hr => hyC r (Ico_subset_Icc_self hr)) t ht
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm (t - t₀)] at hb
  beta_reduce
  exact hb

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
  intro t ht
  rcases lt_or_ge t₀ t₁ with h01 | h10
  · -- the contraction estimate, from `‖x t₀ - y t₀‖ = 0`
    have hb := h t₀ t₁ h01 x y hx hy hxC hyC t ht
    beta_reduce at hb
    rw [h₀, sub_self, norm_zero, mul_zero] at hb
    exact sub_eq_zero.1 (norm_le_zero_iff.1 hb)
  · -- a window with `t₁ ≤ t₀` contains only `t₀`
    rw [le_antisymm (ht.2.trans h10) ht.1]
    exact h₀

/-- **Contracting systems have unique solutions**: a system infinitesimally contracting on the whole
space, with any rate, has unique solutions. -/
@[blueprint "thm:continuousSystem-isInfinitesimallyContractingOn-hasUniqueSolutions"
  (title := "Contracting systems have unique solutions")
  (statement := /-- If the system is infinitesimally contracting on the whole state space
    (\cref{def:continuousSystem-isInfinitesimallyContractingOn}), with any rate, it has unique
    solutions (\cref{def:continuousSystem-hasUniqueSolutions}). -/)
  (proof := /-- Trajectories are right trajectories
    (\cref{lem:continuousSystem-isTrajectoryOn-isRightTrajectoryOn}); apply
    \cref{thm:continuousSystem-isInfinitesimallyContractingOn-eqOn} with $C$ the whole space. -/)]
theorem IsInfinitesimallyContractingOn.hasUniqueSolutions
    (h : s.IsInfinitesimallyContractingOn u univ c) : s.HasUniqueSolutions u :=
  fun _ _ _ _ hx hy h₀ =>
    h.eqOn hx.isRightTrajectoryOn hy.isRightTrajectoryOn (fun _ _ => mem_univ _)
      (fun _ _ => mem_univ _) h₀

end ContinuousSystem

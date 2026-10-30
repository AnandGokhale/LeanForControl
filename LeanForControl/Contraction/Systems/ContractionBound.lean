import LeanForControl.Contraction.Systems.Defs
import LeanForControl.Contraction.Norms.OneSidedLipschitz
import Architect

/-!
# The contraction bound for one-sided Lipschitz systems

A system whose vector field is one-sided Lipschitz with `-c` on a set `C`, in any norm, is
infinitesimally contracting with rate `c` on `C`:

* `ContinuousSystem.IsContractingOn.of_oneSidedLipschitz_conj` — the same in coordinates
  `z = e x`: `osL ≤ -c` for the field in those coordinates gives contraction in `‖e (x - y)‖`;
* `ContinuousSystem.IsInfinitesimallyContractingOn.of_oneSidedLipschitz` —
  `osL(F(t, ·, u(t))) ≤ -c` on `C` for all `t` gives `IsInfinitesimallyContractingOn s u C c`;
* `ContinuousSystem.IsInfinitesimallyContractingOn.of_logNorm` — the Jacobian form:
  `μ(DF(t, x)) ≤ -c` on an open convex `C`;
* `ContinuousSystem.IsInfinitesimallyContractingOn.of_affine` — `F(t, x, u(t)) = A x + b(t)` with
  `μ(A) ≤ -c`;
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

/-- **The contraction bound in a change of coordinates**: for `e : E ≃L[ℝ] F`, if the vector field
in the coordinates `z = e x`, `z ↦ e (F(t, e⁻¹ z, u(t)))`, has `osL ≤ -c` on `e '' C` for every
`t`, the system is contracting with rate `c` on `C` in the distance `‖e (x - y)‖`. -/
@[blueprint "thm:continuousSystem-isContractingOn-of-oneSidedLipschitz-conj"
  (title := "Contraction bound in a change of coordinates")
  (statement := /-- Let $e : E \to F$ be an invertible bounded linear map.  If
    $\operatorname{osL}\bigl(z \mapsto e\, F(t, e^{-1} z, u(t))\bigr) \le -c$ on $e(C)$
    (\cref{def:oneSidedLipschitz}) for every $t$, the system is contracting with rate $c$ on $C$
    (\cref{def:continuousSystem-isContractingOn}) in the distance $\|e(x - y)\|$. -/)
  (proof := /-- If $x$ is a right trajectory (\cref{def:continuousSystem-isRightTrajectoryOn}),
    $e \circ x$ has right derivative $e\, F(t, e^{-1}(e\, x(t)), u(t))$; apply
    \cref{thm:norm-sub-le-exp-integral-of-oneSidedLipschitz} with $b = -c$ to $e \circ x$ and
    $e \circ y$. -/)]
theorem IsContractingOn.of_oneSidedLipschitz_conj {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : E ≃L[ℝ] F)
    (hF : ∀ t, osL (fun z => e (s.vectorField u t (e.symm z))) on (e '' C) ≤ ((-c : ℝ) : EReal)) :
    s.IsContractingOn u C (fun x y => ‖e (x - y)‖) c := by
  intro t₀ t₁ _ x y hx hy hxC hyC t ht
  -- in the coordinates `e`, a right trajectory follows the conjugate field
  have hright {z : ℝ → E} (hz : s.IsRightTrajectoryOn u z (Icc t₀ t₁)) (r : ℝ)
      (hr : r ∈ Ico t₀ t₁) :
      HasDerivWithinAt (e ∘ z) (e (s.vectorField u r (e.symm (e (z r))))) (Ici r) r := by
    rw [e.symm_apply_apply]
    exact e.hasFDerivAt.comp_hasDerivWithinAt r (hz.hasDerivWithinAt_Ici hr)
  -- the distance between `e ∘ x` and `e ∘ y` with the constant rate `b = -c`
  have hb := norm_sub_le_exp_integral_of_oneSidedLipschitz
    (v := fun r z => e (s.vectorField u r (e.symm z))) (b := fun _ => -c) continuous_const
    (fun r _ => hF r) (e.continuous.comp_continuousOn hx.1) (hright hx)
    (e.continuous.comp_continuousOn hy.1) (hright hy)
    (fun r hr => mem_image_of_mem e (hxC r (Ico_subset_Icc_self hr)))
    (fun r hr => mem_image_of_mem e (hyC r (Ico_subset_Icc_self hr))) t ht
  simp only [Function.comp_apply, ← map_sub, intervalIntegral.integral_const, smul_eq_mul] at hb
  rw [mul_comm (t - t₀)] at hb
  exact hb

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
  (proof := /-- \cref{thm:continuousSystem-isContractingOn-of-oneSidedLipschitz-conj} with $e$ the
    identity. -/)]
theorem IsInfinitesimallyContractingOn.of_oneSidedLipschitz
    (hF : ∀ t, osL (s.vectorField u t) on C ≤ ((-c : ℝ) : EReal)) :
    s.IsInfinitesimallyContractingOn u C c := by
  simpa using IsContractingOn.of_oneSidedLipschitz_conj (ContinuousLinearEquiv.refl ℝ E)
    (by simpa using hF)

/-- **The Jacobian form of the contraction bound**: on an open convex `C`, if the vector field has
derivative `DF t x` with `μ(DF t x) ≤ -c` at every `x ∈ C`, the system is infinitesimally
contracting with rate `c` on `C`. -/
@[blueprint "thm:continuousSystem-isInfinitesimallyContractingOn-of-logNorm"
  (title := "Contraction from the log norm of the Jacobian")
  (statement := /-- Let $C$ be open and convex.  If $x \mapsto F(t, x, u(t))$ has derivative
    $DF(t, x)$ with $\mu(DF(t, x)) \le -c$ (\cref{def:logNorm}) for every $t$ and $x \in C$, the
    system is infinitesimally contracting with rate $c$ on $C$
    (\cref{def:continuousSystem-isInfinitesimallyContractingOn}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Chapter 3. -/)
  (proof := /-- The Jacobian test (\cref{thm:oneSidedLipschitz-eq-iSup-logNorm}) gives
    $\operatorname{osL}(F(t, \cdot, u(t))) \le -c$ on $C$;
    apply \cref{thm:continuousSystem-isInfinitesimallyContractingOn-of-oneSidedLipschitz}. -/)]
theorem IsInfinitesimallyContractingOn.of_logNorm [Nontrivial E] {DF : ℝ → E → E →L[ℝ] E}
    (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hF : ∀ t, ∀ x ∈ C, HasFDerivAt (s.vectorField u t) (DF t x) x)
    (hμ : ∀ t, ∀ x ∈ C, μ (DF t x) ≤ -c) :
    s.IsInfinitesimallyContractingOn u C c :=
  -- the Jacobian test turns the log-norm bound into the one-sided Lipschitz bound
  .of_oneSidedLipschitz fun t => (oneSidedLipschitz_le_iff_logNorm_le hCo hCc (hF t) _).2 (hμ t)

/-- **Affine systems**: if `F(t, x, u(t)) = A x + b(t)` with `μ(A) ≤ -c`, the system is
infinitesimally contracting with rate `c` on the whole space. -/
@[blueprint "thm:continuousSystem-isInfinitesimallyContractingOn-of-affine"
  (title := "Contracting affine systems")
  (statement := /-- If the vector field is affine, $F(t, x, u(t)) = A x + b(t)$ for a bounded
    operator $A$, and $\mu(A) \le -c$ (\cref{def:logNorm}), the system is infinitesimally
    contracting with rate $c$ on the whole space
    (\cref{def:continuousSystem-isInfinitesimallyContractingOn}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Chapter 3. -/)
  (proof := /-- $\operatorname{osL}(x \mapsto A x + b(t)) = \mu(A)$
    (\cref{thm:oneSidedLipschitz-affine}); apply
    \cref{thm:continuousSystem-isInfinitesimallyContractingOn-of-oneSidedLipschitz}. -/)]
theorem IsInfinitesimallyContractingOn.of_affine [Nontrivial E] (A : E →L[ℝ] E) (b : ℝ → E)
    (hF : ∀ t x, s.vectorField u t x = A x + b t) (hA : μ A ≤ -c) :
    s.IsInfinitesimallyContractingOn u univ c :=
  -- `osL(x ↦ A x + b(t)) = μ(A)`
  .of_oneSidedLipschitz fun t => by
    rw [show s.vectorField u t = fun x => A x + b t from funext (hF t), oneSidedLipschitz_affine]
    exact EReal.coe_le_coe_iff.2 hA

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

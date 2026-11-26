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
  `osL(F(t, ·, u(t))) ≤ -c` on `C` for almost every `t` gives
  `IsInfinitesimallyContractingOn s u C c`;
* `ContinuousSystem.IsInfinitesimallyContractingOn.of_logNorm` — the Jacobian form:
  `μ(DF(t, x)) ≤ -c` on an open convex `C`, for almost every `t`;
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

variable {E U Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {s : ContinuousSystem E U Y} {u : ℝ → U} {C : Set E} {c : ℝ}

/-- **The contraction bound in a change of coordinates**: for `e : E ≃L[ℝ] F`, if the vector field
in the coordinates `z = e x`, `z ↦ e (F(t, e⁻¹ z, u(t)))`, has `osL ≤ -c` on `e '' C` for almost
every `t`, the system is contracting with rate `c` on `C` in the distance `‖e (x - y)‖`. -/
@[blueprint "thm:continuousSystem-isContractingOn-of-oneSidedLipschitz-conj"
  (title := "Contraction bound in a change of coordinates")
  (statement := /-- Let $e : E \to F$ be an invertible bounded linear map.  If
    $\operatorname{osL}\bigl(z \mapsto e\, F(t, e^{-1} z, u(t))\bigr) \le -c$ on $e(C)$
    (\cref{def:oneSidedLipschitz}) for almost every $t$, the system is contracting with rate $c$
    on $C$ (\cref{def:continuousSystem-isContractingOn}) in the distance $\|e(x - y)\|$. -/)
  (proof := /-- A trajectory $x$ on $[t_0, t_1]$ (\cref{def:continuousSystem-isTrajectoryOn}) is
    absolutely continuous
    (\cref{lem:continuousSystem-isTrajectoryOn-absolutelyContinuousOnInterval}) with derivative
    $F(t, x(t), u(t))$ at almost every $t$
    (\cref{lem:continuousSystem-isTrajectoryOn-ae-hasDerivAt}), so $e \circ x$ is absolutely
    continuous with derivative $e\, F(t, e^{-1}(e\, x(t)), u(t))$ at almost every $t$; apply
    \cref{thm:norm-sub-le-exp-integral-of-oneSidedLipschitz} with $b = -c$ to $e \circ x$ and
    $e \circ y$. -/)]
theorem IsContractingOn.of_oneSidedLipschitz_conj {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : E ≃L[ℝ] F)
    (hF : ∀ᵐ t, osL (fun z => e (s.vectorField u t (e.symm z))) on (e '' C) ≤ ((-c : ℝ) : EReal)) :
    s.IsContractingOn u C (fun x y => ‖e (x - y)‖) c := by
  intro t₀ t₁ h01 x y hx hy hxC hyC t ht
  -- in the coordinates `e`, a trajectory is absolutely continuous and follows the conjugate field
  -- almost everywhere
  have hconj {z : ℝ → E} (hz : s.IsTrajectoryOn u z (Icc t₀ t₁)) :
      AbsolutelyContinuousOnInterval (e ∘ z) t₀ t₁ ∧
        ∀ᵐ r, r ∈ Ioo t₀ t₁ → HasDerivAt (e ∘ z) (e (s.vectorField u r (e.symm (e (z r))))) r := by
    refine ⟨(e : E →L[ℝ] F).lipschitzWith.comp_absolutelyContinuousOnInterval
      (hz.absolutelyContinuousOnInterval (uIcc_of_le h01.le).subset), ?_⟩
    filter_upwards [hz.ae_hasDerivAt] with r hr hr'
    rw [e.symm_apply_apply]
    exact e.hasFDerivAt.comp_hasDerivAt r (hr (by rwa [interior_Icc]))
  -- the distance between `e ∘ x` and `e ∘ y` with the constant rate `b = -c`
  have hb := norm_sub_le_exp_integral_of_oneSidedLipschitz
    (v := fun r z => e (s.vectorField u r (e.symm z))) (b := fun _ => -c) intervalIntegrable_const
    (hF.mono fun _ hr _ => hr) (hconj hx).1 (hconj hx).2 (hconj hy).1 (hconj hy).2
    (.of_forall fun r hr => mem_image_of_mem e (hxC r (Ioo_subset_Icc_self hr)))
    (.of_forall fun r hr => mem_image_of_mem e (hyC r (Ioo_subset_Icc_self hr))) t ht
  simp only [Function.comp_apply, ← map_sub, intervalIntegral.integral_const, smul_eq_mul] at hb
  rw [mul_comm (t - t₀)] at hb
  exact hb

/-- **The contraction bound**: if `osL(F(t, ·, u(t))) ≤ -c` on `C` for almost every `t`, the system
is infinitesimally contracting with rate `c` on `C`. -/
@[blueprint "thm:continuousSystem-isInfinitesimallyContractingOn-of-oneSidedLipschitz"
  (title := "Contraction bound")
  (statement := /-- If the vector field (\cref{def:continuousSystem-vectorField}) satisfies
    $\operatorname{osL}(F(t, \cdot, u(t))) \le -c$ on $C$ (\cref{def:oneSidedLipschitz}) for
    almost every $t$, the system is infinitesimally contracting with rate $c$ on $C$
    (\cref{def:continuousSystem-isInfinitesimallyContractingOn}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Chapter 3. -/)
  (proof := /-- \cref{thm:continuousSystem-isContractingOn-of-oneSidedLipschitz-conj} with $e$ the
    identity. -/)]
theorem IsInfinitesimallyContractingOn.of_oneSidedLipschitz
    (hF : ∀ᵐ t, osL (s.vectorField u t) on C ≤ ((-c : ℝ) : EReal)) :
    s.IsInfinitesimallyContractingOn u C c := by
  simpa using IsContractingOn.of_oneSidedLipschitz_conj (ContinuousLinearEquiv.refl ℝ E)
    (by
      simp only [ContinuousLinearEquiv.refl_apply, ContinuousLinearEquiv.coe_refl', image_id_eq,
        id_eq, ContinuousLinearEquiv.refl_symm, vectorField_apply, EReal.coe_neg]
      exact hF)

/-- **The Jacobian form of the contraction bound**: on an open convex `C`, if for almost every `t`
the vector field has derivative `DF t x` with `μ(DF t x) ≤ -c` at every `x ∈ C`, the system is
infinitesimally contracting with rate `c` on `C`. -/
@[blueprint "thm:continuousSystem-isInfinitesimallyContractingOn-of-logNorm"
  (title := "Contraction from the log norm of the Jacobian")
  (statement := /-- Let $C$ be open and convex.  If, for almost every $t$, $x \mapsto F(t, x, u(t))$
    has derivative $DF(t, x)$ with $\mu(DF(t, x)) \le -c$ (\cref{def:logNorm}) at every $x \in C$,
    the system is infinitesimally contracting with rate $c$ on $C$
    (\cref{def:continuousSystem-isInfinitesimallyContractingOn}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Chapter 3. -/)
  (proof := /-- The Jacobian test (\cref{thm:oneSidedLipschitz-eq-iSup-logNorm}) gives
    $\operatorname{osL}(F(t, \cdot, u(t))) \le -c$ on $C$ for almost every $t$;
    apply \cref{thm:continuousSystem-isInfinitesimallyContractingOn-of-oneSidedLipschitz}. -/)]
theorem IsInfinitesimallyContractingOn.of_logNorm [Nontrivial E] {DF : ℝ → E → E →L[ℝ] E}
    (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hF : ∀ᵐ t, ∀ x ∈ C, HasFDerivAt (s.vectorField u t) (DF t x) x)
    (hμ : ∀ᵐ t, ∀ x ∈ C, μ (DF t x) ≤ -c) :
    s.IsInfinitesimallyContractingOn u C c := by
  -- the Jacobian test turns the log-norm bound into the one-sided Lipschitz bound
  refine .of_oneSidedLipschitz ?_
  filter_upwards [hF, hμ] with t hFt hμt
  exact (oneSidedLipschitz_le_iff_logNorm_le hCo hCc hFt _).2 hμt

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
  .of_oneSidedLipschitz <| .of_forall fun t => by
    rw [show s.vectorField u t = fun x => A x + b t from funext (hF t), oneSidedLipschitz_affine]
    exact EReal.coe_le_coe_iff.2 hA

/-- **Forward uniqueness**: in a system infinitesimally contracting on `C`, two trajectories
in `C` that start at the same point agree. -/
@[blueprint "thm:continuousSystem-isInfinitesimallyContractingOn-eqOn"
  (title := "Forward uniqueness for contracting systems")
  (statement := /-- If the system is infinitesimally contracting on $C$
    (\cref{def:continuousSystem-isInfinitesimallyContractingOn}), with any rate, and $x, y$ are
    trajectories (\cref{def:continuousSystem-isTrajectoryOn}) on $[t_0, t_1]$ with values in $C$
    and $x(t_0) = y(t_0)$, then $x = y$ on $[t_0, t_1]$. -/)
  (proof := /-- The contraction estimate bounds $\|x(t) - y(t)\|$ by a multiple of
    $\|x(t_0) - y(t_0)\| = 0$. -/)]
theorem IsInfinitesimallyContractingOn.eqOn (h : s.IsInfinitesimallyContractingOn u C c)
    {x y : ℝ → E} {t₀ t₁ : ℝ}
    (hx : s.IsTrajectoryOn u x (Icc t₀ t₁)) (hy : s.IsTrajectoryOn u y (Icc t₀ t₁))
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
  (proof := /-- Apply \cref{thm:continuousSystem-isInfinitesimallyContractingOn-eqOn} with $C$ the
    whole space. -/)]
theorem IsInfinitesimallyContractingOn.hasUniqueSolutions
    (h : s.IsInfinitesimallyContractingOn u univ c) : s.HasUniqueSolutions u :=
  fun _ _ _ _ hx hy h₀ => h.eqOn hx hy (fun _ _ => mem_univ _) (fun _ _ => mem_univ _) h₀

end ContinuousSystem

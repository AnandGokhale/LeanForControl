import LeanForControl.Contraction.Norms.CurveNormDerivative
import Mathlib.Analysis.Calculus.Deriv.Inv
import Architect

/-!
# `Contraction.Norms.LogNorm` — the logarithmic norm and Lumer's property

* `logNorm A` — the logarithmic norm `μ(A) = lim_{h → 0⁺} (‖I + h A‖ - 1) / h` of a bounded
  operator: the right derivative of the operator norm at the identity in the direction `A`.
* `RegularPairing.pairing_le_logNorm` — Lumer's inequality, `⟦A x, x⟧ ≤ μ(A) ‖x‖²`.
* `RegularPairing.logNorm_le` — conversely, `⟦A x, x⟧ ≤ c ‖x‖²` for all `x` implies `μ(A) ≤ c`.

Together they say that `μ(A)` is the least `c` with `⟦A x, x⟧ ≤ c ‖x‖²` for all `x`: Lumer's
equality `μ(A) = sup_{x ≠ 0} ⟦A x, x⟧ / ‖x‖²`, for every regular pairing.

The basic properties of `μ` then follow from those of a pairing, through the regular pairing of the
norm: subadditivity, positive homogeneity, the translation property `μ(A + c I) = μ(A) + c`, the
norm of difference property `|μ(A) - μ(B)| ≤ ‖A - B‖`, and the product property
`-μ(A) ‖x‖ ≤ ‖A x‖`.  A change of coordinates that preserves the norm preserves the log norm
(`logNorm_conj`).

References: F. Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), equation (2.22),
Remark 2.9, Lemma 2.10 and Definition 2.17; A. V. Proskurnikov and F. Bullo, *Regular Pairings for
Nonquadratic Lyapunov Functions and Contraction Analysis*, SIAM J. Control Optim. 64(1):496–521
(2026), doi:10.1137/24M1689685, Definitions 2.1 and 3.1 and Theorem 3.5.
-/

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The logarithmic norm** of a bounded operator, `μ(A) = lim_{h → 0⁺} (‖I + h A‖ - 1) / h`: the
right derivative of the operator norm at the identity in the direction `A`. -/
@[blueprint "def:logNorm"
  (title := "Logarithmic norm")
  (statement := /-- The \emph{logarithmic norm} of a bounded linear operator $A$ on a real normed
    space is
    \[ \mu(A) = \lim_{h \to 0^+} \frac{\|I + h A\| - 1}{h}, \]
    the right derivative of the induced norm at $I$ in the direction $A$; the limit exists by
    \cref{lem:hasDerivWithinAt-norm-add-smul}.

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0), equation (2.22)
    and Remark 2.9. -/)]
noncomputable def logNorm (A : E →L[ℝ] E) : ℝ :=
  derivWithin (fun h : ℝ => ‖(1 : E →L[ℝ] E) + h • A‖) (Ioi 0) 0

namespace RegularPairing

/-- **Lumer's inequality**: `⟦A x, x⟧ ≤ μ(A) ‖x‖²`, for every regular pairing. -/
@[blueprint "thm:regularPairing-pairing-le-logNorm"
  (title := "Lumer's inequality")
  (statement := /-- For a regular pairing (\cref{def:regularPairing}) and a bounded linear operator
    $A$, $\pair{A x}{x} \le \mu(A) \|x\|^2$ for all $x$ (\cref{def:logNorm}).

    Reference: Proskurnikov and Bullo, SIAM J. Control Optim. (2026), Theorem 3.5 (iv). -/)
  (proof := /-- By Deimling's inequality (\cref{thm:regularPairing-le-ofNorm}),
    $\pair{Ax}{x}$ is at most $\|x\|$ times the right derivative of $h \mapsto \|x + h A x\|$
    at $0$.  That function lies below $h \mapsto \|I + h A\| \, \|x\|$ and touches it at $0$, so
    its right derivative is at most $\mu(A) \|x\|$
    (\cref{lem:hasDerivWithinAt-le-of-le-of-eq}). -/)]
theorem pairing_le_logNorm (p : RegularPairing E) (A : E →L[ℝ] E) (x : E) :
    p (A x) x ≤ logNorm A * ‖x‖ ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  -- `‖x + h A x‖ ≤ ‖I + h A‖ ‖x‖`, with equality at `h = 0`
  have hle := (hasDerivWithinAt_norm_add_smul (A x) x).le_of_le_of_eq
    ((hasDerivWithinAt_norm_add_smul A 1).mul_const ‖x‖) (by simp)
    (Eventually.of_forall fun h => by simpa using ((1 : E →L[ℝ] E) + h • A).le_opNorm x)
  calc p (A x) x ≤ ofNorm E (A x) x := p.le_ofNorm _ _
    _ ≤ ‖x‖ * (logNorm A * ‖x‖) := by
        rw [ofNorm_apply]
        exact mul_le_mul_of_nonneg_left hle (norm_nonneg x)
    _ = logNorm A * ‖x‖ ^ 2 := by ring

/-- **The converse of Lumer's inequality**: if `⟦A x, x⟧ ≤ c ‖x‖²` for all `x`, then `μ(A) ≤ c`. -/
@[blueprint "thm:regularPairing-logNorm-le"
  (title := "Converse of Lumer's inequality")
  (statement := /-- For a regular pairing (\cref{def:regularPairing}) on a nontrivial space, if
    $\pair{A x}{x} \le c \|x\|^2$ for all $x$, then $\mu(A) \le c$ (\cref{def:logNorm}).  With
    \cref{thm:regularPairing-pairing-le-logNorm}, this is Lumer's equality
    $\mu(A) = \sup_{x \ne 0} \pair{Ax}{x} / \|x\|^2$.

    Reference: Proskurnikov and Bullo, SIAM J. Control Optim. (2026), Theorem 3.5 (vii). -/)
  (proof := /-- Fix $x$, $h > 0$ with $hc < 1$, and $y = x + h A x$.  The right derivative of
    $s \mapsto \|y - s A x\|$ at $0$ is at most its difference quotient at $s = h$, which is
    $(\|x\| - \|y\|)/h$; by the lower Deimling inequality
    (\cref{thm:regularPairing-le-ofNorm}) this gives
    $\|y\|(\|y\| - \|x\|) \le h \pair{A x}{y}$.  Since $A x = A y - h A^2 x$, subadditivity and
    Cauchy--Schwarz give $\pair{Ax}{y} \le c \|y\|^2 + h \|A\|^2 \|x\| \|y\|$.  Hence
    $(1 - hc)\|y\| \le (1 + h^2 \|A\|^2)\|x\|$, that is,
    $\|I + h A\| \le (1 + h^2 \|A\|^2)/(1 - h c)$, a function equal to $1$ at $h = 0$ with right
    derivative $c$ there (\cref{lem:hasDerivWithinAt-le-of-le-of-eq}). -/)]
theorem logNorm_le [Nontrivial E] (p : RegularPairing E) {A : E →L[ℝ] E} {c : ℝ}
    (hc : ∀ x, p (A x) x ≤ c * ‖x‖ ^ 2) : logNorm A ≤ c := by
  set K := ‖A‖ ^ 2
  -- for small `h > 0`, `‖I + h A‖ ≤ (1 + h² ‖A‖²) / (1 - h c)`, which has right derivative `c`
  have hg : HasDerivWithinAt (fun h : ℝ => (1 + h * h * K) / (1 - h * c)) c (Ioi 0) 0 :=
    (HasDerivAt.fun_div
      ((((hasDerivAt_id' (0 : ℝ)).mul (hasDerivAt_id' 0)).mul_const K).const_add 1)
      (((hasDerivAt_id' (0 : ℝ)).mul_const c).const_sub 1) (by norm_num)).hasDerivWithinAt
      |>.congr_deriv (by simp)
  have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), h * c < 1 := nhdsWithin_le_nhds
    (((continuous_id.mul continuous_const).tendsto' 0 0 (by simp)).eventually (gt_mem_nhds one_pos))
  refine (hasDerivWithinAt_norm_add_smul A 1).le_of_le_of_eq hg (by simp) ?_
  filter_upwards [self_mem_nhdsWithin, hsmall] with h (hh : 0 < h) hhc
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (by positivity) (by linarith))
    fun x => ?_
  set y := x + h • A x with hy
  rw [show ((1 : E →L[ℝ] E) + h • A) x = y by simp [hy], div_mul_eq_mul_div,
    le_div_iff₀ (by linarith)]
  -- `‖y‖ (‖y‖ - ‖x‖) ≤ h ⟦A x, y⟧`: the slope of `s ↦ ‖y - s A x‖` and the lower Deimling bound
  have hslope := derivWithin_norm_add_smul_le (-(A x)) y hh
  rw [show y + h • -(A x) = x by simp [hy], le_div_iff₀ hh] at hslope
  have hdeim := p.neg_ofNorm_neg_le (A x) y
  rw [ofNorm_apply] at hdeim
  -- `⟦A x, y⟧ ≤ c ‖y‖² + h ‖A‖² ‖x‖ ‖y‖`, from `A x = A y - h A² x`
  have hAx : A x = A y + (-h) • A (A x) := by
    rw [hy, map_add, map_smul]
    module
  have hpair : p (A x) y ≤ c * ‖y‖ ^ 2 + ‖(-h) • A (A x)‖ * ‖y‖ := by
    conv_lhs => rw [hAx]
    exact (p.add_left_le _ _ _).trans (add_le_add (hc y) (p.le_norm_mul_norm _ _))
  have hA2 : ‖(-h) • A (A x)‖ ≤ h * (K * ‖x‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hh]
    gcongr
    calc ‖A (A x)‖ ≤ ‖A‖ * ‖A x‖ := A.le_opNorm _
      _ ≤ ‖A‖ * (‖A‖ * ‖x‖) := by gcongr; exact A.le_opNorm x
      _ = K * ‖x‖ := by ring
  rcases (norm_nonneg y).eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]
    positivity
  have key : ‖y‖ * ((1 - h * c) * ‖y‖) ≤ ‖y‖ * ((1 + h * h * K) * ‖x‖) := by
    nlinarith [mul_le_mul_of_nonneg_left hslope (norm_nonneg y),
      mul_le_mul_of_nonneg_left hdeim hh.le, mul_le_mul_of_nonneg_left hpair hh.le,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA2 (norm_nonneg y)) hh.le]
  linarith [le_of_mul_le_mul_left key h0]

end RegularPairing

/-! ### Basic properties -/

open RegularPairing

@[simp] lemma logNorm_zero : logNorm (0 : E →L[ℝ] E) = 0 := by
  simp [logNorm]

section Properties

variable [Nontrivial E]

/-- **Subadditivity of the log norm**, `μ(A + B) ≤ μ(A) + μ(B)`. -/
@[blueprint "lem:logNorm-add-le"
  (title := "Subadditivity of the log norm")
  (latexEnv := "lemma")
  (statement := /-- $\mu(A + B) \le \mu(A) + \mu(B)$ (\cref{def:logNorm}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0), Lemma 2.10,
    (2.29b). -/)
  (proof := /-- For the regular pairing of the norm, subadditivity and Lumer's inequality give
    $\pair{(A + B)x}{x} \le \pair{Ax}{x} + \pair{Bx}{x} \le (\mu(A) + \mu(B))\|x\|^2$; apply
    \cref{thm:regularPairing-logNorm-le}. -/)]
theorem logNorm_add_le (A B : E →L[ℝ] E) : logNorm (A + B) ≤ logNorm A + logNorm B :=
  RegularPairing.logNorm_le (ofNorm E) fun x => by
    rw [ContinuousLinearMap.add_apply, add_mul]
    exact ((ofNorm E).add_left_le _ _ _).trans (add_le_add
      ((ofNorm E).pairing_le_logNorm A x) ((ofNorm E).pairing_le_logNorm B x))

/-- **Positive homogeneity of the log norm**, `μ(a A) = a μ(A)` for `a ≥ 0`.  For `a < 0`,
`μ(a A) = |a| μ(-A)`. -/
@[blueprint "lem:logNorm-smul"
  (title := "Positive homogeneity of the log norm")
  (latexEnv := "lemma")
  (statement := /-- $\mu(a A) = a \, \mu(A)$ for $a \ge 0$ (\cref{def:logNorm}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0), Lemma 2.10,
    (2.29a). -/)
  (proof := /-- $\pair{aAx}{x} = a \pair{Ax}{x} \le a \mu(A) \|x\|^2$ gives $\mu(aA) \le a\mu(A)$;
    for $a > 0$, apply this to $a^{-1}$ and $aA$ for the reverse. -/)]
theorem logNorm_smul (A : E →L[ℝ] E) {a : ℝ} (ha : 0 ≤ a) : logNorm (a • A) = a * logNorm A := by
  have hle : ∀ {a : ℝ}, 0 ≤ a → ∀ B : E →L[ℝ] E, logNorm (a • B) ≤ a * logNorm B := fun ha B =>
    RegularPairing.logNorm_le (ofNorm E) fun x => by
      rw [ContinuousLinearMap.smul_apply, (ofNorm E).smul_left _ ha, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((ofNorm E).pairing_le_logNorm B x) ha
  refine le_antisymm (hle ha A) ?_
  rcases ha.eq_or_lt with rfl | ha
  · simp
  calc a * logNorm A = a * logNorm (a⁻¹ • a • A) := by
        rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
    _ ≤ a * (a⁻¹ * logNorm (a • A)) :=
        mul_le_mul_of_nonneg_left (hle (inv_nonneg.2 ha.le) _) ha.le
    _ = logNorm (a • A) := by field_simp

/-- **The translation property of the log norm**, `μ(A + c I) = μ(A) + c`. -/
@[blueprint "lem:logNorm-add-smul-one"
  (title := "Translation property of the log norm")
  (latexEnv := "lemma")
  (statement := /-- $\mu(A + c I) = \mu(A) + c$ for every $c \in \mathbb{R}$
    (\cref{def:logNorm}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0), Lemma 2.10,
    (2.29c). -/)
  (proof := /-- By partial linearity (\cref{lem:regularPairing-add-smul-self}),
    $\pair{Ax + cx}{x} = \pair{Ax}{x} + c\|x\|^2 \le (\mu(A) + c)\|x\|^2$, so
    $\mu(A + cI) \le \mu(A) + c$; apply this to $A + cI$ and $-c$ for the reverse. -/)]
theorem logNorm_add_smul_one (A : E →L[ℝ] E) (c : ℝ) :
    logNorm (A + c • (1 : E →L[ℝ] E)) = logNorm A + c := by
  have hle (B : E →L[ℝ] E) (c : ℝ) : logNorm (B + c • (1 : E →L[ℝ] E)) ≤ logNorm B + c :=
    RegularPairing.logNorm_le (ofNorm E) fun x => by
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, (ofNorm E).add_smul_self, add_mul]
      exact add_le_add_left ((ofNorm E).pairing_le_logNorm B x) _
  refine le_antisymm (hle A c) ?_
  have h := hle (A + c • 1) (-c)
  rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero] at h
  linarith

/-- `μ(c I) = c`. -/
lemma logNorm_smul_one (c : ℝ) : logNorm (c • (1 : E →L[ℝ] E)) = c := by
  simpa using logNorm_add_smul_one (0 : E →L[ℝ] E) c

/-- **The log norm is at most the norm**, `μ(A) ≤ ‖A‖`. -/
lemma logNorm_le_norm (A : E →L[ℝ] E) : logNorm A ≤ ‖A‖ :=
  RegularPairing.logNorm_le (ofNorm E) fun x => by
    calc ofNorm E (A x) x ≤ ‖A x‖ * ‖x‖ := (ofNorm E).le_norm_mul_norm _ _
      _ ≤ ‖A‖ * ‖x‖ * ‖x‖ := by gcongr; exact A.le_opNorm x
      _ = ‖A‖ * ‖x‖ ^ 2 := by ring

/-- **The norm of difference property of the log norm**, `|μ(A) - μ(B)| ≤ ‖A - B‖`. -/
@[blueprint "lem:abs-logNorm-sub-logNorm-le"
  (title := "Norm of difference property of the log norm")
  (latexEnv := "lemma")
  (statement := /-- $|\mu(A) - \mu(B)| \le \|A - B\|$ (\cref{def:logNorm}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0), Lemma 2.10,
    (2.29e). -/)
  (proof := /-- By subadditivity (\cref{lem:logNorm-add-le}),
    $\mu(A) \le \mu(B) + \mu(A - B) \le \mu(B) + \|A - B\|$, since $\mu(C) \le \|C\|$ by
    Cauchy--Schwarz; exchange $A$ and $B$. -/)]
theorem abs_logNorm_sub_logNorm_le (A B : E →L[ℝ] E) :
    |logNorm A - logNorm B| ≤ ‖A - B‖ := by
  have h (A B : E →L[ℝ] E) : logNorm A - logNorm B ≤ ‖A - B‖ := by
    have := logNorm_add_le B (A - B)
    rw [add_sub_cancel] at this
    linarith [logNorm_le_norm (A - B)]
  exact abs_sub_le_iff.2 ⟨h A B, by rw [norm_sub_rev]; exact h B A⟩

end Properties

/-- **The product property of the log norm**, `-μ(A) ‖x‖ ≤ ‖A x‖`.  Applied to `-A` it gives
`-μ(-A) ‖x‖ ≤ ‖A x‖` as well. -/
@[blueprint "lem:neg-logNorm-mul-norm-le"
  (title := "Product property of the log norm")
  (latexEnv := "lemma")
  (statement := /-- $-\mu(A) \|x\| \le \|Ax\|$ for all $x$ (\cref{def:logNorm}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0), Lemma 2.10,
    (2.29d). -/)
  (proof := /-- For the regular pairing of the norm, Cauchy--Schwarz and Lumer's inequality give
    $-\|Ax\| \|x\| \le \pair{Ax}{x} \le \mu(A)\|x\|^2$; divide by $\|x\|$. -/)]
theorem neg_logNorm_mul_norm_le (A : E →L[ℝ] E) (x : E) : -logNorm A * ‖x‖ ≤ ‖A x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h₁ := (ofNorm E).pairing_le_logNorm A x
  have h₂ := (abs_le.1 ((ofNorm E).abs_le_norm_mul_norm (A x) x)).1
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  nlinarith

/-- **A norm-preserving change of coordinates preserves the operator norm**: if `e : E → F` is
linear, invertible and `‖e x‖ = ‖x‖`, then `‖e B e⁻¹‖ = ‖B‖`. -/
theorem opNorm_conj {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F)
    (he : ∀ x, ‖e x‖ = ‖x‖) (B : E →L[ℝ] E) : ‖(e ∘L B ∘L e.symm : F →L[ℝ] F)‖ = ‖B‖ := by
  rw [← e.conjContinuousAlgEquiv_apply]
  have he' (y : F) : ‖e.symm y‖ = ‖y‖ := by rw [← he, e.apply_symm_apply]
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_)
  · rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply, he, ← he' y]
    exact B.le_opNorm _
  · calc ‖B x‖ = ‖e.conjContinuousAlgEquiv B (e x)‖ := by simp [he]
      _ ≤ ‖e.conjContinuousAlgEquiv B‖ * ‖e x‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖e.conjContinuousAlgEquiv B‖ * ‖x‖ := by rw [he]

/-- **A norm-preserving change of coordinates preserves the log norm**: if `e : E → F` is linear,
invertible and `‖e x‖ = ‖x‖`, then `μ(e A e⁻¹) = μ(A)`. -/
@[blueprint "lem:logNorm-conj"
  (title := "Log norm under a norm-preserving change of coordinates")
  (latexEnv := "lemma")
  (statement := /-- Let $e : E \to F$ be an invertible bounded linear map with $\|e x\| = \|x\|$
    for all $x$.  Then $\mu(e A e^{-1}) = \mu(A)$ for every bounded linear operator $A$ on $E$
    (\cref{def:logNorm}). -/)
  (proof := /-- Conjugation by $e$ preserves operator norms (both $\|e B e^{-1} y\| \le \|B\|
    \|y\|$ and $\|B x\| = \|e B e^{-1} (e x)\| \le \|e B e^{-1}\| \|x\|$), and
    $e(I + hA)e^{-1} = I + h \, eAe^{-1}$, so $\|I + h \, eAe^{-1}\| = \|I + hA\|$ for every
    $h$. -/)]
theorem logNorm_conj {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F)
    (he : ∀ x, ‖e x‖ = ‖x‖) (A : E →L[ℝ] E) :
    logNorm (e ∘L A ∘L e.symm : F →L[ℝ] F) = logNorm A := by
  rw [← e.conjContinuousAlgEquiv_apply]
  unfold logNorm
  congr 1
  ext h
  rw [← opNorm_conj e he (1 + h • A), ← e.conjContinuousAlgEquiv_apply, map_add, map_one,
    map_smul]

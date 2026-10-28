import LeanForControl.Contraction.Norms.CurveNormDerivative
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Architect

/-!
# `Contraction.Norms.LogNorm` — the logarithmic norm and Lumer's property

The log norm `μ(A) = lim_{h → 0⁺} (‖I + h A‖ - 1) / h` is defined in `Defs.lean`.

* `RegularPairing.pairing_le_logNorm` — Lumer's inequality, `⟦A x, x⟧ ≤ μ(A) ‖x‖²`.
* `RegularPairing.logNorm_le` — conversely, `⟦A x, x⟧ ≤ c ‖x‖²` for all `x` implies `μ(A) ≤ c`.

Together they say that `μ(A)` is the least `c` with `⟦A x, x⟧ ≤ c ‖x‖²` for all `x`: Lumer's
equality `μ(A) = sup_{x ≠ 0} ⟦A x, x⟧ / ‖x‖²`, for every regular pairing.

The basic properties of `μ` then follow from those of a pairing, through the regular pairing of the
norm: subadditivity, positive homogeneity, the translation property `μ(A + c I) = μ(A) + c`, the
norm of difference property `|μ(A) - μ(B)| ≤ ‖A - B‖`, and the product property
`-μ(A) ‖x‖ ≤ ‖A x‖`.  A change of coordinates that preserves the norm preserves the log norm
(`logNorm_conj`).  It is convex, so on a polytope of operators it is at most its largest
value at a vertex (`logNorm_le_sup'_of_mem_convexHull`), and `μ(A) < 0` bounds the inverse,
`‖A⁻¹‖ ≤ -1/μ(A)` (`opNorm_symm_le_of_logNorm_neg`).

On a real inner product space the pairing is the inner product, so:

* `logNorm_le_iff_inner_le` — `μ(A) ≤ c` iff `⟪A v, v⟫ ≤ c ‖v‖²` for all `v`;
* `logNorm_isGreatest_inner` — in finite dimension, `μ(A)` is the largest eigenvalue of the
  symmetric part `(A + A*) / 2`, with `A*` the adjoint for that inner product.

References: F. Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), equation (2.22),
Remark 2.9, Lemma 2.10 and Definition 2.17; A. V. Proskurnikov and F. Bullo, *Regular Pairings for
Nonquadratic Lyapunov Functions and Contraction Analysis*, SIAM J. Control Optim. 64(1):496–521
(2026), doi:10.1137/24M1689685, Definitions 2.1 and 3.1 and Theorem 3.5.
-/

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open scoped LogNorm

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
    p (A x) x ≤ μ A * ‖x‖ ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  -- `‖x + h A x‖ ≤ ‖I + h A‖ ‖x‖`, with equality at `h = 0`
  have hle := (hasDerivWithinAt_norm_add_smul (A x) x).le_of_le_of_eq
    ((hasDerivWithinAt_norm_add_smul A 1).mul_const ‖x‖) (by simp)
    (Eventually.of_forall fun h => by simpa using ((1 : E →L[ℝ] E) + h • A).le_opNorm x)
  calc p (A x) x ≤ ofNorm E (A x) x := p.le_ofNorm _ _
    _ ≤ ‖x‖ * (μ A * ‖x‖) := by
        rw [ofNorm_apply]
        exact mul_le_mul_of_nonneg_left hle (norm_nonneg x)
    _ = μ A * ‖x‖ ^ 2 := by ring

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

@[simp] lemma logNorm_zero : μ (0 : E →L[ℝ] E) = 0 := by
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
theorem logNorm_add_le (A B : E →L[ℝ] E) : μ (A + B) ≤ μ A + μ B :=
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
theorem logNorm_smul (A : E →L[ℝ] E) {a : ℝ} (ha : 0 ≤ a) : μ (a • A) = a * μ A := by
  have hle : ∀ {a : ℝ}, 0 ≤ a → ∀ B : E →L[ℝ] E, μ (a • B) ≤ a * μ B := fun ha B =>
    RegularPairing.logNorm_le (ofNorm E) fun x => by
      rw [ContinuousLinearMap.smul_apply, (ofNorm E).smul_left _ ha, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((ofNorm E).pairing_le_logNorm B x) ha
  refine le_antisymm (hle ha A) ?_
  rcases ha.eq_or_lt with rfl | ha
  · simp
  calc a * μ A = a * μ (a⁻¹ • a • A) := by
        rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
    _ ≤ a * (a⁻¹ * μ (a • A)) :=
        mul_le_mul_of_nonneg_left (hle (inv_nonneg.2 ha.le) _) ha.le
    _ = μ (a • A) := by field_simp

/-- **Homogeneity of the log norm for `a ≤ 0`**, `μ(a A) = |a| μ(-A)`. -/
lemma logNorm_smul_of_nonpos (A : E →L[ℝ] E) {a : ℝ} (ha : a ≤ 0) : μ (a • A) = -a * μ (-A) := by
  rw [← logNorm_smul _ (neg_nonneg.2 ha), smul_neg, neg_smul, _root_.neg_neg]

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
    μ (A + c • (1 : E →L[ℝ] E)) = μ A + c := by
  have hle (B : E →L[ℝ] E) (c : ℝ) : μ (B + c • (1 : E →L[ℝ] E)) ≤ μ B + c :=
    RegularPairing.logNorm_le (ofNorm E) fun x => by
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, (ofNorm E).add_smul_self, add_mul]
      exact add_le_add_left ((ofNorm E).pairing_le_logNorm B x) _
  refine le_antisymm (hle A c) ?_
  have h := hle (A + c • 1) (-c)
  rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero] at h
  linarith

/-- `μ(c I) = c`. -/
lemma logNorm_smul_one (c : ℝ) : μ (c • (1 : E →L[ℝ] E)) = c := by
  simpa using logNorm_add_smul_one (0 : E →L[ℝ] E) c

/-- **The log norm is at most the norm**, `μ(A) ≤ ‖A‖`. -/
lemma logNorm_le_norm (A : E →L[ℝ] E) : μ A ≤ ‖A‖ :=
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
    |μ A - μ B| ≤ ‖A - B‖ := by
  have h (A B : E →L[ℝ] E) : μ A - μ B ≤ ‖A - B‖ := by
    have := logNorm_add_le B (A - B)
    rw [add_sub_cancel] at this
    linarith [logNorm_le_norm (A - B)]
  exact abs_sub_le_iff.2 ⟨h A B, by rw [norm_sub_rev]; exact h B A⟩

/-- The log norm is `1`-Lipschitz, by the norm of difference property; in particular it is
continuous. -/
lemma lipschitzWith_logNorm : LipschitzWith 1 (logNorm : (E →L[ℝ] E) → ℝ) :=
  LipschitzWith.of_dist_le_mul fun A B => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
    exact abs_logNorm_sub_logNorm_le A B

/-- **The log norm is convex**, by subadditivity and positive homogeneity. -/
lemma convexOn_logNorm : ConvexOn ℝ univ (logNorm : (E →L[ℝ] E) → ℝ) :=
  ⟨convex_univ, fun A _ B _ a b ha hb _ => by
    simp only [smul_eq_mul]
    calc μ (a • A + b • B) ≤ μ (a • A) + μ (b • B) := logNorm_add_le _ _
      _ = a * μ A + b * μ B := by rw [logNorm_smul _ ha, logNorm_smul _ hb]⟩

/-- **The log norm on a polytope of operators** is at most its largest value at a vertex:
`μ(A) ≤ maxⱼ μ(Aⱼ)` for `A` in the convex hull of `A₁, …, Aₘ`.  For the norm, this is Mathlib's
`convexOn_norm` with `ConvexOn.le_sup_of_mem_convexHull`. -/
@[blueprint "thm:logNorm-le-sup-of-mem-convexHull"
  (title := "Log norm on a polytope of matrices")
  (statement := /-- If $A$ lies in the convex hull of $A_1, \dots, A_m$, then
    $\mu(A) \le \max_j \mu(A_j)$ (\cref{def:logNorm}). -/)
  (proof := /-- $\mu$ is convex, by subadditivity (\cref{lem:logNorm-add-le}) and positive
    homogeneity (\cref{lem:logNorm-smul}); a convex function on a polytope is at most its
    largest value at a vertex. -/)]
theorem logNorm_le_sup'_of_mem_convexHull {t : Finset (E →L[ℝ] E)} {A : E →L[ℝ] E}
    (hA : A ∈ convexHull ℝ (t : Set (E →L[ℝ] E))) :
    μ A ≤ t.sup' (Finset.coe_nonempty.1 (convexHull_nonempty_iff.1 ⟨A, hA⟩)) logNorm :=
  convexOn_logNorm.le_sup_of_mem_convexHull (subset_univ _) hA

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

/-- The product property for `-A`, `-μ(-A) ‖x‖ ≤ ‖A x‖`. -/
lemma neg_logNorm_neg_mul_norm_le (A : E →L[ℝ] E) (x : E) : -μ (-A) * ‖x‖ ≤ ‖A x‖ := by
  simpa using neg_logNorm_mul_norm_le (-A) x

/-- **The uniform monotonicity property of the log norm**: if `μ(A) < 0`, then
`‖A⁻¹‖ ≤ -1 / μ(A)`. -/
@[blueprint "lem:opNorm-symm-le-of-logNorm-neg"
  (title := "Uniform monotonicity property of the log norm")
  (latexEnv := "lemma")
  (statement := /-- If $A$ is invertible and $\mu(A) < 0$, then
    $\|A^{-1}\| \le -1/\mu(A)$ (\cref{def:logNorm}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0), Lemma 2.10. -/)
  (proof := /-- The product property (\cref{lem:neg-logNorm-mul-norm-le}) at $x = A^{-1} y$ gives
    $-\mu(A) \|A^{-1} y\| \le \|y\|$. -/)]
theorem opNorm_symm_le_of_logNorm_neg (A : E ≃L[ℝ] E) (hA : μ (A : E →L[ℝ] E) < 0) :
    ‖(A.symm : E →L[ℝ] E)‖ ≤ -1 / μ (A : E →L[ℝ] E) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (div_pos_of_neg_of_neg (by norm_num) hA).le
    fun y => ?_
  have h := neg_logNorm_mul_norm_le (A : E →L[ℝ] E) (A.symm y)
  rw [ContinuousLinearEquiv.coe_coe, A.apply_symm_apply] at h
  rw [ContinuousLinearEquiv.coe_coe, div_mul_eq_mul_div, le_div_iff_of_neg hA]
  linarith

/-- The log norm is continuous. -/
lemma continuous_logNorm : Continuous (logNorm : (E →L[ℝ] E) → ℝ) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact continuous_of_const fun A B => by
      congr 1
      ext x
      exact Subsingleton.elim _ _
  · exact lipschitzWith_logNorm.continuous

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
    μ (e ∘L A ∘L e.symm : F →L[ℝ] F) = μ A := by
  rw [← e.conjContinuousAlgEquiv_apply]
  unfold logNorm
  congr 1
  ext h
  rw [← opNorm_conj e he (1 + h • A), ← e.conjContinuousAlgEquiv_apply, map_add, map_one,
    map_smul]

/-! ### Inner product spaces -/

section InnerProduct

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]

/-- **The log norm on a real inner product space is a quadratic-form bound**: `μ(A) ≤ c` iff
`⟪A v, v⟫ ≤ c ‖v‖²` for all `v`. -/
@[blueprint "thm:logNorm-le-iff-inner-le"
  (title := "The log norm on an inner product space")
  (statement := /-- On a real inner product space, $\mu(A) \le c$ if and only if
    $\langle A v, v \rangle \le c \|v\|^2$ for all $v$ (\cref{def:logNorm}). -/)
  (proof := /-- Lumer's property (\cref{thm:regularPairing-pairing-le-logNorm},
    \cref{thm:regularPairing-logNorm-le}) for the inner product
    (\cref{def:regularPairing-ofInner}). -/)]
theorem logNorm_le_iff_inner_le (A : E →L[ℝ] E) (c : ℝ) :
    μ A ≤ c ↔ ∀ v, ⟪A v, v⟫ ≤ c * ‖v‖ ^ 2 :=
  ⟨fun h v => ((RegularPairing.ofInner E).pairing_le_logNorm A v).trans
    (mul_le_mul_of_nonneg_right h (sq_nonneg _)), (RegularPairing.ofInner E).logNorm_le⟩

/-- **The log norm on a finite-dimensional real inner product space** is the largest eigenvalue of
the symmetric part `(A + A*) / 2`.  Here `A*` is the adjoint for *this* inner product: on `ℝⁿ` with
the standard inner product it is `Aᵀ` (`Matrix.logNorm_euclidean_isGreatest`); for a weighted
inner product `xᵀ P y` it is `P⁻¹ Aᵀ P`, and `Matrix.logNormL2PosDef_isGreatest` states that
case with `P` explicit. -/
theorem logNorm_isGreatest_inner [FiniteDimensional ℝ E] (A : E →L[ℝ] E) :
    IsGreatest {a | Module.End.HasEigenvalue
      (((2⁻¹ : ℝ) • (A + ContinuousLinearMap.adjoint A) : E →L[ℝ] E) : E →ₗ[ℝ] E) a}
      (μ A) := by
  set S : E →L[ℝ] E := (2⁻¹ : ℝ) • (A + ContinuousLinearMap.adjoint A)
  have hS (x : E) : ⟪S x, x⟫ = ⟪A x, x⟫ := by
    simp only [S, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      real_inner_smul_left, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
      real_inner_comm (A x)]
    ring
  have hsymm : (S : E →ₗ[ℝ] E).IsSymmetric := fun x y => by
    simp only [ContinuousLinearMap.coe_coe, S, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, real_inner_smul_left, real_inner_smul_right, inner_add_left,
      inner_add_right, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right, real_inner_comm (A y)]
    ring
  -- every eigenvalue of `S` is at most `μ(A)`
  have hub (a : ℝ) (ha : Module.End.HasEigenvalue (S : E →ₗ[ℝ] E) a) : a ≤ μ A := by
    obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
    have h := (RegularPairing.ofInner E).pairing_le_logNorm A v
    rw [RegularPairing.ofInner_apply, ← hS, show S v = a • v from hv.apply_eq_smul,
      real_inner_smul_left, real_inner_self_eq_norm_sq] at h
    exact le_of_mul_le_mul_right h (pow_pos (norm_pos_iff.2 hv.2) 2)
  -- `μ(A)` is at most the supremum of the Rayleigh quotient of `S`, an eigenvalue of `S`
  have hev := hsymm.hasEigenvalue_iSup_of_finiteDimensional
  have hle : μ A ≤ ⨆ x : { x : E // x ≠ 0 },
      RCLike.re ⟪(S : E →ₗ[ℝ] E) x, x⟫ / ‖(x : E)‖ ^ 2 := by
    refine (RegularPairing.ofInner E).logNorm_le fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hb : BddAbove (Set.range fun x : { x : E // x ≠ 0 } =>
        RCLike.re ⟪(S : E →ₗ[ℝ] E) x, x⟫ / ‖(x : E)‖ ^ 2) := by
      refine ⟨‖S‖, ?_⟩
      rintro _ ⟨⟨y, hy⟩, rfl⟩
      have hy' : 0 < ‖y‖ ^ 2 := by positivity
      simp only [ContinuousLinearMap.coe_coe, RCLike.re_to_real]
      rw [div_le_iff₀ hy']
      calc ⟪S y, y⟫ ≤ ‖S y‖ * ‖y‖ := real_inner_le_norm _ _
        _ ≤ ‖S‖ * ‖y‖ * ‖y‖ := by gcongr; exact S.le_opNorm y
        _ = ‖S‖ * ‖y‖ ^ 2 := by ring
    have h := le_ciSup hb ⟨x, hx⟩
    simp only [ContinuousLinearMap.coe_coe, RCLike.re_to_real] at h
    rw [div_le_iff₀ (by positivity)] at h
    rw [RegularPairing.ofInner_apply, ← hS]
    simpa only [ContinuousLinearMap.coe_coe, RCLike.re_to_real] using h
  exact ⟨le_antisymm (hub _ hev) hle ▸ hev, hub⟩

end InnerProduct

import LeanForControl.Contraction.Norms.LpPairings
import LeanForControl.Analysis.FrechetDerivative
import Architect

/-!
# `Contraction.Norms.OneSidedLipschitz` — one-sided Lipschitz constants

The one-sided Lipschitz constant `osL F on C` (`oneSidedLipschitz`, in `Defs.lean`) extends the log
norm from linear to nonlinear maps, `osL(F) = sup_{x ≠ y ∈ C} ⟦F x - F y; x - y⟧ / ‖x - y‖²`.

* `oneSidedLipschitz_le_iff` — `osL F on C ≤ b` iff `⟦F x - F y; x - y⟧ ≤ b ‖x - y‖²` on `C`;
  `RegularPairing.pairing_le_of_oneSidedLipschitz_le` — then the same holds for every regular
  pairing; `oneSidedLipschitz_le_iff_inner` — on an inner product space, the pairing is `⟪·,·⟫`.
* `oneSidedLipschitz_affine` — `osL(x ↦ A x + d) = μ(A)`.
* `oneSidedLipschitz_mem_Icc_of_lipschitzOnWith` — `-Lip(F) ≤ osL(F) ≤ Lip(F)`.
* **The Jacobian test**: on an open convex set, for `F` differentiable on `C`,
  `osL F on C = sup_{x ∈ C} μ(DF(x))` (`oneSidedLipschitz_eq_iSup_logNorm`), so
  `osL F on C ≤ b` iff `μ(DF(x)) ≤ b` on `C` (`oneSidedLipschitz_le_iff_logNorm_le`), and every
  regular pairing gives the same condition (`RegularPairing.logNorm_fderiv_le_iff`).
* Properties, as for the log norm: subadditivity, positive homogeneity, translation, the lower
  bound `‖F x - F y‖ ≥ -osL(F) ‖x - y‖`, the norm of difference, and injectivity when `osL < 0`.
* Maps of `ℝⁿ` with Jacobian matrix `J`: `osL_{p,R} F on C = sup_x μ_{p,R}(J x)` and
  `osL_{2,P^½} F on C = sup_x μ_{2,P^½}(J x)`; the increment forms for `√(xᵀ P x)` and for any
  regular pairing of `‖R x‖_p` (the sign and max pairings for `p = 1, ∞`); and, for weighted ℓ¹ and
  ℓ∞ conditions, the tests `ηᵀ J ≤ b ηᵀ` and `J η ≤ b η` as increments along ordered pairs.

References: F. Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), Chapter 3;
A. V. Proskurnikov and F. Bullo, *Regular Pairings for Nonquadratic Lyapunov Functions and
Contraction Analysis*, SIAM J. Control Optim. 64(1):496–521 (2026), doi:10.1137/24M1689685.
-/

open Set Filter Topology
open scoped LogNorm ENNReal NNReal RealInnerProductSpace

/-! ### General normed spaces -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E} {F G : E → E}

/-- **`osL` through the pairing of the norm**: `osL F on C ≤ b` iff
`⟦F x - F y; x - y⟧ ≤ b ‖x - y‖²` for all `x, y ∈ C`. -/
@[blueprint "thm:oneSidedLipschitz-le-iff"
  (title := "One-sided Lipschitz bounds through the pairing")
  (statement := /-- $\operatorname{osL}(F) \le b$ on $C$ (\cref{def:oneSidedLipschitz}) if and only
    if $\pair{F(x) - F(y)}{x - y} \le b \|x - y\|^2$ for all $x, y \in C$, for the regular
    pairing of the norm (\cref{def:regularPairing-ofNorm}). -/)]
theorem oneSidedLipschitz_le_iff (b : ℝ) :
    osL F on C ≤ b ↔
      ∀ x ∈ C, ∀ y ∈ C, ⟦F x - F y; x - y⟧ ≤ b * ‖x - y‖ ^ 2 := by
  simp only [oneSidedLipschitz, iSup_le_iff, EReal.coe_le_coe_iff,
    RegularPairing.ofNorm_eq_normPairing]
  refine forall₂_congr fun x _ => forall₂_congr fun y _ => ?_
  rcases eq_or_ne x y with rfl | hxy
  · simp [normPairing]
  -- for `x ≠ y`, clear the denominator `‖x - y‖² > 0`
  simpa [hxy] using div_le_iff₀ (pow_pos (norm_pos_iff.2 (sub_ne_zero.2 hxy)) 2)

/-- Each quotient `⟦F x - F y; x - y⟧ / ‖x - y‖²` is at most `osL F on C`. -/
lemma le_oneSidedLipschitz {x y : E} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    ((⟦F x - F y; x - y⟧ / ‖x - y‖ ^ 2 : ℝ) : EReal) ≤ osL F on C :=
  le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))

/-- `osL F on C ≤ X` as soon as every quotient `⟦F x - F y; x - y⟧ / ‖x - y‖²` is. -/
lemma oneSidedLipschitz_le_of_forall {X : EReal}
    (h : ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
      ((⟦F x - F y; x - y⟧ / ‖x - y‖ ^ 2 : ℝ) : EReal) ≤ X) :
    osL F on C ≤ X :=
  iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => h x hx y hy hxy

/-- **Every regular pairing obeys a one-sided Lipschitz bound**: if `osL F on C ≤ b`, then
`p (F x - F y) (x - y) ≤ b ‖x - y‖²` for every regular pairing `p` of the norm. -/
@[blueprint "thm:regularPairing-pairing-le-of-oneSidedLipschitz-le"
  (title := "One-sided Lipschitz bounds for every pairing")
  (statement := /-- If $\operatorname{osL}(F) \le b$ on $C$ (\cref{def:oneSidedLipschitz}), then
    $\pair{F(x) - F(y)}{x - y} \le b \|x - y\|^2$ for all $x, y \in C$ and every regular pairing
    (\cref{def:regularPairing}). -/)]
theorem RegularPairing.pairing_le_of_oneSidedLipschitz_le (p : RegularPairing E)
    {b : ℝ}
    (h : osL F on C ≤ b) {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    ⟦F x - F y; x - y⟧_p ≤ b * ‖x - y‖ ^ 2 :=
  (p.le_ofNorm _ _).trans ((oneSidedLipschitz_le_iff b).1 h x hx y hy)

/-- **`osL` of an affine map is the log norm**: `osL(x ↦ A x + d) = μ(A)`. -/
@[blueprint "thm:oneSidedLipschitz-affine"
  (title := "One-sided Lipschitz constant of an affine map")
  (statement := /-- For a bounded linear operator $A$ on a nontrivial normed space and a vector
    $d$, $\operatorname{osL}(x \mapsto A x + d) = \mu(A)$
    (\cref{def:oneSidedLipschitz,def:logNorm}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Chapter 3. -/)]
theorem oneSidedLipschitz_affine [Nontrivial E] (A : E →L[ℝ] E) (d : E) :
    osL (fun x => A x + d) = (μ A : EReal) := by
  have hinc (x y : E) : A x + d - (A y + d) = A (x - y) := by rw [map_sub]; abel
  refine le_antisymm ((oneSidedLipschitz_le_iff _).2 fun x _ y _ => ?_) ?_
  · -- Lumer's inequality for the increment `A (x - y)`
    rw [hinc]
    exact (RegularPairing.ofNorm E).pairing_le_logNorm A (x - y)
  · -- every real bound `b ≥ osL` bounds `⟦A z; z⟧ ≤ b ‖z‖²` (take `x = z`, `y = 0`), so `μ(A) ≤ b`
    refine EReal.le_of_forall_lt_iff_le.1 fun b hb => EReal.coe_le_coe_iff.2 ?_
    refine (RegularPairing.ofNorm E).logNorm_le fun z => ?_
    simpa [hinc] using
      (oneSidedLipschitz_le_iff b).1 hb.le z (mem_univ z) 0 (mem_univ 0)

/-- **A Lipschitz constant bounds `osL`**: `-Lip(F) ≤ osL(F) ≤ Lip(F)` on a set with two points or
more. -/
@[blueprint "thm:oneSidedLipschitz-le-of-lipschitzOnWith"
  (title := "Lipschitz constants bound one-sided Lipschitz constants")
  (statement := /-- If $C$ has two points or more and $F$ is Lipschitz on $C$ with constant $K$,
    then $-K \le \operatorname{osL}(F) \le K$ on $C$ (\cref{def:oneSidedLipschitz}). -/)
  (proof := /-- For $x \ne y$ in $C$, the two-sided Cauchy--Schwarz inequality
    (\cref{lem:regularPairing-abs-le-norm-mul-norm}) gives
    $|\pair{F(x) - F(y)}{x - y}| \le \|F(x) - F(y)\| \|x - y\| \le K \|x - y\|^2$. -/)]
theorem oneSidedLipschitz_mem_Icc_of_lipschitzOnWith {K : ℝ≥0} (h : LipschitzOnWith K F C)
    (hC : C.Nontrivial) : osL F on C ∈ Icc (-((K : ℝ) : EReal)) ((K : ℝ) : EReal) := by
  -- two-sided Cauchy–Schwarz for the pairing, then the Lipschitz bound
  have hCS (x : E) (hx : x ∈ C) (y : E) (hy : y ∈ C) :
      |⟦F x - F y; x - y⟧| ≤ K * ‖x - y‖ ^ 2 := by
    have hL : ‖F x - F y‖ ≤ K * ‖x - y‖ := by
      simpa [dist_eq_norm] using h.dist_le_mul x hx y hy
    calc _ ≤ ‖F x - F y‖ * ‖x - y‖ := (RegularPairing.ofNorm E).abs_le_norm_mul_norm _ _
      _ ≤ K * ‖x - y‖ * ‖x - y‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      _ = K * ‖x - y‖ ^ 2 := by ring
  refine ⟨?_, (oneSidedLipschitz_le_iff _).2 fun x hx y hy => (abs_le.1 (hCS x hx y hy)).2⟩
  -- the quotient at one pair `x ≠ y` is already `≥ -K`
  obtain ⟨x, hx, y, hy, hxy⟩ := hC
  refine le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy ?_))
  rw [← EReal.coe_neg, EReal.coe_le_coe_iff,
    le_div_iff₀ (pow_pos (norm_pos_iff.2 (sub_ne_zero.2 hxy)) 2), neg_mul]
  exact (abs_le.1 (hCS x hx y hy)).1

section Jacobian

variable [Nontrivial E] {DF : E → E →L[ℝ] E}

/-- **The Jacobian test for any pairing**: on an open convex set, for `F` differentiable on `C`,
`μ(DF(x)) ≤ b` on `C` iff `⟦F x - F y; x - y⟧ ≤ b ‖x - y‖²` on `C`, for every regular pairing of
the norm.  So the increment condition does not depend on the pairing. -/
@[blueprint "thm:regularPairing-logNorm-fderiv-le-iff"
  (title := "The Jacobian test for any regular pairing")
  (statement := /-- Let $C$ be open and convex and $F$ differentiable on $C$.  For
    every regular pairing (\cref{def:regularPairing}),
    \[ \mu(DF(x)) \le b \text{ for all } x \in C \iff
      \pair{F(x) - F(y)}{x - y} \le b \|x - y\|^2 \text{ for all } x, y \in C. \] -/)
  (proof := /-- The pairing is Lipschitz, hence continuous, in its first argument:
    $|\pair{u}{w} - \pair{u'}{w}| \le \|u - u'\| \|w\|$
    (\cref{lem:regularPairing-abs-sub-le}).

    ($\Rightarrow$) Fix $x, y \in C$ and set $w = x - y$.  By convexity the segment
    $y + t w$, $t \in [0, 1]$, lies in $C$.  Let
    \[ \psi(t) = \pair{F(y + t w) - F(y)}{w} - t \, b \|w\|^2 . \]
    Then $\psi(0) = \pair{0}{w} = 0$, and $\psi$ is continuous on $[0, 1]$, since $F$ is
    differentiable, hence continuous, along the segment.  We show that at every $t \in [0, 1)$ the
    right difference quotients of $\psi$ are eventually below every $r > 0$; the mean value
    inequality for right difference quotients then gives $\psi(1) \le 0$, which is the claim.

    Fix $t$ and let $s > t$.  Writing
    $F(y + s w) - F(y) = \bigl(F(y + s w) - F(y + t w)\bigr) + \bigl(F(y + t w) - F(y)\bigr)$,
    subadditivity and positive homogeneity of the pairing in its first argument give
    \[ \frac{\psi(s) - \psi(t)}{s - t} \le \pair{q(s)}{w} - b \|w\|^2, \qquad
      q(s) = \frac{F(y + s w) - F(y + t w)}{s - t}. \]
    By the chain rule, $q(s) \to DF(y + t w) w$ as $s \to t^+$, so by continuity of the pairing,
    $\pair{q(s)}{w} \to \pair{DF(y + t w) w}{w}$.  Lumer's inequality
    (\cref{thm:regularPairing-pairing-le-logNorm}) and the hypothesis give
    \[ \pair{DF(y + t w) w}{w} \le \mu\bigl(DF(y + t w)\bigr) \|w\|^2 \le b \|w\|^2 , \]
    so eventually $\pair{q(s)}{w} < b \|w\|^2 + r$, and the difference quotient of $\psi$ is
    below $r$.

    This is the integral argument
    $\pair{\int_0^1 DF(y + s w) w \, ds}{w} \le \int_0^1 \pair{DF(y + s w) w}{w} \, ds$ carried out
    one step at a time: subadditivity replaces the inequality for the integral, and the mean value
    inequality replaces integration.  It uses neither completeness of $E$ nor continuity of $DF$.

    ($\Leftarrow$) Fix $x \in C$ and $v \in E$.  Since $C$ is open, $x + h v \in C$ for small
    $h > 0$, and the hypothesis at the pair $x + h v$, $x$, with homogeneity of the pairing in
    both arguments, gives
    \[ \pair{\tfrac{1}{h} \bigl(F(x + h v) - F(x)\bigr)}{v} \le b \|v\|^2 . \]
    As $h \to 0^+$ the quotient tends to $DF(x) v$, so $\pair{DF(x) v}{v} \le b \|v\|^2$ for every
    $v$, and the converse of Lumer's inequality (\cref{thm:regularPairing-logNorm-le}) gives
    $\mu(DF(x)) \le b$. -/)]
theorem RegularPairing.logNorm_fderiv_le_iff (p : RegularPairing E) (hCo : IsOpen C)
    (hCc : Convex ℝ C) (hF : ∀ x ∈ C, HasFDerivAt F (DF x) x)
    (b : ℝ) :
    (∀ x ∈ C, μ (DF x) ≤ b) ↔ ∀ x ∈ C, ∀ y ∈ C, ⟦F x - F y; x - y⟧_p ≤ b * ‖x - y‖ ^ 2 := by
  -- the pairing is Lipschitz, hence continuous, in its first argument
  have hpc (w : E) : Continuous fun u => p u w :=
    (LipschitzWith.of_dist_le_mul (K := ‖w‖₊) fun u u' => by
      rw [Real.dist_eq, dist_eq_norm, coe_nnnorm, mul_comm]
      exact p.abs_sub_le u u' w).continuous
  constructor
  · intro hb x hx y hy
    set w := x - y
    have hz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : y + t • w ∈ C := hCc.add_smul_sub_mem hy hx ht
    have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        HasDerivAt (fun s : ℝ => F (y + s • w)) (DF (y + t • w) w) t := by
      simpa using (hF _ (hz t ht)).comp_hasDerivAt t
        (((hasDerivAt_id t).smul_const w).const_add y)
    -- along the segment, `ψ t = ⟦F (y + t w) - F y; w⟧ - t b ‖w‖²` starts at `0` and has right
    -- slopes `≤ 0`, so the mean value inequality gives `ψ 1 ≤ 0`
    let ψ : ℝ → ℝ := fun t => p (F (y + t • w) - F y) w - t * (b * ‖w‖ ^ 2)
    have hψ : ∀ t ∈ Icc (0 : ℝ) 1, ψ t ≤ 0 := by
      refine image_le_of_liminf_slope_right_le_deriv_boundary (B := fun _ => 0) (B' := fun _ => 0)
        (fun t ht => ?_) (by simp [ψ]) continuousOn_const
        (fun _ _ => hasDerivWithinAt_const _ _ _) fun t ht r hr => ?_
      · exact (((hpc w).continuousAt.comp ((hd t ht).continuousAt.sub continuousAt_const)).sub
          (continuousAt_id.mul continuousAt_const)).continuousWithinAt
      · have ht' : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
        -- the difference quotients of `s ↦ F (y + s w)` tend to `DF (y + t w) w`, and Lumer
        -- bounds `⟦DF (y + t w) w; w⟧ ≤ μ (DF (y + t w)) ‖w‖² ≤ b ‖w‖²`
        have hlim := ((hpc w).tendsto _).comp
          ((hd t ht').tendsto_slope.mono_left (nhdsGT_le_nhdsNE t))
        have hL : p (DF (y + t • w) w) w < b * ‖w‖ ^ 2 + r :=
          ((p.pairing_le_logNorm _ w).trans (mul_le_mul_of_nonneg_right
            (hb _ (hz t ht')) (sq_nonneg _))).trans_lt (lt_add_of_pos_right _ hr)
        refine (Filter.Eventually.frequently ?_)
        filter_upwards [hlim.eventually (gt_mem_nhds hL), self_mem_nhdsWithin]
          with s hs (hst : t < s)
        have hst' : 0 < s - t := sub_pos.2 hst
        -- subadditivity and homogeneity of the pairing in its first argument
        have hsub : p (F (y + s • w) - F y) w ≤
            (s - t) * p (slope (fun s : ℝ => F (y + s • w)) t s) w + p (F (y + t • w) - F y) w := by
          rw [slope_def_module, ← p.smul_left _ hst'.le, smul_inv_smul₀ hst'.ne']
          simpa using p.add_left_le (F (y + s • w) - F (y + t • w)) (F (y + t • w) - F y) w
        simp only [Function.comp_apply] at hs
        rw [slope_def_field]
        calc (ψ s - ψ t) / (s - t)
            ≤ p (slope (fun s : ℝ => F (y + s • w)) t s) w - b * ‖w‖ ^ 2 := by
              rw [div_le_iff₀ hst']
              simp only [ψ]
              nlinarith [hsub]
          _ < r := by linarith
    simpa [ψ, w] using hψ 1 ⟨zero_le_one, le_rfl⟩
  · -- `⟦DF x v; v⟧` is the limit of `⟦(F (x + t v) - F x) / t; v⟧ ≤ b ‖v‖²` as `t → 0⁺`
    intro hb x hx
    refine p.logNorm_le fun v => (hF x hx).apply_le_of_increment_le (hCo.mem_nhds hx) (hpc v)
      (fun a ha u => p.smul_left a ha u v) v fun t ht hmem => ?_
    have hb' := hb _ hmem x hx
    rw [show x + t • v - x = t • v by abel, p.smul_right t ht.le, norm_smul,
      Real.norm_of_nonneg ht.le] at hb'
    exact le_of_mul_le_mul_left (hb'.trans_eq (by ring)) ht

/-- **The Jacobian test**: on an open convex set, for `F` differentiable on `C`,
`osL F on C = sup_{x ∈ C} μ(DF(x))`. -/
@[blueprint "thm:oneSidedLipschitz-eq-iSup-logNorm"
  (title := "The Jacobian test for one-sided Lipschitz constants")
  (statement := /-- Let $C$ be open and convex and $F$ differentiable on $C$, with
    derivative $DF$.  Then
    \[ \operatorname{osL}(F) = \sup_{x \in C} \mu(DF(x)) \]
    on $C$ (\cref{def:oneSidedLipschitz,def:logNorm}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Chapter 3. -/)
  (proof := /-- For a real $b$, $\operatorname{osL}(F) \le b$ on $C$ if and only if
    $\pair{F(x) - F(y)}{x - y} \le b \|x - y\|^2$ on $C$ for the pairing of the norm
    (\cref{thm:oneSidedLipschitz-le-iff}), which holds if and only if $\mu(DF(x)) \le b$ on $C$
    (\cref{thm:regularPairing-logNorm-fderiv-le-iff}).  Two extended reals with the same real
    upper bounds are equal. -/)]
theorem oneSidedLipschitz_eq_iSup_logNorm (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hF : ∀ x ∈ C, HasFDerivAt F (DF x) x) :
    osL F on C = ⨆ x ∈ C, (μ (DF x) : EReal) := by
  have h := (RegularPairing.ofNorm E).logNorm_fderiv_le_iff hCo hCc hF
  refine le_antisymm (EReal.le_of_forall_lt_iff_le.1 fun b hb => ?_) (iSup₂_le fun x hx => ?_)
  · -- `μ (DF) < b` on `C` gives the pairing bound with `b`
    exact (oneSidedLipschitz_le_iff b).2 <| (h b).1 fun x hx =>
      EReal.coe_le_coe_iff.1 ((le_iSup₂ (f := fun x _ => (μ (DF x) : EReal)) x hx).trans hb.le)
  · -- every real `b > osL` bounds the pairing, hence `μ (DF x) ≤ b`
    refine EReal.le_of_forall_lt_iff_le.1 fun b hb => EReal.coe_le_coe_iff.2 ?_
    exact (h b).2 ((oneSidedLipschitz_le_iff b).1 hb.le) x hx

/-- **The Jacobian test as a bound**: on an open convex set, for `F` differentiable on `C`,
`osL F on C ≤ b` iff `μ(DF(x)) ≤ b` for all `x ∈ C`. -/
theorem oneSidedLipschitz_le_iff_logNorm_le (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hF : ∀ x ∈ C, HasFDerivAt F (DF x) x) (b : ℝ) :
    osL F on C ≤ b ↔ ∀ x ∈ C, μ (DF x) ≤ b := by
  simp [oneSidedLipschitz_eq_iSup_logNorm hCo hCc hF]

end Jacobian

/-! #### Properties -/

/-- **Subadditivity**: `osL(F + G) ≤ osL(F) + osL(G)`. -/
@[blueprint "thm:oneSidedLipschitz-properties"
  (title := "Properties of one-sided Lipschitz constants")
  (statement := /-- On a set $C$ (with two points or more for the homogeneity), the one-sided
    Lipschitz constant (\cref{def:oneSidedLipschitz}) satisfies
    \begin{itemize}
      \item $\operatorname{osL}(F + G) \le \operatorname{osL}(F) + \operatorname{osL}(G)$;
      \item $\operatorname{osL}(a F) = a \operatorname{osL}(F)$ for $a \ge 0$;
      \item $\operatorname{osL}(F + a \operatorname{id}) = \operatorname{osL}(F) + a$;
      \item $\|F(x) - F(y)\| \ge -b \|x - y\|$ when $\operatorname{osL}(F) \le b$;
      \item $\operatorname{osL}(F) \le \operatorname{osL}(G) + K$ when $F - G$ is Lipschitz with
        constant $K$;
      \item $F$ is injective on $C$ when $\operatorname{osL}(F) < 0$.
    \end{itemize}

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Chapter 3. -/)]
theorem oneSidedLipschitz_add_le :
    osL (F + G) on C ≤ osL F on C + osL G on C := by
  refine oneSidedLipschitz_le_of_forall fun x hx y hy hxy => ?_
  have hw : 0 < ‖x - y‖ ^ 2 := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 hxy)) 2
  -- subadditivity of the pairing at the increments of `F` and `G`
  have hadd := (RegularPairing.ofNorm E).add_left_le (F x - F y) (G x - G y) (x - y)
  simp only [RegularPairing.ofNorm_eq_normPairing] at hadd
  calc ((normPairing ((F + G) x - (F + G) y) (x - y) / ‖x - y‖ ^ 2 : ℝ) : EReal)
      ≤ ((normPairing (F x - F y) (x - y) / ‖x - y‖ ^ 2 : ℝ) : EReal) +
          ((normPairing (G x - G y) (x - y) / ‖x - y‖ ^ 2 : ℝ) : EReal) := by
        rw [← EReal.coe_add, EReal.coe_le_coe_iff, ← add_div, Pi.add_apply, Pi.add_apply,
          add_sub_add_comm]
        gcongr
    _ ≤ osL F on C + osL G on C :=
        add_le_add (le_oneSidedLipschitz hx hy hxy) (le_oneSidedLipschitz hx hy hxy)

/-- **Positive homogeneity**: `osL(a F) = a osL(F)` for `a ≥ 0`. -/
theorem oneSidedLipschitz_smul {a : ℝ} (ha : 0 ≤ a) (hC : C.Nontrivial) :
    osL (a • F) on C = (a : EReal) * osL F on C := by
  -- `osL (c G) ≤ c osL G` for `c ≥ 0`, termwise by homogeneity of the pairing
  have hle (G : E → E) {c : ℝ} (hc : 0 ≤ c) : osL (c • G) on C ≤ (c : EReal) * osL G on C := by
    refine oneSidedLipschitz_le_of_forall fun x hx y hy hxy => ?_
    rw [Pi.smul_apply, Pi.smul_apply, ← smul_sub, (RegularPairing.ofNorm E).smul_left c hc,
      mul_div_assoc, EReal.coe_mul]
    exact mul_le_mul_of_nonneg_left (le_oneSidedLipschitz hx hy hxy) (EReal.coe_nonneg.2 hc)
  refine le_antisymm (hle F ha) ?_
  rcases ha.eq_or_lt with rfl | ha
  · -- `a = 0`: `osL 0 = 0`, at any pair of distinct points
    obtain ⟨x, hx, y, hy, hxy⟩ := hC
    simpa [normPairing] using le_oneSidedLipschitz (F := (0 : ℝ) • F) hx hy hxy
  · -- `a > 0`: `osL F = osL (a⁻¹ (a F)) ≤ a⁻¹ osL (a F)`
    have h := hle (a • F) (inv_nonneg.2 ha.le)
    rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at h
    calc (a : EReal) * osL F on C ≤ (a : EReal) * ((a⁻¹ : ℝ) * osL (a • F) on C) :=
          mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.2 ha.le)
      _ = osL (a • F) on C := by
          rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ ha.ne', EReal.coe_one, one_mul]

/-- **Translation**: `osL(F + a id) = osL(F) + a`. -/
theorem oneSidedLipschitz_add_smul_id (a : ℝ) :
    osL (fun x => F x + a • x) on C = osL F on C + a := by
  -- `osL (G + c id) ≤ osL G + c`, termwise by partial linearity of the pairing
  have hle (G : E → E) (c : ℝ) : osL (fun x => G x + c • x) on C ≤ osL G on C + c := by
    refine oneSidedLipschitz_le_of_forall fun x hx y hy hxy => ?_
    have hw : 0 < ‖x - y‖ ^ 2 := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 hxy)) 2
    rw [show G x + c • x - (G y + c • y) = G x - G y + c • (x - y) by rw [smul_sub]; abel,
      (RegularPairing.ofNorm E).add_smul_self, add_div, mul_div_cancel_right₀ _ hw.ne',
      EReal.coe_add]
    exact add_le_add (le_oneSidedLipschitz hx hy hxy) le_rfl
  refine le_antisymm (hle F a) ?_
  -- the reverse: `F = (F + a id) - a id`
  have h := hle (fun x => F x + a • x) (-a)
  simp only [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero] at h
  calc osL F on C + a ≤ osL (fun x => F x + a • x) on C + ((-a : ℝ) : EReal) + a :=
        add_le_add h le_rfl
    _ = osL (fun x => F x + a • x) on C := by
        rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]

/-- **The lower bound**: if `osL F on C ≤ b`, then `‖F x - F y‖ ≥ -b ‖x - y‖` on `C`. -/
theorem neg_mul_norm_sub_le_of_oneSidedLipschitz_le {b : ℝ}
    (h : osL F on C ≤ b) {x y : E}
    (hx : x ∈ C) (hy : y ∈ C) : -b * ‖x - y‖ ≤ ‖F x - F y‖ := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  -- `-‖F x - F y‖ ‖x - y‖ ≤ ⟦F x - F y; x - y⟧ ≤ b ‖x - y‖²`, then divide by `‖x - y‖ > 0`
  have hb := (oneSidedLipschitz_le_iff b).1 h x hx y hy
  have hCS := (abs_le.1 ((RegularPairing.ofNorm E).abs_le_norm_mul_norm (F x - F y) (x - y))).1
  have hw : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  nlinarith

/-- **The norm of difference**: `osL(F) ≤ osL(G) + Lip(F - G)`. -/
theorem oneSidedLipschitz_le_add_of_lipschitzOnWith {K : ℝ≥0}
    (h : LipschitzOnWith K (F - G) C) :
    osL F on C ≤ osL G on C + ((K : ℝ) : EReal) := by
  refine oneSidedLipschitz_le_of_forall fun x hx y hy hxy => ?_
  have hw : 0 < ‖x - y‖ ^ 2 := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 hxy)) 2
  -- `F x - F y = (G x - G y) + ((F - G) x - (F - G) y)`: subadditivity, then Cauchy–Schwarz and
  -- the Lipschitz bound on the second term
  have hadd := (RegularPairing.ofNorm E).add_left_le (G x - G y) ((F - G) x - (F - G) y) (x - y)
  have hCS := (RegularPairing.ofNorm E).le_norm_mul_norm ((F - G) x - (F - G) y) (x - y)
  have hL : ‖(F - G) x - (F - G) y‖ ≤ K * ‖x - y‖ := by
    simpa [dist_eq_norm] using h.dist_le_mul x hx y hy
  rw [show G x - G y + ((F - G) x - (F - G) y) = F x - F y by simp only [Pi.sub_apply]; abel]
    at hadd
  simp only [RegularPairing.ofNorm_eq_normPairing] at hadd hCS
  calc ((normPairing (F x - F y) (x - y) / ‖x - y‖ ^ 2 : ℝ) : EReal)
      ≤ ((normPairing (G x - G y) (x - y) / ‖x - y‖ ^ 2 : ℝ) : EReal) + ((K : ℝ) : EReal) := by
        rw [← EReal.coe_add, EReal.coe_le_coe_iff, div_add' _ _ _ hw.ne']
        gcongr
        nlinarith [norm_nonneg (x - y), norm_nonneg ((F - G) x - (F - G) y)]
    _ ≤ osL G on C + ((K : ℝ) : EReal) := add_le_add (le_oneSidedLipschitz hx hy hxy) le_rfl

/-- **Uniform monotonicity**: a map with `osL F on C < 0` is injective on `C`. -/
theorem injOn_of_oneSidedLipschitz_neg (h : osL F on C < 0) : InjOn F C := by
  -- a real `b < 0` above `osL`, then the lower bound `‖F x - F y‖ ≥ -b ‖x - y‖`
  obtain ⟨b, hb, hb0⟩ := EReal.exists_between_coe_real h
  have hb0 : b < 0 := EReal.coe_lt_coe_iff.1 hb0
  intro x hx y hy hxy
  have := neg_mul_norm_sub_le_of_oneSidedLipschitz_le hb.le hx hy
  rw [hxy, sub_self, norm_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (by nlinarith [norm_nonneg (x - y)]))

end General

/-! ### Inner product spaces -/

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {C : Set E} {F : E → E}

/-- **`osL` on an inner product space**: `osL F on C ≤ b` iff
`⟪F x - F y, x - y⟫ ≤ b ‖x - y‖²` for all `x, y ∈ C`. -/
@[blueprint "thm:oneSidedLipschitz-le-iff-inner"
  (title := "One-sided Lipschitz bounds on an inner product space")
  (statement := /-- On a real inner product space, $\operatorname{osL}(F) \le b$ on $C$
    (\cref{def:oneSidedLipschitz}) if and only if
    $\langle F(x) - F(y), x - y \rangle \le b \|x - y\|^2$ for all $x, y \in C$. -/)
  (proof := /-- The pairing of the norm is the inner product: for $w \ne 0$ the norm is
    differentiable at $w$ with derivative $\langle \cdot, w \rangle / \|w\|$; apply
    \cref{thm:oneSidedLipschitz-le-iff}. -/)]
theorem oneSidedLipschitz_le_iff_inner (b : ℝ) :
    osL F on C ≤ b ↔ ∀ x ∈ C, ∀ y ∈ C, ⟪F x - F y, x - y⟫ ≤ b * ‖x - y‖ ^ 2 := by
  simp only [oneSidedLipschitz_le_iff, RegularPairing.normPairing_eq_inner]

end Inner

/-! ### Maps of `ℝⁿ` -/

namespace Matrix

open WithLp (toLp ofLp)

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {C : Set (n → ℝ)}
  {F : (n → ℝ) → n → ℝ} {J : (n → ℝ) → Matrix n n ℝ}

/-- **The Jacobian test in a weighted ℓᵖ norm**: on an open convex set, for `F` differentiable
with Jacobian matrix `J`, `osL_{p,R} F on C = sup_{x ∈ C} μ_{p,R}(J x)`. -/
@[blueprint "thm:oneSidedLipschitzLpWeight-eq-iSup"
  (title := "The Jacobian test in weighted $\\ell_p$ and $\\ell_2$ norms")
  (statement := /-- Let $C \subseteq \mathbb{R}^n$ be open and convex and $F$
    differentiable on $C$ with Jacobian matrix $J$.  For $p \in [1, \infty]$ and invertible $R$,
    and for $P \succ 0$,
    \[ \operatorname{osL}_{p,R}(F) = \sup_{x \in C} \mu_{p,R}(J(x)), \qquad
      \operatorname{osL}_{2,P^{1/2}}(F) = \sup_{x \in C} \mu_{2,P^{1/2}}(J(x)). \] -/)
  (proof := /-- \cref{thm:oneSidedLipschitz-eq-iSup-logNorm} in the weighted norm, where the
    derivative of $F$ is the matrix $J(x)$ acting on $\mathbb{R}^n$. -/)]
theorem oneSidedLipschitzLpWeight_eq_iSup (p : ℝ≥0∞) [Fact (1 ≤ p)] {R : Matrix n n ℝ}
    (hR : IsUnit R) (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hF : ∀ x ∈ C, HasJacobianAt F (J x) x) :
    osL_{p, R} F on C = ⨆ x ∈ C, (μ_{p, R} (J x) : EReal) := by
  -- the identity of `ℝⁿ`, from the sup norm to `‖R x‖_p`, carries the derivative across
  let e : (n → ℝ) ≃L[ℝ] WeightedNorm (toWeight p hR) :=
    (PiLp.continuousLinearEquiv p ℝ fun _ : n => ℝ).symm.trans
      (WeightedNorm.equiv (toWeight p hR))
  -- the set as the definition writes it, `R '' (toLp '' C)`, which is `e '' C`
  have hset : WeightedNorm.equiv (toWeight p hR) '' (toLp p '' C) = e '' C := by
    rw [Set.image_image]
    rfl
  have key := @oneSidedLipschitz_eq_iSup_logNorm (WeightedNorm (toWeight p hR)) _ _
    (WeightedNorm.equiv (toWeight p hR) '' (toLp p '' C)) (fun z => e (F (e.symm z))) _
    (fun z => (e : (n → ℝ) →L[ℝ] _).comp
      ((J (e.symm z)).toCLM.comp (e.symm : _ →L[ℝ] n → ℝ)))
    (hset ▸ e.isOpenMap C hCo) (hset ▸ hCc.linear_image e.toLinearEquiv.toLinearMap)
    (by rw [hset]; rintro _ ⟨x, hx, rfl⟩; simpa using (hF x hx).conj e)
  conv at key => rhs; rw [hset, iSup_image]
  rw [oneSidedLipschitzLpWeight, dif_pos hR, WeightedNorm.oneSidedLipschitz]
  convert key using 2
  -- `μ_{p,R}(J x)` is, by definition, the log norm of the operator `e J(x) e⁻¹`
  funext x
  simp only [logNormLpWeight, dif_pos hR, WeightedNorm.logNorm, e.symm_apply_apply]
  rfl

/-- **The Jacobian test in the norm `√(xᵀ P x)`**: on an open convex set, for `F` differentiable
with Jacobian matrix `J`, `osL_{2,P^½} F on C = sup_{x ∈ C} μ_{2,P^½}(J x)`. -/
theorem oneSidedLipschitzL2PosDef_eq_iSup {P : Matrix n n ℝ} (hP : P.PosDef)
    (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hF : ∀ x ∈ C, HasJacobianAt F (J x) x) :
    osL_{2,P^½} F on C = ⨆ x ∈ C, (μ_{2,P^½} (J x) : EReal) := by
  -- the general test in the norm `√(xᵀ P x)`, with `F` and its derivative moved there by the
  -- identity `e`
  set e := WeightedEuclidean.equiv hP
  rw [oneSidedLipschitzL2PosDef, dif_pos hP]
  simp only [logNormL2PosDef, dif_pos hP]
  rw [oneSidedLipschitz_eq_iSup_logNorm (e.isOpenMap C hCo)
    (hCc.linear_image e.toLinearEquiv.toLinearMap)
    (DF := fun z => WeightedEuclidean.toCLM hP (J (e.symm z))) (by
      rintro _ ⟨x, hx, rfl⟩
      beta_reduce
      rw [e.symm_apply_apply]
      exact (hF x hx).conj e), iSup_image]
  simp only [e.symm_apply_apply]

omit [DecidableEq n] [Nonempty n] in
/-- **`osL` in the norm `√(xᵀ P x)` as an increment condition**: `osL_{2,P^½} F on C ≤ b` iff
`(F x - F y)ᵀ P (x - y) ≤ b (x - y)ᵀ P (x - y)` for all `x, y ∈ C`. -/
@[blueprint "thm:oneSidedLipschitzL2PosDef-le-iff"
  (title := "Weighted Euclidean one-sided Lipschitz bounds")
  (statement := /-- For $P \succ 0$, $\operatorname{osL}_{2,P^{1/2}}(F) \le b$ on $C$ if and only
    if $(F(x) - F(y))^\top P (x - y) \le b \, (x - y)^\top P (x - y)$ for all $x, y \in C$.  With
    \cref{thm:oneSidedLipschitzLpWeight-eq-iSup,thm:logNormL2PosDef-le-iff-lmi}, both are
    equivalent to $P J(x) + J(x)^\top P \preceq 2 b P$ on $C$ for differentiable
    $F$ on an open convex $C$. -/)
  (proof := /-- \cref{thm:oneSidedLipschitz-le-iff-inner} in the inner product
    $x^\top P y$. -/)]
theorem oneSidedLipschitzL2PosDef_le_iff {P : Matrix n n ℝ} (hP : P.PosDef)
    (b : ℝ) :
    osL_{2,P^½} F on C ≤ b ↔
      ∀ x ∈ C, ∀ y ∈ C, (F x - F y) ⬝ᵥ (P *ᵥ (x - y)) ≤ b * ((x - y) ⬝ᵥ (P *ᵥ (x - y))) := by
  -- the inner-product form in `xᵀ P y`, whose norm squared is `xᵀ P x`
  rw [oneSidedLipschitzL2PosDef, dif_pos hP, oneSidedLipschitz_le_iff_inner b]
  simp only [forall_mem_image, ContinuousLinearEquiv.symm_apply_apply]
  refine forall₂_congr fun x _ => forall₂_congr fun y _ => ?_
  rw [← real_inner_self_eq_norm_sq, WeightedEuclidean.inner_def, WeightedEuclidean.inner_def]
  exact Iff.rfl

/-- **`osL` in a weighted ℓᵖ norm through any pairing**: on an open convex set, for `F`
differentiable on `C`, `osL_{p,R} F on C ≤ b` iff
`⟦R (F x - F y); R (x - y)⟧ ≤ b ‖R (x - y)‖ₚ²` on `C`, for every
regular pairing of the ℓᵖ norm; with the sign (`p = 1`) or max (`p = ∞`) pairing it is explicit. -/
@[blueprint "thm:oneSidedLipschitzLpWeight-le-iff-pairing"
  (title := "Weighted $\\ell_p$ one-sided Lipschitz bounds through a pairing")
  (statement := /-- Let $C$ be open and convex, $F$ differentiable on $C$, $R$
    invertible, and $\pair{\cdot}{\cdot}$ a regular pairing for the $\ell_p$ norm, for instance
    the sign (\cref{def:regularPairing-sign}) or max (\cref{def:regularPairing-max}) pairing.
    Then $\operatorname{osL}_{p,R}(F) \le b$ on $C$ if and only if
    $\pair{R(F(x) - F(y))}{R(x - y)} \le b \|R(x - y)\|_p^2$ for all $x, y \in C$. -/)
  (proof := /-- \cref{thm:oneSidedLipschitzLpWeight-eq-iSup} and
    \cref{thm:regularPairing-logNorm-fderiv-le-iff} for the weighted pairing
    (\cref{def:regularPairing-weighted}). -/)]
theorem oneSidedLipschitzLpWeight_le_iff_pairing (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (q : RegularPairing (WithLp p (n → ℝ))) {R : Matrix n n ℝ} (hR : IsUnit R)
    (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hF : ∀ x ∈ C, HasJacobianAt F (J x) x) (b : ℝ) :
    osL_{p, R} F on C ≤ b ↔ ∀ x ∈ C, ∀ y ∈ C,
      ⟦toLp p (R *ᵥ (F x - F y)); toLp p (R *ᵥ (x - y))⟧_q ≤ b * ‖toLp p (R *ᵥ (x - y))‖ ^ 2 := by
  -- the identity of `ℝⁿ` into the weighted space, as in `oneSidedLipschitzLpWeight_eq_iSup`
  let e : (n → ℝ) ≃L[ℝ] WeightedNorm (toWeight p hR) :=
    (PiLp.continuousLinearEquiv p ℝ fun _ : n => ℝ).symm.trans
      (WeightedNorm.equiv (toWeight p hR))
  -- `μ_{p,R}(J x) ≤ b` on `C` is the any-pairing Jacobian test for `e F e⁻¹` on `e C`
  have key := (q.weighted (toWeight p hR)).logNorm_fderiv_le_iff (C := e '' C)
    (F := fun z => e (F (e.symm z)))
    (DF := fun z => (e : (n → ℝ) →L[ℝ] _).comp
      ((J (e.symm z)).toCLM.comp (e.symm : _ →L[ℝ] n → ℝ)))
    (e.isOpenMap C hCo) (hCc.linear_image e.toLinearEquiv.toLinearMap)
    (by rintro _ ⟨x, hx, rfl⟩; simpa using (hF x hx).conj e) b
  simp only [forall_mem_image, e.symm_apply_apply, ← map_sub] at key
  rw [oneSidedLipschitzLpWeight_eq_iSup p hR hCo hCc hF]
  simp only [iSup₂_le_iff, EReal.coe_le_coe_iff]
  convert key using 4 with x hx
  · simp only [logNormLpWeight, dif_pos hR, WeightedNorm.logNorm]
    rfl
  · -- `⟦e u; e v⟧_{q,R} = ⟦R u; R v⟧_q` and `‖e v‖ = ‖R v‖ₚ`
    simp only [e, ContinuousLinearEquiv.trans_apply, RegularPairing.weighted_equiv,
      WeightedNorm.norm_equiv]
    rfl

/-! #### Weighted ℓ¹ and ℓ∞ tests along ordered increments -/

omit [Fintype n] [Nonempty n] in
/-- A matrix with nonnegative off-diagonal entries (a Metzler matrix) is its own Metzler majorant,
so its weighted ℓ¹ and ℓ∞ log norms are `maxⱼ (ηᵀ A)ⱼ / ηⱼ` and `maxᵢ (A η)ᵢ / ηᵢ`. -/
theorem metzlerMajorant_eq_self {A : Matrix n n ℝ} (hA : A.IsMetzler) :
    metzlerMajorant A = A := by
  ext i j
  unfold metzlerMajorant
  split_ifs with h
  · rw [h]
  · exact abs_of_nonneg (hA i j h)

omit [Nonempty n] in
/-- **The weighted ℓ¹ test along ordered increments**: on an open convex set, for `F`
differentiable on `C` with Jacobian matrix `J`, `ηᵀ J(x) ≤ b ηᵀ` on `C` iff
`ηᵀ (F x - F y) ≤ b ηᵀ (x - y)` for all
`y ≤ x` in `C`.  For a Metzler `J` and `η > 0`, the left side is `μ_{1,[η]}(J x) ≤ b`. -/
@[blueprint "thm:row-test-iff-ordered-increments"
  (title := "Weighted $\\ell_1$ and $\\ell_\\infty$ tests along ordered increments")
  (statement := /-- Let $C \subseteq \mathbb{R}^n$ be open and convex and $F$
    differentiable on $C$ with Jacobian matrix $J$, and let $\eta \in \mathbb{R}^n$ and
    $b \in \mathbb{R}$.  Then
    \[ \eta^\top J(x) \le b \eta^\top \text{ on } C \iff
      \eta^\top (F(x) - F(y)) \le b \eta^\top (x - y) \text{ for all } y \le x \text{ in } C, \]
    \[ J(x) \eta \le b \eta \text{ on } C \iff
      F(y + \beta \eta) - F(y) \le b \beta \eta
      \text{ for all } \beta > 0,\ y, y + \beta\eta \in C. \]
    For a Metzler $J$ and $\eta > 0$, the left sides are $\mu_{1,[\eta]}(J(x)) \le b$ and
    $\mu_{\infty,[\eta]^{-1}}(J(x)) \le b$
    (\cref{thm:logNorm-l1-diagonal-le-iff,thm:logNorm-linfty-diagonal-le-iff}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Chapter 3. -/)
  (proof := /-- $\Rightarrow$: by the mean value theorem for the real function
    $t \mapsto \eta^\top F(y + t(x - y))$, $\eta^\top (F(x) - F(y)) = \eta^\top J(c)(x - y)$
    for some $c$ on the segment, and $\eta^\top J(c)(x - y) \le b \eta^\top (x - y)$ since
    $x - y \ge 0$; for the second test, apply it to each component $F_i$ along
    $y + t \beta \eta$.  $\Leftarrow$: divide the increment condition at $x = y + h e_j$ (resp.
    $y + \beta \eta$) by $h$ (resp. $\beta$) and let it tend to $0^+$. -/)]
theorem row_le_iff_ordered_increments (η : n → ℝ) (b : ℝ) (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hF : ∀ x ∈ C, HasJacobianAt F (J x) x) :
    (∀ x ∈ C, η ᵥ* J x ≤ b • η) ↔
      ∀ x ∈ C, ∀ y ∈ C, y ≤ x → η ⬝ᵥ (F x - F y) ≤ b * (η ⬝ᵥ (x - y)) := by
  -- `η ⬝ᵥ F` has derivative `v ↦ η ⬝ᵥ J(x) v`
  let ℓ : (n → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ η)
  constructor
  · -- Lagrange's mean value theorem on the segment `[y, x]`, where `x - y ≥ 0`
    intro h x hx y hy hyx
    obtain ⟨z, hz, hmvt⟩ := domain_mvt (f := fun z => η ⬝ᵥ F z)
      (f' := fun z => ℓ.comp (J z).toCLM)
      (fun z hz => (ℓ.hasFDerivAt.comp z (hF z hz)).hasFDerivWithinAt) hCc hy hx
    simp only [ℓ, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
      dotProductBilin_apply_apply, toCLM_apply] at hmvt
    rw [dotProduct_sub, hmvt, dotProduct_mulVec, ← smul_eq_mul, ← smul_dotProduct]
    exact dotProduct_le_dotProduct_of_nonneg_right (h z (hCc.segment_subset hy hx hz))
      (sub_nonneg.2 hyx)
  · -- the increment condition at `x + t eⱼ ≥ x`, divided by `t → 0⁺`
    intro h x hx j
    have key := (hF x hx).apply_le_of_increment_le (hCo.mem_nhds hx) ℓ.continuous
      (fun a _ u => by rw [map_smul, smul_eq_mul]) (Pi.single j 1) (c := b * η j)
      fun t ht hmem => by
        have hinc := h _ hmem x hx (le_add_of_nonneg_right
          (smul_nonneg ht.le (Pi.single_nonneg.2 zero_le_one)))
        rw [add_sub_cancel_left, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at hinc
        simpa [ℓ, mul_left_comm] using hinc
    simpa [ℓ, dotProduct_mulVec, dotProduct_single] using key

omit [Nonempty n] in
/-- **The weighted ℓ∞ test along increments in the direction `η`**: on an open convex set, for `F`
differentiable on `C` with Jacobian matrix `J`, `J(x) η ≤ b η` on `C` iff
`F(y + β η) - F(y) ≤ b β η` whenever `β > 0` and `y, y + β η ∈ C`.  For a Metzler `J` and
`η > 0`, the left side is `μ_{∞,[η]⁻¹}(J x) ≤ b`. -/
theorem col_le_iff_increments_along (η : n → ℝ) (b : ℝ) (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hF : ∀ x ∈ C, HasJacobianAt F (J x) x) :
    (∀ x ∈ C, J x *ᵥ η ≤ b • η) ↔
      ∀ y ∈ C, ∀ β > 0, y + β • η ∈ C → F (y + β • η) - F y ≤ (b * β) • η := by
  -- `Fᵢ` has derivative `v ↦ (J(x) v)ᵢ`
  let πᵢ (i : n) : (n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  constructor
  · -- Lagrange's mean value theorem for `Fᵢ` on the segment `[y, y + β η]`
    intro h y hy β hβ hyβ i
    obtain ⟨z, hz, hmvt⟩ := domain_mvt (f := fun z => F z i)
      (f' := fun z => (πᵢ i).comp (J z).toCLM)
      (fun z hz => ((πᵢ i).hasFDerivAt.comp z (hF z hz)).hasFDerivWithinAt) hCc hy hyβ
    simp only [πᵢ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, toCLM_apply,
      add_sub_cancel_left, mulVec_smul, Pi.smul_apply, smul_eq_mul] at hmvt
    have hJ := h z (hCc.segment_subset hy hyβ hz) i
    simp only [Pi.smul_apply, smul_eq_mul] at hJ ⊢
    rw [Pi.sub_apply, hmvt]
    nlinarith
  · -- the increment condition at `x + t η`, divided by `t → 0⁺`
    intro h x hx i
    have key := (hF x hx).apply_le_of_increment_le (hCo.mem_nhds hx) (πᵢ i).continuous
      (fun a _ u => by rw [map_smul, smul_eq_mul]) η (c := b * η i) fun t ht hmem => by
        have hinc := h x hx t ht hmem i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hinc
        simpa [πᵢ, mul_comm, mul_left_comm] using hinc
    simpa [πᵢ] using key

end Matrix

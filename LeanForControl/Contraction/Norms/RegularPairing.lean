import LeanForControl.Contraction.Norms.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import LeanForControl.Analysis.Norm
import LeanForControl.Analysis.DiniDeriv
import Architect

/-!
# `Contraction.Norms.RegularPairing` — the algebra of regular pairings, and constructions

Facts that follow from the axioms of a regular pairing alone, the two regular pairings every
space of interest carries, and the weighted pairing of a weighted norm.

* `abs_le_norm_mul_norm`, `abs_sub_le` — the two-sided Cauchy–Schwarz inequality, and Lipschitz
  continuity in the first argument.
* `add_smul_self` — partial linearity, `⟦x + a y, y⟧ = ⟦x, y⟧ + a ‖y‖²` for every real `a`.
* `RegularPairing.ofInner` — the inner product of an inner product space.
* `RegularPairing.ofNorm` — the regular pairing of the norm, on every normed space: the right
  derivative of the norm, `⟦x, y⟧ = ‖y‖ · d⁺/dh ‖y + h x‖ |_{h = 0}`.
* `RegularPairing.weighted` — a regular pairing and an invertible weight `R` give the regular
  pairing `⟦x, y⟧_R = ⟦R x, R y⟧` for the weighted norm `‖x‖_R = ‖R x‖`.

References: A. V. Proskurnikov and F. Bullo, *Regular Pairings for Nonquadratic Lyapunov
Functions and Contraction Analysis*, SIAM J. Control Optim. 64(1):496–521 (2026),
doi:10.1137/24M1689685, Lemma 2.6, Definitions 2.3 and 3.3, Theorem 3.5 and Corollary 3.9.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace RegularPairing

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : RegularPairing E)

@[simp] lemma zero_left (y : E) : p 0 y = 0 := by
  simpa using p.smul_left 0 le_rfl 0 y

@[simp] lemma zero_right (x : E) : p x 0 = 0 := by
  simpa using p.smul_right 0 le_rfl x 0

/-- **The two-sided Cauchy–Schwarz inequality** `|⟦x, y⟧| ≤ ‖x‖ ‖y‖`: the lower bound follows from
subadditivity, `0 = ⟦0, y⟧ ≤ ⟦x, y⟧ + ⟦-x, y⟧`. -/
@[blueprint "lem:regularPairing-abs-le-norm-mul-norm"
  (title := "Cauchy--Schwarz inequality for a regular pairing")
  (latexEnv := "lemma")
  (statement := /-- For a regular pairing (\cref{def:regularPairing}),
    $|\pair{x}{y}| \le \|x\| \, \|y\|$ for all $x, y$. -/)
  (proof := /-- The upper bound is an axiom.  For the lower bound,
    $0 = \pair{0}{y} \le \pair{x}{y} + \pair{-x}{y} \le \pair{x}{y} + \|x\| \, \|y\|$. -/)]
lemma abs_le_norm_mul_norm (x y : E) : |p x y| ≤ ‖x‖ * ‖y‖ := by
  have h := p.add_left_le x (-x) y
  rw [add_neg_cancel, zero_left] at h
  have h' := p.le_norm_mul_norm (-x) y
  rw [norm_neg] at h'
  exact abs_le.2 ⟨by linarith, p.le_norm_mul_norm x y⟩

/-- **A regular pairing is Lipschitz in its first argument**, with constant `‖y‖`. -/
@[blueprint "lem:regularPairing-abs-sub-le"
  (title := "Lipschitz continuity in the first argument")
  (latexEnv := "lemma")
  (statement := /-- For a regular pairing (\cref{def:regularPairing}),
    $|\pair{x_1}{y} - \pair{x_2}{y}| \le \|x_1 - x_2\| \, \|y\|$ for all $x_1, x_2, y$.

    Reference: Proskurnikov and Bullo, SIAM J. Control Optim. (2026), Lemma 2.6. -/)
  (proof := /-- By subadditivity and Cauchy--Schwarz,
    $\pair{x_1}{y} \le \pair{x_1 - x_2}{y} + \pair{x_2}{y} \le \|x_1 - x_2\| \|y\|
    + \pair{x_2}{y}$; exchange $x_1$ and $x_2$. -/)]
lemma abs_sub_le (x₁ x₂ y : E) : |p x₁ y - p x₂ y| ≤ ‖x₁ - x₂‖ * ‖y‖ := by
  have h₁ := p.add_left_le (x₁ - x₂) x₂ y
  have h₂ := p.add_left_le (x₂ - x₁) x₁ y
  rw [sub_add_cancel] at h₁ h₂
  have h₃ := p.le_norm_mul_norm (x₁ - x₂) y
  have h₄ := p.le_norm_mul_norm (x₂ - x₁) y
  rw [norm_sub_rev] at h₄
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- `⟦a y, y⟧ = a ‖y‖²` for every real `a`: for `a ≥ 0` by homogeneity, for `a < 0` by the
straight-angle property. -/
lemma smul_self (a : ℝ) (y : E) : p (a • y) y = a * ‖y‖ ^ 2 := by
  rcases le_total 0 a with ha | ha
  · rw [p.smul_left a ha, p.self]
  · have h : a • y = (-a) • -y := by rw [smul_neg, neg_smul, _root_.neg_neg]
    rw [h, p.smul_left (-a) (by linarith), p.neg_self]
    ring

/-- **Partial linearity**: `⟦x + a y, y⟧ = ⟦x, y⟧ + a ‖y‖²` for every real `a`. -/
@[blueprint "lem:regularPairing-add-smul-self"
  (title := "Partial linearity of a regular pairing")
  (latexEnv := "lemma")
  (statement := /-- For a regular pairing (\cref{def:regularPairing}),
    $\pair{x + a y}{y} = \pair{x}{y} + a \|y\|^2$ for all $x, y$ and every $a \in \mathbb{R}$.

    Reference: Proskurnikov and Bullo, SIAM J. Control Optim. (2026), Definition 3.3 and
    Theorem 3.5, (i) $\Rightarrow$ (ii). -/)
  (proof := /-- The straight-angle property gives $\pair{a y}{y} = a \|y\|^2$ for every real $a$.
    Subadditivity gives $\pair{x + a y}{y} \le \pair{x}{y} + a\|y\|^2$, and, applied to
    $x = (x + a y) + (-a) y$, the reverse inequality. -/)]
lemma add_smul_self (x y : E) (a : ℝ) : p (x + a • y) y = p x y + a * ‖y‖ ^ 2 := by
  have h₁ := p.add_left_le x (a • y) y
  have h₂ := p.add_left_le (x + a • y) ((-a) • y) y
  rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero] at h₂
  rw [p.smul_self] at h₁ h₂
  linarith

end Algebra

/-! ### The inner product -/

section Inner

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The inner product is a regular pairing**, `⟦x, y⟧ = ⟪x, y⟫`. -/
@[blueprint "def:regularPairing-ofInner"
  (title := "The inner product as a regular pairing")
  (statement := /-- On a real inner product space, $\pair{x}{y} = \langle x, y \rangle$ is a
    regular pairing (\cref{def:regularPairing}). -/)]
noncomputable def ofInner : RegularPairing E where
  toFun x y := ⟪x, y⟫
  add_left_le x₁ x₂ y := (inner_add_left x₁ x₂ y).le
  smul_left a _ x y := real_inner_smul_left x y a
  smul_right a _ x y := real_inner_smul_right x y a
  neg_neg x y := inner_neg_neg x y
  self x := real_inner_self_eq_norm_sq x
  le_norm_mul_norm x y := real_inner_le_norm x y
  neg_self x := by rw [inner_neg_left, real_inner_self_eq_norm_sq]

@[simp] lemma ofInner_apply (x y : E) : ofInner E x y = ⟪x, y⟫ := rfl

end Inner

/-! ### The regular pairing of the norm -/

section Norm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `∂⁺‖y‖[x]`: the right derivative of the norm at `y` in the direction `x`. -/
local notation "∂⁺‖" y "‖[" x "]" => derivWithin (fun h : ℝ => ‖y + h • x‖) (Ioi 0) 0

/-- The chain rule for `h ↦ a h`: `h ↦ ‖y + (a h) x‖` has right derivative `a ∂⁺‖y‖[x]`. -/
private lemma hasDerivWithinAt_norm_add_mul_smul {a : ℝ} (ha : 0 < a) (x y : E) :
    HasDerivWithinAt (fun h : ℝ => ‖y + (a * h) • x‖) (a * ∂⁺‖y‖[x]) (Ioi 0) 0 := by
  have := HasDerivWithinAt.scomp (g₁ := fun h : ℝ => ‖y + h • x‖) 0
    (by simp only [mul_zero]; exact hasDerivWithinAt_norm_add_smul x y)
    ((hasDerivAt_id' 0).const_mul a).hasDerivWithinAt
    (fun h (hh : 0 < h) => mul_pos ha hh : MapsTo (a * ·) (Ioi 0) (Ioi 0))
  simp only [Function.comp_def, mul_one, smul_eq_mul] at this
  exact this

/-- **The regular pairing of the norm**, on every normed space: its right derivative,
`⟦x, y⟧ = ‖y‖ · d⁺/dh ‖y + h x‖ |_{h = 0}`, the upper James–Miličić–Tapia pairing. -/
@[blueprint "def:regularPairing-ofNorm"
  (title := "The regular pairing of a norm")
  (statement := /-- On a real normed space,
    \[ \pair{x}{y} = \|y\| \lim_{h \to 0^+} \frac{\|y + h x\| - \|y\|}{h} \]
    is a regular pairing (\cref{def:regularPairing}); the limit exists because
    $h \mapsto \|y + h x\|$ is convex.

    Reference: Proskurnikov and Bullo, SIAM J. Control Optim. (2026), Definition 2.3 and
    Corollary 3.9. -/)
  (proof := /-- Each axiom is a property of the right derivative of $h \mapsto \|y + h x\|$,
    obtained by comparing that function with one whose derivative is known.
    Subadditivity: $y + h(x_1 + x_2)$ is the midpoint of $y + 2h x_1$ and $y + 2h x_2$.
    Cauchy--Schwarz: $\|y + h x\| \le \|y\| + h \|x\|$.  Compatibility with the norm and the
    straight-angle property: $\|x \pm h x\| = (1 \pm h)\|x\|$ for $0 \le h < 1$. -/)]
noncomputable def ofNorm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    RegularPairing E where
  toFun x y := ‖y‖ * ∂⁺‖y‖[x]
  add_left_le x₁ x₂ y := by
    -- `y + h (x₁ + x₂)` is the midpoint of `y + 2h x₁` and `y + 2h x₂`
    have hle := (hasDerivWithinAt_norm_add_smul (x₁ + x₂) y).le_of_le_of_eq
      (((hasDerivWithinAt_norm_add_mul_smul two_pos x₁ y).div_const 2).add
        ((hasDerivWithinAt_norm_add_mul_smul two_pos x₂ y).div_const 2)) (by simp)
      (Eventually.of_forall fun h => by
        simp only [Pi.add_apply]
        rw [show y + h • (x₁ + x₂) = (1 / 2 : ℝ) • (y + (2 * h) • x₁) +
          (1 / 2 : ℝ) • (y + (2 * h) • x₂) by module]
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num)]
        ring)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hle.trans_eq (by ring)) (norm_nonneg y)
  smul_left a ha x y := by
    rcases ha.eq_or_lt with rfl | ha
    · simp
    -- `‖y + h (a x)‖ = ‖y + (a h) x‖`
    rw [((hasDerivWithinAt_norm_add_mul_smul ha x y).congr (fun h _ => by
      rw [smul_smul, mul_comm]) (by simp)).derivWithin (uniqueDiffWithinAt_Ioi 0)]
    ring
  smul_right a ha x y := by
    rcases ha.eq_or_lt with rfl | ha
    · simp
    -- `‖a y + h x‖ = a ‖y + (a⁻¹ h) x‖`
    have hscale (h : ℝ) : ‖a • y + h • x‖ = a * ‖y + (a⁻¹ * h) • x‖ := by
      rw [show a • y + h • x = a • (y + (a⁻¹ * h) • x) by
        rw [smul_add, smul_smul, mul_inv_cancel_left₀ ha.ne'], norm_smul,
        Real.norm_of_nonneg ha.le]
    rw [(((hasDerivWithinAt_norm_add_mul_smul (inv_pos.2 ha) x y).const_mul a).congr
      (fun h _ => hscale h) (hscale 0)).derivWithin (uniqueDiffWithinAt_Ioi 0), norm_smul,
      Real.norm_of_nonneg ha.le]
    field_simp
  neg_neg x y := by simp only [smul_neg, ← neg_add, norm_neg]
  self x := by
    -- along the ray through `x`, `‖x + h x‖ = (1 + h) ‖x‖`
    have hray : HasDerivWithinAt (fun h : ℝ => ‖x + h • x‖) ‖x‖ (Ioi 0) 0 := by
      refine ((((hasDerivAt_id' (0 : ℝ)).const_add 1).mul_const ‖x‖).hasDerivWithinAt
        |>.congr_of_eventuallyEq ?_ (by simp)).congr_deriv (one_mul _)
      filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      rw [show x + h • x = (1 + h) • x by module, norm_smul, Real.norm_of_nonneg (by linarith)]
    rw [hray.derivWithin (uniqueDiffWithinAt_Ioi 0), sq]
  le_norm_mul_norm x y := by
    -- `‖y + h x‖ ≤ ‖y‖ + h ‖x‖`
    have hle := (hasDerivWithinAt_norm_add_smul x y).le_of_le_of_eq
      (((hasDerivAt_id' (0 : ℝ)).mul_const ‖x‖).const_add ‖y‖).hasDerivWithinAt (by simp)
      (eventually_mem_nhdsWithin.mono fun h (hh : 0 < h) => by
        simpa [norm_smul, abs_of_pos hh] using norm_add_le y (h • x))
    rw [mul_comm ‖x‖]
    exact mul_le_mul_of_nonneg_left (hle.trans_eq (one_mul _)) (norm_nonneg y)
  neg_self x := by
    -- the straight angle: `‖x - h x‖ = (1 - h) ‖x‖` for `0 < h < 1`
    have hray : HasDerivWithinAt (fun h : ℝ => ‖x + h • -x‖) (-‖x‖) (Ioi 0) 0 := by
      refine ((((hasDerivAt_id' (0 : ℝ)).const_sub 1).mul_const ‖x‖).hasDerivWithinAt
        |>.congr_of_eventuallyEq ?_ (by simp)).congr_deriv (by ring)
      filter_upwards [Ioo_mem_nhdsGT one_pos] with h hh
      rw [show x + h • -x = (1 - h) • x by module, norm_smul,
        Real.norm_of_nonneg (by linarith [hh.2])]
    rw [hray.derivWithin (uniqueDiffWithinAt_Ioi 0)]
    ring

lemma ofNorm_apply (x y : E) :
    ofNorm E x y = ‖y‖ * derivWithin (fun h : ℝ => ‖y + h • x‖) (Ioi 0) 0 := rfl

end Norm

/-! ### Weighted pairings -/

section Weighted

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The weighted pairing**: a regular pairing on `F` and an invertible weight `R : E → F` give the
regular pairing `⟦x, y⟧_R = ⟦R x, R y⟧` for the weighted norm `‖x‖_R = ‖R x‖`. -/
@[blueprint "def:regularPairing-weighted"
  (title := "Weighted regular pairing")
  (statement := /-- Let $\pair{\cdot}{\cdot}$ be a regular pairing (\cref{def:regularPairing}) on
    $F$ and $R : E \to F$ an invertible bounded linear map.  Then
    $\pair{x}{y}_R = \pair{R x}{R y}$ is a regular pairing for the weighted norm
    $\|x\|_R = \|R x\|$ (\cref{def:weightedNorm}). -/)
  (proof := /-- $R$ is linear and $\|R x\| = \|x\|_R$, so each axiom for $\pair{\cdot}{\cdot}_R$ is
    the same axiom for $\pair{\cdot}{\cdot}$ at $R x$, $R y$. -/)]
noncomputable def weighted (p : RegularPairing F) (R : E ≃L[ℝ] F) :
    RegularPairing (WeightedNorm R) where
  toFun x y := p (WeightedNorm.weight R x) (WeightedNorm.weight R y)
  add_left_le x₁ x₂ y := by rw [map_add]; exact p.add_left_le _ _ _
  smul_left a ha x y := by rw [map_smul]; exact p.smul_left a ha _ _
  smul_right a ha x y := by rw [map_smul]; exact p.smul_right a ha _ _
  neg_neg x y := by rw [map_neg, map_neg]; exact p.neg_neg _ _
  self x := by rw [p.self, WeightedNorm.norm_weight]
  le_norm_mul_norm x y := by
    simpa only [WeightedNorm.norm_weight] using p.le_norm_mul_norm _ _
  neg_self x := by rw [map_neg, p.neg_self, WeightedNorm.norm_weight]

/-- `⟦x, y⟧_R = ⟦R x, R y⟧`, for vectors `x, y` of `E` measured in the weighted norm. -/
@[simp] lemma weighted_equiv (p : RegularPairing F) (R : E ≃L[ℝ] F) (x y : E) :
    p.weighted R (WeightedNorm.equiv R x) (WeightedNorm.equiv R y) = p (R x) (R y) := by
  simp [weighted, WeightedNorm.equiv]

end Weighted

end RegularPairing

import LeanForControl.Contraction.Norms.Lp
import Architect

/-!
# `Contraction.Norms.LpPairings` — the sign and max pairings

The regular pairings of the ℓ¹ and ℓ∞ norms on `ℝⁿ`, in closed form:

* `RegularPairing.sign` — the sign pairing `⟦x; y⟧₁ = ‖y‖₁ Σᵢ sign(yᵢ) xᵢ` for `‖·‖₁`;
* `RegularPairing.max` — the max pairing `⟦x; y⟧∞ = max_{i ∈ I∞(y)} yᵢ xᵢ` for `‖·‖∞`, where
  `I∞(y) = {i : |yᵢ| = ‖y‖∞}`.

With a weight `R`, `RegularPairing.weighted` gives the weighted pairings `⟦R x; R y⟧₁` and
`⟦R x; R y⟧∞`.  Through Lumer's inequality and its converse:

* `Matrix.logNormLpWeight_le_iff_pairing` — for any regular pairing of the ℓᵖ norm,
  `μ_{p,R}(A) ≤ c` iff `⟦R A x; R x⟧ ≤ c ‖R x‖ₚ²` for all `x`; with `RegularPairing.sign n`
  (`p = 1`) or `RegularPairing.max n` (`p = ∞`) the pairing is explicit.

References: F. Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), Section 2.4;
A. V. Proskurnikov and F. Bullo, *Regular Pairings for Nonquadratic Lyapunov Functions and
Contraction Analysis*, SIAM J. Control Optim. 64(1):496–521 (2026), doi:10.1137/24M1689685.
-/

open scoped LogNorm ENNReal

namespace RegularPairing

variable (n : Type*) [Fintype n]

/-! ### The sign pairing -/

/-- `|sign(y) x| ≤ |x|`. -/
private lemma sign_mul_le_abs (y x : ℝ) : (SignType.sign y : ℝ) * x ≤ |x| := by
  rcases lt_trichotomy y 0 with h | rfl | h
  · simp [sign_neg h, neg_le_abs]
  · simp
  · simp [sign_pos h, le_abs_self]

/-- **The sign pairing** `⟦x; y⟧₁ = ‖y‖₁ Σᵢ sign(yᵢ) xᵢ`, a regular pairing for the ℓ¹ norm. -/
@[blueprint "def:regularPairing-sign"
  (title := "The sign pairing")
  (statement := /-- On $\mathbb{R}^n$ with the $\ell_1$ norm,
    \[ \pair{x}{y}_1 = \|y\|_1 \sum_i \operatorname{sign}(y_i) \, x_i \]
    is a regular pairing (\cref{def:regularPairing}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Section 2.4. -/)
  (proof := /-- It is linear in $x$, and $\operatorname{sign}(a y) = \operatorname{sign}(y)$ for
    $a > 0$.  Since $\operatorname{sign}(x_i) x_i = |x_i|$,
    $\pair{\pm x}{x}_1 = \pm \|x\|_1^2$; since $\operatorname{sign}(y_i) x_i \le |x_i|$,
    $\pair{x}{y}_1 \le \|x\|_1 \|y\|_1$. -/)]
noncomputable def sign : RegularPairing (WithLp 1 (n → ℝ)) where
  toFun x y := ‖y‖ * ∑ i, (SignType.sign (y i) : ℝ) * x i
  add_left_le x₁ x₂ y := by
    simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib, le_refl]
  smul_left a _ x y := by
    simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  smul_right a ha x y := by
    rcases ha.eq_or_lt with rfl | ha
    · simp
    simp only [PiLp.smul_apply, smul_eq_mul, sign_mul, sign_pos ha, norm_smul,
      Real.norm_of_nonneg ha.le]
    simp [mul_assoc]
  neg_neg x y := by simp [Left.sign_neg]
  self x := by simp [sign_mul_self, PiLp.norm_eq_of_L1, sq]
  le_norm_mul_norm x y := by
    rw [mul_comm ‖x‖]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg y)
    rw [PiLp.norm_eq_of_L1]
    exact Finset.sum_le_sum fun i _ => by simpa using sign_mul_le_abs (y i) (x i)
  neg_self x := by simp [sign_mul_self, PiLp.norm_eq_of_L1, sq]

lemma sign_apply (x y : WithLp 1 (n → ℝ)) :
    sign n x y = ‖y‖ * ∑ i, (SignType.sign (y i) : ℝ) * x i := rfl

/-! ### The max pairing -/

/-- `I∞(y) = {i : |yᵢ| = ‖y‖∞}`, the coordinates where `y` attains its sup norm. -/
noncomputable def maxIndices (y : WithLp ∞ (n → ℝ)) : Finset n :=
  Finset.univ.filter fun i => |y i| = ‖y‖

variable {n}

lemma abs_le_norm_of_top (y : WithLp ∞ (n → ℝ)) (i : n) : |y i| ≤ ‖y‖ := by
  simpa using PiLp.norm_apply_le y i

lemma maxIndices_nonempty [Nonempty n] (y : WithLp ∞ (n → ℝ)) : (maxIndices n y).Nonempty := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => ‖y i‖)
  exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, by
    rw [PiLp.norm_eq_ciSup]; simpa using hi⟩⟩

/-- `I∞(a y) = I∞(y)` for `a > 0`. -/
private lemma maxIndices_smul {a : ℝ} (ha : 0 < a) (y : WithLp ∞ (n → ℝ)) :
    maxIndices n (a • y) = maxIndices n y := by
  ext i
  simp [maxIndices, norm_smul, abs_mul, abs_of_pos ha, ha.ne']

private lemma maxIndices_neg (y : WithLp ∞ (n → ℝ)) : maxIndices n (-y) = maxIndices n y := by
  ext i
  simp [maxIndices]

variable (n) [Nonempty n]

/-- **The max pairing** `⟦x; y⟧∞ = max_{i ∈ I∞(y)} yᵢ xᵢ`, a regular pairing for the ℓ∞ norm. -/
@[blueprint "def:regularPairing-max"
  (title := "The max pairing")
  (statement := /-- On $\mathbb{R}^n$ with the $\ell_\infty$ norm,
    \[ \pair{x}{y}_\infty = \max_{i \in I_\infty(y)} y_i x_i, \qquad
      I_\infty(y) = \{ i : |y_i| = \|y\|_\infty \}, \]
    is a regular pairing (\cref{def:regularPairing}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Section 2.4. -/)
  (proof := /-- A maximum of linear functions of $x$ is subadditive and positively homogeneous in
    $x$, and $I_\infty(a y) = I_\infty(y)$ for $a > 0$.  For $i \in I_\infty(x)$,
    $\pm x_i x_i = \pm \|x\|_\infty^2$; and $y_i x_i \le |y_i| |x_i| \le \|y\|_\infty
    \|x\|_\infty$. -/)]
noncomputable def max : RegularPairing (WithLp ∞ (n → ℝ)) where
  toFun x y := (maxIndices n y).sup' (maxIndices_nonempty y) fun i => y i * x i
  add_left_le x₁ x₂ y := Finset.sup'_le _ _ fun i hi => by
    rw [PiLp.add_apply, mul_add]
    exact add_le_add (Finset.le_sup' (fun i => y i * x₁ i) hi)
      (Finset.le_sup' (fun i => y i * x₂ i) hi)
  smul_left a ha x y := by
    rw [Finset.comp_sup'_eq_sup'_comp _ (a * ·) fun _ _ => mul_max_of_nonneg _ _ ha]
    exact Finset.sup'_congr _ rfl fun i _ => by
      simp only [PiLp.smul_apply, smul_eq_mul, Function.comp_apply]
      ring
  smul_right a ha x y := by
    rcases ha.eq_or_lt with rfl | ha
    · simp
    rw [Finset.comp_sup'_eq_sup'_comp _ (a * ·) fun _ _ => mul_max_of_nonneg _ _ ha.le]
    exact Finset.sup'_congr _ (maxIndices_smul ha y) fun i _ => by
      simp only [PiLp.smul_apply, smul_eq_mul, Function.comp_apply]
      ring
  neg_neg x y := Finset.sup'_congr _ (maxIndices_neg y) fun i _ => by simp
  self x := by
    rw [← Finset.sup'_const (maxIndices_nonempty x) (‖x‖ ^ 2)]
    exact Finset.sup'_congr _ rfl fun i hi => by
      rw [← (Finset.mem_filter.1 hi).2, sq_abs, sq]
  le_norm_mul_norm x y := Finset.sup'_le _ _ fun i _ => by
    calc y i * x i ≤ |y i| * |x i| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ ‖y‖ * ‖x‖ := mul_le_mul (abs_le_norm_of_top y i) (abs_le_norm_of_top x i)
          (abs_nonneg _) (norm_nonneg _)
      _ = ‖x‖ * ‖y‖ := mul_comm _ _
  neg_self x := by
    rw [← Finset.sup'_const (maxIndices_nonempty x) (-‖x‖ ^ 2)]
    exact Finset.sup'_congr _ rfl fun i hi => by
      rw [← (Finset.mem_filter.1 hi).2, PiLp.neg_apply, mul_neg, sq_abs, sq]

lemma max_apply (x y : WithLp ∞ (n → ℝ)) :
    max n x y = (maxIndices n y).sup' (maxIndices_nonempty y) fun i => y i * x i := rfl

end RegularPairing

namespace Matrix

open WithLp (toLp ofLp)

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- **Weighted ℓᵖ log norms through a pairing**: for a regular pairing `⟦·; ·⟧` of the ℓᵖ norm and
an invertible `R`, `μ_{p,R}(A) ≤ c` iff `⟦R A x; R x⟧ ≤ c ‖R x‖ₚ²` for all `x`.  With the sign
pairing (`p = 1`) or the max pairing (`p = ∞`) the left side is explicit. -/
@[blueprint "thm:logNormLpWeight-le-iff-pairing"
  (title := "Weighted $\\ell_p$ log norms through a pairing")
  (statement := /-- Let $\pair{\cdot}{\cdot}$ be a regular pairing (\cref{def:regularPairing}) for
    the $\ell_p$ norm on $\mathbb{R}^n$, for instance the sign pairing
    (\cref{def:regularPairing-sign}) for $p = 1$ or the max pairing
    (\cref{def:regularPairing-max}) for $p = \infty$.  For an invertible $R$, a matrix $A$ and
    $c \in \mathbb{R}$,
    \[ \mu_{p,R}(A) \le c \iff \pair{R A x}{R x} \le c \|R x\|_p^2 \text{ for all } x. \]
    The right side is $\pair{A x}{x}_R \le c \|x\|_{p,R}^2$ for the weighted pairing
    (\cref{def:regularPairing-weighted}). -/)
  (proof := /-- $\mu_{p,R}(A) = \mu_p(R A R^{-1})$ (\cref{thm:logNormLpWeight-eq}); apply Lumer's
    inequality (\cref{thm:regularPairing-pairing-le-logNorm}) and its converse
    (\cref{thm:regularPairing-logNorm-le}) to $R A R^{-1}$, and substitute $y = R x$. -/)]
theorem logNormLpWeight_le_iff_pairing (q : RegularPairing (WithLp p (n → ℝ))) {R : Matrix n n ℝ}
    (hR : IsUnit R) (A : Matrix n n ℝ) (c : ℝ) :
    μ_{p, R} A ≤ c ↔
      ∀ x : n → ℝ, ⟦toLp p (R *ᵥ A *ᵥ x); toLp p (R *ᵥ x)⟧_q ≤ c * ‖toLp p (R *ᵥ x)‖ ^ 2 := by
  have hdet := (isUnit_iff_isUnit_det R).1 hR
  rw [logNormLpWeight_eq p hR, logNormLp]
  -- `R A R⁻¹` applied to `R x` is `R A x`
  have hRx (x : n → ℝ) : toLpCLM p (R * A * R⁻¹) (toLp p (R *ᵥ x)) = toLp p (R *ᵥ A *ᵥ x) := by
    simp [toLpCLM, toLpLin_apply, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul R hdet]
  constructor
  · intro h x
    rw [← hRx]
    exact (q.pairing_le_logNorm _ _).trans (mul_le_mul_of_nonneg_right h (sq_nonneg _))
  · intro h
    refine q.logNorm_le fun y => ?_
    have hy : y = toLp p (R *ᵥ R⁻¹ *ᵥ ofLp y) := by
      simp [mulVec_mulVec, mul_nonsing_inv R hdet]
    rw [hy, hRx]
    exact h _

end Matrix

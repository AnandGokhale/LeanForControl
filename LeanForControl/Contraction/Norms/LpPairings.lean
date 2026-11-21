import LeanForControl.Contraction.Norms.Lp
import Architect

/-!
# `Contraction.Norms.LpPairings` — the sign and max pairings

The regular pairings of the ℓ¹ and ℓ∞ norms on `ℝⁿ`, in closed form:

* `RegularPairing.sign` — the sign pairing `⟦x; y⟧₁ = ‖y‖₁ Σᵢ sign(yᵢ) xᵢ` for `‖·‖₁`;
* `RegularPairing.max` — the max pairing `⟦x; y⟧∞ = max_{i ∈ I∞(y)} yᵢ xᵢ` for `‖·‖∞`, where
  `I∞(y) = {i : |yᵢ| = ‖y‖∞}`.

With a weight `R`, `RegularPairing.weighted` gives the weighted pairings `⟦R x; R y⟧₁` and
`⟦R x; R y⟧∞`.  They make explicit the pairing tests for any regular pairing of the ℓᵖ norm,
`Matrix.logNormLpWeight_le_iff_pairing` (`Lp.lean`) and
`Matrix.oneSidedLipschitzLpWeight_le_iff_pairing` (`OneSidedLipschitz.lean`).  Nothing else depends
on this file.

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

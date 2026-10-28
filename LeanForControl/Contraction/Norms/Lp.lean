import LeanForControl.Contraction.Norms.WeightedNorm
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Convex.Quasiconvex
import Architect

/-!
# `Contraction.Norms.Lp` — log norms of matrices for the ℓᵖ norms

Explicit formulas for the log norm of a matrix `A ∈ ℝⁿˣⁿ` acting on `ℝⁿ` with an ℓᵖ norm, plain or
weighted.  After `open scoped LogNorm`, `μ_{p} A` is the ℓᵖ log norm, `μ_{p, R} A` the log norm in
the weighted norm `‖x‖_{p,R} = ‖R x‖_p`, and `μ_{2,P^½} A` the log norm in `√(xᵀ P x)`; these, the
Metzler majorant and `λ_max` are defined in `Defs.lean`.

* `Matrix.logNormLpWeight_eq` — `μ_{p,R}(A) = μ_p(R A R⁻¹)`, for every `p` and invertible `R`.
* `Matrix.logNorm_linfty`, `Matrix.logNorm_l1` — `μ_∞(A) = maxᵢ (aᵢᵢ + ∑_{j ≠ i} |aᵢⱼ|)` and
  `μ_1(A) = maxⱼ (aⱼⱼ + ∑_{i ≠ j} |aᵢⱼ|)`; `Matrix.logNorm_toLin'` is the ℓ∞ formula for a matrix
  acting on `n → ℝ`, the form a Jacobian meets.
* `Matrix.logNorm_l1_diagonal`, `Matrix.logNorm_linfty_diagonal` — the diagonally weighted ℓ¹ and
  ℓ∞ log norms, `μ_{1,[η]}` and `μ_{∞,[η]⁻¹}`; `Matrix.logNorm_l1_diagonal_le_iff`,
  `Matrix.logNorm_linfty_diagonal_le_iff` — as linear inequalities `ηᵀ |A|_M ≤ b ηᵀ` and
  `|A|_M η ≤ b η` in the Metzler majorant `|A|_M`; both are quasiconvex in `η`.
* `Matrix.logNormL2PosDef_le_iff`, `Matrix.logNormL2PosDef_eq_lambdaMax` — for `P ≻ 0` and the
  norm `√(xᵀ P x)`, written `μ_{2,P^½}`: `μ_{2,P^½}(A) ≤ c` iff `vᵀ P A v ≤ c vᵀ P v`, and
  `μ_{2,P^½}(A) = λ_max((P A P⁻¹ + Aᵀ) / 2)`, with `λ_max = Matrix.lambdaMax`.  Both come from the
  inner-product results in `LogNorm.lean`.
* `Matrix.logNormL2PosDef_le_iff_lmi` — the LMI form `μ_{2,P^½}(A) ≤ b ⟺ Aᵀ P + P A ⪯ 2 b P`;
  quasiconvex in `P`.
* `Matrix.logNormLpWeight_two_eq` — a weight on the Euclidean norm is a `P`:
  `μ_{2,R}(A) = μ_{2,(RᵀR)^½}(A)`.
* `Matrix.logNorm_euclidean_le_iff`, `Matrix.logNorm_euclidean_eq_lambdaMax` — the case `P = I`
  (`Matrix.logNormL2PosDef_one`): `μ_2(A) ≤ c` iff `vᵀ A v ≤ c vᵀ v`, and
  `μ_2(A) = λ_max((A + Aᵀ) / 2)`.

References: F. Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), Section 2.4.3,
Table 2.1 and Lemma 2.11.
-/

open Set Filter Topology
open scoped LogNorm ENNReal
open scoped Matrix.Norms.Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ### The matrix log norms `μ_{p}` and `μ_{p, R}` -/

section Weight

omit [Nonempty n]

variable (p : ENNReal) [Fact (1 ≤ p)]

/-- **Weighted log norms of matrices**, `μ_{p,R}(A) = μ_p(R A R⁻¹)`, for every `p` and every
invertible weight `R`. -/
@[blueprint "thm:logNormLpWeight-eq"
  (title := "Weighted log norms of matrices")
  (statement := /-- For $p \in [1, \infty]$, an invertible $R \in \mathbb{R}^{n \times n}$ and
    $A \in \mathbb{R}^{n \times n}$, the log norm induced by $\|x\|_{p,R} = \|R x\|_p$ is
    $\mu_{p,R}(A) = \mu_p(R A R^{-1})$.

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Lemma 2.11. -/)
  (proof := /-- \cref{thm:weightedNorm-logNorm-eq}, with $R$ carrying $A$ to $R A R^{-1}$. -/)]
theorem logNormLpWeight_eq {R : Matrix n n ℝ} (hR : IsUnit R) (A : Matrix n n ℝ) :
    μ_{p, R} A = μ_{p} (R * A * R⁻¹) := by
  rw [logNormLpWeight, dif_pos hR, WeightedNorm.logNorm_eq, logNormLp]
  -- the weight carries `A` to `R A R⁻¹`
  congr 1
  ext x
  simp [toLpCLM, toLpLin_apply, mulVec_mulVec, Matrix.mul_assoc]

/-- The identity weight changes nothing, `μ_{p,I}(A) = μ_p(A)`. -/
lemma logNormLpWeight_one (A : Matrix n n ℝ) : μ_{p, (1 : Matrix n n ℝ)} A = μ_{p} A := by
  rw [logNormLpWeight_eq p isUnit_one, inv_one, Matrix.mul_one, Matrix.one_mul]

end Weight

/-- **The ℓ∞ induced norm of a matrix is its largest absolute row sum**, `‖A‖∞ = maxᵢ ∑ⱼ |aᵢⱼ|`. -/
theorem linfty_opNorm_eq_sup' (M : Matrix n n ℝ) :
    ‖M‖ = Finset.univ.sup' Finset.univ_nonempty fun i => ∑ j, |M i j| := by
  refine le_antisymm ?_ (Finset.sup'_le _ _ fun i _ => ?_)
  · have h : ‖M‖₊ ≤ ⟨_, (Finset.le_sup' (fun i => ∑ j, |M i j|) (Finset.mem_univ
        (Classical.arbitrary n))).trans' (by positivity)⟩ := by
      rw [linfty_opNNNorm_def]
      refine Finset.sup_le fun i _ => ?_
      rw [← NNReal.coe_le_coe, NNReal.coe_sum]
      simp only [coe_nnnorm, Real.norm_eq_abs]
      exact Finset.le_sup' (fun i => ∑ j, |M i j|) (Finset.mem_univ i)
    exact NNReal.coe_le_coe.2 h
  · have h : ∑ j, ‖M i j‖₊ ≤ ‖M‖₊ := by
      rw [linfty_opNNNorm_def]
      exact Finset.le_sup (f := fun i => ∑ j, ‖M i j‖₊) (Finset.mem_univ i)
    have h' := NNReal.coe_le_coe.2 h
    simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using h'

/-- **The ℓ∞ log norm of a matrix acting on `n → ℝ`**, `maxᵢ (aᵢᵢ + ∑_{j ≠ i} |aᵢⱼ|)`.  The sup norm
is the native norm of `n → ℝ`, so this is the form a Jacobian `LinearMap.toMatrix' (fderiv ℝ f x)`
meets; `logNorm_linfty` states it as `μ_{∞}`. -/
theorem logNorm_toLin' (A : Matrix n n ℝ) :
    μ (LinearMap.toContinuousLinearMap (Matrix.toLin' A)) =
      Finset.univ.sup' Finset.univ_nonempty
        fun i => A i i + ∑ j ∈ Finset.univ.erase i, |A i j| := by
  set c : n → ℝ := fun i => A i i + ∑ j ∈ Finset.univ.erase i, |A i j|
  set C := Finset.univ.sup' Finset.univ_nonempty c
  -- the `i`-th row sum of `I + h A` is `1 + h cᵢ` when `1 + h aᵢᵢ ≥ 0`
  have hrow (h : ℝ) (hh : 0 ≤ h) (i : n) (hi : 0 ≤ 1 + h * A i i) :
      ∑ j, |((1 : Matrix n n ℝ) + h • A) i j| = 1 + h * c i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [add_apply, one_apply_eq, smul_apply, smul_eq_mul]
    rw [abs_of_nonneg hi, Finset.sum_congr rfl fun j hj => by
      rw [one_apply_ne (Finset.ne_of_mem_erase hj).symm, zero_add, abs_mul, abs_of_nonneg hh],
      ← Finset.mul_sum]
    ring
  -- so, for small `h > 0`, `‖I + h A‖∞ = 1 + h C`
  have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), h * ∑ i, |A i i| < 1 := nhdsWithin_le_nhds
    (((continuous_id.mul continuous_const).tendsto' 0 0 (by simp)).eventually (gt_mem_nhds one_pos))
  have hnorm : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ‖(1 : (n → ℝ) →L[ℝ] (n → ℝ)) + h • LinearMap.toContinuousLinearMap (Matrix.toLin' A)‖ =
        1 + h * C := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with h (hh : 0 < h) hK
    have hi (i : n) : 0 ≤ 1 + h * A i i := by
      have := mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => abs_nonneg (A j j))
        (Finset.mem_univ i)) hh.le
      nlinarith [neg_abs_le (A i i)]
    rw [← linfty_opNorm_toMatrix]
    simp only [ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_smul, map_add, map_smul,
      LinearMap.coe_toContinuousLinearMap, LinearMap.toMatrix'_toLin']
    rw [show LinearMap.toMatrix' ((1 : (n → ℝ) →L[ℝ] (n → ℝ)) : (n → ℝ) →ₗ[ℝ] (n → ℝ)) = 1 from
      LinearMap.toMatrix'_id, linfty_opNorm_eq_sup']
    refine le_antisymm (Finset.sup'_le _ _ fun i _ => ?_) ?_
    · rw [hrow h hh.le i (hi i)]
      gcongr
      exact Finset.le_sup' c (Finset.mem_univ i)
    · obtain ⟨i, -, hiC⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty c
      rw [show C = c i from hiC, ← hrow h hh.le i (hi i)]
      exact Finset.le_sup' (fun i => ∑ j, |((1 : Matrix n n ℝ) + h • A) i j|) (Finset.mem_univ i)
  -- an affine function of `h` with slope `C`
  have hg : HasDerivWithinAt (fun h : ℝ => 1 + h * C) C (Ioi 0) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).mul_const C).const_add 1).hasDerivWithinAt.congr_deriv (one_mul C)
  exact (hg.congr_of_eventuallyEq hnorm (by simp)).derivWithin (uniqueDiffWithinAt_Ioi 0)

/-- **The ℓ∞ log norm**, `μ_{∞}(A) = maxᵢ (aᵢᵢ + ∑_{j ≠ i} |aᵢⱼ|)`. -/
@[blueprint "thm:logNorm-linfty"
  (title := "The $\\ell_\\infty$ log norm")
  (statement := /-- For $A \in \mathbb{R}^{n \times n}$ acting on $\mathbb{R}^n$ with the
    $\ell_\infty$ norm, the log norm (\cref{def:logNorm}) is
    \[ \mu_\infty(A) = \max_{i} \Bigl( a_{ii} + \sum_{j \ne i} |a_{ij}| \Bigr). \]

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Table 2.1. -/)
  (proof := /-- The $\ell_\infty$ induced norm is the largest absolute row sum.  For $h > 0$ so
    small that $1 + h a_{ii} \ge 0$ for all $i$, the $i$-th row sum of $I + hA$ is
    $1 + h (a_{ii} + \sum_{j \ne i} |a_{ij}|)$, so
    $\|I + hA\|_\infty = 1 + h \max_i (a_{ii} + \sum_{j \ne i} |a_{ij}|)$, an affine function of
    $h$. -/)]
theorem logNorm_linfty (A : Matrix n n ℝ) :
    μ_{∞} A = Finset.univ.sup' Finset.univ_nonempty
      fun i => A i i + ∑ j ∈ Finset.univ.erase i, |A i j| := by
  -- `WithLp ∞ (n → ℝ)` and `n → ℝ` carry the same norm
  let e := PiLp.continuousLinearEquiv ∞ ℝ (fun _ : n => ℝ)
  rw [logNormLp, ← logNorm_conj e (fun x => PiLp.norm_ofLp x),
    show (e ∘L toLpCLM ∞ A ∘L e.symm : (n → ℝ) →L[ℝ] (n → ℝ)) =
      LinearMap.toContinuousLinearMap (Matrix.toLin' A) by ext; simp [e, toLpCLM, toLpLin_apply],
    logNorm_toLin']

/-- **The ℓ¹ induced norm of a matrix is its largest absolute column sum**, `‖A‖₁ = ‖Aᵀ‖∞`. -/
theorem l1_opNorm_eq_linfty_transpose (M : Matrix n n ℝ) :
    ‖LinearMap.toContinuousLinearMap (toLpLin 1 1 M)‖ = ‖Mᵀ‖ := by
  rw [linfty_opNorm_eq_sup']
  simp only [transpose_apply]
  set C := Finset.univ.sup' Finset.univ_nonempty fun j => ∑ i, |M i j|
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ ((Finset.le_sup'
    (fun j => ∑ i, |M i j|) (Finset.mem_univ (Classical.arbitrary n))).trans' (by positivity))
    fun v => ?_) (Finset.sup'_le _ _ fun j _ => ?_)
  · -- `‖M v‖₁ ≤ ∑ᵢ ∑ⱼ |mᵢⱼ| |vⱼ| = ∑ⱼ (∑ᵢ |mᵢⱼ|) |vⱼ| ≤ C ‖v‖₁`
    simp only [LinearMap.coe_toContinuousLinearMap', toLpLin_apply, PiLp.norm_eq_of_L1,
      Real.norm_eq_abs, mulVec, dotProduct]
    calc ∑ i, |∑ j, M i j * v j| ≤ ∑ i, ∑ j, |M i j| * |v j| :=
          Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans_eq
            (Finset.sum_congr rfl fun j _ => abs_mul _ _)
      _ = ∑ j, (∑ i, |M i j|) * |v j| := by rw [Finset.sum_comm]; simp [Finset.sum_mul]
      _ ≤ ∑ j, C * |v j| := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
          (Finset.le_sup' (fun j => ∑ i, |M i j|) (Finset.mem_univ j)) (abs_nonneg _)
      _ = C * ∑ j, |v j| := by rw [Finset.mul_sum]
  · -- the `j`-th column sum is `‖M eⱼ‖₁ ≤ ‖M‖₁ ‖eⱼ‖₁`
    have h := (LinearMap.toContinuousLinearMap (toLpLin 1 1 M)).le_opNorm (PiLp.single 1 j 1)
    simpa [toLpLin_apply, PiLp.norm_eq_of_L1, mulVec_single_one, Real.norm_eq_abs] using h

/-- **The ℓ¹ log norm**, `μ₁(A) = maxⱼ (aⱼⱼ + ∑_{i ≠ j} |aᵢⱼ|)`, for `A` acting on `ℝⁿ` with the
ℓ¹ norm. -/
@[blueprint "thm:logNorm-l1"
  (title := "The $\\ell_1$ log norm")
  (statement := /-- For $A \in \mathbb{R}^{n \times n}$ acting on $\mathbb{R}^n$ with the
    $\ell_1$ norm, the log norm (\cref{def:logNorm}) is
    \[ \mu_1(A) = \max_{j} \Bigl( a_{jj} + \sum_{i \ne j} |a_{ij}| \Bigr) = \mu_\infty(A^\top). \]

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Table 2.1. -/)
  (proof := /-- The $\ell_1$ induced norm of a matrix is the largest absolute column sum, the
    $\ell_\infty$ induced norm of its transpose.  So $\|I + hA\|_1 = \|I + hA^\top\|_\infty$ for
    every $h$, and $\mu_1(A) = \mu_\infty(A^\top)$ (\cref{thm:logNorm-linfty}). -/)]
theorem logNorm_l1 (A : Matrix n n ℝ) :
    μ_{1} A =
      Finset.univ.sup' Finset.univ_nonempty
        fun j => A j j + ∑ i ∈ Finset.univ.erase j, |A i j| := by
  have h := logNorm_toLin' Aᵀ
  simp only [transpose_apply] at h
  rw [← h, logNormLp, toLpCLM]
  unfold logNorm
  congr 1
  ext h
  rw [show (1 : WithLp 1 (n → ℝ) →L[ℝ] WithLp 1 (n → ℝ)) +
      h • LinearMap.toContinuousLinearMap (toLpLin 1 1 A) =
      LinearMap.toContinuousLinearMap (toLpLin 1 1 (1 + h • A)) by ext; simp,
    l1_opNorm_eq_linfty_transpose, ← linfty_opNorm_toMatrix]
  simp only [ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_smul, map_add, map_smul,
    LinearMap.coe_toContinuousLinearMap, LinearMap.toMatrix'_toLin', transpose_add,
    transpose_smul, transpose_one]
  rw [show LinearMap.toMatrix' ((1 : (n → ℝ) →L[ℝ] (n → ℝ)) : (n → ℝ) →ₗ[ℝ] (n → ℝ)) = 1 from
    LinearMap.toMatrix'_id]

/-! ### Diagonally weighted ℓ¹ and ℓ∞ log norms -/

omit [Nonempty n] in
/-- A diagonal matrix with nonzero entries is a weight. -/
private lemma isUnit_diagonal_of_ne {d : n → ℝ} (hd : ∀ i, d i ≠ 0) : IsUnit (diagonal d) :=
  isUnit_diagonal.2 (Pi.isUnit_iff.2 fun i => (hd i).isUnit)

omit [Nonempty n] in
/-- The inverse of a diagonal weight. -/
private lemma inv_diagonal_of_ne {d : n → ℝ} (hd : ∀ i, d i ≠ 0) :
    (diagonal d)⁻¹ = diagonal fun i => (d i)⁻¹ :=
  inv_eq_right_inv (by simp [diagonal_mul_diagonal, mul_inv_cancel₀ (hd _)])

/-- **The diagonally weighted ℓ¹ log norm**, for `‖x‖_{1,[η]} = ∑ᵢ ηᵢ |xᵢ|`:
`μ_{1,[η]}(A) = maxⱼ (aⱼⱼ + ∑_{i ≠ j} |aᵢⱼ| ηᵢ / ηⱼ)`. -/
@[blueprint "thm:logNorm-l1-diagonal"
  (title := "The diagonally weighted $\\ell_1$ log norm")
  (statement := /-- For $\eta \in \mathbb{R}^n_{>0}$ and $A \in \mathbb{R}^{n \times n}$, the log
    norm induced by $\|x\|_{1,[\eta]} = \sum_i \eta_i |x_i|$ is
    \[ \mu_{1,[\eta]}(A) = \max_{j} \Bigl( a_{jj} + \sum_{i \ne j} |a_{ij}|
      \frac{\eta_i}{\eta_j} \Bigr). \]

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Section 2.4.3. -/)
  (proof := /-- $\mu_{1,[\eta]}(A) = \mu_1([\eta] A [\eta]^{-1})$ (\cref{thm:logNormLpWeight-eq}),
    and $[\eta] A [\eta]^{-1}$ has entries $\eta_i a_{ij} / \eta_j$; apply
    \cref{thm:logNorm-l1}. -/)]
theorem logNorm_l1_diagonal {η : n → ℝ} (hη : ∀ i, 0 < η i) (A : Matrix n n ℝ) :
    μ_{1, diagonal η} A = Finset.univ.sup' Finset.univ_nonempty
      fun j => A j j + ∑ i ∈ Finset.univ.erase j, |A i j| * η i / η j := by
  rw [logNormLpWeight_eq 1 (isUnit_diagonal_of_ne fun i => (hη i).ne'),
    inv_diagonal_of_ne fun i => (hη i).ne', logNorm_l1]
  refine Finset.sup'_congr Finset.univ_nonempty rfl fun j _ => ?_
  simp only [mul_diagonal, diagonal_mul]
  have hj := (hη j).ne'
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_mul, abs_mul, abs_of_pos (hη i), abs_inv, abs_of_pos (hη j)]
    ring

/-- **The diagonally weighted ℓ∞ log norm**, for `‖x‖_{∞,[η]⁻¹} = maxᵢ |xᵢ| / ηᵢ`:
`μ_{∞,[η]⁻¹}(A) = maxᵢ (aᵢᵢ + ∑_{j ≠ i} |aᵢⱼ| ηⱼ / ηᵢ)`. -/
@[blueprint "thm:logNorm-linfty-diagonal"
  (title := "The diagonally weighted $\\ell_\\infty$ log norm")
  (statement := /-- For $\eta \in \mathbb{R}^n_{>0}$ and $A \in \mathbb{R}^{n \times n}$, the log
    norm induced by $\|x\|_{\infty,[\eta]^{-1}} = \max_i |x_i| / \eta_i$ is
    \[ \mu_{\infty,[\eta]^{-1}}(A) = \max_{i} \Bigl( a_{ii} + \sum_{j \ne i} |a_{ij}|
      \frac{\eta_j}{\eta_i} \Bigr). \]

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Section 2.4.3. -/)
  (proof := /-- $\mu_{\infty,[\eta]^{-1}}(A) = \mu_\infty([\eta]^{-1} A [\eta])$
    (\cref{thm:logNormLpWeight-eq}), and $[\eta]^{-1} A [\eta]$ has entries
    $a_{ij} \eta_j / \eta_i$; apply \cref{thm:logNorm-linfty}. -/)]
theorem logNorm_linfty_diagonal {η : n → ℝ} (hη : ∀ i, 0 < η i) (A : Matrix n n ℝ) :
    μ_{∞, diagonal fun i => (η i)⁻¹} A = Finset.univ.sup' Finset.univ_nonempty
      fun i => A i i + ∑ j ∈ Finset.univ.erase i, |A i j| * η j / η i := by
  rw [logNormLpWeight_eq ∞ (isUnit_diagonal_of_ne fun i => inv_ne_zero (hη i).ne'),
    inv_diagonal_of_ne fun i => inv_ne_zero (hη i).ne', logNorm_linfty]
  refine Finset.sup'_congr Finset.univ_nonempty rfl fun i _ => ?_
  simp only [mul_diagonal, diagonal_mul, inv_inv]
  have hi := (hη i).ne'
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [abs_mul, abs_mul, abs_inv, abs_of_pos (hη i), abs_of_pos (hη j)]
    ring

/-- **The diagonally weighted ℓ¹ log norm as a linear inequality**: for `η > 0`,
`μ_{1,[η]}(A) ≤ b` iff `ηᵀ |A|_M ≤ b ηᵀ`. -/
@[blueprint "thm:logNorm-l1-diagonal-le-iff"
  (title := "The diagonally weighted $\\ell_1$ log norm as a linear inequality")
  (statement := /-- For $\eta \in \mathbb{R}^n_{>0}$, $\mu_{1,[\eta]}(A) \le b$ if and only if
    $\eta^\top |A|_{\mathrm{M}} \le b \, \eta^\top$ entrywise, where the Metzler majorant
    $|A|_{\mathrm{M}}$ has entries $a_{ii}$ on the diagonal and $|a_{ij}|$ off it. -/)
  (proof := /-- Multiply the $j$-th term of \cref{thm:logNorm-l1-diagonal} by $\eta_j > 0$. -/)]
theorem logNorm_l1_diagonal_le_iff {η : n → ℝ} (hη : ∀ i, 0 < η i) (A : Matrix n n ℝ) (b : ℝ) :
    μ_{1, diagonal η} A ≤ b ↔ ∀ j, ∑ i, η i * metzlerMajorant A i j ≤ b * η j := by
  rw [logNorm_l1_diagonal hη, Finset.sup'_le_iff]
  refine forall_congr' fun j => ?_
  have hsum : ∑ i, η i * metzlerMajorant A i j =
      η j * (A j j + ∑ i ∈ Finset.univ.erase j, |A i j| * η i / η j) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), mul_add, Finset.mul_sum]
    congr 1
    · simp [metzlerMajorant]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have := (hη j).ne'
      simp only [metzlerMajorant, if_neg (Finset.ne_of_mem_erase hi)]
      field_simp
  simp only [Finset.mem_univ, true_implies, hsum]
  constructor <;> intro h <;> nlinarith [hη j]

/-- **The diagonally weighted ℓ∞ log norm as a linear inequality**: for `η > 0`,
`μ_{∞,[η]⁻¹}(A) ≤ b` iff `|A|_M η ≤ b η`. -/
@[blueprint "thm:logNorm-linfty-diagonal-le-iff"
  (title := "The diagonally weighted $\\ell_\\infty$ log norm as a linear inequality")
  (statement := /-- For $\eta \in \mathbb{R}^n_{>0}$, $\mu_{\infty,[\eta]^{-1}}(A) \le b$ if and
    only if $|A|_{\mathrm{M}} \, \eta \le b \, \eta$ entrywise. -/)
  (proof := /-- Multiply the $i$-th term of \cref{thm:logNorm-linfty-diagonal} by
    $\eta_i > 0$. -/)]
theorem logNorm_linfty_diagonal_le_iff {η : n → ℝ} (hη : ∀ i, 0 < η i) (A : Matrix n n ℝ)
    (b : ℝ) :
    μ_{∞, diagonal fun i => (η i)⁻¹} A ≤ b ↔ ∀ i, ∑ j, metzlerMajorant A i j * η j ≤ b * η i := by
  rw [logNorm_linfty_diagonal hη, Finset.sup'_le_iff]
  refine forall_congr' fun i => ?_
  have hsum : ∑ j, metzlerMajorant A i j * η j =
      η i * (A i i + ∑ j ∈ Finset.univ.erase i, |A i j| * η j / η i) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), mul_add, Finset.mul_sum]
    congr 1
    · simp [metzlerMajorant, mul_comm]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have := (hη i).ne'
      simp only [metzlerMajorant, if_neg (Finset.ne_of_mem_erase hj).symm]
      field_simp
  simp only [Finset.mem_univ, true_implies, hsum]
  constructor <;> intro h <;> nlinarith [hη i]

/-- **The diagonally weighted ℓ¹ and ℓ∞ log norms are quasiconvex in the weight**: their sublevel
sets in `η > 0` are cut out by linear inequalities. -/
theorem quasiconvexOn_logNorm_l1_diagonal (A : Matrix n n ℝ) :
    QuasiconvexOn ℝ {η : n → ℝ | ∀ i, 0 < η i} fun η => μ_{1, diagonal η} A := by
  intro r η ⟨hη, hηr⟩ ζ ⟨hζ, hζr⟩ a c ha hc hac
  have hpos (i : n) : 0 < (a • η + c • ζ) i := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha
    · simpa [show c = 1 by linarith] using hζ i
    · exact add_pos_of_pos_of_nonneg (mul_pos ha (hη i)) (mul_nonneg hc (hζ i).le)
  refine ⟨hpos, (logNorm_l1_diagonal_le_iff hpos A r).2 fun j => ?_⟩
  have h₁ := (logNorm_l1_diagonal_le_iff hη A r).1 hηr j
  have h₂ := (logNorm_l1_diagonal_le_iff hζ A r).1 hζr j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_assoc,
    ← Finset.mul_sum]
  nlinarith

@[inherit_doc quasiconvexOn_logNorm_l1_diagonal]
theorem quasiconvexOn_logNorm_linfty_diagonal (A : Matrix n n ℝ) :
    QuasiconvexOn ℝ {η : n → ℝ | ∀ i, 0 < η i}
      fun η => μ_{∞, diagonal fun i => (η i)⁻¹} A := by
  intro r η ⟨hη, hηr⟩ ζ ⟨hζ, hζr⟩ a c ha hc hac
  have hpos (i : n) : 0 < (a • η + c • ζ) i := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha
    · simpa [show c = 1 by linarith] using hζ i
    · exact add_pos_of_pos_of_nonneg (mul_pos ha (hη i)) (mul_nonneg hc (hζ i).le)
  refine ⟨hpos, (logNorm_linfty_diagonal_le_iff hpos A r).2 fun i => ?_⟩
  have h₁ := (logNorm_linfty_diagonal_le_iff hη A r).1 hηr i
  have h₂ := (logNorm_linfty_diagonal_le_iff hζ A r).1 hζr i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    mul_left_comm _ a, mul_left_comm _ c, ← Finset.mul_sum]
  nlinarith

open scoped RealInnerProductSpace

/-- **The weighted Euclidean log norm as a quadratic-form bound**: for `P ≻ 0`,
`μ_{2,P^½}(A) ≤ c` iff `vᵀ P A v ≤ c vᵀ P v` for all `v`. -/
@[blueprint "thm:logNormL2PosDef-le-iff"
  (title := "The weighted Euclidean log norm as a quadratic-form bound")
  (statement := /-- For $P \succ 0$ and $A \in \mathbb{R}^{n \times n}$, the log norm induced by
    $\|x\|_{2,P^{1/2}} = \sqrt{x^\top P x}$ satisfies $\mu_{2,P^{1/2}}(A) \le c$ if and only if
    $v^\top P A v \le c \, v^\top P v$ for all $v \in \mathbb{R}^n$. -/)
  (proof := /-- \cref{thm:logNorm-le-iff-inner-le} for the inner product $x^\top P y$, in which
    $\langle A v, v \rangle = v^\top P A v$. -/)]
theorem logNormL2PosDef_le_iff {P : Matrix n n ℝ} (hP : P.PosDef) (A : Matrix n n ℝ) (c : ℝ) :
    μ_{2,P^½} A ≤ c ↔ ∀ v : n → ℝ, v ⬝ᵥ ((P * A) *ᵥ v) ≤ c * (v ⬝ᵥ (P *ᵥ v)) := by
  have hPt : Pᵀ = P := by simpa using hP.isHermitian.eq
  rw [logNormL2PosDef, dif_pos hP, logNorm_le_iff_inner_le]
  refine forall_congr' fun v => ?_
  rw [← real_inner_self_eq_norm_sq, WeightedEuclidean.inner_def, WeightedEuclidean.inner_def]
  -- `(A v)ᵀ P v = vᵀ P A v`, as `P` is symmetric
  have key : (A *ᵥ v) ⬝ᵥ (P *ᵥ (v : n → ℝ)) = v ⬝ᵥ ((P * A) *ᵥ v) := by
    calc (A *ᵥ v) ⬝ᵥ (P *ᵥ (v : n → ℝ)) = (P *ᵥ (v : n → ℝ)) ⬝ᵥ (A *ᵥ v) := dotProduct_comm _ _
      _ = ((v : n → ℝ) ᵥ* P) ⬝ᵥ (A *ᵥ v) := by rw [← vecMul_transpose, hPt]
      _ = v ⬝ᵥ ((P * A) *ᵥ v) := by rw [← dotProduct_mulVec, mulVec_mulVec]
  change (A *ᵥ v) ⬝ᵥ (P *ᵥ v) ≤ _ ↔ _
  rw [key]

open scoped MatrixOrder in
/-- **The weighted Euclidean log norm as an LMI**: for `P ≻ 0`, `μ_{2,P^½}(A) ≤ b` iff
`Aᵀ P + P A ⪯ 2 b P`, the Lyapunov contractivity LMI. -/
@[blueprint "thm:logNormL2PosDef-le-iff-lmi"
  (title := "The weighted Euclidean log norm as an LMI")
  (statement := /-- For $P \succ 0$, $\mu_{2,P^{1/2}}(A) \le b$ if and only if
    $A^\top P + P A \preceq 2 b P$. -/)
  (proof := /-- \cref{thm:logNormL2PosDef-le-iff}, with
    $v^\top (A^\top P + P A) v = 2 v^\top P A v$. -/)]
theorem logNormL2PosDef_le_iff_lmi {P : Matrix n n ℝ} (hP : P.PosDef) (A : Matrix n n ℝ) (b : ℝ) :
    μ_{2,P^½} A ≤ b ↔ Aᵀ * P + P * A ≤ (2 * b) • P := by
  have hPt : Pᵀ = P := by simpa using hP.isHermitian.eq
  -- `vᵀ Aᵀ P v = vᵀ P A v`
  have hq (v : n → ℝ) : v ⬝ᵥ ((Aᵀ * P) *ᵥ v) = v ⬝ᵥ ((P * A) *ᵥ v) := by
    rw [dotProduct_mulVec, ← transpose_transpose (Aᵀ * P), vecMul_transpose, dotProduct_comm,
      transpose_mul, transpose_transpose, hPt]
  have hherm : ((2 * b) • P - (Aᵀ * P + P * A)).IsHermitian := by
    simp only [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_add,
      transpose_smul, transpose_mul, transpose_transpose, hPt, add_comm (P * A)]
  rw [logNormL2PosDef_le_iff hP, Matrix.le_iff, posSemidef_iff_dotProduct_mulVec]
  simp only [hherm, true_and, star_trivial, sub_mulVec, add_mulVec, smul_mulVec,
    dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul, hq]
  refine forall_congr' fun v => ?_
  constructor <;> intro h <;> linarith

/-- **The weighted Euclidean log norm is quasiconvex in `P`**: its sublevel sets in `P ≻ 0` are
cut out by the LMI `Aᵀ P + P A ⪯ 2 b P`. -/
theorem quasiconvexOn_logNormL2PosDef (A : Matrix n n ℝ) :
    QuasiconvexOn ℝ {P : Matrix n n ℝ | P.PosDef} fun P => μ_{2,P^½} A := by
  intro r P ⟨hP, hPr⟩ Q ⟨hQ, hQr⟩ a c ha hc hac
  have hR : (a • P + c • Q).PosDef := by
    refine posDef_iff_dotProduct_mulVec.2
      ⟨(hP.isHermitian.smul (.all a)).add (hQ.isHermitian.smul (.all c)), fun v hv => ?_⟩
    have h₁ := (posDef_iff_dotProduct_mulVec.1 hP).2 hv
    have h₂ := (posDef_iff_dotProduct_mulVec.1 hQ).2 hv
    simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha
    · simpa [show c = 1 by linarith] using h₂
    · exact add_pos_of_pos_of_nonneg (mul_pos ha h₁) (mul_nonneg hc h₂.le)
  refine ⟨hR, (logNormL2PosDef_le_iff hR A r).2 fun v => ?_⟩
  have h₁ := (logNormL2PosDef_le_iff hP A r).1 hPr v
  have h₂ := (logNormL2PosDef_le_iff hQ A r).1 hQr v
  simp only [Matrix.add_mul, Matrix.smul_mul, add_mulVec, smul_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  nlinarith

/-- `μ_{2,P^½}(A)` is the largest element of the spectrum of `(P A P⁻¹ + Aᵀ) / 2`.  That matrix
is not symmetric, but it is similar to the symmetric part of `A` in the inner product `xᵀ P y`, so
its spectrum is real and has a largest element. -/
theorem logNormL2PosDef_isGreatest {P : Matrix n n ℝ} (hP : P.PosDef) (A : Matrix n n ℝ) :
    IsGreatest (spectrum ℝ ((2⁻¹ : ℝ) • (P * A * P⁻¹ + Aᵀ))) (μ_{2,P^½} A) := by
  have hPt : Pᵀ = P := by simpa using hP.isHermitian.eq
  have hdet : IsUnit P.det := (hP.det_pos).ne'.isUnit
  -- `(M x)ᵀ y = xᵀ (Mᵀ y)`
  have hT (M : Matrix n n ℝ) (x y : n → ℝ) : (M *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Mᵀ *ᵥ y) := by
    rw [dotProduct_comm, dotProduct_mulVec, ← vecMul_transpose, transpose_transpose,
      dotProduct_comm]
  -- in the inner product `xᵀ P y`, the adjoint of `A` is `P⁻¹ Aᵀ P`
  have hadj : ContinuousLinearMap.adjoint (WeightedEuclidean.toCLM hP A) =
      WeightedEuclidean.toCLM hP (P⁻¹ * Aᵀ * P) := by
    refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_).symm
    rw [WeightedEuclidean.inner_def, WeightedEuclidean.inner_def]
    change ((P⁻¹ * Aᵀ * P) *ᵥ (x : n → ℝ)) ⬝ᵥ (P *ᵥ (y : n → ℝ)) =
      (x : n → ℝ) ⬝ᵥ (P *ᵥ (A *ᵥ (y : n → ℝ)))
    rw [hT, mulVec_mulVec, mulVec_mulVec, transpose_mul, transpose_mul, transpose_transpose,
      transpose_nonsing_inv, hPt, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul P hdet,
      Matrix.mul_one]
  have hS : ((((2⁻¹ : ℝ) • (WeightedEuclidean.toCLM hP A +
      ContinuousLinearMap.adjoint (WeightedEuclidean.toCLM hP A))) :
      WeightedEuclidean hP →L[ℝ] WeightedEuclidean hP) :
        WeightedEuclidean hP →ₗ[ℝ] WeightedEuclidean hP) =
      (Matrix.toLin' ((2⁻¹ : ℝ) • (A + P⁻¹ * Aᵀ * P)) :
        WeightedEuclidean hP →ₗ[ℝ] WeightedEuclidean hP) := by
    rw [hadj]
    ext x
    simp [WeightedEuclidean.toCLM]
    rfl
  -- conjugating by `P` turns `(A + P⁻¹ Aᵀ P) / 2` into `(P A P⁻¹ + Aᵀ) / 2`
  set u : (Matrix n n ℝ)ˣ := (Matrix.isUnit_iff_isUnit_det P).2 hdet |>.unit
  have key : (2⁻¹ : ℝ) • (P * A * P⁻¹ + Aᵀ) =
      (u : Matrix n n ℝ) * ((2⁻¹ : ℝ) • (A + P⁻¹ * Aᵀ * P)) *
        ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    have hu : ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) = P⁻¹ :=
      (inv_eq_right_inv (u.mul_inv)).symm
    rw [hu, show (u : Matrix n n ℝ) = P from rfl]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
      mul_nonsing_inv P hdet, Matrix.mul_one, ← Matrix.mul_assoc P P⁻¹, Matrix.one_mul]
  rw [logNormL2PosDef, dif_pos hP, key, spectrum.units_conjugate]
  convert logNorm_isGreatest_inner (WeightedEuclidean.toCLM hP A) using 1
  ext a
  rw [Set.mem_setOf_eq, hS, Module.End.hasEigenvalue_iff_mem_spectrum,
    ← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv' (R := ℝ) (n := n))]
  rfl

/-- **The weighted Euclidean log norm**: for `P ≻ 0`, `μ_{2,P^½}(A) = λ_max((P A P⁻¹ + Aᵀ) / 2)`.
See `logNormL2PosDef_isGreatest`. -/
@[blueprint "thm:logNormL2PosDef-eq-lambdaMax"
  (title := "The weighted Euclidean log norm")
  (statement := /-- For $P \succ 0$ and $A \in \mathbb{R}^{n \times n}$, the log norm induced by
    $\|x\|_{2,P^{1/2}} = \sqrt{x^\top P x}$ is
    \[ \mu_{2,P^{1/2}}(A) = \lambda_{\max}\Bigl( \frac{P A P^{-1} + A^\top}{2} \Bigr). \]

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0), Lemma 2.11,
    (2.35). -/)
  (proof := /-- In the inner product $x^\top P y$ the adjoint of $A$ is $P^{-1} A^\top P$, so
    $\mu_{2,P^{1/2}}(A)$ is the largest eigenvalue of $(A + P^{-1} A^\top P)/2$; conjugating by
    $P$ gives $(P A P^{-1} + A^\top)/2$, with the same spectrum. -/)]
theorem logNormL2PosDef_eq_lambdaMax {P : Matrix n n ℝ} (hP : P.PosDef) (A : Matrix n n ℝ) :
    μ_{2,P^½} A = lambdaMax ((2⁻¹ : ℝ) • (P * A * P⁻¹ + Aᵀ)) :=
  (logNormL2PosDef_isGreatest hP A).csSup_eq.symm

omit [Nonempty n] in
/-- **A weight on the Euclidean norm is a positive definite `P`**: `‖R x‖₂ = √(xᵀ (Rᵀ R) x)`, so
for an invertible `R`, `μ_{2,R}(A) = μ_{2,(RᵀR)^½}(A)`. -/
theorem logNormLpWeight_two_eq {R : Matrix n n ℝ} (hR : IsUnit R) (A : Matrix n n ℝ) :
    μ_{2, R} A = μ_{2,(Rᵀ * R)^½} A := by
  have hP : (Rᵀ * R).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      PosDef.conjTranspose_mul_self R (mulVec_injective_iff_isUnit.2 hR)
  -- `x ↦ R x`, from `√(xᵀ Rᵀ R x)` to the Euclidean norm
  let e : WeightedEuclidean hP ≃L[ℝ] EuclideanSpace ℝ n := LinearEquiv.toContinuousLinearEquiv
    ((WithLp.linearEquiv 2 ℝ (n → ℝ)).symm.trans (toWeight 2 hR).toLinearEquiv)
  have he (x : WeightedEuclidean hP) : ‖e x‖ = ‖x‖ := by
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, WeightedEuclidean.inner_def]
    change (R *ᵥ x) ⬝ᵥ star (R *ᵥ x) = _
    rw [star_trivial]
    rw [← mulVec_mulVec, dotProduct_mulVec (x : n → ℝ) Rᵀ, vecMul_transpose]
  rw [logNormLpWeight_eq 2 hR, logNormL2PosDef, dif_pos hP, logNormLp, ← logNorm_conj e he]
  congr 1
  ext x : 1
  change WithLp.toLp 2 ((R * A * R⁻¹) *ᵥ x.ofLp) = WithLp.toLp 2 (R *ᵥ (A *ᵥ (R⁻¹ *ᵥ x.ofLp)))
  simp [mulVec_mulVec, Matrix.mul_assoc]

/-! ### The Euclidean norm, `P = I` -/

omit [Nonempty n] in
/-- The Euclidean norm is the weighted one with `P = I`: `μ_2(A) = μ_{2,I^½}(A)`. -/
lemma logNormL2PosDef_one (A : Matrix n n ℝ) : μ_{2,(1 : Matrix n n ℝ)^½} A = μ_{2} A := by
  -- `ℝⁿ` with the Euclidean norm, viewed in the inner product `xᵀ I y`
  let e : EuclideanSpace ℝ n ≃L[ℝ] WeightedEuclidean PosDef.one :=
    LinearEquiv.toContinuousLinearEquiv (WithLp.linearEquiv 2 ℝ (n → ℝ))
  have he (x : EuclideanSpace ℝ n) : ‖e x‖ = ‖x‖ := by
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, WeightedEuclidean.inner_def,
      one_mulVec]
    rfl
  rw [logNormL2PosDef, dif_pos PosDef.one, logNormLp, ← logNorm_conj e he]
  rfl

/-- **The Euclidean log norm of a matrix as a quadratic-form bound**: `μ₂(A) ≤ c` iff
`vᵀ A v ≤ c vᵀ v` for all `v`. -/
@[blueprint "thm:logNorm-euclidean-le-iff"
  (title := "The Euclidean log norm as a quadratic-form bound")
  (statement := /-- For $A \in \mathbb{R}^{n \times n}$ acting on $\mathbb{R}^n$ with the Euclidean
    norm, $\mu_2(A) \le c$ if and only if $v^\top A v \le c \, v^\top v$ for all
    $v \in \mathbb{R}^n$ (\cref{def:logNorm}). -/)
  (proof := /-- \cref{thm:logNormL2PosDef-le-iff} with $P = I$. -/)]
theorem logNorm_euclidean_le_iff (A : Matrix n n ℝ) (c : ℝ) :
    μ_{2} A ≤ c ↔ ∀ v : n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ c * (v ⬝ᵥ v) := by
  simpa [logNormL2PosDef_one] using logNormL2PosDef_le_iff PosDef.one A c

open scoped MatrixOrder in
/-- **The Euclidean log norm as an LMI**: `μ₂(A) ≤ b` iff `Aᵀ + A ⪯ 2 b I`. -/
theorem logNorm_euclidean_le_iff_lmi (A : Matrix n n ℝ) (b : ℝ) :
    μ_{2} A ≤ b ↔ Aᵀ + A ≤ (2 * b) • (1 : Matrix n n ℝ) := by
  simpa [logNormL2PosDef_one] using logNormL2PosDef_le_iff_lmi PosDef.one A b

/-- `μ₂(A)` is the largest element of the spectrum of the symmetric part `(A + Aᵀ) / 2`. -/
theorem logNorm_euclidean_isGreatest (A : Matrix n n ℝ) :
    IsGreatest (spectrum ℝ ((2⁻¹ : ℝ) • (A + Aᵀ))) (μ_{2} A) := by
  simpa [logNormL2PosDef_one] using logNormL2PosDef_isGreatest PosDef.one A

/-- **The Euclidean log norm of a matrix**, `μ₂(A) = λ_max((A + Aᵀ) / 2)`. -/
@[blueprint "thm:logNorm-euclidean-eq-lambdaMax"
  (title := "The Euclidean log norm")
  (statement := /-- For $A \in \mathbb{R}^{n \times n}$ acting on $\mathbb{R}^n$ with the Euclidean
    norm,
    \[ \mu_2(A) = \lambda_{\max}\Bigl( \frac{A + A^\top}{2} \Bigr) \]
    (\cref{def:logNorm}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Table 2.1. -/)
  (proof := /-- \cref{thm:logNormL2PosDef-eq-lambdaMax} with $P = I$. -/)]
theorem logNorm_euclidean_eq_lambdaMax (A : Matrix n n ℝ) :
    μ_{2} A = lambdaMax ((2⁻¹ : ℝ) • (A + Aᵀ)) :=
  (logNorm_euclidean_isGreatest A).csSup_eq.symm

end Matrix

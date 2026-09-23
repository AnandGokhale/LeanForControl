import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Eigenpairs, generalized eigenspaces, and spectral mapping for matrices

This file collects matrix-algebra facts about eigenpairs that have no system semantics:
real/imaginary transport of a real matrix along a complexified eigenpair, bilinear forms
vanishing under a no-resonance condition on generalized eigenspaces (used to build
Lyapunov--Sylvester solutions), and reverse spectral mapping for the matrix exponential.

Reference: standard finite-dimensional spectral theory.
-/

namespace MatrixAlgebra

open Matrix

variable {n : ℕ}

/-! ## Real/imaginary transport along a complexified eigenpair -/

/-- A real matrix commutes with taking the real part of a complex vector entrywise.

This has nothing to do with eigenvalues: it holds for every complex vector `w`, and is
just "multiplying by a real number commutes with taking the real part," summed over the
matrix product. -/
lemma mulVec_re (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℂ) :
    A *ᵥ (fun i ↦ (w i).re) = fun i ↦ (A.map (algebraMap ℝ ℂ) *ᵥ w) i |>.re := by
  ext i
  have hi : (A.map (algebraMap ℝ ℂ) *ᵥ w) i = ∑ j, (A i j : ℂ) * w j := rfl
  rw [hi, ← Complex.reCLM_apply, map_sum]
  change (∑ j, A i j * (w j).re) = _
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- A real matrix commutes with taking the imaginary part of a complex vector entrywise.

This has nothing to do with eigenvalues: it holds for every complex vector `w`, and is
just "multiplying by a real number commutes with taking the imaginary part," summed over
the matrix product. -/
lemma mulVec_im (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℂ) :
    A *ᵥ (fun i ↦ (w i).im) = fun i ↦ (A.map (algebraMap ℝ ℂ) *ᵥ w) i |>.im := by
  ext i
  have hi : (A.map (algebraMap ℝ ℂ) *ᵥ w) i = ∑ j, (A i j : ℂ) * w j := rfl
  rw [hi, ← Complex.imCLM_apply, map_sum]
  change (∑ j, A i j * (w j).im) = _
  simp only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]

/-- If `v` is a complex eigenvector of the complexification of a real matrix `A` with
eigenvalue `μ`, then for any complex scalar `c`, `A` maps the real part of `c • v` to the
real part of `c * μ • v`.

This is `mulVec_re` at `w := c • v`, substituting the eigenvector equation. -/
lemma matrixMulVec_re_smul_eigenpair
    (A : Matrix (Fin n) (Fin n) ℝ) (μ c : ℂ) (v : Fin n → ℂ)
    (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    (fun i ↦ (c * μ * v i).re) = A *ᵥ (fun i ↦ (c * v i).re) := by
  have h := mulVec_re A (c • v)
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [h, Matrix.mulVec_smul, heig]
  ext i
  simp [mul_assoc]

/-- If `v` is a complex eigenvector of the complexification of a real matrix `A` with
eigenvalue `μ`, then for any complex scalar `c`, `A` maps the imaginary part of `c • v` to
the imaginary part of `c * μ • v`.

This is `mulVec_im` at `w := c • v`, substituting the eigenvector equation. -/
lemma matrixMulVec_im_smul_eigenpair
    (A : Matrix (Fin n) (Fin n) ℝ) (μ c : ℂ) (v : Fin n → ℂ)
    (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    (fun i ↦ (c * μ * v i).im) = A *ᵥ (fun i ↦ (c * v i).im) := by
  have h := mulVec_im A (c • v)
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [h, Matrix.mulVec_smul, heig]
  ext i
  simp [mul_assoc]

/-- The real/imaginary decomposition of a complexified eigenpair: `A` maps `Re(v)` and
`Im(v)` to the real and imaginary parts of `μv`, expanded in `μ.re`/`μ.im`.

This is `matrixMulVec_re_smul_eigenpair`/`matrixMulVec_im_smul_eigenpair` at `c = 1`. -/
lemma eigenpair_real_imag
    (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℂ) (v : Fin n → ℂ)
    (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    A *ᵥ (fun i ↦ (v i).re) =
        μ.re • (fun i ↦ (v i).re) - μ.im • (fun i ↦ (v i).im) ∧
      A *ᵥ (fun i ↦ (v i).im) =
        μ.im • (fun i ↦ (v i).re) + μ.re • (fun i ↦ (v i).im) := by
  have hre := matrixMulVec_re_smul_eigenpair A μ 1 v heig
  have him := matrixMulVec_im_smul_eigenpair A μ 1 v heig
  simp only [one_mul] at hre him
  constructor
  · rw [← hre]
    ext i
    simp [Complex.mul_re]
  · rw [← him]
    ext i
    simp [Complex.mul_im, add_comm]

/-! ## Bilinear forms vanishing under a no-resonance condition -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A resonance-avoiding bilinear form vanishes on a pair of generalized eigenspaces.

`hB` says `B` transforms `T`-generalized-eigenvectors additively by `c`; if the pair's
combined eigenvalue `ξ + ν` misses `c`, the form must vanish on that pair. Proved by
strong induction on the sum of the generalized-eigenspace orders. -/
lemma bilinear_eq_zero_on_genEigenspaces
    (T : Module.End ℂ V) (B : V →ₗ[ℂ] (V →ₗ[ℂ] ℂ)) (c ξ ν : ℂ)
    (hB : ∀ x y, B x (T y) + B (T x) y = c * B x y)
    (hres : ξ + ν ≠ c) :
    ∀ (k l : ℕ) (x y : V), x ∈ T.genEigenspace ξ k →
      y ∈ T.genEigenspace ν l → B x y = 0 := by
  intro k l
  induction hsum : k + l using Nat.strong_induction_on generalizing k l with
  | h s ih =>
      intro x y hx hy
      rcases k with _ | k
      · have hx' : x ∈ T.genEigenspace ξ (0 : ℕ∞) := by simpa using hx
        have hxzero :=
          (Module.End.mem_genEigenspace_zero (f := T) (μ := ξ) (x := x)).mp hx'
        subst x
        simp
      rcases l with _ | l
      · have hy' : y ∈ T.genEigenspace ν (0 : ℕ∞) := by simpa using hy
        have hyzero :=
          (Module.End.mem_genEigenspace_zero (f := T) (μ := ν) (x := y)).mp hy'
        subst y
        simp
      let Nx := (T - ξ • (1 : Module.End ℂ V)) x
      let Ny := (T - ν • (1 : Module.End ℂ V)) y
      have hxN : Nx ∈ T.genEigenspace ξ k := by
        rw [Module.End.mem_genEigenspace_nat] at hx ⊢
        simpa only [Nx, pow_succ, Module.End.mul_apply] using hx
      have hyN : Ny ∈ T.genEigenspace ν l := by
        rw [Module.End.mem_genEigenspace_nat] at hy ⊢
        simpa only [Ny, pow_succ, Module.End.mul_apply] using hy
      have hNx : B Nx y = 0 := by
        apply ih (k + (l + 1)) (by omega) k (l + 1) rfl Nx y hxN hy
      have hNy : B x Ny = 0 := by
        apply ih ((k + 1) + l) (by omega) (k + 1) l rfl x Ny hx hyN
      have hrec := hB x y
      have hTx : T x = Nx + ξ • x := by simp [Nx]
      have hTy : T y = Ny + ν • y := by simp [Ny]
      rw [hTx, hTy] at hrec
      simp [hNx, hNy] at hrec
      have hcoeff : ξ + ν - c ≠ 0 := sub_ne_zero.mpr hres
      apply (mul_eq_zero.mp ?_).resolve_left hcoeff
      linear_combination hrec

/-- A nonzero vector in a maximal generalized eigenspace witnesses that eigenvalue. -/
lemma hasEigenvalue_of_mem_maxGenEigenspace_ne_zero
    (T : Module.End ℂ V) {ξ : ℂ} {x : V}
    (hx : x ∈ T.maxGenEigenspace ξ) (hx0 : x ≠ 0) :
    T.HasEigenvalue ξ := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T ξ x).mp hx
  have hk0 : k ≠ 0 := by
    intro hkzero
    subst k
    simpa using hx0 (by simpa using hk)
  apply Module.End.hasEigenvalue_of_hasGenEigenvalue
  rw [Module.End.hasGenEigenvalue_iff, Submodule.ne_bot_iff]
  exact ⟨x, Module.End.mem_genEigenspace_nat.mpr hk, hx0⟩

/-- A resonance-avoiding bilinear form vanishes identically on a finite-dimensional space:
if no pair of `T`-eigenvalues sums to `c`, `bilinear_eq_zero_on_genEigenspaces` applies to
every pair of vectors via the generalized-eigenspace decomposition. -/
lemma bilinear_eq_zero_of_no_resonance
    [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (B : V →ₗ[ℂ] (V →ₗ[ℂ] ℂ)) (c : ℂ)
    (hB : ∀ x y, B x (T y) + B (T x) y = c * B x y)
    (hres : ∀ ξ ν, T.HasEigenvalue ξ → T.HasEigenvalue ν → ξ + ν ≠ c) :
    B = 0 := by
  apply LinearMap.ext
  intro x
  change B x = 0
  rw [← LinearMap.mem_ker]
  have hxall : (⊤ : Submodule ℂ V) ≤ LinearMap.ker B := by
    rw [← T.iSup_maxGenEigenspace_eq_top]
    apply iSup_le
    intro ξ x hx
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro y
    have hyall : (⊤ : Submodule ℂ V) ≤ LinearMap.ker (B x) := by
      rw [← T.iSup_maxGenEigenspace_eq_top]
      apply iSup_le
      intro ν y hy
      rw [LinearMap.mem_ker]
      by_cases hx0 : x = 0
      · simp [hx0]
      by_cases hy0 : y = 0
      · simp [hy0]
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T ξ x).mp hx
      obtain ⟨l, hl⟩ := (Module.End.mem_maxGenEigenspace T ν y).mp hy
      exact bilinear_eq_zero_on_genEigenspaces T B c ξ ν hB
        (hres ξ ν
          (hasEigenvalue_of_mem_maxGenEigenspace_ne_zero T hx hx0)
          (hasEigenvalue_of_mem_maxGenEigenspace_ne_zero T hy hy0))
        k l x y (Module.End.mem_genEigenspace_nat.mpr hk)
          (Module.End.mem_genEigenspace_nat.mpr hl)
    exact LinearMap.mem_ker.mp (hyall Submodule.mem_top)
  exact hxall Submodule.mem_top

/-! ## Compatibility of `Matrix.toBilin'` with matrix multiplication -/

/-- `Matrix.toBilin'` turns right multiplication by `A` into applying `A` on the right. -/
lemma toBilin_right_mul {K : Type*} [CommSemiring K] {n : ℕ}
    (H A : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Matrix.toBilin' (H * A) x y = Matrix.toBilin' H x (A *ᵥ y) := by
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.mulVec_mulVec]

/-- `Matrix.toBilin'` turns left multiplication by `Aᵀ` into applying `A` on the left. -/
lemma toBilin_left_transpose_mul {K : Type*} [CommSemiring K] {n : ℕ}
    (H A : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Matrix.toBilin' (Aᵀ * H) x y = Matrix.toBilin' H (A *ᵥ x) y := by
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec,
    ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, Matrix.dotProduct_mulVec]

/-- A symmetric real matrix's bilinear form is symmetric in its two arguments. -/
lemma toBilin_symm_real
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) (x y : Fin n → ℝ) :
    Matrix.toBilin' H x y = Matrix.toBilin' H y x := by
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose]
  rw [hH.eq, dotProduct_comm]

/-! ## Reverse spectral mapping for the matrix exponential -/

noncomputable section

open scoped Matrix.Norms.Frobenius

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private lemma continuousLinearMap_exp_apply_of_apply_eq_smul
    (T : E →L[ℂ] E) (μ : ℂ) (v : E) (hTv : T v = μ • v) :
    NormedSpace.exp T v = Complex.exp μ • v := by
  have hpow : ∀ k : ℕ, (T ^ k) v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, ContinuousLinearMap.mul_apply, hTv, map_smul, ih]
        rw [smul_smul]
        simp only [pow_succ]
        rw [mul_comm]
  rw [congrFun (NormedSpace.exp_eq_tsum ℂ) T]
  change (ContinuousLinearMap.apply ℂ E v)
    (∑' n : ℕ, ((n.factorial : ℂ)⁻¹) • T ^ n) = _
  rw [(ContinuousLinearMap.apply ℂ E v).map_tsum (NormedSpace.expSeries_summable' T)]
  change (∑' n : ℕ, (((n.factorial : ℂ)⁻¹) • T ^ n) v) = _
  simp_rw [ContinuousLinearMap.smul_apply, hpow, smul_smul]
  have hs : Summable (fun n : ℕ ↦ (n.factorial : ℂ)⁻¹ * μ ^ n) := by
    simpa [smul_eq_mul] using NormedSpace.expSeries_summable' (𝕂 := ℂ) μ
  rw [hs.tsum_smul_const]
  congr 1
  rw [Complex.exp_eq_exp_ℂ]
  simpa [smul_eq_mul] using (congrFun (NormedSpace.exp_eq_tsum ℂ) μ).symm

/-- The matrix exponential acts on an eigenvector by exponentiating its eigenvalue.

Reference: standard power-series functional calculus for the exponential. -/
private lemma exp_mulVec_of_mulVec_eq_smul
    (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) (v : Fin n → ℂ)
    (hAv : A *ᵥ v = μ • v) :
    NormedSpace.exp A *ᵥ v = Complex.exp μ • v := by
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  letI : NormedAlgebra ℚ
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  let e := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  let T := e A
  have hTv : T (WithLp.toLp 2 v) = μ • WithLp.toLp 2 v := by
    simpa [T, e] using congrArg (WithLp.toLp 2) hAv
  have heig := continuousLinearMap_exp_apply_of_apply_eq_smul
    T μ (WithLp.toLp 2 v) hTv
  have he_cont : Continuous e := by
    exact LinearMap.continuous_of_finiteDimensional e.toAlgEquiv.toLinearMap
  have hmap : e (NormedSpace.exp A) = NormedSpace.exp T := by
    simpa [T] using NormedSpace.map_exp e he_cont A
  apply WithLp.toLp_injective 2
  rw [← Matrix.toEuclideanCLM_toLp (NormedSpace.exp A) v]
  change (e (NormedSpace.exp A)) (WithLp.toLp 2 v) = _
  rw [hmap, heig]
  simp

/-- Every spectral value of a complex matrix exponential is the exponential of an
eigenvalue of the original matrix.

This is the reverse inclusion in spectral mapping specialized to finite complex matrices.
It is proved algebraically by restricting `A` to an eigenspace of `exp A`.

Reference: standard spectral-mapping theorem for the matrix exponential. -/
lemma exists_eigenpair_of_mem_spectrum_exp
    (A : Matrix (Fin n) (Fin n) ℂ) {z : ℂ}
    (hz : z ∈ spectrum ℂ (NormedSpace.exp A)) :
    ∃ (μ : ℂ) (v : Fin n → ℂ),
      v ≠ 0 ∧ A *ᵥ v = μ • v ∧ z = Complex.exp μ := by
  have hz' : Module.End.HasEigenvalue (NormedSpace.exp A).toLin' z := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']
    exact hz
  let W : Submodule ℂ (Fin n → ℂ) := Module.End.eigenspace (NormedSpace.exp A).toLin' z
  have hW : W ≠ ⊥ := by simpa [W] using hz'
  letI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hcommMatrix : Commute (NormedSpace.exp A) A := (Commute.refl A).exp_left
  have hcomm : Commute (NormedSpace.exp A).toLin' A.toLin' :=
    hcommMatrix.map Matrix.toLinAlgEquiv'
  have hmap : Set.MapsTo A.toLin' W W := by
    simpa [W] using Module.End.mapsTo_genEigenspace_of_comm hcomm z 1
  let AW : Module.End ℂ W := A.toLin'.restrict hmap
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue AW
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hAwSubtype : AW w = μ • w := hw.apply_eq_smul
  have hAw : A *ᵥ (w : Fin n → ℂ) = μ • (w : Fin n → ℂ) := by
    have := congrArg Subtype.val hAwSubtype
    simpa [AW, Matrix.toLin'_apply'] using this
  have hExpAw : NormedSpace.exp A *ᵥ (w : Fin n → ℂ) = z • (w : Fin n → ℂ) := by
    have hwmem : (w : Fin n → ℂ) ∈
        Module.End.eigenspace (NormedSpace.exp A).toLin' z := w.property
    have := Module.End.mem_eigenspace_iff.mp hwmem
    simpa [Matrix.toLin'_apply'] using this
  have hseries := exp_mulVec_of_mulVec_eq_smul A μ (w : Fin n → ℂ) hAw
  have hzexp : z = Complex.exp μ := by
    apply smul_left_injective ℂ (Subtype.coe_ne_coe.mpr hw.2)
    exact hExpAw.symm.trans hseries
  exact ⟨μ, w, Subtype.coe_ne_coe.mpr hw.2, hAw, hzexp⟩

end

end MatrixAlgebra

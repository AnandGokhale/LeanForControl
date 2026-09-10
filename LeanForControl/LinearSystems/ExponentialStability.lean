import LeanForControl.LinearSystems.Hurwitz
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# A contractive exponential block for Hurwitz matrices

This file derives a discrete contractivity consequence of the Hurwitz condition without
assuming exponential decay.  The proof first establishes the reverse direction of spectral
mapping for the matrix exponential, uses the Gelfand formula to obtain a contractive power,
and then transfers that power back from the complexification to the original real matrix.

The resulting positive integer `m` is the finite block needed to construct continuous-time
decay estimates by splitting time into intervals of length `m`.

Reference: Rudin, *Functional Analysis* (Gelfand's formula and spectral mapping); Khalil,
*Nonlinear Systems* (Hurwitz matrices and exponential stability).
-/

namespace LinearSystems

open Filter Matrix Module NormedSpace Set
open scoped Matrix.Norms.Frobenius Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private lemma continuousLinearMap_exp_apply_of_apply_eq_smul
    (T : E →L[ℂ] E) (μ : ℂ) (v : E) (hTv : T v = μ • v) :
    exp T v = Complex.exp μ • v := by
  have hpow : ∀ k : ℕ, (T ^ k) v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, ContinuousLinearMap.mul_apply, hTv, map_smul, ih]
        rw [smul_smul]
        simp only [pow_succ]
        rw [mul_comm]
  rw [congrFun (exp_eq_tsum ℂ) T]
  change (ContinuousLinearMap.apply ℂ E v)
    (∑' n : ℕ, ((n.factorial : ℂ)⁻¹) • T ^ n) = _
  rw [(ContinuousLinearMap.apply ℂ E v).map_tsum (expSeries_summable' T)]
  change (∑' n : ℕ, (((n.factorial : ℂ)⁻¹) • T ^ n) v) = _
  simp_rw [ContinuousLinearMap.smul_apply, hpow, smul_smul]
  have hs : Summable (fun n : ℕ ↦ (n.factorial : ℂ)⁻¹ * μ ^ n) := by
    simpa [smul_eq_mul] using expSeries_summable' (𝕂 := ℂ) μ
  rw [hs.tsum_smul_const]
  congr 1
  rw [Complex.exp_eq_exp_ℂ]
  simpa [smul_eq_mul] using (congrFun (exp_eq_tsum ℂ) μ).symm

variable {n : ℕ}

/-- The matrix exponential acts on an eigenvector by exponentiating its eigenvalue.

Reference: standard power-series functional calculus for the exponential. -/
private lemma exp_mulVec_of_mulVec_eq_smul
    (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) (v : Fin n → ℂ)
    (hAv : A *ᵥ v = μ • v) :
    exp A *ᵥ v = Complex.exp μ • v := by
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
  have hmap : e (exp A) = exp T := by
    simpa [T] using NormedSpace.map_exp e he_cont A
  apply WithLp.toLp_injective 2
  rw [← Matrix.toEuclideanCLM_toLp (exp A) v]
  change (e (exp A)) (WithLp.toLp 2 v) = _
  rw [hmap, heig]
  simp

/-- Every spectral value of a complex matrix exponential is the exponential of an
eigenvalue of the original matrix.

This is the reverse inclusion in spectral mapping specialized to finite complex matrices.
It is proved algebraically by restricting `A` to an eigenspace of `exp A`.

Reference: standard spectral-mapping theorem for the matrix exponential. -/
private lemma exists_eigenpair_of_mem_spectrum_exp
    (A : Matrix (Fin n) (Fin n) ℂ) {z : ℂ}
    (hz : z ∈ spectrum ℂ (exp A)) :
    ∃ (μ : ℂ) (v : Fin n → ℂ),
      v ≠ 0 ∧ A *ᵥ v = μ • v ∧ z = Complex.exp μ := by
  have hz' : Module.End.HasEigenvalue (exp A).toLin' z := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']
    exact hz
  let W : Submodule ℂ (Fin n → ℂ) := Module.End.eigenspace (exp A).toLin' z
  have hW : W ≠ ⊥ := by simpa [W] using hz'
  letI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hcommMatrix : Commute (exp A) A := (Commute.refl A).exp_left
  have hcomm : Commute (exp A).toLin' A.toLin' :=
    hcommMatrix.map Matrix.toLinAlgEquiv'
  have hmap : MapsTo A.toLin' W W := by
    simpa [W] using Module.End.mapsTo_genEigenspace_of_comm hcomm z 1
  let AW : Module.End ℂ W := A.toLin'.restrict hmap
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue AW
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hAwSubtype : AW w = μ • w := hw.apply_eq_smul
  have hAw : A *ᵥ (w : Fin n → ℂ) = μ • (w : Fin n → ℂ) := by
    have := congrArg Subtype.val hAwSubtype
    simpa [AW, Matrix.toLin'_apply'] using this
  have hExpAw : exp A *ᵥ (w : Fin n → ℂ) = z • (w : Fin n → ℂ) := by
    have hwmem : (w : Fin n → ℂ) ∈
        Module.End.eigenspace (exp A).toLin' z := w.property
    have := Module.End.mem_eigenspace_iff.mp hwmem
    simpa [Matrix.toLin'_apply'] using this
  have hseries := exp_mulVec_of_mulVec_eq_smul A μ (w : Fin n → ℂ) hAw
  have hzexp : z = Complex.exp μ := by
    apply smul_left_injective ℂ (Subtype.coe_ne_coe.mpr hw.2)
    exact hExpAw.symm.trans hseries
  exact ⟨μ, w, Subtype.coe_ne_coe.mpr hw.2, hAw, hzexp⟩

/-- An element with spectral radius strictly below one has a positive power whose norm is
strictly below one.

Reference: Rudin, *Functional Analysis* (Gelfand's spectral-radius formula). -/
private lemma exists_pow_norm_lt_one_of_spectralRadius_lt_one
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    [Nontrivial 𝔸] (a : 𝔸) (ha : spectralRadius ℂ a < 1) :
    ∃ m : ℕ, 0 < m ∧ ‖a ^ m‖ < 1 := by
  have heventually : ∀ᶠ m : ℕ in atTop,
      ((↑‖a ^ m‖₊ : ENNReal) ^ (1 / (m : ℝ))) < 1 :=
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a)
      (Iio_mem_nhds ha)
  have hnonzero : ∀ᶠ m : ℕ in atTop, m ≠ 0 := eventually_ne_atTop 0
  obtain ⟨m, hmroot, hm0⟩ := (heventually.and hnonzero).exists
  refine ⟨m, Nat.pos_of_ne_zero hm0, ?_⟩
  by_contra hnot
  have hbase : (1 : ENNReal) ≤ (↑‖a ^ m‖₊ : ENNReal) := by
    apply ENNReal.coe_le_coe.mpr
    change (1 : ℝ) ≤ ‖a ^ m‖
    exact not_lt.mp hnot
  have hexponent : 0 < (1 / (m : ℝ)) :=
    one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0))
  exact (not_le_of_gt hmroot) (ENNReal.one_le_rpow hbase hexponent)

/-- Entrywise complexification commutes with the matrix exponential.

Original: compatibility bridge for the real and complex matrix exponential. -/
lemma complexification_exp (A : Matrix (Fin n) (Fin n) ℝ) :
    complexification (exp A) = exp (complexification A) := by
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℝ) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  let φ : Matrix (Fin n) (Fin n) ℝ →+* Matrix (Fin n) (Fin n) ℂ :=
    (algebraMap ℝ ℂ).mapMatrix
  have hφ : Continuous φ := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact Complex.continuous_ofReal.comp
      ((continuous_apply j).comp (continuous_apply i))
  simpa [φ, complexification] using NormedSpace.map_exp φ hφ A

/-- Entrywise complexification preserves the Frobenius norm.

Original: norm compatibility bridge for the real and complex matrix spaces. -/
lemma norm_complexification (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖complexification A‖ = ‖A‖ := by
  change ‖A.map (algebraMap ℝ ℂ)‖ = ‖A‖
  exact Matrix.frobenius_norm_map_eq A (algebraMap ℝ ℂ) (fun x ↦ Complex.norm_real x)

/-- Every spectral value of the exponential of a complexified Hurwitz matrix lies strictly
inside the unit disk.

Reference: standard spectral mapping for the matrix exponential and the definition of a
Hurwitz matrix. -/
private lemma norm_lt_one_of_mem_spectrum_exp_complexification
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A) {z : ℂ}
    (hz : z ∈ spectrum ℂ (exp (complexification A))) :
    ‖z‖ < 1 := by
  obtain ⟨μ, v, hv, hAv, rfl⟩ :=
    exists_eigenpair_of_mem_spectrum_exp (complexification A) hz
  rw [Complex.norm_exp]
  exact Real.exp_lt_one_iff.mpr (by simpa using hA μ v hv hAv)

/-- The exponential of a complexified Hurwitz matrix has spectral radius strictly below
one.

Reference: standard spectral mapping for the matrix exponential. -/
lemma spectralRadius_exp_complexification_lt_one
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A) :
    spectralRadius ℂ (exp (complexification A)) < 1 := by
  by_cases hn : n = 0
  · subst n
    have heq : exp (complexification A) = 0 := Subsingleton.elim _ _
    rw [heq, spectrum.spectralRadius_zero]
    exact zero_lt_one
  · letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    apply spectrum.spectralRadius_lt_of_forall_lt
    intro z hz
    simpa only [ENNReal.coe_lt_coe] using
      norm_lt_one_of_mem_spectrum_exp_complexification hA hz

/-- A real Hurwitz matrix has a positive integer-time exponential block with Frobenius norm
strictly below one.

This is the discrete contractivity bridge used by finite-block constructions of continuous
exponential decay.  No decay or Lyapunov-equation result is assumed in its proof.

Reference: Rudin, *Functional Analysis* (Gelfand's formula); Khalil,
*Nonlinear Systems* (Hurwitz matrices and exponential stability). -/
theorem IsHurwitz.exists_norm_exp_nat_smul_lt_one
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A) :
    ∃ m : ℕ, 0 < m ∧ ‖NormedSpace.exp ((m : ℝ) • A)‖ < 1 := by
  by_cases hn : n = 0
  · subst n
    refine ⟨1, Nat.zero_lt_succ 0, ?_⟩
    rw [Subsingleton.elim (exp (((1 : ℕ) : ℝ) • A)) 0]
    norm_num
  · letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    obtain ⟨m, hmpos, hm⟩ := exists_pow_norm_lt_one_of_spectralRadius_lt_one
      (exp (complexification A)) (spectralRadius_exp_complexification_lt_one hA)
    refine ⟨m, hmpos, ?_⟩
    calc
      ‖exp ((m : ℝ) • A)‖ =
          ‖complexification (exp ((m : ℝ) • A))‖ :=
        (norm_complexification _).symm
      _ = ‖exp (complexification ((m : ℝ) • A))‖ := by
        rw [complexification_exp]
      _ = ‖exp (m • complexification A)‖ := by
        congr 2
        ext i j
        simp [complexification]
      _ = ‖exp (complexification A) ^ m‖ := by
        rw [Matrix.exp_nsmul]
      _ < 1 := hm

end

end LinearSystems

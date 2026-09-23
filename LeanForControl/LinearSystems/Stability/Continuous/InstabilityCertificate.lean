import LeanForControl.LinearSystems.Stability.Continuous.DefsHurwitz
import LeanForControl.MatrixAlgebra.QuadraticForm
import LeanForControl.MatrixAlgebra.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Order.Interval.Set.Infinite
import Architect

/-!
# Quadratic certificates for an unstable eigenmode

This file constructs a real quadratic Chetaev certificate from a complex eigenpair
whose eigenvalue has positive real part.  The construction solves a shifted
Lyapunov--Sylvester equation after choosing a nonresonant shift, deriving every
ingredient from finite-dimensional linear algebra.

Reference: Hahn, *Stability of Motion*; Khalil, *Nonlinear Systems*.
-/

open Matrix MatrixAlgebra Set
open scoped RealInnerProductSpace

namespace LinearSystems

variable {n : ℕ}

private def shiftedLyapunovOperator
    (A : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun H := H * A + Aᵀ * H - (2 * a) • H
  map_add' H K := by
    simp only [add_mul, mul_add, smul_add]
    abel
  map_smul' r H := by
    ext i j
    simp [Matrix.mul_apply]
    ring

private lemma shiftedLyapunovOperator_injective_of_no_resonance
    (A : Matrix (Fin n) (Fin n) ℝ) (a : ℝ)
    (hres : ∀ ξ ν,
      Module.End.HasEigenvalue (A.map (algebraMap ℝ ℂ)).mulVecLin ξ →
      Module.End.HasEigenvalue (A.map (algebraMap ℝ ℂ)).mulVecLin ν →
      ξ + ν ≠ (2 * a : ℝ)) :
    Function.Injective (shiftedLyapunovOperator A a) := by
  intro H K hHK
  suffices H - K = 0 by exact sub_eq_zero.mp this
  let D := H - K
  have hD : shiftedLyapunovOperator A a D = 0 := by
    change shiftedLyapunovOperator A a (H - K) = 0
    rw [map_sub, hHK, sub_self]
  let AC : Matrix (Fin n) (Fin n) ℂ := A.map (algebraMap ℝ ℂ)
  let DC : Matrix (Fin n) (Fin n) ℂ := D.map (algebraMap ℝ ℂ)
  let T : Module.End ℂ (Fin n → ℂ) := AC.mulVecLin
  let B : (Fin n → ℂ) →ₗ[ℂ] ((Fin n → ℂ) →ₗ[ℂ] ℂ) :=
    Matrix.toBilin' DC
  have hDC : DC * AC + ACᵀ * DC - (2 * (a : ℂ)) • DC = 0 := by
    ext i j
    have hij := congrFun (congrFun hD i) j
    change (∑ k, D i k * A k j) + (∑ k, A k i * D k j) -
      (2 * a) * D i j = 0 at hij
    change (∑ k, (D i k : ℂ) * (A k j : ℂ)) +
      (∑ k, (A k i : ℂ) * (D k j : ℂ)) -
        (2 * (a : ℂ)) * (D i j : ℂ) = 0
    exact_mod_cast hij
  have hB : ∀ x y, B x (T y) + B (T x) y = (2 * (a : ℂ)) * B x y := by
    intro x y
    have hm :=
      congrArg (fun M : Matrix (Fin n) (Fin n) ℂ ↦ Matrix.toBilin' M x y) hDC
    have hm' : Matrix.toBilin' (DC * AC) x y + Matrix.toBilin' (ACᵀ * DC) x y -
        (2 * (a : ℂ)) * B x y = 0 := by
      simpa [B] using hm
    simp only [B, T, Matrix.mulVecLin_apply]
    rw [← toBilin_right_mul DC AC x y, ← toBilin_left_transpose_mul DC AC x y]
    linear_combination hm'
  have hBzero : B = 0 :=
    bilinear_eq_zero_of_no_resonance T B (2 * (a : ℂ)) hB (by
      intro ξ ν hξ hν
      simpa using hres ξ ν hξ hν)
  have hDCzero : DC = 0 := Matrix.toBilin'.injective (by simpa [B] using hBzero)
  exact Matrix.map_injective Complex.ofReal_injective hDCzero

private lemma exists_symmetric_shifted_lyapunov_solution
    (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℂ) (hμ : 0 < μ.re) :
    ∃ (a : ℝ) (H : Matrix (Fin n) (Fin n) ℝ),
      0 < a ∧ a < μ.re ∧ H.IsHermitian ∧
        H * A + Aᵀ * H - (2 * a) • H = 1 := by
  let T : Module.End ℂ (Fin n → ℂ) :=
    (A.map (algebraMap ℝ ℂ)).mulVecLin
  let resonance : Set ℝ :=
    (fun z : ℂ × ℂ ↦ (z.1 + z.2).re / 2) ''
      (spectrum ℂ T ×ˢ spectrum ℂ T)
  have hres_finite : resonance.Finite := by
    apply Set.Finite.image
    exact T.finite_spectrum.prod T.finite_spectrum
  obtain ⟨a, haIoo, ha_not⟩ :=
    (Set.Ioo_infinite hμ).exists_notMem_finite hres_finite
  have hres : ∀ ξ ν,
      T.HasEigenvalue ξ → T.HasEigenvalue ν → ξ + ν ≠ (2 * a : ℝ) := by
    intro ξ ν hξ hν heq
    apply ha_not
    refine ⟨(ξ, ν), ⟨hξ.mem_spectrum, hν.mem_spectrum⟩, ?_⟩
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.ofReal_re] at hre ⊢
    linarith
  have hinj : Function.Injective (shiftedLyapunovOperator A a) :=
    shiftedLyapunovOperator_injective_of_no_resonance A a (by
      intro ξ ν hξ hν
      exact hres ξ ν hξ hν)
  have hsurj : Function.Surjective (shiftedLyapunovOperator A a) :=
    LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨H, hH⟩ := hsurj (1 : Matrix (Fin n) (Fin n) ℝ)
  have hHt : shiftedLyapunovOperator A a Hᵀ = 1 := by
    have ht := congrArg Matrix.transpose hH
    simpa [shiftedLyapunovOperator, Matrix.transpose_add, Matrix.transpose_sub,
      Matrix.transpose_mul, add_comm] using ht
  have hsymm : H.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hinj (hHt.trans hH.symm)
  exact ⟨a, H, haIoo.1, haIoo.2, hsymm, hH⟩

private lemma exists_positive_quadraticForm_direction
    (A H : Matrix (Fin n) (Fin n) ℝ) (a : ℝ)
    {μ : ℂ} {v : Fin n → ℂ}
    (hv : v ≠ 0)
    (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v)
    (ha : a < μ.re)
    (hHerm : H.IsHermitian)
    (hH : H * A + Aᵀ * H - (2 * a) • H = 1) :
    ∃ w : EuclideanSpace ℝ (Fin n),
      w ≠ 0 ∧ 0 < quadraticForm H w := by
  let x : Fin n → ℝ := fun i ↦ (v i).re
  let y : Fin n → ℝ := fun i ↦ (v i).im
  let B : (Fin n → ℝ) →ₗ[ℝ] ((Fin n → ℝ) →ₗ[ℝ] ℝ) :=
    Matrix.toBilin' H
  have hsymm : H.IsSymm := by
    rw [Matrix.IsSymm, ← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hHerm
  obtain ⟨hAxRaw, hAyRaw⟩ := eigenpair_real_imag A μ v heig
  have hAx : A *ᵥ x = μ.re • x - μ.im • y := by
    simpa only [x, y] using hAxRaw
  have hAy : A *ᵥ y = μ.im • x + μ.re • y := by
    simpa only [x, y] using hAyRaw
  have hBx :=
    congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ Matrix.toBilin' M x x) hH
  have hBy :=
    congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ Matrix.toBilin' M y y) hH
  have hBx' :
      B x (A *ᵥ x) + B (A *ᵥ x) x - (2 * a) * B x x = x ⬝ᵥ x := by
    simpa only [B, map_sub, map_add, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, Matrix.toBilin'_apply',
      Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_smul,
      toBilin_right_mul H A x x, toBilin_left_transpose_mul H A x x] using hBx
  have hBy' :
      B y (A *ᵥ y) + B (A *ᵥ y) y - (2 * a) * B y y = y ⬝ᵥ y := by
    simpa only [B, map_sub, map_add, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, Matrix.toBilin'_apply',
      Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_smul,
      toBilin_right_mul H A y y, toBilin_left_transpose_mul H A y y] using hBy
  have hBsymm (p q : Fin n → ℝ) : B p q = B q p := by
    exact toBilin_symm_real hsymm p q
  have hsum :
      2 * (μ.re - a) * (B x x + B y y) = x ⬝ᵥ x + y ⬝ᵥ y := by
    rw [hAx] at hBx'
    rw [hAy] at hBy'
    simp only [map_sub, map_add, map_smul, LinearMap.sub_apply,
      LinearMap.add_apply, smul_eq_mul] at hBx' hBy'
    simp only [LinearMap.smul_apply, smul_eq_mul] at hBx' hBy'
    rw [hBsymm x y] at hBx'
    rw [hBsymm x y] at hBy'
    linear_combination hBx' + hBy'
  have hvxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hxy
    simp only [not_or, not_not] at hxy
    apply hv
    funext i
    apply Complex.ext
    · exact congrFun hxy.1 i
    · exact congrFun hxy.2 i
  have hnormpos : 0 < x ⬝ᵥ x + y ⬝ᵥ y := by
    rcases hvxy with hx | hy
    · exact add_pos_of_pos_of_nonneg
        (by simpa only [star_trivial] using
          (Matrix.dotProduct_star_self_pos_iff (v := x)).mpr hx)
        (by simpa only [star_trivial] using dotProduct_star_self_nonneg y)
    · exact add_pos_of_nonneg_of_pos
        (by simpa only [star_trivial] using dotProduct_star_self_nonneg x)
        (by simpa only [star_trivial] using
          (Matrix.dotProduct_star_self_pos_iff (v := y)).mpr hy)
  have hqsum : 0 < B x x + B y y := by
    nlinarith [hsum, hnormpos, mul_pos zero_lt_two (sub_pos.mpr ha)]
  have hqx : 0 < B x x ∨ 0 < B y y := by
    by_contra h
    simp only [not_or, not_lt] at h
    linarith
  rcases hqx with hqx | hqy
  · refine ⟨WithLp.toLp 2 x, ?_, ?_⟩
    · intro hx0
      have hx : x = 0 := (WithLp.toLp_eq_zero 2).mp hx0
      rw [hx] at hqx
      simp at hqx
    · unfold quadraticForm
      rw [Matrix.inner_toEuclideanCLM]
      change 0 < x ⬝ᵥ H *ᵥ x
      simpa only [B, Matrix.toBilin'_apply'] using hqx
  · refine ⟨WithLp.toLp 2 y, ?_, ?_⟩
    · intro hy0
      have hy : y = 0 := (WithLp.toLp_eq_zero 2).mp hy0
      rw [hy] at hqy
      simp at hqy
    · unfold quadraticForm
      rw [Matrix.inner_toEuclideanCLM]
      change 0 < y ⬝ᵥ H *ᵥ y
      simpa only [B, Matrix.toBilin'_apply'] using hqy

/-- A complex eigenpair with positive-real eigenvalue yields a real quadratic
Chetaev certificate: a positive shift, a Hermitian matrix, a positive direction,
and a strictly positive-definite shifted Lie-derivative matrix.

The proof chooses a nonresonant shift and solves the resulting finite-dimensional
Lyapunov--Sylvester equation.  Symmetry follows from uniqueness, while the real and
imaginary parts of the eigenvector provide the positive direction.

Reference: Hahn, *Stability of Motion*; Khalil, *Nonlinear Systems*. -/
@[blueprint "thm:positive-real-eigenvalue-quadratic-certificate"
  (statement := /-- A complex eigenpair of a real matrix $A$ with
    $\operatorname{Re}\mu>0$ yields a Hermitian real matrix $H$, a shift
    $\alpha>0$, and a direction $w$ such that $w^{\mathsf T}Hw>0$ and
    \[
      HA+A^{\mathsf T}H-2\alpha H
    \]
    is positive definite. -/)
  (proof := /-- Choose a shift avoiding the finitely many pairwise spectral
    resonances, solve the resulting Lyapunov--Sylvester equation by
    finite-dimensional injectivity, and extract $w$ from the real or imaginary
    part of the supplied eigenvector. -/)]
theorem exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos
    (A : Matrix (Fin n) (Fin n) ℝ) {μ : ℂ} {v : Fin n → ℂ}
    (hv : v ≠ 0)
    (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v)
    (hμ : 0 < μ.re) :
    ∃ (α : ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
        (w : EuclideanSpace ℝ (Fin n)),
      0 < α ∧ H.IsHermitian ∧ w ≠ 0 ∧ 0 < quadraticForm H w ∧
        (H * A + Aᵀ * H - (2 * α) • H).PosDef := by
  obtain ⟨α, H, hα, hαμ, hH, hEq⟩ :=
    exists_symmetric_shifted_lyapunov_solution A μ hμ
  obtain ⟨w, hw, hHw⟩ :=
    exists_positive_quadraticForm_direction A H α hv heig hαμ hH hEq
  refine ⟨α, H, w, hα, hH, hw, hHw, ?_⟩
  rw [hEq]
  exact Matrix.PosDef.one

end LinearSystems

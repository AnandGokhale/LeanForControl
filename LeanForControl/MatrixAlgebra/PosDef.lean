import LeanForControl.MatrixAlgebra.Complexify
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Real.StarOrdered
import Architect

/-!
# Positive (semi)definite matrices

Facts about `P ≻ 0` and `P ⪰ 0` that Mathlib does not have: a convergent sum of positive
semidefinite matrices is positive semidefinite (`posSemidef_tsum`), and a real positive-definite
matrix stays positive definite against *complex* vectors (`PosDef.complexify`), which is what lets
a Lyapunov argument meet an eigenvector.

Reference: standard linear algebra.
-/

namespace Matrix

open scoped ComplexOrder

variable {X : Type*} [Finite X]

/-- **Positive semidefiniteness is preserved by convergent sums.**  Transposition and the quadratic
form `P ↦ xᵀ P x` are continuous and linear, so they pass through the sum. -/
@[blueprint "lem:posSemidef-tsum"
  (title := "A convergent sum of positive semidefinite matrices is positive semidefinite")
  (latexEnv := "lemma")
  (statement := /-- If $(M_i)$ is a summable family of real positive semidefinite matrices, then
    $\sum_i M_i$ is positive semidefinite. -/)
  (proof := /-- Transposition and the quadratic form $P \mapsto x^{\mathsf T}Px$ are continuous
    and linear, so they commute with the sum: the sum is symmetric, and its quadratic form is a
    sum of nonnegative terms. -/)]
lemma posSemidef_tsum {ι : Type*} {M : ι → Matrix X X ℝ} (hs : Summable M)
    (h : ∀ i, (M i).PosSemidef) : (∑' i, M i).PosSemidef := by
  have := Fintype.ofFinite X
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_tsum]
    refine tsum_congr fun i => ?_
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (h i).isHermitian
  · intro x
    -- The quadratic form at `x`, as a continuous linear functional of the matrix.
    let L : Matrix X X ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      { toFun := fun P => star x ⬝ᵥ (P *ᵥ x)
        map_add' := fun P R => by simp [Matrix.add_mulVec, dotProduct_add]
        map_smul' := fun a P => by simp [Matrix.smul_mulVec, dotProduct_smul] }
    have hsum : star x ⬝ᵥ ((∑' i, M i) *ᵥ x) = ∑' i, star x ⬝ᵥ (M i *ᵥ x) := by
      simpa [L, Function.comp_def] using (L.map_tsum hs)
    rw [hsum]
    exact tsum_nonneg fun i => (h i).dotProduct_mulVec_nonneg x

section Complexify

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- A real symmetric matrix pairs symmetrically: `aᵀ P b = bᵀ P a`. -/
private lemma dotProduct_mulVec_comm {P : Matrix X X ℝ} (hP : Pᵀ = P) (a b : X → ℝ) :
    a ⬝ᵥ (P *ᵥ b) = b ⬝ᵥ (P *ᵥ a) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hP, dotProduct_comm]

-- `Fintype X` is used by the proof (sums over `X`) but not by the statement, since
-- `Matrix.PosDef` is phrased with `Finsupp` sums.
set_option linter.unusedFintypeInType false in
omit [DecidableEq X] in
/-- **A real positive-definite matrix is positive definite over `ℂ`.**

Mathlib's `Matrix.PosDef` for a real matrix quantifies over *real* vectors only, but spectral
arguments produce complex eigenvectors. Splitting `v = a + i b` gives
`v* P v = aᵀ P a + bᵀ P b`, real because `P` is symmetric and positive because `v ≠ 0` forces
one of `a`, `b` to be nonzero.

This is what lets a Lyapunov certificate be evaluated against an eigenvector. -/
@[blueprint "lem:matrix-posDef-complexify"
  (title := "Positive definiteness survives complexification")
  (latexEnv := "lemma")
  (statement := /-- If a real matrix $P$ is positive definite, so is its complexification
    $P_{\mathbb C}$, as a Hermitian matrix over $\mathbb C$. -/)
  (proof := /-- Write a complex vector as $v = a + i b$ with $a, b$ real.  Then
    $v^{*}P_{\mathbb C}v = a^{\mathsf T}Pa + b^{\mathsf T}Pb$: the imaginary part cancels
    because $P$ is symmetric, and the real part is positive because $v \ne 0$ forces $a$ or
    $b$ to be nonzero. -/)]
theorem PosDef.complexify {P : Matrix X X ℝ} (hP : P.PosDef) :
    P.complexify.PosDef := by
  have hsymm : Pᵀ = P := hP.isHermitian
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
  · change P.complexifyᴴ = P.complexify
    rw [Matrix.complexify_conjTranspose, hsymm]
  -- Split `v` into real and imaginary parts.
  obtain ⟨a, ha⟩ : ∃ a : X → ℝ, ∀ i, a i = (v i).re := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : X → ℝ, ∀ i, b i = (v i).im := ⟨_, fun _ => rfl⟩
  have hre : ∀ i, ((P.complexify *ᵥ v) i).re = (P *ᵥ a) i := fun i => by
    rw [show a = fun j => (v j).re from funext ha]
    exact (congrFun (P.complexify_mulVec_re v) i).symm
  have him : ∀ i, ((P.complexify *ᵥ v) i).im = (P *ᵥ b) i := fun i => by
    rw [show b = fun j => (v j).im from funext hb]
    exact (congrFun (P.complexify_mulVec_im v) i).symm
  -- `v* P v = aᵀPa + bᵀPb`, with the imaginary part cancelling by symmetry of `P`.
  have hRe : (star v ⬝ᵥ (P.complexify *ᵥ v)).re = a ⬝ᵥ (P *ᵥ a) + b ⬝ᵥ (P *ᵥ b) := by
    simp only [dotProduct, Complex.re_sum, Complex.mul_re, Pi.star_apply, Complex.star_def,
      Complex.conj_re, Complex.conj_im, hre, him, ← ha, ← hb, neg_mul, sub_neg_eq_add]
    rw [← Finset.sum_add_distrib]
  have hIm : (star v ⬝ᵥ (P.complexify *ᵥ v)).im = 0 := by
    have hval : (star v ⬝ᵥ (P.complexify *ᵥ v)).im = a ⬝ᵥ (P *ᵥ b) - b ⬝ᵥ (P *ᵥ a) := by
      simp only [dotProduct, Complex.im_sum, Complex.mul_im, Pi.star_apply, Complex.star_def,
        Complex.conj_re, Complex.conj_im, hre, him, ← ha, ← hb, neg_mul]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hval, sub_eq_zero]
    exact dotProduct_mulVec_comm hsymm a b
  -- `v ≠ 0` forces one of `a`, `b` to be nonzero, so the real part is strictly positive.
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (funext fun i => Complex.ext
      (by rw [← ha i, hcon.1]; simp) (by rw [← hb i, hcon.2]; simp))
  have hnna : 0 ≤ a ⬝ᵥ (P *ᵥ a) := by simpa using hP.posSemidef.dotProduct_mulVec_nonneg a
  have hnnb : 0 ≤ b ⬝ᵥ (P *ᵥ b) := by simpa using hP.posSemidef.dotProduct_mulVec_nonneg b
  have hpos : 0 < a ⬝ᵥ (P *ᵥ a) + b ⬝ᵥ (P *ᵥ b) := by
    rcases hab with h | h
    · have hx := hP.dotProduct_mulVec_pos h; simp only [star_trivial] at hx; linarith
    · have hx := hP.dotProduct_mulVec_pos h; simp only [star_trivial] at hx; linarith
  rw [Complex.lt_def]
  exact ⟨by rw [hRe]; simpa using hpos, by rw [hIm]; simp⟩

end Complexify

end Matrix

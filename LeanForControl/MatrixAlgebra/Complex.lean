import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Architect

/-!
# Complexification of a real matrix

Entrywise complexification `A ↦ A.complexify`, and the properties it commutes with.

Spectral arguments must happen over `ℂ`, because `ℝ` is not algebraically closed, while the
systems the library is about have real coefficients. Every such argument therefore crosses
this bridge, and before this file each crossing spelled the bridge out as
`A.map (algebraMap ℝ ℂ)` and re-derived whatever commutation it needed inline.

The lemmas here are each one line; the point is that they are *named*, so that a proof can
say "complexification commutes with multiplication" rather than reconstructing it. The one
with real content is `Matrix.PosDef.complexify`: a real positive-definite matrix stays
positive definite against *complex* vectors, which is what lets a Lyapunov argument meet an
eigenvector.

Reference: standard. This file is general linear algebra and carries no control-theoretic
citation.
-/

namespace Matrix

open scoped ComplexOrder

variable {m n : Type*}

/-- Entrywise complexification of a real matrix. -/
@[blueprint "def:matrix-complexify"
  (title := "Complexification of a real matrix")
  (statement := /-- For a real matrix $A$, its \emph{complexification} $A_{\mathbb C}$ is
    obtained by applying $\mathbb R \hookrightarrow \mathbb C$ to each entry. -/)]
noncomputable def complexify (A : Matrix m n ℝ) : Matrix m n ℂ :=
  A.map (algebraMap ℝ ℂ)

@[simp] lemma complexify_apply (A : Matrix m n ℝ) (i : m) (j : n) :
    A.complexify i j = (A i j : ℂ) := rfl

lemma complexify_eq_map (A : Matrix m n ℝ) :
    A.complexify = A.map (algebraMap ℝ ℂ) := rfl

/-! ### What complexification commutes with -/

@[simp] lemma complexify_zero : (0 : Matrix m n ℝ).complexify = 0 := by ext i j; simp

@[simp] lemma complexify_add (A B : Matrix m n ℝ) :
    (A + B).complexify = A.complexify + B.complexify := by ext i j; simp

@[simp] lemma complexify_neg (A : Matrix m n ℝ) :
    (-A).complexify = -A.complexify := by ext i j; simp

@[simp] lemma complexify_sub (A B : Matrix m n ℝ) :
    (A - B).complexify = A.complexify - B.complexify := by ext i j; simp

@[simp] lemma complexify_smul (c : ℝ) (A : Matrix m n ℝ) :
    (c • A).complexify = (c : ℂ) • A.complexify := by ext i j; simp

@[simp] lemma complexify_transpose (A : Matrix m n ℝ) :
    Aᵀ.complexify = A.complexifyᵀ := by ext i j; simp

lemma complexify_conjTranspose (A : Matrix m n ℝ) :
    A.complexifyᴴ = Aᵀ.complexify := by ext i j; simp

section Square

variable {X : Type*}

@[simp] lemma complexify_one [DecidableEq X] : (1 : Matrix X X ℝ).complexify = 1 := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

@[simp] lemma complexify_mul [Fintype X] (A B : Matrix X X ℝ) :
    (A * B).complexify = A.complexify * B.complexify := by
  ext i j
  simp [Matrix.mul_apply, Complex.ofReal_sum]

end Square

/-! ### Complexification is isometric

Stated once per matrix norm, because the two are different instances on the same type, each
selected by a scoped `open`. Both tracks need it: the Peano--Baker/stability development works
in the `L∞` operator norm, the Lyapunov-equation development in the Frobenius norm.
-/

open scoped Matrix.Norms.Frobenius in
/-- Complexification preserves the Frobenius norm. -/
lemma frobenius_norm_complexify {X Y : Type*} [Fintype X] [Fintype Y] (M : Matrix X Y ℝ) :
    ‖M.complexify‖ = ‖M‖ :=
  Matrix.frobenius_norm_map_eq _ _ fun x => Complex.norm_real x

open scoped Matrix.Norms.Operator in
/-- Complexification preserves the `L∞` operator norm. -/
lemma linfty_opNorm_complexify {X : Type*} [Fintype X] (M : Matrix X X ℝ) :
    ‖M.complexify‖ = ‖M‖ := by
  simp [Matrix.linfty_opNorm_def]

/-! ### Complexification against vectors -/

section MulVec

variable {X : Type*} [Fintype X]

/-- A real matrix commutes with taking the real part of a complex vector, entrywise. -/
lemma complexify_mulVec_re (A : Matrix X X ℝ) (w : X → ℂ) :
    A *ᵥ (fun i => (w i).re) = fun i => (A.complexify *ᵥ w) i |>.re := by
  ext i
  simp [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re]

/-- A real matrix commutes with taking the imaginary part of a complex vector, entrywise. -/
lemma complexify_mulVec_im (A : Matrix X X ℝ) (w : X → ℂ) :
    A *ᵥ (fun i => (w i).im) = fun i => (A.complexify *ᵥ w) i |>.im := by
  ext i
  simp [Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im]

/-- A real matrix commutes with conjugating a complex vector: its entries are their own
conjugates. -/
lemma complexify_mulVec_star (A : Matrix X X ℝ) (v : X → ℂ) :
    A.complexify *ᵥ star v = star (A.complexify *ᵥ v) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

end MulVec

/-! ### Eigenpairs through the real/imaginary split -/

section Eigenpair

variable {X : Type*} [Fintype X]

/-- If `v` is a complex eigenvector of the complexification of a real matrix `A` with
eigenvalue `μ`, then for any complex scalar `c`, `A` maps the real part of `c • v` to the
real part of `c * μ • v`.

This is `complexify_mulVec_re` at `w := c • v`, substituting the eigenvector equation. -/
lemma complexify_mulVec_re_smul_eigenpair
    (A : Matrix X X ℝ) (μ c : ℂ) (v : X → ℂ)
    (heig : A.complexify *ᵥ v = μ • v) :
    (fun i ↦ (c * μ * v i).re) = A *ᵥ (fun i ↦ (c * v i).re) := by
  have h := A.complexify_mulVec_re (c • v)
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [h, Matrix.mulVec_smul, heig]
  ext i
  simp [mul_assoc]

/-- If `v` is a complex eigenvector of the complexification of a real matrix `A` with
eigenvalue `μ`, then for any complex scalar `c`, `A` maps the imaginary part of `c • v` to
the imaginary part of `c * μ • v`.

This is `complexify_mulVec_im` at `w := c • v`, substituting the eigenvector equation. -/
lemma complexify_mulVec_im_smul_eigenpair
    (A : Matrix X X ℝ) (μ c : ℂ) (v : X → ℂ)
    (heig : A.complexify *ᵥ v = μ • v) :
    (fun i ↦ (c * μ * v i).im) = A *ᵥ (fun i ↦ (c * v i).im) := by
  have h := A.complexify_mulVec_im (c • v)
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [h, Matrix.mulVec_smul, heig]
  ext i
  simp [mul_assoc]

/-- The real/imaginary decomposition of a complexified eigenpair: `A` maps `Re(v)` and
`Im(v)` to the real and imaginary parts of `μv`, expanded in `μ.re`/`μ.im`.

This is `complexify_mulVec_re_smul_eigenpair`/`complexify_mulVec_im_smul_eigenpair` at `c = 1`. -/
lemma eigenpair_real_imag
    (A : Matrix X X ℝ) (μ : ℂ) (v : X → ℂ)
    (heig : A.complexify *ᵥ v = μ • v) :
    A *ᵥ (fun i ↦ (v i).re) =
        μ.re • (fun i ↦ (v i).re) - μ.im • (fun i ↦ (v i).im) ∧
      A *ᵥ (fun i ↦ (v i).im) =
        μ.im • (fun i ↦ (v i).re) + μ.re • (fun i ↦ (v i).im) := by
  have hre := complexify_mulVec_re_smul_eigenpair A μ 1 v heig
  have him := complexify_mulVec_im_smul_eigenpair A μ 1 v heig
  simp only [one_mul] at hre him
  constructor
  · rw [← hre]
    ext i
    simp [Complex.mul_re]
  · rw [← him]
    ext i
    simp [Complex.mul_im, add_comm]

end Eigenpair

/-! ### Positive definiteness survives complexification -/

section PosDef

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

end PosDef

end Matrix

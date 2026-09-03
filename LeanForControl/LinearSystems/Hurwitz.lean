import LeanForControl.LinearSystems.Basic
import Mathlib.Analysis.Complex.Basic
import Architect

/-!
# Hurwitz matrices

This file defines continuous-time Hurwitz stability for real square matrices through
eigenpairs of their complexification.  The eigenpair formulation matches the concrete
matrix-vector equations used by the Hautus development and avoids choosing an enumeration
of eigenvalues.

The definition intentionally allows zero-dimensional matrices.  In dimension zero there
are no nonzero eigenvectors, so every matrix is Hurwitz with every rate; the theorem
`isHurwitzWithRate_fin_zero` records this convention explicitly.

Reference: standard continuous-time linear systems terminology.
-/

namespace LinearSystems

open Matrix

variable {n : ℕ}

/-- The entrywise complexification of a real matrix. -/
noncomputable def complexification (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A.map (algebraMap ℝ ℂ)

/-- A real matrix is Hurwitz with decay rate `α` when every complex eigenvalue `μ`
satisfies `μ.re < -α`.

This is stated using nonzero eigenvectors rather than an eigenvalue enumeration so it can
be used directly with PBH/Hautus arguments.

Reference: standard continuous-time linear systems terminology. -/
@[blueprint "def:isHurwitzWithRate"
  (statement := /-- A real square matrix $A$ is \emph{Hurwitz with decay rate}
    $\alpha$ when every complex eigenpair $(\mu,v)$ with $v \ne 0$ satisfies
    $\operatorname{Re}(\mu) < -\alpha$. -/)]
def IsHurwitzWithRate (α : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (μ : ℂ) (v : Fin n → ℂ), v ≠ 0 →
    complexification A *ᵥ v = μ • v → μ.re < -α

/-- A real matrix is Hurwitz when all of its complex eigenvalues have negative real part.

Reference: standard continuous-time linear systems terminology. -/
@[blueprint "def:isHurwitz"
  (statement := /-- A real square matrix is \emph{Hurwitz} when every complex
    eigenvalue has strictly negative real part. -/)]
abbrev IsHurwitz (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsHurwitzWithRate 0 A

/-- Ordinary Hurwitz stability is exactly Hurwitz stability with rate zero.

Original: this is the compatibility lemma for the rate-indexed definition. -/
theorem isHurwitz_iff_isHurwitzWithRate_zero (A : Matrix (Fin n) (Fin n) ℝ) :
    IsHurwitz A ↔ IsHurwitzWithRate 0 A :=
  Iff.rfl

/-- A certified Hurwitz decay rate may be weakened.

Original: monotonicity of the rate-indexed predicate. -/
theorem IsHurwitzWithRate.mono {A : Matrix (Fin n) (Fin n) ℝ} {α β : ℝ}
    (hA : IsHurwitzWithRate α A) (hβα : β ≤ α) :
    IsHurwitzWithRate β A := by
  intro μ v hv hAv
  have hμ := hA μ v hv hAv
  linarith

/-- Zero-dimensional matrices are Hurwitz with every rate, vacuously, because there is no
nonzero eigenvector.

Original: documents the chosen zero-dimensional convention. -/
theorem isHurwitzWithRate_fin_zero (α : ℝ) (A : Matrix (Fin 0) (Fin 0) ℝ) :
    IsHurwitzWithRate α A := by
  intro μ v hv
  exfalso
  apply hv
  funext i
  exact i.elim0

/-- Complexifying a real spectral shift and applying it to a vector adds the corresponding
complex scalar multiple of that vector.

Original: bridge used by the spectral-shift characterization. -/
lemma complexification_add_smul_one_mulVec
    (A : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (v : Fin n → ℂ) :
    complexification (A + α • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ v =
      complexification A *ᵥ v + (α : ℂ) • v := by
  simp [complexification, Matrix.map_add, Matrix.map_smul', Matrix.add_mulVec,
    Matrix.smul_mulVec]

/-- A matrix has decay rate `α` exactly when shifting it by `α I` makes it Hurwitz.

The sign is positive: an eigenvalue `μ` of `A` becomes `μ + α` for `A + α I`, so
`Re μ < -α` is equivalent to `Re (μ + α) < 0`.

Reference: the standard spectral-shift property for scalar multiples of the identity. -/
@[blueprint "thm:isHurwitzWithRate-iff-spectral-shift"
  (statement := /-- A real matrix $A$ is Hurwitz with decay rate $\alpha$ if and only if
    the spectrally shifted matrix $A + \alpha I$ is Hurwitz. -/)
  (proof := /-- A complex eigenvalue $\mu$ of $A$ becomes $\mu + \alpha$ after the shift,
    and $\operatorname{Re}(\mu) < -\alpha$ is equivalent to
    $\operatorname{Re}(\mu + \alpha) < 0$. -/)]
theorem isHurwitzWithRate_iff_add_smul_one
    (α : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    IsHurwitzWithRate α A ↔ IsHurwitz (A + α • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  constructor
  · intro hA μ v hv hshift
    have hbase : complexification A *ᵥ v = (μ - α) • v := by
      rw [complexification_add_smul_one_mulVec] at hshift
      rw [sub_smul]
      exact eq_sub_of_add_eq hshift
    have hμ := hA (μ - α) v hv hbase
    simp only [Complex.sub_re, Complex.ofReal_re] at hμ
    linarith
  · intro hshift μ v hv hbase
    have heig : complexification (A + α • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ v =
        (μ + α) • v := by
      rw [complexification_add_smul_one_mulVec, hbase]
      simp [add_smul]
    have hμ := hshift (μ + α) v hv heig
    simp only [Complex.add_re, Complex.ofReal_re] at hμ
    linarith

/-- The one-by-one matrix with entry `-γ` has every decay rate strictly below `γ`.
This is a concrete sanity check for the eigenpair definition and its sign convention.

Original: direct computation included as a sanity check for the definition. -/
theorem isHurwitzWithRate_neg_one_by_one {α γ : ℝ} (hαγ : α < γ) :
    IsHurwitzWithRate α ((-γ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  intro μ v hv hAv
  have hv0 : v 0 ≠ 0 := by
    intro hv0
    apply hv
    funext i
    fin_cases i
    exact hv0
  have heig := congrFun hAv 0
  have hμ : μ = (-γ : ℝ) := by
    apply mul_right_cancel₀ hv0
    simpa [complexification, Matrix.mulVec, dotProduct] using heig.symm
  rw [hμ]
  simp only [Complex.ofReal_re]
  linarith

end LinearSystems

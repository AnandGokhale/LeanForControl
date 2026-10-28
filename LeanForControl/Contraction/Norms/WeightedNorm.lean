import LeanForControl.Contraction.Norms.LogNorm
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Architect

/-!
# `Contraction.Norms.WeightedNorm` — weighted norms

Given an invertible linear map `R : E → F`, the weight, the weighted norm `‖x‖_R = ‖R x‖` is a
norm on `E`.  `WeightedNorm R` is `E` equipped with it.  It is a normed space like any other, so
every result proved for an arbitrary norm (regular pairings, the curve norm derivative, the
logarithmic norm and Lumer's property) applies to it unchanged.

`WeightedNorm R`, the operator norm `‖A‖_R` and the log norm `μ_R(A)` in it, and the matrix weights
`Matrix.toWeight` are defined in `Defs.lean`.

* `WeightedNorm.opNorm_eq`, `WeightedNorm.logNorm_eq` — `‖A‖_R = ‖R A R⁻¹‖` and
  `μ_R(A) = μ(R A R⁻¹)`.

References: F. Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), Section 2.3 and
Lemma 2.11.
-/

open scoped LogNorm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

namespace WeightedNorm

variable (R : E ≃L[ℝ] F)

/-- Moving `A` to the weighted space and then to `F` by `R` is `R A R⁻¹`. -/
private lemma weight_comp (A : E →L[ℝ] E) :
    (weight R ∘L (equiv R ∘L A ∘L (equiv R).symm : WeightedNorm R →L[ℝ] WeightedNorm R) ∘L
      (weight R).symm : F →L[ℝ] F) = R ∘L A ∘L R.symm := by
  ext x
  simp [equiv]

/-- **Weighted operator norms**: `‖A‖_R = ‖R A R⁻¹‖`. -/
theorem opNorm_eq (A : E →L[ℝ] E) : opNorm R A = ‖(R ∘L A ∘L R.symm : F →L[ℝ] F)‖ := by
  rw [opNorm, ← weight_comp R A, opNorm_conj _ (norm_weight R)]

/-- **Weighted log norms**: `μ_R(A) = μ(R A R⁻¹)`. -/
@[blueprint "thm:weightedNorm-logNorm-eq"
  (title := "Weighted operator and log norms")
  (statement := /-- For an invertible weight $R$ (\cref{def:weightedNorm}) and a bounded linear
    operator $A$, the operator norm and the log norm (\cref{def:logNorm}) induced by
    $\|\cdot\|_R$ are
    \[ \|A\|_R = \|R A R^{-1}\| \qquad \text{and} \qquad \mu_R(A) = \mu(R A R^{-1}). \]

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Lemma 2.11. -/)
  (proof := /-- $\|A x\|_R = \|(R A R^{-1})(R x)\|$, and $R$ maps the unit sphere of
    $\|\cdot\|_R$ onto that of $\|\cdot\|$; apply \cref{lem:logNorm-conj}. -/)]
theorem logNorm_eq (A : E →L[ℝ] E) :
    μ[R] A = μ (R ∘L A ∘L R.symm : F →L[ℝ] F) := by
  rw [logNorm, ← weight_comp R A, _root_.logNorm_conj _ (norm_weight R)]

end WeightedNorm

import LeanForControl.Contraction.Norms.LogNorm
import Architect

/-!
# `Contraction.Norms.WeightedNorm` — weighted norms

Given an invertible linear map `R : E → F`, the weight, the weighted norm `‖x‖_R = ‖R x‖` is a
norm on `E`.  `WeightedNorm R` is `E` equipped with it.  It is a normed space like any other, so
every result proved for an arbitrary norm (regular pairings, the curve norm derivative, the
logarithmic norm and Lumer's property) applies to it unchanged.

* `WeightedNorm R` — `E` with the norm `‖x‖_R = ‖R x‖`; `WeightedNorm.equiv R x` is the vector `x`
  measured in it, and `norm_equiv` reads `‖x‖_R = ‖R x‖`.
* `WeightedNorm.opNorm R A`, `WeightedNorm.logNorm R A` — `‖A‖_R` and `μ_R(A)`, the operator norm
  and the log norm of an operator `A` on `E`, measured in the weighted norm.
* `WeightedNorm.opNorm_eq`, `WeightedNorm.logNorm_eq` — `‖A‖_R = ‖R A R⁻¹‖` and
  `μ_R(A) = μ(R A R⁻¹)`.

References: F. Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), Section 2.3 and
Lemma 2.11.
-/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The weighted norm** `‖x‖_R = ‖R x‖`, for an invertible linear weight `R : E → F`:
`WeightedNorm R` is `E` equipped with it. -/
@[blueprint "def:weightedNorm"
  (title := "Weighted norm")
  (statement := /-- Given an invertible bounded linear map $R : E \to F$, the \emph{weighted norm}
    on $E$ is $\|x\|_R = \|R x\|$.  It is a norm because $R$ is linear and injective.

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Section 2.3. -/)]
def WeightedNorm (_R : E ≃L[ℝ] F) : Type _ := E

namespace WeightedNorm

variable (R : E ≃L[ℝ] F)

instance : AddCommGroup (WeightedNorm R) := inferInstanceAs (AddCommGroup E)

instance : Module ℝ (WeightedNorm R) := inferInstanceAs (Module ℝ E)

instance [Nontrivial E] : Nontrivial (WeightedNorm R) := inferInstanceAs (Nontrivial E)

/-- `R` on the weighted space, as a linear map: the norm is pulled back along it. -/
private def weightₗ : WeightedNorm R ≃ₗ[ℝ] F := R.toLinearEquiv

noncomputable instance : NormedAddCommGroup (WeightedNorm R) :=
  NormedAddCommGroup.induced _ _ (weightₗ R) (weightₗ R).injective

noncomputable instance : NormedSpace ℝ (WeightedNorm R) :=
  NormedSpace.induced ℝ _ _ (weightₗ R)

/-- `R`, from the weighted space onto `F`: it preserves the norm, `‖R x‖ = ‖x‖_R`. -/
private noncomputable def weight : WeightedNorm R ≃L[ℝ] F :=
  (LinearIsometryEquiv.mk (weightₗ R) fun _ => rfl).toContinuousLinearEquiv

private lemma norm_weight (x : WeightedNorm R) : ‖weight R x‖ = ‖x‖ := rfl

/-- The identity from `E` to the weighted space: the vector `x`, measured in the weighted norm. -/
noncomputable def equiv : E ≃L[ℝ] WeightedNorm R := R.trans (weight R).symm

/-- `‖x‖_R = ‖R x‖`. -/
lemma norm_equiv (x : E) : ‖equiv R x‖ = ‖R x‖ := by
  rw [← norm_weight, equiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]

/-- `‖A‖_R`: the operator norm of `A`, measured in the weighted norm. -/
noncomputable def opNorm (A : E →L[ℝ] E) : ℝ :=
  ‖(equiv R ∘L A ∘L (equiv R).symm : WeightedNorm R →L[ℝ] WeightedNorm R)‖

/-- `μ_R(A)`: the log norm of `A`, measured in the weighted norm. -/
noncomputable def logNorm (A : E →L[ℝ] E) : ℝ :=
  _root_.logNorm (equiv R ∘L A ∘L (equiv R).symm : WeightedNorm R →L[ℝ] WeightedNorm R)

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
    logNorm R A = _root_.logNorm (R ∘L A ∘L R.symm : F →L[ℝ] F) := by
  rw [logNorm, ← weight_comp R A, _root_.logNorm_conj _ (norm_weight R)]

end WeightedNorm

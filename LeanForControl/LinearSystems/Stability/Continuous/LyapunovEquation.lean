import LeanForControl.Analysis.SpectralRadius
import LeanForControl.LinearSystems.Stability.Continuous.Hurwitz
import LeanForControl.LinearSystems.Stability.DefsStability
import LeanForControl.MatrixAlgebra.Exponential
import LeanForControl.MatrixAlgebra.QuadraticForm
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Architect

/-!
# The continuous-time Lyapunov equation

This file defines the continuous-time Lyapunov equation and constructs its positive-definite
solution from a strict contraction of one matrix-exponential time step. The proof uses an
integral on one finite time block and the resulting convergent discrete Lyapunov series. It
also connects `MatrixAlgebra.QuadraticForm`'s generic quadratic-form machinery to the
equation: the derivative identity that makes a solution's quadratic form decrease along a
linear vector field.

Reference: Khalil, *Nonlinear Systems*.
-/

namespace LinearSystems

open Filter Matrix MatrixAlgebra MeasureTheory Set
open scoped Matrix.Norms.Frobenius RealInnerProductSpace Topology BigOperators ComplexOrder

section General

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The continuous linear map extracting entry `(i, j)` of a matrix.

Original: shared row/column projection helper for interval-integral and tsum
entrywise commutation arguments. -/
private noncomputable def entryCLM (i j : X) : Matrix X X ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.proj i : Matrix X X ℝ →L[ℝ] (X → ℝ))

/-- The continuous linear map evaluating the quadratic form `xᵀ P x` in its matrix
argument `P`, for a fixed vector `x`.

Original: shared quadratic-form-as-CLM helper for interval-integral and tsum
commutation arguments. -/
private noncomputable def quadraticEvalCLM (x : X → ℝ) : Matrix X X ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun P ↦ dotProduct (star x) (P *ᵥ x)
    map_add' := fun P R ↦ by simp [Matrix.add_mulVec, dotProduct_add]
    map_smul' := fun a P ↦ by simp [Matrix.smul_mulVec, dotProduct_smul] }

private noncomputable def lyapunovKernel
    (A Q : Matrix X X ℝ) (t : ℝ) :
    Matrix X X ℝ :=
  NormedSpace.exp (t • Aᵀ) * Q * NormedSpace.exp (t • A)

private noncomputable def finiteLyapunovIntegral
    (A Q : Matrix X X ℝ) (m : ℕ) :
    Matrix X X ℝ :=
  ∫ t in (0 : ℝ)..(m : ℝ), lyapunovKernel A Q t

private def lyapunovOperator (A : Matrix X X ℝ) :
    Matrix X X ℝ →ₗ[ℝ] Matrix X X ℝ where
  toFun P := P * A + Aᵀ * P
  map_add' P R := by simp only [add_mul, mul_add, add_assoc]; ac_rfl
  map_smul' a P := by simp only [RingHom.id_apply, smul_add, smul_mul_assoc, mul_smul_comm]

private noncomputable def conjugationOperator (C : Matrix X X ℝ) :
    Matrix X X ℝ →L[ℝ] Matrix X X ℝ :=
  ContinuousLinearMap.mulLeftRight ℝ _ Cᵀ C

private lemma hasDerivAt_lyapunovKernel_operator
    (A W : Matrix X X ℝ) (t : ℝ) :
    HasDerivAt (lyapunovKernel A W)
      (lyapunovKernel A (W * A + Aᵀ * W) t) t := by
  have hleft := (hasDerivAt_exp_smul_const Aᵀ t).mul_const W
  have hright := hasDerivAt_exp_smul_const' A t
  simpa only [lyapunovKernel, mul_add, add_mul, mul_assoc, add_comm] using hleft.mul hright

private lemma hasDerivAt_lyapunovKernel
    (A Q : Matrix X X ℝ) (t : ℝ) :
    HasDerivAt (lyapunovKernel A Q)
      (Aᵀ * lyapunovKernel A Q t + lyapunovKernel A Q t * A) t := by
  have hleft := (hasDerivAt_exp_smul_const' Aᵀ t).mul_const Q
  have hright := hasDerivAt_exp_smul_const A t
  simpa only [lyapunovKernel, mul_assoc] using hleft.mul hright

private lemma continuous_lyapunovKernel
    (A Q : Matrix X X ℝ) : Continuous (lyapunovKernel A Q) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_lyapunovKernel_operator A Q t).continuousAt

private lemma finiteLyapunovIntegral_operator
    (A W : Matrix X X ℝ) (m : ℕ) :
    finiteLyapunovIntegral A (W * A + Aᵀ * W) m =
      (NormedSpace.exp ((m : ℝ) • A))ᵀ * W * NormedSpace.exp ((m : ℝ) • A) - W := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_lyapunovKernel_operator A W t)
    ((continuous_lyapunovKernel A (W * A + Aᵀ * W)).intervalIntegrable 0 (m : ℝ))
  rw [finiteLyapunovIntegral]
  rw [h]
  simp only [lyapunovKernel, zero_smul, NormedSpace.exp_zero, one_mul, mul_one]
  congr 2
  rw [← Matrix.exp_transpose]
  congr 2

private lemma finiteLyapunovIntegral_lyapunovOperator
    (A Q : Matrix X X ℝ) (m : ℕ) :
    finiteLyapunovIntegral A Q m * A + Aᵀ * finiteLyapunovIntegral A Q m =
      (NormedSpace.exp ((m : ℝ) • A))ᵀ * Q * NormedSpace.exp ((m : ℝ) • A) - Q := by
  let L : Matrix X X ℝ →L[ℝ] Matrix X X ℝ :=
    LinearMap.toContinuousLinearMap (lyapunovOperator A)
  have hint : IntervalIntegrable (lyapunovKernel A Q) volume 0 (m : ℝ) :=
    (continuous_lyapunovKernel A Q).intervalIntegrable 0 (m : ℝ)
  have hmap := L.intervalIntegral_comp_comm hint
  calc
    finiteLyapunovIntegral A Q m * A + Aᵀ * finiteLyapunovIntegral A Q m =
        L (finiteLyapunovIntegral A Q m) := rfl
    _ = ∫ t in (0 : ℝ)..(m : ℝ), L (lyapunovKernel A Q t) := by
      simpa only [finiteLyapunovIntegral] using hmap.symm
    _ = finiteLyapunovIntegral A (Q * A + Aᵀ * Q) m := by
      apply intervalIntegral.integral_congr
      intro t _
      simpa [L, lyapunovOperator, add_comm] using (hasDerivAt_lyapunovKernel A Q t).unique
        (hasDerivAt_lyapunovKernel_operator A Q t)
    _ = (NormedSpace.exp ((m : ℝ) • A))ᵀ * Q *
          NormedSpace.exp ((m : ℝ) • A) - Q :=
      finiteLyapunovIntegral_operator A Q m

private lemma conjugationOperator_norm_lt_one
    (C : Matrix X X ℝ) (hC : ‖C‖ < 1) :
    ‖conjugationOperator C‖ < 1 := by
  calc
    ‖conjugationOperator C‖ ≤ ‖Cᵀ‖ * ‖C‖ :=
      ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ _ Cᵀ C
    _ = ‖C‖ * ‖C‖ := by rw [Matrix.frobenius_norm_transpose]
    _ < 1 := by nlinarith [norm_nonneg C]

private lemma tendsto_conjugationOperator_pow_apply_zero
    (C W : Matrix X X ℝ) (hC : ‖C‖ < 1) :
    Tendsto (fun k : ℕ ↦ ((conjugationOperator C) ^ k) W) atTop (nhds 0) := by
  let T : Matrix X X ℝ →L[ℝ] Matrix X X ℝ :=
    conjugationOperator C
  change Tendsto (fun k : ℕ ↦ (T ^ k) W) atTop (nhds 0)
  let ev :
      (Matrix X X ℝ →L[ℝ] Matrix X X ℝ) →L[ℝ]
        Matrix X X ℝ :=
    (ContinuousLinearMap.apply ℝ (Matrix X X ℝ)) W
  have hpows := tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (show ‖T‖ < 1 from conjugationOperator_norm_lt_one C hC)
  have happ := ev.continuous.continuousAt.tendsto.comp hpows
  simpa [ev, Function.comp_def] using happ

private lemma eq_zero_of_conjugationOperator_fixed
    (C W : Matrix X X ℝ) (hC : ‖C‖ < 1)
    (hfixed : conjugationOperator C W = W) : W = 0 := by
  have hpow (k : ℕ) : ((conjugationOperator C) ^ k) W = W := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ']
        simp only [ContinuousLinearMap.mul_apply, ih, hfixed]
  have hzero := tendsto_conjugationOperator_pow_apply_zero C W hC
  have hconst : Tendsto (fun _ : ℕ ↦ W) atTop (nhds 0) := by
    exact hzero.congr' (Eventually.of_forall fun k ↦ hpow k)
  exact tendsto_nhds_unique tendsto_const_nhds hconst

private lemma lyapunovOperator_injective_of_exp_norm_lt_one
    (A : Matrix X X ℝ) (m : ℕ)
    (hC : ‖NormedSpace.exp ((m : ℝ) • A)‖ < 1) :
    Function.Injective (lyapunovOperator A) := by
  let C := NormedSpace.exp ((m : ℝ) • A)
  intro W Y hXY
  let D := W - Y
  have hDop : D * A + Aᵀ * D = 0 := by
    change (lyapunovOperator A) D = 0
    rw [map_sub, hXY, sub_self]
  have hendpoint := finiteLyapunovIntegral_operator A D m
  rw [hDop, finiteLyapunovIntegral] at hendpoint
  simp only [lyapunovKernel, mul_zero, zero_mul, intervalIntegral.integral_zero] at hendpoint
  have hfixed : conjugationOperator C D = D := by
    change Cᵀ * D * C = D
    exact sub_eq_zero.mp hendpoint.symm
  have hDzero := eq_zero_of_conjugationOperator_fixed C D hC hfixed
  exact sub_eq_zero.mp hDzero

private lemma finiteLyapunovIntegral_posDef
    (A Q : Matrix X X ℝ) (m : ℕ)
    (hQ : Q.PosDef) (hm : 0 < m) :
    (finiteLyapunovIntegral A Q m).PosDef := by
  have hint : IntervalIntegrable (lyapunovKernel A Q) volume 0 (m : ℝ) :=
    (continuous_lyapunovKernel A Q).intervalIntegrable 0 (m : ℝ)
  have hentry (i j : X) :
      finiteLyapunovIntegral A Q m i j =
        ∫ t in (0 : ℝ)..(m : ℝ), lyapunovKernel A Q t i j := by
    have h := (entryCLM i j).intervalIntegral_comp_comm hint
    simpa [entryCLM, Function.comp_def, finiteLyapunovIntegral] using h.symm
  have hkernelHermitian (t : ℝ) : (lyapunovKernel A Q t).IsHermitian := by
    let B := NormedSpace.exp (t • A)
    have hleft : NormedSpace.exp (t • Aᵀ) = Bᴴ := by
      change NormedSpace.exp (t • Aᵀ) = (NormedSpace.exp (t • A))ᴴ
      rw [← Matrix.exp_conjTranspose]
      congr 2
    rw [lyapunovKernel, hleft]
    exact Matrix.isHermitian_conjTranspose_mul_mul B hQ.isHermitian
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian]
    ext i j
    simp only [Matrix.conjTranspose_apply, star_id_of_comm]
    rw [hentry, hentry]
    apply intervalIntegral.integral_congr
    intro t _
    have ht := hkernelHermitian t
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_apply, star_id_of_comm] using
      congrFun (congrFun ht i) j
  · intro x hx
    have hquadraticIntegral :
        dotProduct (star x) (finiteLyapunovIntegral A Q m *ᵥ x) =
          ∫ t in (0 : ℝ)..(m : ℝ),
            dotProduct (star x) (lyapunovKernel A Q t *ᵥ x) := by
      have h := (quadraticEvalCLM x).intervalIntegral_comp_comm hint
      simpa [quadraticEvalCLM, Function.comp_def, finiteLyapunovIntegral] using h.symm
    have hquadraticPos (t : ℝ) :
        0 < dotProduct (star x) (lyapunovKernel A Q t *ᵥ x) := by
      let B := NormedSpace.exp (t • A)
      have hB_injective : Function.Injective B.mulVec :=
        Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_exp (t • A))
      have hBx : B *ᵥ x ≠ 0 := by
        intro hzero
        apply hx
        apply hB_injective
        simpa using hzero
      have hkernel : lyapunovKernel A Q t = Bᴴ * Q * B := by
        change NormedSpace.exp (t • Aᵀ) * Q * NormedSpace.exp (t • A) = Bᴴ * Q * B
        congr 2
        rw [← Matrix.exp_conjTranspose]
        congr 2
      rw [hkernel]
      simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using
        hQ.dotProduct_mulVec_pos hBx
    rw [hquadraticIntegral]
    apply intervalIntegral.integral_pos (Nat.cast_pos.mpr hm)
    · change ContinuousOn (fun t ↦ (quadraticEvalCLM x) (lyapunovKernel A Q t)) (Icc 0 (m : ℝ))
      exact ((quadraticEvalCLM x).continuous.comp (continuous_lyapunovKernel A Q)).continuousOn
    · intro t _
      exact (hquadraticPos t).le
    · exact ⟨0, ⟨le_rfl, Nat.cast_nonneg m⟩, hquadraticPos 0⟩

private lemma posDef_conjugationOperator
    (C W : Matrix X X ℝ) (hC : IsUnit C) (hW : W.PosDef) :
    (conjugationOperator C W).PosDef := by
  have hconj : conjugationOperator C W = Cᴴ * W * C := by
    ext i j
    simp [conjugationOperator]
  rw [hconj]
  exact hW.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hC)

private lemma summable_conjugationOperator_pow_apply
    (C W : Matrix X X ℝ) (hC : ‖C‖ < 1) :
    Summable (fun k : ℕ ↦ ((conjugationOperator C) ^ k) W) := by
  let ev :
      (Matrix X X ℝ →L[ℝ] Matrix X X ℝ) →L[ℝ]
        Matrix X X ℝ :=
    (ContinuousLinearMap.apply ℝ (Matrix X X ℝ)) W
  have hs := (summable_geometric_of_norm_lt_one
    (conjugationOperator_norm_lt_one C hC)).map ev ev.continuous
  simpa [ev, Function.comp_def] using hs

private lemma lyapunovOperator_conjugationOperator
    (A C W : Matrix X X ℝ) (hAC : Commute A C) :
    lyapunovOperator A (conjugationOperator C W) =
      conjugationOperator C (lyapunovOperator A W) := by
  have hAtCt : Aᵀ * Cᵀ = Cᵀ * Aᵀ := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hAC.eq.symm
  change (Cᵀ * W * C) * A + Aᵀ * (Cᵀ * W * C) =
    Cᵀ * (W * A + Aᵀ * W) * C
  calc
    (Cᵀ * W * C) * A + Aᵀ * (Cᵀ * W * C) =
        Cᵀ * W * (C * A) + (Aᵀ * Cᵀ) * W * C := by
      simp only [mul_assoc]
    _ = Cᵀ * W * (A * C) + (Cᵀ * Aᵀ) * W * C := by
      rw [hAC.eq.symm, hAtCt]
    _ = Cᵀ * (W * A + Aᵀ * W) * C := by
      simp only [mul_add, add_mul, mul_assoc]

private lemma lyapunovOperator_conjugationOperator_pow
    (A C W : Matrix X X ℝ) (hAC : Commute A C) (k : ℕ) :
    lyapunovOperator A (((conjugationOperator C) ^ k) W) =
      ((conjugationOperator C) ^ k) (lyapunovOperator A W) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ']
      simp only [ContinuousLinearMap.mul_apply]
      rw [lyapunovOperator_conjugationOperator A C _ hAC, ih]

private lemma tsum_conjugationOperator_pow_apply_posDef
    (C R : Matrix X X ℝ) (hCunit : IsUnit C)
    (hCnorm : ‖C‖ < 1) (hR : R.PosDef) :
    (∑' k : ℕ, ((conjugationOperator C) ^ k) R).PosDef := by
  let term : ℕ → Matrix X X ℝ :=
    fun k ↦ ((conjugationOperator C) ^ k) R
  have hs : Summable term := summable_conjugationOperator_pow_apply C R hCnorm
  have htermPos (k : ℕ) : (term k).PosDef := by
    induction k with
    | zero => simpa [term] using hR
    | succ k ih =>
        rw [show term (k + 1) = conjugationOperator C (term k) by
          simp only [term, pow_succ', ContinuousLinearMap.mul_apply]]
        exact posDef_conjugationOperator C (term k) hCunit ih
  have hentry (i j : X) :
      (∑' k : ℕ, term k) i j = ∑' k : ℕ, term k i j := by
    have h := (entryCLM i j).map_tsum hs
    simpa [entryCLM, Function.comp_def] using h
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian]
    ext i j
    simp only [Matrix.conjTranspose_apply, star_id_of_comm]
    rw [hentry, hentry]
    apply tsum_congr
    intro k
    have hk := (htermPos k).isHermitian
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_apply, star_id_of_comm] using
      congrFun (congrFun hk i) j
  · intro x hx
    have hqsum :
        dotProduct (star x) ((∑' k : ℕ, term k) *ᵥ x) =
          ∑' k : ℕ, dotProduct (star x) (term k *ᵥ x) := by
      have h := (quadraticEvalCLM x).map_tsum hs
      simpa [quadraticEvalCLM, Function.comp_def] using h
    have hqsummable : Summable (fun k ↦ dotProduct (star x) (term k *ᵥ x)) := by
      simpa [quadraticEvalCLM, Function.comp_def] using
        hs.map (quadraticEvalCLM x) (quadraticEvalCLM x).continuous
    rw [hqsum, hqsummable.tsum_eq_zero_add]
    have hhead : 0 < dotProduct (star x) (term 0 *ᵥ x) :=
      (htermPos 0).dotProduct_mulVec_pos hx
    exact add_pos_of_pos_of_nonneg hhead (tsum_nonneg fun k ↦
      ((htermPos (k + 1)).dotProduct_mulVec_pos hx).le)

/-- If one positive integer time step of the matrix exponential is a strict contraction,
then every positive-definite forcing matrix `Q` has a positive-definite solution of
`P A + Aᵀ P = -Q`, unique among all matrix solutions.

Reference: Khalil, *Nonlinear Systems*. -/
@[blueprint "thm:exists-posDef-unique-lyapunov-solution-of-contraction"
  (title := "The Lyapunov equation from a contracting exponential")
  (statement := /-- Suppose $\|e^{Am}\| < 1$ for some integer $m > 0$.  Then for every
    positive definite $Q$ there is a positive definite $P$ with
    $PA + A^{\mathsf T}P = -Q$ (\cref{def:continuousLyapunovEquation}), and $P$ is the unique
    matrix solution.

    Reference: Khalil, \emph{Nonlinear Systems}.
  -/)
  (proof := /-- Write $L(P) = PA + A^{\mathsf T}P$ for the Lyapunov operator,
    $C = e^{Am}$, and $T(W) = C^{\mathsf T}WC$ for the congruence (Stein) operator.

    \emph{One block.}  Let $R = \int_{0}^{m} e^{tA^{\mathsf T}}Qe^{tA}\,\mathrm{d}t$.
    Differentiating the integrand two ways and equating the derivatives by uniqueness gives
    the key identity $L(R) = T(Q) - Q$.  $R$ is positive definite because the integrand is,
    pointwise, and positive definiteness survives the integral.

    \emph{Summing the blocks.}  $\|C\| < 1$ makes $\|T\| < 1$, so $\sum_{k} T^{k}R$ converges;
    call it $P$.  It is positive definite, being a convergent sum of positive definite terms.
    Since $A$ and $C$ commute, $L$ commutes with $T$, so
    $L(T^{k}R) = T^{k+1}Q - T^{k}Q$ and the series for $L(P)$ telescopes to $-Q$.

    \emph{Uniqueness.}  A contraction has only the trivial fixed point, so $L$ is injective;
    two solutions with the same forcing therefore coincide.

    The contraction is taken in the Frobenius norm, the only place in the construction where
    $\|C^{\mathsf T}\| = \|C\|$ is needed. -/)]
theorem exists_posDef_unique_solution_continuous_lyapunov_of_exp_nat_norm_lt_one
    (A Q : Matrix X X ℝ) (hQ : Q.PosDef)
    (hcontract : ∃ m : ℕ, 0 < m ∧ ‖NormedSpace.exp ((m : ℝ) • A)‖ < 1) :
    ∃ P : Matrix X X ℝ,
      P.PosDef ∧ ContinuousLyapunovEquation A P Q ∧
        ∀ S : Matrix X X ℝ,
          ContinuousLyapunovEquation A S Q → S = P := by
  obtain ⟨m, hm, hC⟩ := hcontract
  let C := NormedSpace.exp ((m : ℝ) • A)
  let R := finiteLyapunovIntegral A Q m
  let T := conjugationOperator C
  let P := ∑' k : ℕ, (T ^ k) R
  have hinjective : Function.Injective (lyapunovOperator A) :=
    lyapunovOperator_injective_of_exp_norm_lt_one A m hC
  have hsummable : Summable (fun k : ℕ ↦ (T ^ k) R) := by
    exact summable_conjugationOperator_pow_apply C R hC
  have hPpos : P.PosDef := by
    exact tsum_conjugationOperator_pow_apply_posDef C R
      (Matrix.isUnit_exp ((m : ℝ) • A)) hC (finiteLyapunovIntegral_posDef A Q m hQ hm)
  have hAC : Commute A C := by
    exact ((Commute.refl A).smul_right (m : ℝ)).exp_right
  have hRoperator : lyapunovOperator A R = T Q - Q := by
    change R * A + Aᵀ * R = Cᵀ * Q * C - Q
    exact finiteLyapunovIntegral_lyapunovOperator A Q m
  have htermOperator (k : ℕ) :
      lyapunovOperator A ((T ^ k) R) = (T ^ (k + 1)) Q - (T ^ k) Q := by
    rw [lyapunovOperator_conjugationOperator_pow A C R hAC k, hRoperator, map_sub]
    congr 1
  have hQsummable : Summable (fun k : ℕ ↦ (T ^ k) Q) := by
    exact summable_conjugationOperator_pow_apply C Q hC
  have hQshiftSummable : Summable (fun k : ℕ ↦ (T ^ (k + 1)) Q) := by
    exact (summable_nat_add_iff (f := fun k : ℕ ↦ (T ^ k) Q) 1).mpr hQsummable
  have htelescope :
      HasSum (fun k : ℕ ↦ (T ^ (k + 1)) Q - (T ^ k) Q) (-Q) := by
    have hsum := hQshiftSummable.hasSum.sub hQsummable.hasSum
    have hsplit := hQsummable.tsum_eq_zero_add
    have hlimit :
        (∑' k : ℕ, (T ^ (k + 1)) Q) - (∑' k : ℕ, (T ^ k) Q) = -Q := by
      rw [hsplit]
      simp
    rw [hlimit] at hsum
    exact hsum
  have hPoperator : lyapunovOperator A P = -Q := by
    let L : Matrix X X ℝ →L[ℝ] Matrix X X ℝ :=
      LinearMap.toContinuousLinearMap (lyapunovOperator A)
    have hmap := L.map_tsum hsummable
    calc
      lyapunovOperator A P = L P := rfl
      _ = ∑' k : ℕ, L ((T ^ k) R) := by simpa only [P] using hmap
      _ = ∑' k : ℕ, ((T ^ (k + 1)) Q - (T ^ k) Q) := by
        apply tsum_congr
        intro k
        exact htermOperator k
      _ = -Q := htelescope.tsum_eq
  refine ⟨P, hPpos, hPoperator, ?_⟩
  intro S hSsolve
  apply hinjective
  change S * A + Aᵀ * S = P * A + Aᵀ * P
  rw [show S * A + Aᵀ * S = -Q from hSsolve]
  exact hPoperator.symm

-- `DecidableEq X` is used by the proof (the matrix exponential needs the ring structure) but
-- not by the statement, which mentions only `PosDef` and the Lyapunov equation.
set_option linter.unusedDecidableInType false in
/-- A Hurwitz matrix admits a positive-definite solution of the continuous-time Lyapunov
equation for every positive-definite forcing matrix, and that solution is unique among all
matrix solutions.

Reference: Khalil, *Nonlinear Systems*. -/
@[blueprint "thm:hurwitz-lyapunov-equation"
  (title := "Lyapunov equation for a Hurwitz matrix")
  (statement := /-- If a real matrix $A$ is Hurwitz, then for every positive-definite
    $Q$ there is a positive-definite matrix $P$ satisfying
    $PA+A^{\mathsf T}P=-Q$, and this $P$ is the unique matrix solution.

omit [DecidableEq X] in
    Reference: Khalil, \emph{Nonlinear Systems}.
  -/)
  (proof := /-- A contracting integer-time matrix exponential is obtained from
    the Hurwitz spectrum.  Integrating over one time block and summing the
    resulting discrete Lyapunov series constructs $P$; contraction proves
    convergence and uniqueness. -/)]
theorem IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov
    {A : Matrix X X ℝ} (hA : IsHurwitz A)
    (Q : Matrix X X ℝ) (hQ : Q.PosDef) :
    ∃ P : Matrix X X ℝ,
      P.PosDef ∧ ContinuousLyapunovEquation A P Q ∧
        ∀ S : Matrix X X ℝ,
          ContinuousLyapunovEquation A S Q → S = P :=
  by
  refine exists_posDef_unique_solution_continuous_lyapunov_of_exp_nat_norm_lt_one A Q hQ ?_
  rcases isEmpty_or_nonempty X with _ | _
  · exact ⟨1, one_pos, by
      rw [Subsingleton.elim (NormedSpace.exp (((1 : ℕ) : ℝ) • A)) 0]; simp⟩
  · obtain ⟨m, hm0, hm⟩ := exists_pow_norm_lt_one_of_spectralRadius_lt_one
      (NormedSpace.exp A.complexify)
      (MatrixAlgebra.spectralRadius_exp_complexify_lt_one A hA)
    refine ⟨m, hm0, ?_⟩
    calc ‖NormedSpace.exp ((m : ℝ) • A)‖
        = ‖(NormedSpace.exp ((m : ℝ) • A)).complexify‖ :=
          (Matrix.frobenius_norm_complexify _).symm
      _ = ‖NormedSpace.exp A.complexify ^ m‖ := by
          rw [MatrixAlgebra.complexification_exp, ← Matrix.exp_nsmul]
          congr 2
          ext i j
          simp
      _ < 1 := hm

/-! ## The Lyapunov equation

Hespanha's Theorem 8.2 relates `IsHurwitz` to the solvability of `PA + AᵀP = -Q`. This is the
direction a Lyapunov certificate is *used* in: exhibiting one `P` proves stability.
-/

section LyapunovEquation

variable {M P Q : Matrix X X ℝ}

omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.2, (4) ⟹ (3).**
A positive-definite solution of the Lyapunov equation with positive-definite forcing certifies
that `M` is Hurwitz.

Pairing the equation against a complex eigenvector `Mv = μv` gives
`2 Re(μ) · v*Pv = -v*Qv`, and both quadratic forms are strictly positive, so `Re μ < 0`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.2. -/
@[blueprint "thm:isHurwitz-of-continuousLyapunovEquation"
  (title := "A Lyapunov certificate proves the spectrum lies in the open left half-plane")
  (statement := /-- If $P$ and $Q$ are positive definite and $PM + M^{\mathsf T}P = -Q$, then
    every eigenvalue of $M$ has strictly negative real part.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.2.
  -/)
  (proof := /-- Complexify the equation and pair it against an eigenvector $v$ of $M$ with
    eigenvalue $\mu$.  The two terms contribute $\mu\,v^{*}Pv$ and
    $\bar\mu\,v^{*}Pv$, so the left-hand side is $2\operatorname{Re}(\mu)\,v^{*}Pv$ while the
    right-hand side is $-v^{*}Qv$.  Both $v^{*}Pv$ and $v^{*}Qv$ are strictly positive
    (\cref{lem:matrix-posDef-complexify}), so $\operatorname{Re}(\mu) < 0$. -/)]
theorem isHurwitz_of_continuousLyapunovEquation
    (hP : P.PosDef) (hQ : Q.PosDef) (h : ContinuousLyapunovEquation M P Q) :
    IsHurwitz M := by
  intro μ v hv hMv
  -- The equation, complexified.
  have hc : P.complexify * M.complexify + M.complexifyᵀ * P.complexify = -Q.complexify := by
    simpa [ContinuousLyapunovEquation] using congrArg Matrix.complexify h
  -- Pair it against `v`. The first term contributes `μ`, the second `conj μ`.
  have hpair : (μ + (starRingEnd ℂ) μ) * (star v ⬝ᵥ (P.complexify *ᵥ v))
      = -(star v ⬝ᵥ (Q.complexify *ᵥ v)) := by
    have hL : star v ⬝ᵥ ((P.complexify * M.complexify) *ᵥ v)
        = μ * (star v ⬝ᵥ (P.complexify *ᵥ v)) := by
      rw [← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    have hR : star v ⬝ᵥ ((M.complexifyᵀ * P.complexify) *ᵥ v)
        = (starRingEnd ℂ) μ * (star v ⬝ᵥ (P.complexify *ᵥ v)) := by
      rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose,
        Matrix.transpose_transpose, Matrix.complexify_mulVec_star, hMv]
      simp [smul_eq_mul]
    have := congrArg (fun N : Matrix X X ℂ => star v ⬝ᵥ (N *ᵥ v)) hc
    simpa [Matrix.add_mulVec, dotProduct_add, hL, hR, Matrix.neg_mulVec, add_mul] using this
  -- Both quadratic forms are strictly positive, so `Re μ < 0`.
  obtain ⟨hp, hp'⟩ := Complex.lt_def.mp (hP.complexify.dotProduct_mulVec_pos hv)
  obtain ⟨hq, _⟩ := Complex.lt_def.mp (hQ.complexify.dotProduct_mulVec_pos hv)
  have hre := congrArg Complex.re hpair
  rw [Complex.add_conj] at hre
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
    zero_mul, sub_zero, ← hp'] at hre
  simp only [Complex.zero_re] at hp hq
  nlinarith

omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.2, (5) ⟹ (3).**
The Lyapunov matrix *inequality* `PM + MᵀP ≺ 0` certifies the same thing as the equation:
take the forcing to be minus the residual.

Stated through positive definiteness of `-(PM + MᵀP)` rather than through a matrix order
relation, so that it needs no Loewner order on matrices. -/
@[blueprint "thm:isHurwitz-of-posDef-neg-lyapunovResidual"
  (title := "The Lyapunov inequality certifies the Hurwitz condition")
  (statement := /-- If $P$ is positive definite and $-(PM + M^{\mathsf T}P)$ is positive
    definite, then $M$ is Hurwitz (\cref{def:stability-isHurwitz}).

    This is Hespanha's Theorem 8.2, $(5) \Rightarrow (3)$.  It is stated through positive
    definiteness of the negated residual rather than through a matrix order relation, so that
    it needs no Loewner order.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.2.
  -/)
  (proof := /-- Take the forcing to be minus the residual and apply
    \cref{thm:isHurwitz-of-continuousLyapunovEquation}. -/)]
theorem isHurwitz_of_posDef_neg_lyapunovResidual (hP : P.PosDef)
    (hneg : (-(P * M + Mᵀ * P)).PosDef) :
    IsHurwitz M :=
  isHurwitz_of_continuousLyapunovEquation hP hneg (by
    simp [ContinuousLyapunovEquation])

omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.2, (4) ⟹ (5).**
If *every* positive-definite forcing is achievable, then in particular the identity is, and
the resulting `P` satisfies the Lyapunov inequality.

The content is just the instantiation `Q := 1`; it is recorded separately because it is the
edge of Theorem 8.2's cycle that carries no mathematics. -/
@[blueprint "lem:exists-posDef-neg-lyapunovResidual-of-forall-posDef"
  (title := "From every forcing to one certificate")
  (latexEnv := "lemma")
  (statement := /-- If every positive definite $Q$ admits a positive definite solution of
    $PM + M^{\mathsf T}P = -Q$ (\cref{def:continuousLyapunovEquation}), then some positive
    definite $P$ makes $-(PM + M^{\mathsf T}P)$ positive definite.

    This is Hespanha's Theorem 8.2, $(4) \Rightarrow (5)$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.2.
  -/)
  (proof := /-- Instantiate the forcing at $Q = I$; the residual is then $-I$, whose negation
    is the identity.  The edge carries no mathematics beyond the instantiation. -/)]
theorem exists_posDef_neg_lyapunovResidual_of_forall_posDef
    (h : ∀ Q : Matrix X X ℝ, Q.PosDef →
      ∃ S : Matrix X X ℝ, S.PosDef ∧ ContinuousLyapunovEquation M S Q) :
    ∃ S : Matrix X X ℝ, S.PosDef ∧ (-(S * M + Mᵀ * S)).PosDef := by
  classical
  obtain ⟨S, hS, hEq⟩ := h 1 Matrix.PosDef.one
  refine ⟨S, hS, ?_⟩
  rw [show S * M + Mᵀ * S = -1 from hEq]
  simpa using Matrix.PosDef.one

/-! ### The equivalences -/

-- `DecidableEq X` is used by the proof (it instantiates the forcing at `1`) but not by the
-- statement.
set_option linter.unusedDecidableInType false in
/-- **Hespanha, Theorem 8.2, (3) ⟺ (4).**
`A` is Hurwitz exactly when every positive-definite forcing admits a positive-definite
solution of the Lyapunov equation, unique among all matrix solutions. -/
@[blueprint "thm:isHurwitz-iff-forall-posDef-exists-solution"
  (title := "Hurwitz is solvability of the Lyapunov equation for every forcing")
  (statement := /-- A real square matrix $A$ is Hurwitz (\cref{def:stability-isHurwitz}) if and
    only if for every positive definite $Q$ there is a positive definite $P$ with
    $PA + A^{\mathsf T}P = -Q$ (\cref{def:continuousLyapunovEquation}), unique among all
    matrix solutions.

    This is Hespanha's Theorem 8.2, $(3) \Leftrightarrow (4)$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.2.
  -/)
  (proof := /-- Forwards is \cref{thm:hurwitz-lyapunov-equation}.  Backwards, instantiate the
    forcing at $Q = I$ and apply
    \cref{thm:isHurwitz-of-continuousLyapunovEquation}. -/)]
theorem isHurwitz_iff_forall_posDef_exists_solution (A : Matrix X X ℝ) :
    IsHurwitz A ↔ ∀ R : Matrix X X ℝ, R.PosDef →
      ∃ S : Matrix X X ℝ, S.PosDef ∧ ContinuousLyapunovEquation A S R ∧
        ∀ T : Matrix X X ℝ, ContinuousLyapunovEquation A T R → T = S := by
  refine ⟨fun hA R hR => hA.exists_posDef_unique_solution_continuous_lyapunov R hR, fun h => ?_⟩
  obtain ⟨S, hS, hEq, -⟩ := h 1 Matrix.PosDef.one
  exact isHurwitz_of_continuousLyapunovEquation hS Matrix.PosDef.one hEq

-- As above: the forcing is instantiated at `1` inside the proof only.
set_option linter.unusedDecidableInType false in
/-- **Hespanha, Theorem 8.2, (3) ⟺ (5).**
`A` is Hurwitz exactly when some positive-definite `P` makes the Lyapunov residual negative
definite. This is the form a certificate is supplied in. -/
@[blueprint "thm:isHurwitz-iff-exists-posDef-lyapunovResidual"
  (title := "Hurwitz is the existence of one Lyapunov certificate")
  (statement := /-- A real square matrix $A$ is Hurwitz (\cref{def:stability-isHurwitz}) if and
    only if some positive definite $P$ makes $-(PA + A^{\mathsf T}P)$ positive definite.

    This is Hespanha's Theorem 8.2, $(3) \Leftrightarrow (5)$, and the form in which a
    Lyapunov certificate is actually supplied: one matrix, not a family.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.2.
  -/)
  (proof := /-- Forwards, \cref{thm:hurwitz-lyapunov-equation} produces a solution for each
    forcing and \cref{lem:exists-posDef-neg-lyapunovResidual-of-forall-posDef} extracts one
    certificate from them; backwards is
    \cref{thm:isHurwitz-of-posDef-neg-lyapunovResidual}. -/)]
theorem isHurwitz_iff_exists_posDef_lyapunovResidual (A : Matrix X X ℝ) :
    IsHurwitz A ↔ ∃ S : Matrix X X ℝ, S.PosDef ∧ (-(S * A + Aᵀ * S)).PosDef := by
  constructor
  · intro hA
    refine exists_posDef_neg_lyapunovResidual_of_forall_posDef fun R hR => ?_
    obtain ⟨S, hS, hEq, -⟩ := hA.exists_posDef_unique_solution_continuous_lyapunov R hR
    exact ⟨S, hS, hEq⟩
  · rintro ⟨S, hS, hneg⟩
    exact isHurwitz_of_posDef_neg_lyapunovResidual hS hneg

/-! ### The rate form

`PA + AᵀP ≼ -2c P` is the Lyapunov inequality carrying an explicit decay rate: along a
trajectory it gives `V̇ ≤ -2c V` for `V = xᵀPx`, hence `V(t) ≤ V(0) e^{-2ct}`. It is the shape
every contraction and guaranteed-decay-rate condition is written in.

It is stated through positive *semi*definiteness of `-(PA + AᵀP) - 2c P`, which is the
Loewner inequality `PA + AᵀP ≼ -2c P` without needing an order on matrices.
-/

omit [DecidableEq X] in
/-- **The rate form implies Hurwitz.**
A positive-definite `P` satisfying `PA + AᵀP ≼ -2c P` with `c > 0` certifies that `A` is
Hurwitz: the residual is then at least `2c P`, which is positive definite. -/
@[blueprint "thm:isHurwitz-of-posDef-lyapunovRate"
  (title := "The rate form certifies the Hurwitz condition")
  (statement := /-- If $P$ is positive definite, $c > 0$, and
    $PA + A^{\mathsf T}P \preceq -2cP$ — that is, $-(PA + A^{\mathsf T}P) - 2cP$ is positive
    semidefinite — then $A$ is Hurwitz (\cref{def:stability-isHurwitz}).

    Along a trajectory this inequality gives $\dot V \le -2cV$ for $V = x^{\mathsf T}Px$, so
    it certifies not merely stability but a decay rate. -/)
  (proof := /-- Split $-(PA + A^{\mathsf T}P)$ as
    $\bigl(-(PA + A^{\mathsf T}P) - 2cP\bigr) + 2cP$: positive semidefinite plus positive
    definite is positive definite, so
    \cref{thm:isHurwitz-of-posDef-neg-lyapunovResidual} applies. -/)]
theorem isHurwitz_of_posDef_lyapunovRate {A S : Matrix X X ℝ} {c : ℝ} (hc : 0 < c)
    (hS : S.PosDef) (hres : (-(S * A + Aᵀ * S) - (2 * c) • S).PosSemidef) :
    IsHurwitz A := by
  refine isHurwitz_of_posDef_neg_lyapunovResidual hS ?_
  have hsplit : -(S * A + Aᵀ * S)
      = (-(S * A + Aᵀ * S) - (2 * c) • S) + (2 * c) • S := (sub_add_cancel _ _).symm
  rw [hsplit]
  exact Matrix.PosDef.posSemidef_add hres (hS.smul (by positivity))

-- The proof shifts by `c • 1`, so it needs `DecidableEq X`; the statement does not.
set_option linter.unusedDecidableInType false in
/-- **Hurwitz implies the rate form.**
A Hurwitz matrix admits a positive-definite `P` and a rate `c > 0` with `PA + AᵀP ≼ -2c P`.

The trick is to solve the Lyapunov equation for the *shifted* matrix. A Hurwitz `A` has a
positive spectral margin `c` (`IsHurwitz.exists_pos_isHurwitzWithRate`), so `A + cI` is still
Hurwitz; solving `S(A + cI) + (A + cI)ᵀS = -1` and expanding gives
`SA + AᵀS = -1 - 2cS`, so the residual `-(SA + AᵀS) - 2cS` is exactly the identity.

No domination bound between two positive-definite matrices is needed — the residual is not
merely bounded below, it is `1`. -/
@[blueprint "thm:exists-posDef-lyapunovRate-of-isHurwitz"
  (title := "A Hurwitz matrix admits a rate certificate")
  (statement := /-- If $A$ is Hurwitz (\cref{def:stability-isHurwitz}) then there are a
    positive definite $P$ and a rate $c > 0$ with
    $PA + A^{\mathsf T}P \preceq -2cP$. -/)
  (proof := /-- Solve the Lyapunov equation for the \emph{shifted} matrix.  A Hurwitz $A$ has
    a positive spectral margin $c$ (\cref{thm:isHurwitz-exists-pos-rate}), so $A + cI$ is
    still Hurwitz (\cref{thm:isHurwitzWithRate-iff-spectral-shift}).  Solving
    $P(A + cI) + (A + cI)^{\mathsf T}P = -I$ (\cref{thm:hurwitz-lyapunov-equation}) and
    expanding gives $PA + A^{\mathsf T}P = -I - 2cP$, so the residual
    $-(PA + A^{\mathsf T}P) - 2cP$ is \emph{exactly} the identity.

    No domination bound between two positive definite matrices is needed: the residual is not
    merely bounded below, it is $I$. -/)]
theorem exists_posDef_lyapunovRate_of_isHurwitz {A : Matrix X X ℝ} (hA : IsHurwitz A) :
    ∃ (S : Matrix X X ℝ) (c : ℝ), 0 < c ∧ S.PosDef ∧
      (-(S * A + Aᵀ * S) - (2 * c) • S).PosSemidef := by
  obtain ⟨c, hc, hrate⟩ := hA.exists_pos_isHurwitzWithRate
  have hshift : IsHurwitz (A + c • (1 : Matrix X X ℝ)) :=
    (isHurwitzWithRate_iff_add_smul_one c A).1 hrate
  obtain ⟨S, hS, hEq, -⟩ :=
    hshift.exists_posDef_unique_solution_continuous_lyapunov 1 Matrix.PosDef.one
  refine ⟨S, c, hc, hS, ?_⟩
  -- Expanding the shifted equation leaves the identity as the residual.
  have hexp : -(S * A + Aᵀ * S) - (2 * c) • S = 1 := by
    have := hEq
    simp only [ContinuousLyapunovEquation, Matrix.add_mul, Matrix.mul_add, Matrix.transpose_add,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul] at this
    rw [show (2 * c) • S = c • S + c • S by module] at *
    linear_combination (norm := module) -this
  rw [hexp]
  exact Matrix.PosSemidef.one

-- `DecidableEq X` is used by the forward direction's proof, not by the statement.
set_option linter.unusedDecidableInType false in
/-- **Hespanha, Theorem 8.2, (3) ⟺ (6).**
`A` is Hurwitz exactly when some positive-definite `S` and some rate `c > 0` satisfy
`SA + AᵀS ≼ -2c S`.

This is the rate-carrying refinement of clause (5): it does not merely certify stability, it
exhibits a decay rate, since `V = xᵀSx` then obeys `V̇ ≤ -2c V`. -/
@[blueprint "thm:isHurwitz-iff-exists-posDef-lyapunovRate"
  (title := "Hurwitz is the existence of a rate certificate")
  (statement := /-- A real square matrix $A$ is Hurwitz (\cref{def:stability-isHurwitz}) if and
    only if there are a positive definite $P$ and a rate $c > 0$ with
    $PA + A^{\mathsf T}P \preceq -2cP$.

    This is clause 6 of \cref{thm:lyapunovStability-tfae}, which is not in Hespanha's list.  It
    is the rate-carrying refinement of
    \cref{thm:isHurwitz-iff-exists-posDef-lyapunovResidual}, and the shape every contraction
    and guaranteed-decay-rate condition is written in. -/)
  (proof := /-- \cref{thm:exists-posDef-lyapunovRate-of-isHurwitz} and
    \cref{thm:isHurwitz-of-posDef-lyapunovRate}. -/)]
theorem isHurwitz_iff_exists_posDef_lyapunovRate (A : Matrix X X ℝ) :
    IsHurwitz A ↔ ∃ (S : Matrix X X ℝ) (c : ℝ), 0 < c ∧ S.PosDef ∧
      (-(S * A + Aᵀ * S) - (2 * c) • S).PosSemidef := by
  refine ⟨exists_posDef_lyapunovRate_of_isHurwitz, ?_⟩
  rintro ⟨S, c, hc, hS, hres⟩
  exact isHurwitz_of_posDef_lyapunovRate hc hS hres

end LyapunovEquation

end General

section QuadraticForm

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A solution of the Lyapunov equation makes the derivative of the `P`-quadratic form
along the linear vector field equal to minus the `Q`-quadratic form.

Reference: the continuous-time Lyapunov-equation identity. -/
@[blueprint "thm:fderiv-centeredQuadraticForm-linear-general"
  (title := "A Lyapunov solution makes its quadratic form decrease")
  (statement := /-- Let $P$ solve $PA + A^{\mathsf T}P = -Q$
    (\cref{def:continuousLyapunovEquation}).  Then the derivative of the centered quadratic
    form $x \mapsto (x - x_{\mathrm{eq}})^{\mathsf T}P(x - x_{\mathrm{eq}})$
    (\cref{def:quadraticForm}) along the linear vector field $y \mapsto Ay$ is
    \[
      -\,(x - x_{\mathrm{eq}})^{\mathsf T}Q\,(x - x_{\mathrm{eq}}).
    \]

    This is what makes a Lyapunov solution a Lyapunov \emph{function}: the forcing $Q$ is
    exactly the dissipation rate. -/)
  (proof := /-- The derivative of the quadratic form in the direction $Ay$ is
    $\langle y, Py'\rangle + \langle y', Py\rangle$ with $y' = Ay$, which is the form
    represented by $PA + A^{\mathsf T}P$.  Transporting the equation through
    $\mathtt{toEuclideanCLM}$ — under which transpose becomes adjoint — rewrites that as
    $-Q$. -/)]
theorem fderiv_centeredQuadraticForm_linear_general
    {A P Q : Matrix (Fin n) (Fin n) ℝ}
    (hEq : ContinuousLyapunovEquation A P Q)
    (x_eq x : ℝⁿ) :
    fderiv ℝ (centeredQuadraticForm P x_eq) x
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (x - x_eq)) =
      -quadraticForm Q (x - x_eq) := by
  rw [fderiv_centeredQuadraticForm_apply]
  let y := x - x_eq
  let a := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A
  let p := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P
  let q := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q
  have htranspose :
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Aᵀ = star a := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial A]
    exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).map_star' A
  have hclm : p * a + star a * p = -q := by
    have hEq' : P * A + Aᵀ * P = -Q := hEq
    have h := congrArg (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) hEq'
    have h' :
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P *
              Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A +
            Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Aᵀ *
              Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P =
            -Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q := by
      simpa using h
    change p * a + Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Aᵀ * p = -q at h'
    rwa [htranspose] at h'
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [← inner_add_right]
  change inner ℝ y ((p * a + star a * p) y) = -quadraticForm Q y
  rw [hclm]
  simp [quadraticForm, q]

/-- For identity forcing, the quadratic derivative along the linear vector field is
`-‖x - x_eq‖²`.

Reference: the continuous-time Lyapunov-equation identity. -/
@[blueprint "lem:fderiv-centeredQuadraticForm-linear"
  (title := "Identity forcing gives decrease at the squared norm")
  (latexEnv := "lemma")
  (statement := /-- For $P$ solving $PA + A^{\mathsf T}P = -I$
    (\cref{def:continuousLyapunovEquation}), the derivative of the centered quadratic form
    (\cref{def:quadraticForm}) along $y \mapsto Ay$ is
    $-\|x - x_{\mathrm{eq}}\|^{2}$. -/)
  (proof := /-- \cref{thm:fderiv-centeredQuadraticForm-linear-general} at $Q = I$, where the
    quadratic form is the squared Euclidean norm. -/)]
theorem fderiv_centeredQuadraticForm_linear
    {A P : Matrix (Fin n) (Fin n) ℝ}
    (hEq : ContinuousLyapunovEquation A P 1)
    (x_eq x : ℝⁿ) :
    fderiv ℝ (centeredQuadraticForm P x_eq) x
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (x - x_eq)) =
      -‖x - x_eq‖ ^ 2 := by
  rw [fderiv_centeredQuadraticForm_linear_general hEq]
  simp [quadraticForm]

end QuadraticForm

end LinearSystems

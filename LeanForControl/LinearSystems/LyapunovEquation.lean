import LeanForControl.LinearSystems.DefsLyapunov
import LeanForControl.LinearSystems.ExponentialStability
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Architect

/-!
# The continuous-time Lyapunov equation

This file constructs the positive-definite solution of the continuous-time Lyapunov equation
from a strict contraction of one matrix-exponential time step. The proof uses an integral on
one finite time block and the resulting convergent discrete Lyapunov series.

Reference: Khalil, *Nonlinear Systems*.
-/

namespace LinearSystems

open Filter Matrix MeasureTheory Set
open scoped Matrix.Norms.Frobenius Topology BigOperators

variable {n : ℕ}

private noncomputable def lyapunovKernel
    (A Q : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  NormedSpace.exp (t • Aᵀ) * Q * NormedSpace.exp (t • A)

private noncomputable def finiteLyapunovIntegral
    (A Q : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∫ t in (0 : ℝ)..(m : ℝ), lyapunovKernel A Q t

private def lyapunovOperator (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun P := P * A + Aᵀ * P
  map_add' P R := by simp only [add_mul, mul_add, add_assoc]; ac_rfl
  map_smul' a P := by simp only [RingHom.id_apply, smul_add, smul_mul_assoc, mul_smul_comm]

private noncomputable def conjugationOperator (C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ContinuousLinearMap.mulLeftRight ℝ _ Cᵀ C

private lemma hasDerivAt_lyapunovKernel_operator
    (A X : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (lyapunovKernel A X)
      (lyapunovKernel A (X * A + Aᵀ * X) t) t := by
  have hleft := (hasDerivAt_exp_smul_const Aᵀ t).mul_const X
  have hright := hasDerivAt_exp_smul_const' A t
  simpa only [lyapunovKernel, mul_add, add_mul, mul_assoc, add_comm] using hleft.mul hright

private lemma hasDerivAt_lyapunovKernel
    (A Q : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (lyapunovKernel A Q)
      (Aᵀ * lyapunovKernel A Q t + lyapunovKernel A Q t * A) t := by
  have hleft := (hasDerivAt_exp_smul_const' Aᵀ t).mul_const Q
  have hright := hasDerivAt_exp_smul_const A t
  simpa only [lyapunovKernel, mul_assoc] using hleft.mul hright

private lemma continuous_lyapunovKernel
    (A Q : Matrix (Fin n) (Fin n) ℝ) : Continuous (lyapunovKernel A Q) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_lyapunovKernel_operator A Q t).continuousAt

private lemma finiteLyapunovIntegral_operator
    (A X : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    finiteLyapunovIntegral A (X * A + Aᵀ * X) m =
      (NormedSpace.exp ((m : ℝ) • A))ᵀ * X * NormedSpace.exp ((m : ℝ) • A) - X := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_lyapunovKernel_operator A X t)
    ((continuous_lyapunovKernel A (X * A + Aᵀ * X)).intervalIntegrable 0 (m : ℝ))
  rw [finiteLyapunovIntegral]
  rw [h]
  simp only [lyapunovKernel, zero_smul, NormedSpace.exp_zero, one_mul, mul_one]
  congr 2
  rw [← Matrix.exp_transpose]
  congr 2

private lemma finiteLyapunovIntegral_lyapunovOperator
    (A Q : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    finiteLyapunovIntegral A Q m * A + Aᵀ * finiteLyapunovIntegral A Q m =
      (NormedSpace.exp ((m : ℝ) • A))ᵀ * Q * NormedSpace.exp ((m : ℝ) • A) - Q := by
  let L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
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

private lemma finiteLyapunovIntegral_neg
    (A Q : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    finiteLyapunovIntegral A (-Q) m = -finiteLyapunovIntegral A Q m := by
  simp [finiteLyapunovIntegral, lyapunovKernel]

private lemma conjugationOperator_norm_lt_one
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : ‖C‖ < 1) :
    ‖conjugationOperator C‖ < 1 := by
  calc
    ‖conjugationOperator C‖ ≤ ‖Cᵀ‖ * ‖C‖ :=
      ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ _ Cᵀ C
    _ = ‖C‖ * ‖C‖ := by rw [Matrix.frobenius_norm_transpose]
    _ < 1 := by nlinarith [norm_nonneg C]

private lemma tendsto_conjugationOperator_pow_apply_zero
    (C X : Matrix (Fin n) (Fin n) ℝ) (hC : ‖C‖ < 1) :
    Tendsto (fun k : ℕ ↦ ((conjugationOperator C) ^ k) X) atTop (nhds 0) := by
  let T : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    conjugationOperator C
  change Tendsto (fun k : ℕ ↦ (T ^ k) X) atTop (nhds 0)
  let ev :
      (Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ) →L[ℝ]
        Matrix (Fin n) (Fin n) ℝ :=
    (ContinuousLinearMap.apply ℝ (Matrix (Fin n) (Fin n) ℝ)) X
  have hpows := tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (show ‖T‖ < 1 from conjugationOperator_norm_lt_one C hC)
  have happ := ev.continuous.continuousAt.tendsto.comp hpows
  simpa [ev, Function.comp_def] using happ

private lemma eq_zero_of_conjugationOperator_fixed
    (C X : Matrix (Fin n) (Fin n) ℝ) (hC : ‖C‖ < 1)
    (hfixed : conjugationOperator C X = X) : X = 0 := by
  have hpow (k : ℕ) : ((conjugationOperator C) ^ k) X = X := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ']
        simp only [ContinuousLinearMap.mul_apply, ih, hfixed]
  have hzero := tendsto_conjugationOperator_pow_apply_zero C X hC
  have hconst : Tendsto (fun _ : ℕ ↦ X) atTop (nhds 0) := by
    exact hzero.congr' (Eventually.of_forall fun k ↦ hpow k)
  exact tendsto_nhds_unique tendsto_const_nhds hconst

private lemma lyapunovOperator_injective_of_exp_norm_lt_one
    (A : Matrix (Fin n) (Fin n) ℝ) (m : ℕ)
    (hC : ‖NormedSpace.exp ((m : ℝ) • A)‖ < 1) :
    Function.Injective (lyapunovOperator A) := by
  let C := NormedSpace.exp ((m : ℝ) • A)
  intro X Y hXY
  let D := X - Y
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
    (A Q : Matrix (Fin n) (Fin n) ℝ) (m : ℕ)
    (hQ : Q.PosDef) (hm : 0 < m) :
    (finiteLyapunovIntegral A Q m).PosDef := by
  have hint : IntervalIntegrable (lyapunovKernel A Q) volume 0 (m : ℝ) :=
    (continuous_lyapunovKernel A Q).intervalIntegrable 0 (m : ℝ)
  have hentry (i j : Fin n) :
      finiteLyapunovIntegral A Q m i j =
        ∫ t in (0 : ℝ)..(m : ℝ), lyapunovKernel A Q t i j := by
    let row : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ) :=
      ContinuousLinearMap.proj i
    let entry : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj j).comp row
    have h := entry.intervalIntegral_comp_comm hint
    simpa [entry, row, Function.comp_def, finiteLyapunovIntegral] using h.symm
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
    let quadratic : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ := {
      toFun P := dotProduct (star x) (P *ᵥ x)
      map_add' P R := by simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' a P := by simp [Matrix.smul_mulVec, dotProduct_smul] }
    let quadraticCLM : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap quadratic
    have hquadraticIntegral :
        dotProduct (star x) (finiteLyapunovIntegral A Q m *ᵥ x) =
          ∫ t in (0 : ℝ)..(m : ℝ),
            dotProduct (star x) (lyapunovKernel A Q t *ᵥ x) := by
      have h := quadraticCLM.intervalIntegral_comp_comm hint
      simpa [quadraticCLM, quadratic, Function.comp_def, finiteLyapunovIntegral] using h.symm
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
    · change ContinuousOn (fun t ↦ quadraticCLM (lyapunovKernel A Q t)) (Icc 0 (m : ℝ))
      exact (quadraticCLM.continuous.comp (continuous_lyapunovKernel A Q)).continuousOn
    · intro t _
      exact (hquadraticPos t).le
    · exact ⟨0, ⟨le_rfl, Nat.cast_nonneg m⟩, hquadraticPos 0⟩

private lemma posDef_conjugationOperator
    (C X : Matrix (Fin n) (Fin n) ℝ) (hC : IsUnit C) (hX : X.PosDef) :
    (conjugationOperator C X).PosDef := by
  have hconj : conjugationOperator C X = Cᴴ * X * C := by
    ext i j
    simp [conjugationOperator]
  rw [hconj]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact Matrix.isHermitian_conjTranspose_mul_mul C hX.isHermitian
  · intro x hx
    have hCx : C *ᵥ x ≠ 0 := by
      intro hzero
      apply hx
      apply Matrix.mulVec_injective_of_isUnit hC
      simpa using hzero
    simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using
      hX.dotProduct_mulVec_pos hCx

private lemma summable_conjugationOperator_pow_apply
    (C X : Matrix (Fin n) (Fin n) ℝ) (hC : ‖C‖ < 1) :
    Summable (fun k : ℕ ↦ ((conjugationOperator C) ^ k) X) := by
  let ev :
      (Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ) →L[ℝ]
        Matrix (Fin n) (Fin n) ℝ :=
    (ContinuousLinearMap.apply ℝ (Matrix (Fin n) (Fin n) ℝ)) X
  have hs := (summable_geometric_of_norm_lt_one
    (conjugationOperator_norm_lt_one C hC)).map ev ev.continuous
  simpa [ev, Function.comp_def] using hs

private lemma lyapunovOperator_conjugationOperator
    (A C X : Matrix (Fin n) (Fin n) ℝ) (hAC : Commute A C) :
    lyapunovOperator A (conjugationOperator C X) =
      conjugationOperator C (lyapunovOperator A X) := by
  have hAtCt : Aᵀ * Cᵀ = Cᵀ * Aᵀ := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hAC.eq.symm
  change (Cᵀ * X * C) * A + Aᵀ * (Cᵀ * X * C) =
    Cᵀ * (X * A + Aᵀ * X) * C
  calc
    (Cᵀ * X * C) * A + Aᵀ * (Cᵀ * X * C) =
        Cᵀ * X * (C * A) + (Aᵀ * Cᵀ) * X * C := by
      simp only [mul_assoc]
    _ = Cᵀ * X * (A * C) + (Cᵀ * Aᵀ) * X * C := by
      rw [hAC.eq.symm, hAtCt]
    _ = Cᵀ * (X * A + Aᵀ * X) * C := by
      simp only [mul_add, add_mul, mul_assoc]

private lemma lyapunovOperator_conjugationOperator_pow
    (A C X : Matrix (Fin n) (Fin n) ℝ) (hAC : Commute A C) (k : ℕ) :
    lyapunovOperator A (((conjugationOperator C) ^ k) X) =
      ((conjugationOperator C) ^ k) (lyapunovOperator A X) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ']
      simp only [ContinuousLinearMap.mul_apply]
      rw [lyapunovOperator_conjugationOperator A C _ hAC, ih]

private lemma tsum_conjugationOperator_pow_apply_posDef
    (C R : Matrix (Fin n) (Fin n) ℝ) (hCunit : IsUnit C)
    (hCnorm : ‖C‖ < 1) (hR : R.PosDef) :
    (∑' k : ℕ, ((conjugationOperator C) ^ k) R).PosDef := by
  let term : ℕ → Matrix (Fin n) (Fin n) ℝ :=
    fun k ↦ ((conjugationOperator C) ^ k) R
  have hs : Summable term := summable_conjugationOperator_pow_apply C R hCnorm
  have htermPos (k : ℕ) : (term k).PosDef := by
    induction k with
    | zero => simpa [term] using hR
    | succ k ih =>
        rw [show term (k + 1) = conjugationOperator C (term k) by
          simp only [term, pow_succ', ContinuousLinearMap.mul_apply]]
        exact posDef_conjugationOperator C (term k) hCunit ih
  have hentry (i j : Fin n) :
      (∑' k : ℕ, term k) i j = ∑' k : ℕ, term k i j := by
    let row : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ) :=
      ContinuousLinearMap.proj i
    let entry : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj j).comp row
    have h := entry.map_tsum hs
    simpa [entry, row, Function.comp_def] using h
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
    let quadratic : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ := {
      toFun P := dotProduct (star x) (P *ᵥ x)
      map_add' P S := by simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' a P := by simp [Matrix.smul_mulVec, dotProduct_smul] }
    let quadraticCLM : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap quadratic
    have hqsum :
        dotProduct (star x) ((∑' k : ℕ, term k) *ᵥ x) =
          ∑' k : ℕ, dotProduct (star x) (term k *ᵥ x) := by
      have h := quadraticCLM.map_tsum hs
      simpa [quadraticCLM, quadratic, Function.comp_def] using h
    have hqsummable : Summable (fun k ↦ dotProduct (star x) (term k *ᵥ x)) := by
      simpa [quadraticCLM, quadratic, Function.comp_def] using
        hs.map quadraticCLM quadraticCLM.continuous
    rw [hqsum, hqsummable.tsum_eq_zero_add]
    have hhead : 0 < dotProduct (star x) (term 0 *ᵥ x) :=
      (htermPos 0).dotProduct_mulVec_pos hx
    exact add_pos_of_pos_of_nonneg hhead (tsum_nonneg fun k ↦
      ((htermPos (k + 1)).dotProduct_mulVec_pos hx).le)

/-- If one positive integer time step of the matrix exponential is a strict contraction,
then every positive-definite forcing matrix `Q` has a positive-definite solution of
`P A + Aᵀ P = -Q`, unique among all matrix solutions.

Reference: Khalil, *Nonlinear Systems*. -/
theorem exists_posDef_unique_solution_continuous_lyapunov_of_exp_nat_norm_lt_one
    (A Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef)
    (hcontract : ∃ m : ℕ, 0 < m ∧ ‖NormedSpace.exp ((m : ℝ) • A)‖ < 1) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ,
      P.PosDef ∧ SolvesContinuousLyapunovEquation A P Q ∧
        ∀ S : Matrix (Fin n) (Fin n) ℝ,
          SolvesContinuousLyapunovEquation A S Q → S = P := by
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
    let L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
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

/-- A Hurwitz matrix admits a positive-definite solution of the continuous-time Lyapunov
equation for every positive-definite forcing matrix, and that solution is unique among all
matrix solutions.

Reference: Khalil, *Nonlinear Systems*. -/
@[blueprint "thm:hurwitz-lyapunov-equation"
  (statement := /-- If a real matrix $A$ is Hurwitz, then for every positive-definite
    $Q$ there is a positive-definite matrix $P$ satisfying
    $PA+A^{\mathsf T}P=-Q$, and this $P$ is the unique matrix solution. -/)
  (proof := /-- A contracting integer-time matrix exponential is obtained from
    the Hurwitz spectrum.  Integrating over one time block and summing the
    resulting discrete Lyapunov series constructs $P$; contraction proves
    convergence and uniqueness. -/)]
theorem IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ,
      P.PosDef ∧ SolvesContinuousLyapunovEquation A P Q ∧
        ∀ S : Matrix (Fin n) (Fin n) ℝ,
          SolvesContinuousLyapunovEquation A S Q → S = P :=
  exists_posDef_unique_solution_continuous_lyapunov_of_exp_nat_norm_lt_one
    A Q hQ hA.exists_norm_exp_nat_smul_lt_one

end LinearSystems

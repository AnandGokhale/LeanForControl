import LeanForControl.LinearSystems.Solutions.DefsCtsLTV
import LeanForControl.LinearSystems.Solutions.CtsLTV
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Architect

/-!
# Continuous-time LTI solutions: the matrix exponential

Theorems specializing the LTV Peano-Baker series (`CtsLTV.lean`) to a *constant* state matrix
`A`, building up to Theorem 6.1: for LTI systems `ẋ = Ax`, the state transition matrix collapses
to the classical closed form `Φ(t,t₀) = e^{A(t-t₀)}` (6.2). This is what lets every LTV property
already proved in `CtsLTV.lean` (existence, uniqueness, semigroup, invertibility, variation of
constants) be reused directly for LTI by specialization, rather than re-derived from scratch.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6.
-/

namespace LinearSystems

open scoped Matrix.Norms.Operator Nat
open Matrix MeasureTheory intervalIntegral

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)

/-- **(6.1), term-level.** For a *constant* state matrix `A`, the `k`-th Peano-Baker term
collapses to the closed form `((t-t₀)^k / k!) • A^k`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, equation (6.1). -/
theorem peanoBakerTerm_const (k : ℕ) (t t₀ : ℝ) :
    peanoBakerTerm (fun _ => A) k t t₀ = ((t - t₀) ^ k / (k)! : ℝ) • A ^ k := by
  induction k generalizing t with
  | zero =>
    change (1 : Matrix (Fin n) (Fin n) ℝ) = _
    norm_num
  | succ k ih =>
    change (∫ s in t₀..t, A * peanoBakerTerm (fun _ => A) k s t₀) = _
    simp_rw [ih, Algebra.mul_smul_comm, ← pow_succ']
    rw [intervalIntegral.integral_smul_const]
    congr 1
    have hpow_integral : (∫ s in t₀..t, (s - t₀) ^ k) = (t - t₀) ^ (k + 1) / (k + 1) := by
      rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ k) t₀]
      simp [integral_pow]
    have hk_fac_ne : ((k)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    simp_rw [div_eq_inv_mul, intervalIntegral.integral_const_mul, hpow_integral,
      Nat.factorial_succ]
    push_cast
    field_simp

/-- **(6.1).** For a *constant* state matrix `A`, the continuous-time state transition matrix
is given by the power series `Φ(t,t₀) = Σ_{k=0}^∞ ((t-t₀)^k / k!) A^k` — summing
`peanoBakerTerm_const` termwise.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, equation (6.1). -/
theorem stateTransitionMatrix_const_eq_tsum (t t₀ : ℝ) :
    stateTransitionMatrix (fun _ => A) t t₀ = ∑' k, ((t - t₀) ^ k / (k)! : ℝ) • A ^ k := by
  unfold stateTransitionMatrix
  exact tsum_congr fun k => peanoBakerTerm_const A k t t₀

/-- **(6.2).** For a *constant* state matrix `A`, the continuous-time state transition matrix
collapses to the matrix exponential `Φ(t,t₀) = e^{A(t-t₀)}`. This is what lets every LTV
property already proved for `stateTransitionMatrix` (existence, uniqueness, semigroup,
invertibility, variation of constants) be reused directly for LTI by specialization.

Proof: sum `peanoBakerTerm_const` termwise and match against Mathlib's own series
characterization of `exp` (`NormedSpace.exp_eq_tsum`).

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, equation (6.2). -/
theorem stateTransitionMatrix_const (t t₀ : ℝ) :
    stateTransitionMatrix (fun _ => A) t t₀ = NormedSpace.exp ((t - t₀) • A) := by
  unfold stateTransitionMatrix
  simp only [NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
  refine tsum_congr fun k => ?_
  rw [peanoBakerTerm_const, smul_pow, smul_smul, div_eq_inv_mul]

/-- **P6.1, uniqueness half.** `e^{A(t-t₀)} *ᵥ x₀` is the *unique* solution of `ẋ = Ax`,
`x(t₀) = x₀`, for a *constant* state matrix `A` — a direct corollary of the LTV uniqueness
theorem `stateTransitionMatrix_mulVec_unique`, specialized at `A := fun _ => A` and rewritten
via the bridge lemma `stateTransitionMatrix_const`. No new ODE-theoretic content: uniqueness
for LTI systems is just uniqueness for LTV systems at a constant state matrix.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, Property P6.1. -/
theorem exp_mulVec_unique {t₀ t₁ : ℝ} (x₀ : Fin n → ℝ)
    {z : ℝ → Fin n → ℝ} (hz : IsIntegralSolution t₀ t₁ z x₀ (fun _ v => A *ᵥ v))
    (hz_cont : ContinuousOn z (Set.uIcc t₀ t₁)) :
    ∀ t ∈ Set.uIcc t₀ t₁, z t = NormedSpace.exp ((t - t₀) • A) *ᵥ x₀ := by
  intro t ht
  have := stateTransitionMatrix_mulVec_unique (A := fun _ => A) continuous_const
    (M := ‖A‖) (fun _ _ => le_refl _) x₀ hz hz_cont t ht
  rwa [stateTransitionMatrix_const] at this

/-- **P6.2.** For every fixed `t₀`, the `i`-th column of `e^{A(t-t₀)}` is the unique solution to
`ẋ = Ax`, `x(t₀) = eᵢ`, where `eᵢ` is the `i`-th standard basis vector — the column-restatement
of `exp_mulVec_unique`, a direct corollary of the LTV theorem `stateTransitionMatrix_col_unique`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, Property P6.2. -/
theorem exp_col_unique {t₀ t₁ : ℝ} (i : Fin n)
    {z : ℝ → Fin n → ℝ} (hz : IsIntegralSolution t₀ t₁ z (Pi.single i 1) (fun _ v => A *ᵥ v))
    (hz_cont : ContinuousOn z (Set.uIcc t₀ t₁)) :
    ∀ t ∈ Set.uIcc t₀ t₁, z t = (NormedSpace.exp ((t - t₀) • A)).col i := by
  intro t ht
  have := stateTransitionMatrix_col_unique (A := fun _ => A) continuous_const
    (M := ‖A‖) (fun _ _ => le_refl _) i hz hz_cont t ht
  rwa [stateTransitionMatrix_const] at this

/-!
## P6.3 and P6.5 are proved elsewhere

`MatrixAlgebra/Exponential.lean` carries the semigroup property `e^{At} e^{Aτ} = e^{A(t+τ)}`
(P6.3) and the finite-polynomial form `e^{At} = Σ αᵢ(t) Aⁱ` (P6.5, via Cayley-Hamilton (6.6)).
Both are statements about `exp` and `A` alone — no trajectory, no initial time, no state
transition matrix — so neither needs the LTV solution theory this file is built on.

What stays here is what genuinely specializes LTV to a constant `A`: the Peano-Baker collapse
(6.1), the closed form (6.2), and uniqueness (P6.1, P6.2).
-/

end LinearSystems

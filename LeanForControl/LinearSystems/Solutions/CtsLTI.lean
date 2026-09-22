import LeanForControl.LinearSystems.Solutions.DefsCtsLTV
import LeanForControl.LinearSystems.Solutions.CtsLTV
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
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

/-- **P6.3 (semigroup property).** `e^{At} e^{Aτ} = e^{A(t+τ)}` for every `t, τ ∈ ℝ`.

Proof: `t • A` and `τ • A` always commute (same matrix), so `Matrix.exp_add_of_commute` applies
directly; `add_smul` matches the exponent.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, Property P6.3. -/
theorem exp_const_add (t τ : ℝ) :
    NormedSpace.exp (t • A) * NormedSpace.exp (τ • A) = NormedSpace.exp ((t + τ) • A) := by
  have h : Commute (t • A) (τ • A) := (Commute.refl A).smul_left t |>.smul_right τ
  rw [add_smul]
  exact (Matrix.exp_add_of_commute (t • A) (τ • A) h).symm

/-!
## P6.5 (sketch): `e^{At}` as a finite polynomial in `A`

**This section is a proof sketch, not a finished development** — the crux growth bound
(`powModCharpoly_coeff_growth`) is `sorry`'d. The plan, avoiding eigenvalues/Jordan form entirely
(see conversation): `powModCharpolyCoeff A i k` is (up to a fixed linear reindexing) the
`k`-fold iterate of a *fixed* linear map on the finite-dimensional space of degree-`<n`
polynomials ("multiply by `X`, then reduce mod `A.charpoly`"), so its growth is bounded by
submultiplicativity of that map's operator norm — exactly the technique
`norm_peanoBakerTerm_le` already uses, just for a different recursively-iterated linear map.
-/

open Polynomial in
/-- Pure proof plumbing for P6.5, not part of its public interface: the coefficient `āᵢ(k)` of
equation (6.6), i.e. the coefficient of `X^i` in `X^k` reduced modulo `A.charpoly`. -/
private noncomputable def powModCharpolyCoeff (i : Fin n) (k : ℕ) : ℝ :=
  (X ^ k %ₘ Matrix.charpoly A).coeff i

/-- **(6.6).** Every power of `A` reduces to a linear combination of `A^0,...,A^(n-1)` — a direct
reading-off of `Matrix.pow_eq_aeval_mod_charpoly` (Cayley-Hamilton) via `powModCharpolyCoeff`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, equation (6.6). -/
private theorem pow_eq_sum_powModCharpolyCoeff (k : ℕ) :
    A ^ k = ∑ i : Fin n, powModCharpolyCoeff A i k • A ^ (i : ℕ) := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    exact Subsingleton.elim _ _
  · have hne1 : Matrix.charpoly A ≠ 1 := by
      intro h
      have h0 : (Matrix.charpoly A).natDegree = 0 := by rw [h]; exact Polynomial.natDegree_one
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h0
      omega
    have hdeg : (Polynomial.X ^ k %ₘ Matrix.charpoly A).natDegree < n := by
      have h1 := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ k)
        (Matrix.charpoly_monic A) hne1
      rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h1
    rw [Matrix.pow_eq_aeval_mod_charpoly, Polynomial.aeval_eq_sum_range' hdeg,
      ← Fin.sum_univ_eq_sum_range]
    rfl

/-- **Crux growth bound (sorry'd).** The coefficients `āᵢ(k)` grow at most exponentially in `k`.
See the section docstring for the intended (eigenvalue-free) proof strategy. -/
private theorem powModCharpoly_coeff_growth (i : Fin n) :
    ∃ C M0 : ℝ, 0 < M0 ∧ ∀ k, |powModCharpolyCoeff A i k| ≤ C * M0 ^ k := by
  sorry

/-- The scalar series defining `αᵢ(t)` converges, by comparison with the scalar exponential
series — the same technique as `summable_peanoBakerTerm`, fed by `powModCharpoly_coeff_growth`. -/
theorem summable_alphaCoeff (i : Fin n) (t : ℝ) :
    Summable (fun k => t ^ k * powModCharpolyCoeff A i k / (k)!) := by
  obtain ⟨C, M0, _, hbound⟩ := powModCharpoly_coeff_growth A i
  apply Summable.of_norm_bounded (g := fun k => C * (M0 * |t|) ^ k / (k)!)
  · have hexp : Summable (fun k => (M0 * |t|) ^ k / (k)!) := Real.summable_pow_div_factorial _
    simpa [mul_div_assoc] using hexp.mul_left C
  · intro k
    rw [Real.norm_eq_abs]
    calc |t ^ k * powModCharpolyCoeff A i k / (k)!|
        = |t| ^ k * |powModCharpolyCoeff A i k| / (k)! := by
          rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
      _ ≤ |t| ^ k * (C * M0 ^ k) / (k)! := by gcongr; exact hbound k
      _ = C * (M0 * |t|) ^ k / (k)! := by ring

/-- **αᵢ(t)**, the scalar coefficient functions of P6.5:
`αᵢ(t) := Σ_{k=0}^∞ tᵏ āᵢ(k) / k!`. -/
noncomputable def alphaCoeff (i : Fin n) (t : ℝ) : ℝ :=
  ∑' k, t ^ k * powModCharpolyCoeff A i k / (k)!

/-- **P6.5.** `e^{At} = Σ_{i=0}^{n-1} αᵢ(t) A^i` for scalar functions `α₀,...,α_{n-1}`.

Proof: substitute (6.6) into the exponential series (via `NormedSpace.exp_eq_tsum`) and swap the
(finite `i`, infinite `k`) order of summation, using `summable_alphaCoeff` to justify the swap.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, equation (6.5) / Property
P6.5. -/
theorem exp_eq_sum_alphaCoeff (t : ℝ) :
    NormedSpace.exp (t • A) = ∑ i : Fin n, alphaCoeff A i t • A ^ (i : ℕ) := by
  simp only [NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
  have hstep : ∀ k : ℕ, ((k)!⁻¹ : ℝ) • (t • A) ^ k =
      ∑ i : Fin n, (t ^ k * powModCharpolyCoeff A i k / (k)!) • A ^ (i : ℕ) := by
    intro k
    rw [smul_pow, pow_eq_sum_powModCharpolyCoeff, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    ring
  rw [tsum_congr hstep,
    Summable.tsum_finsetSum (fun i _ => (summable_alphaCoeff A i t).smul_const (A ^ (i : ℕ)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(summable_alphaCoeff A i t).tsum_smul_const, alphaCoeff]

end LinearSystems

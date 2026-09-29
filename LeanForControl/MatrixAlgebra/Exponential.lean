import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

import Architect

/-!
# The matrix exponential as an algebraic object

This file collects facts relating the matrix exponential to entrywise complexification —
algebraic and norm-compatibility bridges between the real and complex matrix exponential,
with no system semantics (no Hurwitz hypothesis, no spectral conclusion).

Reference: standard properties of the matrix exponential.
-/

namespace MatrixAlgebra

open Matrix NormedSpace
open scoped Matrix.Norms.Frobenius

variable {n : ℕ}

/-- Entrywise complexification commutes with the matrix exponential. -/
@[blueprint "lem:complexification-exp"
  (title := "Complexification commutes with the matrix exponential")
  (latexEnv := "lemma")
  (statement := /-- Entrywise complexification commutes with the matrix exponential: for a real
    matrix $A$,
    \[
      \overline{\exp(A)} = \exp(\overline{A}),
    \]
    where $\overline{\phantom{A}}$ denotes applying $\mathbb{R} \hookrightarrow \mathbb{C}$
    entrywise.  This is the bridge used to transfer spectral facts, which live over
    $\mathbb{C}$, to norm bounds on a real exponential. -/)
  (proof := /-- Entrywise complexification is a continuous ring homomorphism, and $\exp$
    commutes with any such. -/)]
lemma complexification_exp (A : Matrix (Fin n) (Fin n) ℝ) :
    (exp A).map (algebraMap ℝ ℂ) = exp (A.map (algebraMap ℝ ℂ)) := by
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℝ) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  let φ : Matrix (Fin n) (Fin n) ℝ →+* Matrix (Fin n) (Fin n) ℂ :=
    (algebraMap ℝ ℂ).mapMatrix
  have hφ : Continuous φ := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact Complex.continuous_ofReal.comp
      ((continuous_apply j).comp (continuous_apply i))
  simpa [φ] using NormedSpace.map_exp φ hφ A

section FinitePolynomial

-- Scoped to this section: `open scoped Nat` also brings Euler's totient `φ` into scope, which
-- would shadow the local `φ` in `complexification_exp` above.
open scoped Nat

/-!
## `e^{At}` as a finite polynomial in `A` (Hespanha Chapter 6, P6.3 and P6.5)

These are stated purely in terms of `exp` and `A` — no trajectories, no initial time, no state
transition matrix — so they live here rather than with the LTI solution theory in
`LinearSystems/Solutions/CtsLTI.lean`, which is where the results that *do* mention system
semantics (6.1, 6.2, P6.1, P6.2) stay.
-/

variable (A : Matrix (Fin n) (Fin n) ℝ)

/-- **Semigroup property of the matrix exponential** (Hespanha, P6.3).
`e^{At} e^{Aτ} = e^{A(t+τ)}` for every `t, τ ∈ ℝ`.

Proof: `t • A` and `τ • A` always commute (same matrix), so `Matrix.exp_add_of_commute` applies
directly; `add_smul` matches the exponent.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, Property P6.3. -/
@[blueprint "thm:exp-const-add"
  (title := "Semigroup property of the matrix exponential")
  (statement := /-- Hespanha, P6.3.  For every $t, \tau \in \mathbb{R}$,
    \[
      e^{At}e^{A\tau} = e^{A(t+\tau)} .
    \] -/)
  (proof := /-- $tA$ and $\tau A$ commute, being scalar multiples of the same matrix, so the
    exponential of the sum factors.  The general $e^{X}e^{Y} = e^{X+Y}$ needs commutativity and
    is false without it; here it is free. -/)]
theorem exp_const_add (t τ : ℝ) :
    NormedSpace.exp (t • A) * NormedSpace.exp (τ • A) = NormedSpace.exp ((t + τ) • A) := by
  have h : Commute (t • A) (τ • A) := (Commute.refl A).smul_left t |>.smul_right τ
  rw [add_smul]
  exact (Matrix.exp_add_of_commute (t • A) (τ • A) h).symm

/-!
## P6.5: `e^{At}` as a finite polynomial in `A`

Cayley-Hamilton collapses every power `A^k` onto `A^0,...,A^(n-1)` (6.6), so the exponential
series regroups into `n` scalar series `αᵢ(t)`. What makes that regrouping legitimate is that
the reduced coefficients `āᵢ(k)` grow at most geometrically in `k`
(`powModCharpoly_coeff_growth`), which is what lets the `αᵢ` be compared against the scalar
exponential series — the same technique as `summable_peanoBakerTerm`.

That growth bound is proved by iteration rather than by spectral theory: "multiply by `X`,
reduce mod `A.charpoly`" is a fixed operation on the `n`-dimensional space of degree-`<n`
polynomials, so one step scales the coefficient vector by at most a constant factor. No
eigenvalues and no Jordan form appear anywhere in this section.
-/

open Polynomial in
/-- Pure proof plumbing for P6.5, not part of its public interface: the coefficient `āᵢ(k)` of
equation (6.6), i.e. the coefficient of `X^i` in `X^k` reduced modulo `A.charpoly`. -/
private noncomputable def powModCharpolyCoeff (i : Fin n) (k : ℕ) : ℝ :=
  (X ^ k %ₘ Matrix.charpoly A).coeff i

/-- **Cayley-Hamilton power reduction** (Hespanha, equation (6.6)).
Every power of `A` reduces to a linear combination of `A^0,...,A^(n-1)` — a direct
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

open Polynomial in
/-- **Crux growth bound.** The coefficients `āᵢ(k)` of (6.6) grow at most exponentially in `k`.

Reduction mod `A.charpoly` always leaves degree `< n`, so `X^(k+1) ≡ (X^k %ₘ charpoly) * X`
re-expands the `n` coefficients of `X^k %ₘ charpoly` against the `n` *fixed* polynomials
`X^(j+1) %ₘ charpoly`, `j < n`. One step therefore multiplies the `ℓ¹` size `N k` of the
coefficient vector by at most the constant `M` — the total `ℓ¹` size of those `n` fixed
polynomials — giving `N k ≤ N 0 * M ^ k`. No eigenvalues, no Jordan form. -/
private theorem powModCharpoly_coeff_growth (i : Fin n) :
    ∃ C M0 : ℝ, 0 < M0 ∧ ∀ k, |powModCharpolyCoeff A i k| ≤ C * M0 ^ k := by
  simp only [powModCharpolyCoeff]
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le (i : ℕ)) i.isLt
  set p := A.charpoly with hp
  have hp_monic : p.Monic := A.charpoly_monic
  have hp_deg : p.natDegree = n := by
    rw [hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hne1 : p ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at hp_deg
    omega
  -- Reduction never leaves degree `< n`, so `n` coefficients always suffice.
  have hdeg : ∀ k : ℕ, (X ^ k %ₘ p).natDegree < n := fun k =>
    hp_deg ▸ Polynomial.natDegree_modByMonic_lt (X ^ k : ℝ[X]) hp_monic hne1
  have hsum_mod : ∀ (s : Finset ℕ) (g : ℕ → ℝ[X]),
      (∑ j ∈ s, g j) %ₘ p = ∑ j ∈ s, g j %ₘ p := fun s g =>
    map_sum (Polynomial.modByMonicHom p) g s
  -- `X^(k+1)` and `(X^k %ₘ p) * X` differ by a multiple of `p`, so they reduce alike.
  have hstep : ∀ k : ℕ, X ^ (k + 1) %ₘ p = ((X ^ k %ₘ p) * X) %ₘ p := by
    intro k
    refine Polynomial.modByMonic_eq_of_dvd_sub hp_monic ⟨(X ^ k /ₘ p) * X, ?_⟩
    have h := Polynomial.modByMonic_add_div (X ^ k : ℝ[X]) p
    calc (X : ℝ[X]) ^ (k + 1) - (X ^ k %ₘ p) * X
        = (X ^ k %ₘ p + p * (X ^ k /ₘ p)) * X - (X ^ k %ₘ p) * X := by rw [h]; ring
      _ = p * ((X ^ k /ₘ p) * X) := by ring
  -- Re-expand that against the `n` fixed reduced polynomials `X^(j+1) %ₘ p`.
  have hexp : ∀ k : ℕ, X ^ (k + 1) %ₘ p
      = ∑ j ∈ Finset.range n, (X ^ k %ₘ p).coeff j • (X ^ (j + 1) %ₘ p) := by
    intro k
    rw [hstep k]
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' (X ^ k %ₘ p) (hdeg k)]
    rw [Finset.sum_mul, hsum_mod]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← pow_succ, Polynomial.C_mul', Polynomial.smul_modByMonic]
  have hcoeff : ∀ k m : ℕ, (X ^ (k + 1) %ₘ p).coeff m
      = ∑ j ∈ Finset.range n, (X ^ k %ₘ p).coeff j * (X ^ (j + 1) %ₘ p).coeff m := by
    intro k m
    rw [hexp k, Polynomial.finset_sum_coeff]
    exact Finset.sum_congr rfl fun j _ => by rw [Polynomial.coeff_smul, smul_eq_mul]
  -- `N k` is the `ℓ¹` size of the coefficient vector; `M` that of the `n` fixed polynomials.
  set N : ℕ → ℝ := fun k => ∑ m ∈ Finset.range n, |(X ^ k %ₘ p).coeff m| with hN
  set M : ℝ := ∑ j ∈ Finset.range n, ∑ m ∈ Finset.range n, |(X ^ (j + 1) %ₘ p).coeff m| with hM
  have hM_nonneg : 0 ≤ M :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hN_nonneg : ∀ k, 0 ≤ N k := fun _ => by
    simp only [hN]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- One step costs a factor of at most `M`.
  have hrec : ∀ k, N (k + 1) ≤ M * N k := by
    intro k
    simp only [hN, hM]
    have h1 : ∑ m ∈ Finset.range n, |(X ^ (k + 1) %ₘ p).coeff m|
        ≤ ∑ m ∈ Finset.range n, ∑ j ∈ Finset.range n,
          |(X ^ k %ₘ p).coeff j| * |(X ^ (j + 1) %ₘ p).coeff m| := by
      refine Finset.sum_le_sum fun m _ => ?_
      rw [hcoeff k m]
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq
        (Finset.sum_congr rfl fun j _ => abs_mul _ _)
    rw [Finset.sum_comm] at h1
    refine h1.trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [← Finset.mul_sum, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    exact Finset.single_le_sum (f := fun m => |(X ^ k %ₘ p).coeff m|)
      (fun _ _ => abs_nonneg _) hj
  have hgrow : ∀ k, N k ≤ N 0 * M ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc N (k + 1) ≤ M * N k := hrec k
        _ ≤ M * (N 0 * M ^ k) := mul_le_mul_of_nonneg_left ih hM_nonneg
        _ = N 0 * M ^ (k + 1) := by ring
  refine ⟨N 0, max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun k => ?_⟩
  calc |(X ^ k %ₘ p).coeff (i : ℕ)|
      ≤ N k := Finset.single_le_sum (f := fun m => |(X ^ k %ₘ p).coeff m|)
                 (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr i.isLt)
    _ ≤ N 0 * M ^ k := hgrow k
    _ ≤ N 0 * max M 1 ^ k := by
        have hpow : M ^ k ≤ max M 1 ^ k := by gcongr; exact le_max_left _ _
        exact mul_le_mul_of_nonneg_left hpow (hN_nonneg 0)

/-- Pure proof plumbing for P6.5, not part of its public interface: the scalar series defining
`αᵢ(t)` converges, by comparison with the scalar exponential series — the same technique as
`summable_peanoBakerTerm`, fed by `powModCharpoly_coeff_growth`. -/
private theorem summable_alphaCoeff (i : Fin n) (t : ℝ) :
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

/-- Pure proof plumbing for P6.5, not part of its public interface: the witness `αᵢ(t) :=
Σ_{k=0}^∞ tᵏ āᵢ(k) / k!` for the coefficient functions. P6.5 exposes only their existence —
the particular series is an artifact of this proof, not of the statement. -/
private noncomputable def alphaCoeff (i : Fin n) (t : ℝ) : ℝ :=
  ∑' k, t ^ k * powModCharpolyCoeff A i k / (k)!

/-- **The matrix exponential as a finite polynomial** (Hespanha, P6.5).
`e^{At} = Σ_{i=0}^{n-1} αᵢ(t) A^i` for some scalar functions `α₀,...,α_{n-1}`:
the matrix exponential is a *finite* polynomial in `A`, of degree less than `n`.

The coefficient functions are existentially quantified rather than named. The particular series
this proof builds is an artifact of the technique (reduce `X^k` mod the characteristic
polynomial), not content of the statement, and the collapse to `n` terms is what P6.5 asserts.

Proof: substitute (6.6) into the exponential series (via `NormedSpace.exp_eq_tsum`) and swap the
(finite `i`, infinite `k`) order of summation, using `summable_alphaCoeff` to justify the swap.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, equation (6.5) / Property
P6.5. -/
@[blueprint "thm:exists-exp-eq-sum-smul-pow"
  (title := "The matrix exponential as a finite polynomial")
  (statement := /-- Hespanha, P6.5.  There are scalar functions
    $\alpha_0, \dots, \alpha_{n-1} : \mathbb{R} \to \mathbb{R}$ with
    \[
      e^{At} = \sum_{i=0}^{n-1} \alpha_i(t)\,A^i
      \qquad \text{for every } t .
    \]
    The matrix exponential — an infinite series in $A$ — is a \emph{finite} polynomial in $A$ of
    degree less than $n$, at the cost of coefficients that are transcendental in $t$. -/)
  (proof := /-- Cayley--Hamilton reduces every power $A^k$ to a combination of
    $A^0, \dots, A^{n-1}$, say with coefficients $\bar a_i(k)$; substituting into the exponential
    series and exchanging the finite sum over $i$ with the infinite sum over $k$ exhibits
    $\alpha_i(t) = \sum_k t^k \bar a_i(k)/k!$ as a witness.

    The exchange needs those series to converge, which holds because the reduced coefficients
    grow at most geometrically, $|\bar a_i(k)| \le CM^k$, dominating each $\alpha_i$ by a scalar
    exponential series.  That growth bound is the crux of the proof and is established by
    iteration, not by spectral theory: ``multiply by $X$, reduce modulo the characteristic
    polynomial'' is a fixed linear operation on the $n$-dimensional space of polynomials of
    degree $< n$, so one step scales the $\ell^1$ size of the coefficient vector by at most a
    constant factor.  No eigenvalues and no Jordan form appear anywhere. -/)]
theorem exists_exp_eq_sum_smul_pow :
    ∃ α : Fin n → ℝ → ℝ, ∀ t : ℝ,
      NormedSpace.exp (t • A) = ∑ i : Fin n, α i t • A ^ (i : ℕ) := by
  refine ⟨fun i t => alphaCoeff A i t, fun t => ?_⟩
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

end FinitePolynomial

end MatrixAlgebra

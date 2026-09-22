import LeanForControl.LinearSystems.Realization.Similarity
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Architect

/-!
# Finite determination of realization behavior

The product of the two characteristic polynomials annihilates both state
matrices.  Reducing an arbitrary monomial modulo that common monic polynomial
shows that the first `n₁ + n₂` Markov parameters determine every later one.

Reference: Kailath, *Linear Systems*.
-/

namespace LinearSystems

open Matrix Polynomial

namespace Realization

variable {𝕜 : Type*} [Field 𝕜]
variable {n₁ n₂ m p : ℕ}

/-- Equal Markov parameters through the degree of a polynomial give equal
matrix evaluations of that polynomial between the output and input maps.

Original: polynomial-evaluation infrastructure for LeanForControl. -/
theorem output_aeval_mul_input_eq_of_markovParameter_eq
    (R₁ : Realization 𝕜 n₁ m p) (R₂ : Realization 𝕜 n₂ m p)
    (q : 𝕜[X]) (N : ℕ)
    (hq : q.natDegree < N)
    (hmarkov : ∀ k < N, R₁.markovParameter k = R₂.markovParameter k) :
    R₁.C * Polynomial.aeval R₁.A q * R₁.B =
      R₂.C * Polynomial.aeval R₂.A q * R₂.B := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hkN : k < N := by omega
  simpa [markovParameter, Matrix.mul_assoc] using
    congrArg (fun M => q.coeff k • M) (hmarkov k hkN)

/-- Agreement of feedthrough and the first `n₁ + n₂` Markov parameters
implies full behavioral equivalence.

The bound is obtained from the common annihilating polynomial
`charpoly A₁ * charpoly A₂`, whose degree is `n₁ + n₂`.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "thm:finite-markov-determination"
  (statement := /-- Two realizations of state dimensions $n_1,n_2$ are
    behaviorally equivalent if their feedthrough matrices agree and their
    Markov parameters agree for $0\le k<n_1+n_2$. -/)]
theorem behaviorallyEquivalent_of_markovParameter_eq_lt_add
    (R₁ : Realization 𝕜 n₁ m p) (R₂ : Realization 𝕜 n₂ m p)
    (hD : R₁.D = R₂.D)
    (hmarkov : ∀ k < n₁ + n₂,
      R₁.markovParameter k = R₂.markovParameter k) :
    R₁.BehaviorallyEquivalent R₂ := by
  refine ⟨hD, fun k => ?_⟩
  by_cases hzero : n₁ + n₂ = 0
  · have hn₁ : n₁ = 0 := by omega
    have hn₂ : n₂ = 0 := by omega
    subst n₁
    subst n₂
    simp [markovParameter]
  · let q : 𝕜[X] := R₁.A.charpoly * R₂.A.charpoly
    have hqMonic : q.Monic :=
      R₁.A.charpoly_monic.mul R₂.A.charpoly_monic
    have hqDegree : q.natDegree = n₁ + n₂ := by
      dsimp [q]
      rw [Polynomial.natDegree_mul
        R₁.A.charpoly_monic.ne_zero R₂.A.charpoly_monic.ne_zero,
        Matrix.charpoly_natDegree_eq_dim,
        Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
        Fintype.card_fin]
    have hqNeOne : q ≠ 1 := by
      intro h
      have : q.natDegree = 0 := by rw [h, Polynomial.natDegree_one]
      omega
    have hroot₁ : Polynomial.aeval R₁.A q = 0 := by
      dsimp [q]
      rw [map_mul, Matrix.aeval_self_charpoly, zero_mul]
    have hroot₂ : Polynomial.aeval R₂.A q = 0 := by
      dsimp [q]
      rw [map_mul, Matrix.aeval_self_charpoly, mul_zero]
    let r : 𝕜[X] := X ^ k %ₘ q
    have hrDegree : r.natDegree < n₁ + n₂ := by
      rw [← hqDegree]
      exact Polynomial.natDegree_modByMonic_lt _ hqMonic hqNeOne
    have hrEval :=
      output_aeval_mul_input_eq_of_markovParameter_eq R₁ R₂ r
        (n₁ + n₂) hrDegree hmarkov
    have hpow₁ : Polynomial.aeval R₁.A r = R₁.A ^ k := by
      dsimp [r]
      rw [Polynomial.aeval_modByMonic_eq_self_of_root hroot₁, map_pow,
        Polynomial.aeval_X]
    have hpow₂ : Polynomial.aeval R₂.A r = R₂.A ^ k := by
      dsimp [r]
      rw [Polynomial.aeval_modByMonic_eq_self_of_root hroot₂, map_pow,
        Polynomial.aeval_X]
    simpa [markovParameter, hpow₁, hpow₂] using hrEval

end Realization

end LinearSystems

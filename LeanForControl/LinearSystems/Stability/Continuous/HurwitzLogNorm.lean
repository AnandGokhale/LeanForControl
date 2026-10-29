import LeanForControl.Contraction.Norms.Lp
import LeanForControl.LinearSystems.Stability.Continuous.LyapunovEquation
import Architect

/-!
# Hurwitz matrices and weighted Euclidean log norms

The Lyapunov characterization of Hurwitz matrices, read through the LMI form of the weighted
Euclidean log norm `μ_{2,P^½}`:

* `Matrix.isHurwitz_iff_exists_logNormL2PosDef_neg` — `A` is Hurwitz iff `μ_{2,P^½}(A) < 0` for
  some `P ≻ 0`.
* `Matrix.isHurwitzWithRate_iff_exists_logNormL2PosDef_lt` — more generally, every eigenvalue of
  `A` has real part `< b` iff `μ_{2,P^½}(A) < b` for some `P ≻ 0`.

References: F. Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), Chapter 2.
-/

open scoped LogNorm

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- **Hurwitz matrices are exactly those contracting in some weighted Euclidean norm**: `A` is
Hurwitz iff `μ_{2,P^½}(A) < 0` for some `P ≻ 0`. -/
@[blueprint "thm:isHurwitz-iff-exists-logNormL2PosDef-neg"
  (title := "Hurwitz matrices and weighted Euclidean log norms")
  (statement := /-- $A$ is Hurwitz if and only if $\mu_{2,P^{1/2}}(A) < 0$ for some
    $P \succ 0$. -/)
  (proof := /-- \cref{thm:isHurwitz-iff-exists-posDef-lyapunovRate}, read through
    \cref{thm:logNormL2PosDef-le-iff-lmi}: $A^\top P + P A \preceq -2 c P$ says
    $\mu_{2,P^{1/2}}(A) \le -c$. -/)]
theorem isHurwitz_iff_exists_logNormL2PosDef_neg (A : Matrix n n ℝ) :
    LinearSystems.IsHurwitz A ↔ ∃ P : Matrix n n ℝ, P.PosDef ∧ μ_{2,P^½} A < 0 := by
  rw [LinearSystems.isHurwitz_iff_exists_posDef_lyapunovRate]
  -- `-(P A + Aᵀ P) - 2c P ⪰ 0` is the LMI `Aᵀ P + P A ⪯ 2 (-c) P`
  have hlmi (P : Matrix n n ℝ) (hP : P.PosDef) (c : ℝ) :
      μ_{2,P^½} A ≤ -c ↔ (-(P * A + Aᵀ * P) - (2 * c) • P).PosSemidef := by
    rw [logNormL2PosDef_le_iff_lmi hP, Matrix.le_iff]
    congr! 1
    rw [mul_neg, neg_smul]
    abel
  constructor
  · rintro ⟨P, c, hc, hP, h⟩
    exact ⟨P, hP, ((hlmi P hP c).2 h).trans_lt (neg_lt_zero.2 hc)⟩
  · rintro ⟨P, hP, h⟩
    exact ⟨P, -μ_{2,P^½} A, neg_pos.2 h, hP, (hlmi P hP _).1 (by rw [neg_neg])⟩

/-- **The spectral abscissa is the infimum of the weighted Euclidean log norms**: every eigenvalue
of `A` has real part `< b` iff `μ_{2,P^½}(A) < b` for some `P ≻ 0`.  The case `b = 0` is
`isHurwitz_iff_exists_logNormL2PosDef_neg`. -/
@[blueprint "thm:isHurwitzWithRate-iff-exists-logNormL2PosDef-lt"
  (title := "Spectral abscissa and weighted Euclidean log norms")
  (statement := /-- For every $b \in \mathbb{R}$, every eigenvalue of $A$ has real part less
    than $b$ if and only if $\mu_{2,P^{1/2}}(A) < b$ for some $P \succ 0$.

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Chapter 2. -/)
  (proof := /-- Apply \cref{thm:isHurwitz-iff-exists-logNormL2PosDef-neg} to $A - b I$
    (\cref{thm:isHurwitzWithRate-iff-spectral-shift}) and use
    $\mu_{2,P^{1/2}}(A - b I) = \mu_{2,P^{1/2}}(A) - b$ (\cref{lem:logNorm-add-smul-one}). -/)]
theorem isHurwitzWithRate_iff_exists_logNormL2PosDef_lt (A : Matrix n n ℝ) (b : ℝ) :
    LinearSystems.IsHurwitzWithRate (-b) A ↔ ∃ P : Matrix n n ℝ, P.PosDef ∧ μ_{2,P^½} A < b := by
  rw [LinearSystems.isHurwitzWithRate_iff_add_smul_one, isHurwitz_iff_exists_logNormL2PosDef_neg]
  refine exists_congr fun P => and_congr_right fun hP => ?_
  have h : μ_{2,P^½} (A + (-b) • 1) = μ_{2,P^½} A + -b := by
    rw [logNormL2PosDef, logNormL2PosDef, dif_pos hP, dif_pos hP, ← logNorm_add_smul_one]
    congr 1
    ext x : 1
    apply WeightedEuclidean.ext
    simp [add_mulVec, neg_mulVec, smul_mulVec, one_mulVec]
  rw [h, add_neg_lt_iff_lt_add, zero_add]

end Matrix

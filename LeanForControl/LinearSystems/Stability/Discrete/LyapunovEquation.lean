import LeanForControl.LinearSystems.Stability.Discrete.Schur
import LeanForControl.MatrixAlgebra.PosDef
import LeanForControl.MatrixAlgebra.QuadraticForm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Topology.Instances.Matrix
import Architect

/-!
# `LinearSystems.Stability.Discrete.LyapunovEquation`

The discrete-time Lyapunov equation `Aᵀ P A - P = -Q` and its relation to the Schur condition:
the discrete-time counterpart of `LinearSystems.Stability.Continuous.LyapunovEquation`.

* `IsSchur.exists_posDef_unique_solution_discrete_lyapunov` — for a Schur `A`, every positive
  definite `Q` has a positive definite solution, unique among all matrix solutions.  It is the
  convergent series `P = ∑ₖ (Aᵀ)ᵏ Q Aᵏ`; the geometric envelope of `IsSchur.exists_norm_pow_le`
  makes it converge.  Unlike continuous time no integral is needed.
* `isSchur_of_discreteLyapunovEquation` — conversely, a positive definite solution with positive
  definite forcing certifies that `A` is Schur: paired against an eigenvector `Av = μv` the
  equation reads `(|μ|² - 1) v*Pv = -v*Qv`.
* `DiscreteLyapunovEquation.dotProduct_mulVec_sub` — along `x ↦ A x` the quadratic form
  `xᵀ P x` decreases by exactly `xᵀ Q x`: why a solution is a Lyapunov function.

Norms are the `L∞` operator norm.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.4.
-/

namespace LinearSystems

open Filter Matrix Topology
open scoped Matrix.Norms.Operator ComplexOrder

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## The transpose of a Schur matrix -/

omit [DecidableEq X] in
/-- A matrix and its transpose have the same eigenvalues, so the transpose of a Schur matrix is
Schur. -/
@[blueprint "lem:isSchur-transpose"
  (title := "The transpose of a Schur matrix is Schur")
  (latexEnv := "lemma")
  (statement := /-- If $A$ is Schur (\cref{def:stability-isSchur}) then so is
    $A^{\mathsf T}$. -/)
  (proof := /-- $A$ and $A^{\mathsf T}$ have the same characteristic polynomial, hence the same
    spectrum over $\mathbb{C}$, and the spectrum is the set of eigenvalues
    (\cref{lem:mem-spectrum-iff-exists-eigenpair}). -/)]
lemma IsSchur.transpose {A : Matrix X X ℝ} (hA : IsSchur A) : IsSchur Aᵀ := by
  classical
  intro μ v hv hAv
  have hmem : μ ∈ spectrum ℂ A.complexify := by
    have h : μ ∈ spectrum ℂ (Aᵀ).complexify :=
      (Matrix.mem_spectrum_iff_exists_eigenpair _ _).2 ⟨v, hv, hAv⟩
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at h ⊢
    rwa [Matrix.complexify_transpose, Matrix.charpoly_transpose] at h
  obtain ⟨w, hw, hAw⟩ := (Matrix.mem_spectrum_iff_exists_eigenpair _ _).1 hmem
  exact hA μ w hw hAw

/-! ## Schur gives a solution -/

omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.4, (3) ⟹ (4).**  A Schur matrix admits a positive definite solution of
the discrete-time Lyapunov equation for every positive definite forcing, unique among all matrix
solutions: the series `∑ₖ (Aᵀ)ᵏ Q Aᵏ`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.4. -/
@[blueprint "thm:isSchur-exists-posDef-unique-discrete-lyapunov"
  (title := "Discrete Lyapunov equation for a Schur matrix")
  (statement := /-- If $A$ is Schur (\cref{def:stability-isSchur}), then for every positive
    definite $Q$ there is a positive definite $P$ with $A^{\mathsf T}PA - P = -Q$
    (\cref{def:discreteLyapunovEquation}), and $P$ is the unique matrix solution.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.4.
  -/)
  (proof := /-- Take $P = \sum_{k} (A^{\mathsf T})^{k} Q A^{k}$.  It converges because both $A$
    and $A^{\mathsf T}$ are Schur (\cref{lem:isSchur-transpose}), so their powers decay
    geometrically (\cref{thm:isSchur-exists-norm-pow-le}).  Shifting the index,
    $A^{\mathsf T}PA = P - Q$.  The first term is $Q$ and the others are positive semidefinite,
    so $P$ is positive definite (\cref{lem:posSemidef-tsum}).  For uniqueness, a
    difference $W$ of two solutions satisfies $W = A^{\mathsf T}WA$, hence
    $W = (A^{\mathsf T})^{k}WA^{k} \to 0$. -/)]
theorem IsSchur.exists_posDef_unique_solution_discrete_lyapunov {A : Matrix X X ℝ}
    (hA : IsSchur A) (Q : Matrix X X ℝ) (hQ : Q.PosDef) :
    ∃ P : Matrix X X ℝ, P.PosDef ∧ DiscreteLyapunovEquation A P Q ∧
      ∀ S : Matrix X X ℝ, DiscreteLyapunovEquation A S Q → S = P := by
  classical
  set term : ℕ → Matrix X X ℝ := fun k => (Aᵀ) ^ k * Q * A ^ k with hterm
  -- Summability, from the geometric envelopes of `A` and `Aᵀ`.
  obtain ⟨C, hC, ρ, hρ0, hρ1, hA_bd⟩ := hA.exists_norm_pow_le
  obtain ⟨C', hC', ρ', hρ0', hρ1', hAt_bd⟩ := hA.transpose.exists_norm_pow_le
  have hs : Summable term := by
    refine Summable.of_norm_bounded (g := fun k => C' * ‖Q‖ * C * (ρ' * ρ) ^ k)
      ((summable_geometric_of_lt_one (by positivity)
        (mul_lt_one_of_nonneg_of_lt_one_left hρ0' hρ1' hρ1.le)).mul_left _) fun k => ?_
    calc ‖term k‖ ≤ ‖(Aᵀ) ^ k‖ * ‖Q‖ * ‖A ^ k‖ := by
          simp only [hterm]
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _))
      _ ≤ (C' * ρ' ^ k) * ‖Q‖ * (C * ρ ^ k) := by gcongr; exacts [hAt_bd k, hA_bd k]
      _ = C' * ‖Q‖ * C * (ρ' * ρ) ^ k := by rw [mul_pow]; ring
  set P := ∑' k, term k with hP
  -- `term (k + 1) = Aᵀ (term k) A`.
  have hshift : ∀ k, term (k + 1) = Aᵀ * term k * A := fun k => by
    change (Aᵀ) ^ (k + 1) * Q * A ^ (k + 1) = Aᵀ * ((Aᵀ) ^ k * Q * A ^ k) * A
    rw [pow_succ' (Aᵀ), pow_succ A]
    simp only [Matrix.mul_assoc]
  -- The equation: `Aᵀ P A = ∑ term (k + 1) = P - Q`.
  have hAPA : Aᵀ * P * A = P - Q := by
    have hleft : Aᵀ * P * A = ∑' k, term (k + 1) := by
      rw [hP, ← hs.tsum_mul_left, ← (hs.mul_left Aᵀ).tsum_mul_right]
      exact tsum_congr fun k => (hshift k).symm
    rw [hleft, hP, hs.tsum_eq_zero_add]
    simp [hterm]
  have hEq : DiscreteLyapunovEquation A P Q := by
    rw [DiscreteLyapunovEquation, hAPA]; abel
  -- Positive definiteness: `term 0 = Q`, and every term is `(Aᵏ)ᵀ Q Aᵏ`.
  have hPpos : P.PosDef := by
    rw [hP, hs.tsum_eq_zero_add]
    refine (by simpa [hterm] using hQ : (term 0).PosDef).add_posSemidef
      (posSemidef_tsum ((summable_nat_add_iff 1).mpr hs) fun k => ?_)
    have h := hQ.posSemidef.conjTranspose_mul_mul_same (A ^ (k + 1))
    simpa [hterm, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_pow] using h
  refine ⟨P, hPpos, hEq, fun S hS => ?_⟩
  -- Uniqueness: `W = S - P` satisfies `W = Aᵀ W A`, so `W = (Aᵀ)ᵏ W Aᵏ → 0`.
  set W := S - P with hW
  have hfix : Aᵀ * W * A = W := by
    rw [hW, Matrix.mul_sub, Matrix.sub_mul, eq_add_of_sub_eq (hS : Aᵀ * S * A - S = -Q),
      eq_add_of_sub_eq (hEq : Aᵀ * P * A - P = -Q)]
    abel
  have hpow : ∀ k, (Aᵀ) ^ k * W * A ^ k = W := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc (Aᵀ) ^ (k + 1) * W * A ^ (k + 1) = (Aᵀ) ^ k * (Aᵀ * W * A) * A ^ k := by
            rw [pow_succ (Aᵀ), pow_succ' A]
            simp only [Matrix.mul_assoc]
        _ = W := by rw [hfix, ih]
  have hlim : Tendsto (fun k : ℕ => (Aᵀ) ^ k * W * A ^ k) atTop (𝓝 0) := by
    have h := (((isSchur_iff_tendsto_pow Aᵀ).1 hA.transpose).mul
      (tendsto_const_nhds (x := W))).mul ((isSchur_iff_tendsto_pow A).1 hA)
    simpa using h
  have hW0 : W = 0 := tendsto_nhds_unique (by simp [hpow]) hlim
  exact (sub_eq_zero.mp hW0)

/-! ## A solution certifies Schur -/

section LyapunovEquation

variable {A P Q : Matrix X X ℝ}

omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.4, (4) ⟹ (3).**  A positive definite solution of the discrete-time
Lyapunov equation with positive definite forcing certifies that `A` is Schur.

Pairing the equation against a complex eigenvector `Av = μv` gives
`(|μ|² - 1) · v*Pv = -v*Qv`, and both quadratic forms are strictly positive, so `|μ| < 1`. -/
@[blueprint "thm:isSchur-of-discreteLyapunovEquation"
  (title := "A discrete Lyapunov certificate proves the spectrum lies in the unit disc")
  (statement := /-- If $P$ and $Q$ are positive definite and $A^{\mathsf T}PA - P = -Q$, then
    $A$ is Schur (\cref{def:stability-isSchur}).

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.4.
  -/)
  (proof := /-- Complexify the equation and pair it against an eigenvector $v$ with eigenvalue
    $\mu$: the left-hand side is $(|\mu|^{2} - 1)\,v^{*}Pv$ and the right-hand side is
    $-v^{*}Qv$.  Both quadratic forms are strictly positive
    (\cref{lem:matrix-posDef-complexify}), so $|\mu|^{2} < 1$. -/)]
theorem isSchur_of_discreteLyapunovEquation (hP : P.PosDef) (hQ : Q.PosDef)
    (h : DiscreteLyapunovEquation A P Q) : IsSchur A := by
  intro μ v hv hAv
  -- The equation, complexified.
  have hc : A.complexifyᵀ * P.complexify * A.complexify - P.complexify = -Q.complexify := by
    simpa [DiscreteLyapunovEquation] using congrArg Matrix.complexify h
  -- Pair it against `v`: the first term contributes `conj μ * μ`.
  have hL : star v ⬝ᵥ ((A.complexifyᵀ * P.complexify * A.complexify) *ᵥ v)
      = (starRingEnd ℂ) μ * μ * (star v ⬝ᵥ (P.complexify *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAv, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, Matrix.complexify_mulVec_star, hAv]
    simp [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_assoc, mul_comm]
  have hpair : ((starRingEnd ℂ) μ * μ - 1) * (star v ⬝ᵥ (P.complexify *ᵥ v))
      = -(star v ⬝ᵥ (Q.complexify *ᵥ v)) := by
    have := congrArg (fun N : Matrix X X ℂ => star v ⬝ᵥ (N *ᵥ v)) hc
    simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.neg_mulVec, dotProduct_neg] at this
    rw [sub_mul, one_mul, ← hL]
    exact this
  -- Both quadratic forms are strictly positive, so `|μ|² < 1`.
  have hp := (Complex.lt_def.mp (hP.complexify.dotProduct_mulVec_pos hv)).1
  have hq := (Complex.lt_def.mp (hQ.complexify.dotProduct_mulVec_pos hv)).1
  simp only [Complex.zero_re] at hp hq
  have hμ2 : (starRingEnd ℂ) μ * μ = ((‖μ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']; push_cast; ring
  have hre := congrArg Complex.re hpair
  rw [hμ2, sub_mul, Complex.sub_re, Complex.re_ofReal_mul, one_mul, Complex.neg_re] at hre
  have hsq : ‖μ‖ ^ 2 < 1 := by nlinarith
  nlinarith [norm_nonneg μ]

omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.4, (5) ⟹ (3).**  The discrete Lyapunov *inequality*
`AᵀPA - P ≺ 0` certifies the same thing: take the forcing to be minus the residual. -/
@[blueprint "thm:isSchur-of-posDef-neg-discreteLyapunovResidual"
  (title := "The discrete Lyapunov inequality certifies the Schur condition")
  (statement := /-- If $P$ is positive definite and $-(A^{\mathsf T}PA - P)$ is positive
    definite, then $A$ is Schur (\cref{def:stability-isSchur}).

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.4.
  -/)
  (proof := /-- Take the forcing to be minus the residual and apply
    \cref{thm:isSchur-of-discreteLyapunovEquation}. -/)]
theorem isSchur_of_posDef_neg_discreteLyapunovResidual (hP : P.PosDef)
    (hneg : (-(Aᵀ * P * A - P)).PosDef) : IsSchur A :=
  isSchur_of_discreteLyapunovEquation hP hneg (by simp [DiscreteLyapunovEquation])

/-! ## The equivalences -/

omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.4, (3) ⟺ (4).**  `A` is Schur exactly when every positive definite
forcing admits a positive definite solution of the discrete Lyapunov equation, unique among all
matrix solutions. -/
@[blueprint "thm:isSchur-iff-forall-posDef-exists-discrete-solution"
  (title := "Schur is solvability of the discrete Lyapunov equation for every forcing")
  (statement := /-- A real square matrix $A$ is Schur (\cref{def:stability-isSchur}) if and only
    if for every positive definite $Q$ there is a positive definite $P$ with
    $A^{\mathsf T}PA - P = -Q$ (\cref{def:discreteLyapunovEquation}), unique among all matrix
    solutions.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.4.
  -/)
  (proof := /-- Forwards is \cref{thm:isSchur-exists-posDef-unique-discrete-lyapunov}.
    Backwards, instantiate the forcing at $Q = I$ and apply
    \cref{thm:isSchur-of-discreteLyapunovEquation}. -/)]
theorem isSchur_iff_forall_posDef_exists_discrete_solution (A : Matrix X X ℝ) :
    IsSchur A ↔ ∀ R : Matrix X X ℝ, R.PosDef →
      ∃ S : Matrix X X ℝ, S.PosDef ∧ DiscreteLyapunovEquation A S R ∧
        ∀ T : Matrix X X ℝ, DiscreteLyapunovEquation A T R → T = S := by
  classical
  refine ⟨fun hA R hR => hA.exists_posDef_unique_solution_discrete_lyapunov R hR, fun h => ?_⟩
  obtain ⟨S, hS, hEq, -⟩ := h 1 Matrix.PosDef.one
  exact isSchur_of_discreteLyapunovEquation hS Matrix.PosDef.one hEq

omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.4, (3) ⟺ (5).**  `A` is Schur exactly when some positive definite `P`
makes the discrete Lyapunov residual negative definite. -/
@[blueprint "thm:isSchur-iff-exists-posDef-discreteLyapunovResidual"
  (title := "Schur is the existence of one discrete Lyapunov certificate")
  (statement := /-- A real square matrix $A$ is Schur (\cref{def:stability-isSchur}) if and only
    if some positive definite $P$ makes $-(A^{\mathsf T}PA - P)$ positive definite.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.4.
  -/)
  (proof := /-- Forwards, solve the equation with $Q = I$
    (\cref{thm:isSchur-exists-posDef-unique-discrete-lyapunov}); the residual is then $-I$.
    Backwards is \cref{thm:isSchur-of-posDef-neg-discreteLyapunovResidual}. -/)]
theorem isSchur_iff_exists_posDef_discreteLyapunovResidual (A : Matrix X X ℝ) :
    IsSchur A ↔ ∃ S : Matrix X X ℝ, S.PosDef ∧ (-(Aᵀ * S * A - S)).PosDef := by
  classical
  refine ⟨fun hA => ?_, fun ⟨S, hS, hneg⟩ => isSchur_of_posDef_neg_discreteLyapunovResidual hS
    hneg⟩
  obtain ⟨S, hS, hEq, -⟩ := hA.exists_posDef_unique_solution_discrete_lyapunov 1 Matrix.PosDef.one
  refine ⟨S, hS, ?_⟩
  rw [show Aᵀ * S * A - S = -1 from hEq]
  simpa using Matrix.PosDef.one

/-! ## Along the system -/

omit [DecidableEq X] in
/-- Along `x ↦ A x`, the quadratic form of a solution of the discrete Lyapunov equation
decreases by exactly `xᵀ Q x`: what makes a solution a Lyapunov function. -/
@[blueprint "lem:discreteLyapunovEquation-dotProduct-mulVec-sub"
  (title := "Decrease of the quadratic form along a discrete LTI system")
  (latexEnv := "lemma")
  (statement := /-- If $A^{\mathsf T}PA - P = -Q$ (\cref{def:discreteLyapunovEquation}), then
    for every $x$,
    \[
      (Ax)^{\mathsf T} P (Ax) - x^{\mathsf T} P x = -x^{\mathsf T} Q x.
    \] -/)
  (proof := /-- $(Ax)^{\mathsf T}P(Ax) = x^{\mathsf T}(A^{\mathsf T}PA)x$, and
    $A^{\mathsf T}PA = P - Q$. -/)]
theorem DiscreteLyapunovEquation.dotProduct_mulVec_sub (h : DiscreteLyapunovEquation A P Q)
    (x : X → ℝ) :
    (A *ᵥ x) ⬝ᵥ (P *ᵥ (A *ᵥ x)) - x ⬝ᵥ (P *ᵥ x) = -(x ⬝ᵥ (Q *ᵥ x)) := by
  have hAPA : Aᵀ * (P * A) = P - Q := by
    rw [← Matrix.mul_assoc]
    calc Aᵀ * P * A = (Aᵀ * P * A - P) + P := by abel
      _ = P - Q := by rw [show Aᵀ * P * A - P = -Q from h]; abel
  have h_move : (A *ᵥ x) ⬝ᵥ (P *ᵥ (A *ᵥ x)) = x ⬝ᵥ ((Aᵀ * (P * A)) *ᵥ x) := by
    conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  rw [h_move, hAPA, Matrix.sub_mulVec, dotProduct_sub]
  ring

end LyapunovEquation

end LinearSystems

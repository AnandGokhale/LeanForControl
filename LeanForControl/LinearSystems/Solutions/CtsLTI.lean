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

variable {X : Type*} [Fintype X] [DecidableEq X] (A : Matrix X X ℝ)

/-- **Peano-Baker term for constant `A`** (Hespanha, equation (6.1)).
For a *constant* state matrix `A`, the `k`-th Peano-Baker term
collapses to the closed form `((t-t₀)^k / k!) • A^k`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, equation (6.1). -/
@[blueprint "lem:peanoBakerTerm-const"
  (title := "Peano--Baker terms for a constant matrix")
  (latexEnv := "lemma")
  (statement := /-- For a constant state matrix $A$, the $k$-th Peano--Baker term collapses to
    \[
      \Phi_k(t, t_0) = \frac{(t-t_0)^k}{k!}\,A^k .
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 6, equation (6.1).
  -/)
  (proof := /-- Induction on $k$.  The $k = 0$ term is the identity.  For the step,
    $\Phi_{k+1}(t,t_0) = \int_{t_0}^{t} A\,\Phi_k(s,t_0)\,ds$; substituting the inductive
    hypothesis pulls $A^{k+1}$ out of the integral and leaves
    $\int_{t_0}^{t}(s-t_0)^k ds = (t-t_0)^{k+1}/(k+1)$, which combines with $1/k!$ to give
    $1/(k+1)!$. -/)]
theorem peanoBakerTerm_const (k : ℕ) (t t₀ : ℝ) :
    peanoBakerTerm (fun _ => A) k t t₀ = ((t - t₀) ^ k / (k)! : ℝ) • A ^ k := by
  induction k generalizing t with
  | zero =>
    change (1 : Matrix X X ℝ) = _
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

/-- **Peano-Baker series for constant `A`** (Hespanha, equation (6.1)).
For a *constant* state matrix `A`, the continuous-time state transition matrix
is given by the power series `Φ(t,t₀) = Σ_{k=0}^∞ ((t-t₀)^k / k!) A^k` — summing
`peanoBakerTerm_const` termwise.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, equation (6.1). -/
@[blueprint "lem:stateTransitionMatrix-const-eq-tsum"
  (title := "The LTI state transition matrix as a series")
  (latexEnv := "lemma")
  (statement := /-- For a constant state matrix $A$, the state transition matrix is the power
    series
    \[
      \Phi(t, t_0) = \sum_{k=0}^{\infty} \frac{(t-t_0)^k}{k!}\,A^k .
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 6, equation (6.1).
  -/)
  (proof := /-- Sum \cref{lem:peanoBakerTerm-const} termwise; the Peano--Baker series converges
    for any continuous state matrix, a constant one included. -/)]
theorem stateTransitionMatrix_const_eq_tsum (t t₀ : ℝ) :
    stateTransitionMatrix (fun _ => A) t t₀ = ∑' k, ((t - t₀) ^ k / (k)! : ℝ) • A ^ k := by
  unfold stateTransitionMatrix
  exact tsum_congr fun k => peanoBakerTerm_const A k t t₀

/-- **The matrix exponential as state transition matrix** (Hespanha, equation (6.2)).
For a *constant* state matrix `A`, the continuous-time state transition matrix
collapses to the matrix exponential `Φ(t,t₀) = e^{A(t-t₀)}`. This is what lets every LTV
property already proved for `stateTransitionMatrix` (existence, uniqueness, semigroup,
invertibility, variation of constants) be reused directly for LTI by specialization.

Proof: sum `peanoBakerTerm_const` termwise and match against Mathlib's own series
characterization of `exp` (`NormedSpace.exp_eq_tsum`).

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, equation (6.2). -/
@[blueprint "thm:stateTransitionMatrix-const"
  (title := "The LTI state transition matrix is $e^{A(t-t_{0})}$")
  (statement := /-- For a constant state matrix $A$, the state transition matrix is the matrix
    exponential:
    \[
      \Phi(t, t_0) = e^{A(t-t_0)} .
    \]
    This is the bridge that lets every property already proved for $\Phi$ in the time-varying
    setting — existence, uniqueness, the semigroup law, invertibility, variation of constants —
    be reused for LTI systems by specialization rather than reproved.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 6, equation (6.2).
  -/)
  (proof := /-- Both sides are power series in $A$: \cref{lem:stateTransitionMatrix-const-eq-tsum}
    for the left, the defining series of $\exp$ for the right.  Match them termwise. -/)]
theorem stateTransitionMatrix_const (t t₀ : ℝ) :
    stateTransitionMatrix (fun _ => A) t t₀ = NormedSpace.exp ((t - t₀) • A) := by
  unfold stateTransitionMatrix
  simp only [NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
  refine tsum_congr fun k => ?_
  rw [peanoBakerTerm_const, smul_pow, smul_smul, div_eq_inv_mul]

/-- **LTI uniqueness** (Hespanha, P6.1).
`e^{A(t-t₀)} *ᵥ x₀` is the *unique* solution of `ẋ = Ax`,
`x(t₀) = x₀`, for a *constant* state matrix `A` — a direct corollary of the LTV uniqueness
theorem `stateTransitionMatrix_mulVec_unique`, specialized at `A := fun _ => A` and rewritten
via the bridge lemma `stateTransitionMatrix_const`. No new ODE-theoretic content: uniqueness
for LTI systems is just uniqueness for LTV systems at a constant state matrix.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, Property P6.1. -/
@[blueprint "thm:exp-mulVec-unique"
  (title := "Uniqueness of the LTI state response")
  (statement := /-- Let $A$ be constant and let $z$ be a continuous integral solution of
    $\dot x = Ax$, $x(t_0) = x_0$, on $[t_0, t_1]$.  Then
    $z(t) = e^{A(t-t_0)}x_0$ for every $t$ in that interval.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 6, Property P6.1.
  -/)
  (proof := /-- The time-varying uniqueness theorem applied at the constant state matrix
    $A(\cdot) \equiv A$, whose bound $\|A(t)\| \le \|A\|$ is immediate, then rewritten through
    \cref{thm:stateTransitionMatrix-const}.  There is no new ODE content: uniqueness for LTI is
    uniqueness for LTV at a constant matrix. -/)]
theorem exp_mulVec_unique {t₀ t₁ : ℝ} (x₀ : X → ℝ)
    {z : ℝ → X → ℝ} (hz : IsIntegralSolution t₀ t₁ z x₀ (fun _ v => A *ᵥ v))
    (hz_cont : ContinuousOn z (Set.uIcc t₀ t₁)) :
    ∀ t ∈ Set.uIcc t₀ t₁, z t = NormedSpace.exp ((t - t₀) • A) *ᵥ x₀ := by
  intro t ht
  have := stateTransitionMatrix_mulVec_unique (A := fun _ => A) continuous_const
    (M := ‖A‖) (fun _ _ => le_refl _) x₀ hz hz_cont t ht
  rwa [stateTransitionMatrix_const] at this

/-- **Columns of the matrix exponential** (Hespanha, P6.2).
For every fixed `t₀`, the `i`-th column of `e^{A(t-t₀)}` is the unique solution to
`ẋ = Ax`, `x(t₀) = eᵢ`, where `eᵢ` is the `i`-th standard basis vector — the column-restatement
of `exp_mulVec_unique`, a direct corollary of the LTV theorem `stateTransitionMatrix_col_unique`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, Property P6.2. -/
@[blueprint "thm:exp-col-unique"
  (title := "Columns of the LTI state transition matrix")
  (statement := /-- Let $A$ be constant.  For each $i$, the $i$-th column of $e^{A(t-t_0)}$ is
    the unique continuous integral solution of $\dot x = Ax$ with $x(t_0) = e_i$, the $i$-th
    standard basis vector.  Equivalently, the columns of the matrix exponential are the
    solutions from the standard basis.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 6, Property P6.2.
  -/)
  (proof := /-- \cref{thm:exp-mulVec-unique} at $x_0 = e_i$, in the column form supplied by the
    time-varying column-uniqueness theorem. -/)]
theorem exp_col_unique {t₀ t₁ : ℝ} (i : X)
    {z : ℝ → X → ℝ} (hz : IsIntegralSolution t₀ t₁ z (Pi.single i 1) (fun _ v => A *ᵥ v))
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

/-! ## The time-invariant forced response

For a time-invariant system the state transition matrix is the matrix exponential
(`stateTransitionMatrix_const`), so the variation-of-constants formula collapses to the closed
form every textbook writes. -/

section TimeInvariant

variable {U Y : Type*} [Fintype U] {u : ℝ → U → ℝ}

/-- **Variation of constants, time-invariant case.** For constant `A` and `B` the forced
response is the closed form

    x(t) = e^{A(t-t₀)} x₀ + ∫ τ in t₀..t, e^{A(t-τ)} B u(τ) dτ.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6. -/
@[blueprint "lem:forcedResponse-timeInvariant"
  (title := "Forced response of a time-invariant system")
  (latexEnv := "lemma")
  (statement := /-- For constant $A$ and $B$ the forced response (\cref{def:forcedResponse})
    is
    \[
      x(t) = e^{A(t-t_0)}x_0 + \int_{t_0}^{t} e^{A(t-\tau)}\,B\,u(\tau)\,\mathrm{d}\tau .
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 6.
  -/)
  (proof := /-- \cref{thm:stateTransitionMatrix-const} identifies $\Phi$ with the matrix
    exponential, applied once to the homogeneous term and once under the integral sign. -/)]
theorem forcedResponse_timeInvariant (B : Matrix X U ℝ) (u : ℝ → U → ℝ) (t₀ : ℝ)
    (x₀ : X → ℝ) (t : ℝ) :
    forcedResponse (fun _ => A) (fun _ => B) u t₀ x₀ t
      = NormedSpace.exp ((t - t₀) • A) *ᵥ x₀
        + ∫ τ in t₀..t, NormedSpace.exp ((t - τ) • A) *ᵥ (B *ᵥ u τ) := by
  change stateTransitionMatrix (fun _ => A) t t₀ *ᵥ x₀ +
      (∫ τ in t₀..t, stateTransitionMatrix (fun _ => A) t τ *ᵥ (B *ᵥ u τ)) = _
  rw [stateTransitionMatrix_const]
  congr 1
  exact intervalIntegral.integral_congr fun τ _ => by rw [stateTransitionMatrix_const]

namespace ContinuousLinearSystem.timeInvariant

/-- The closed-form response of a time-invariant system is a trajectory of that system. -/
@[blueprint "thm:isTrajectory-timeInvariant"
  (title := "The time-invariant response is a trajectory")
  (statement := /-- For a time-invariant system (\cref{def:ctsLinearSystem-timeInvariant}) with
    continuous input $u$, the closed form
    \[
      t \mapsto e^{A(t-t_0)}x_0 + \int_{t_0}^{t} e^{A(t-\tau)}\,B\,u(\tau)\,\mathrm{d}\tau
    \]
    is a trajectory (\cref{def:ctsLinearSystem-isTrajectory}) of that system. -/)
  (proof := /-- \cref{thm:isTrajectory-forcedResponse} at the time-invariant system, whose
    coefficient maps are constant and so continuous, rewritten by
    \cref{lem:forcedResponse-timeInvariant}. -/)]
theorem isTrajectory (B : Matrix X U ℝ) (C : Matrix Y X ℝ) (D : Matrix Y U ℝ)
    (hu : Continuous u) (t₀ : ℝ) (x₀ : X → ℝ) :
    (timeInvariant A B C D).IsTrajectory u
      (fun t => NormedSpace.exp ((t - t₀) • A) *ᵥ x₀
        + ∫ τ in t₀..t, NormedSpace.exp ((t - τ) • A) *ᵥ (B *ᵥ u τ)) := by
  have h : (timeInvariant A B C D).IsTrajectory u
      (forcedResponse (fun _ => A) (fun _ => B) u t₀ x₀) :=
    isTrajectory_forcedResponse (timeInvariant A B C D) continuous_const continuous_const hu t₀ x₀
  rwa [funext fun t => forcedResponse_timeInvariant A B u t₀ x₀ t] at h

end ContinuousLinearSystem.timeInvariant

end TimeInvariant

end LinearSystems

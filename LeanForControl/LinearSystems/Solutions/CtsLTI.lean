import Mathlib.Analysis.CStarAlgebra.Matrix
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
open Matrix MeasureTheory intervalIntegral WithLp

variable {X : Type*} [Fintype X] [DecidableEq X] (A : Matrix X X ℝ)

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

namespace ContinuousLTI

omit [Fintype U] in
/-- For an LTI system the state transition operator is the matrix exponential:
`Φ(t, t₀) = e^{A (t - t₀)}`, acting on Euclidean states. -/
theorem stateTransition_toLTV (sys : ContinuousLTI X U Y ℝ) (t t₀ : ℝ) :
    sys.toLTV.stateTransition t t₀ =
      toEuclideanCLM (n := X) (𝕜 := ℝ) (NormedSpace.exp ((t - t₀) • sys.A)) := by
  rw [ContinuousLTV.stateTransition, show sys.toLTV.A = fun _ => sys.A from rfl,
    stateTransitionMatrix_const, NormedSpace.map_exp _ continuous_toEuclideanCLM, map_smul]

/-- The closed-form response of an LTI system is a trajectory of that system. -/
@[blueprint "thm:isTrajectory-timeInvariant"
  (title := "The LTI response is a trajectory")
  (statement := /-- For an LTI system (\cref{def:continuousLTI}) with continuous input $u$, the
    closed form
    \[
      t \mapsto e^{A(t-t_0)}x_0 + \int_{t_0}^{t} e^{A(t-\tau)}\,B\,u(\tau)\,\mathrm{d}\tau
    \]
    is a trajectory (\cref{def:continuousLTV-isTrajectory}) of that system. -/)
  (proof := /-- \cref{thm:isTrajectory-forcedResponse} at the LTV system of the LTI system
    (\cref{def:continuousLTI-toLTV}), whose coefficient maps are constant and so continuous,
    rewritten by \cref{lem:forcedResponse-timeInvariant}. -/)]
theorem isTrajectory [DecidableEq U] (sys : ContinuousLTI X U Y ℝ) {v : ℝ → EuclideanSpace ℝ U}
    (hv : Continuous v) (t₀ : ℝ) (x₀ : X → ℝ) :
    sys.IsTrajectory v
      (fun t => toLp 2 (NormedSpace.exp ((t - t₀) • sys.A) *ᵥ x₀
        + ∫ τ in t₀..t, NormedSpace.exp ((t - τ) • sys.A) *ᵥ (sys.B *ᵥ (v τ).ofLp))) := by
  have h := ContinuousLTV.isTrajectory_forcedResponse sys.toLTV continuous_const continuous_const
    hv t₀ x₀
  simpa only [show sys.toLTV.A = fun _ => sys.A from rfl,
    show sys.toLTV.B = fun _ => sys.B from rfl, forcedResponse_timeInvariant] using h

end ContinuousLTI

end TimeInvariant

end LinearSystems

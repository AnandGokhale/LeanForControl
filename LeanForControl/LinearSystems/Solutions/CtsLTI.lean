import LeanForControl.LinearSystems.Solutions.CtsLTV
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Architect

/-!
# Continuous-time LTI solutions: the matrix exponential

The LTV solution theory (`CtsLTV.lean`) specialized to a *constant* state matrix `A`: the state
transition operator is the matrix exponential `Φ(t,t₀) = e^{A(t-t₀)}` (6.2), so every LTV
property (existence, uniqueness, semigroup, variation of constants) holds for LTI by
specialization. The collapse of the Peano-Baker series itself, `stateTransitionMatrix_const`, is
proved in any Banach algebra in `PeanoBaker.lean`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6.
-/

namespace LinearSystems

open Matrix

variable {X U Y : Type*} [Fintype X] [Fintype U] [Fintype Y] [DecidableEq X] [DecidableEq U]

/-!
## P6.3 and P6.5 are proved elsewhere

`MatrixAlgebra/Exponential.lean` carries the semigroup property `e^{At} e^{Aτ} = e^{A(t+τ)}`
(P6.3) and the finite-polynomial form `e^{At} = Σ αᵢ(t) Aⁱ` (P6.5, via Cayley-Hamilton (6.6)).
Both are statements about `exp` and `A` alone, so neither needs the solution theory.
-/

namespace ContinuousLTI

-- `map_exp` needs some norm on matrices; `exp` itself does not depend on which.
open scoped Matrix.Norms.Operator in
/-- For an LTI system the state transition operator is the matrix exponential:
`Φ(t, t₀) = e^{A (t - t₀)}`, acting on Euclidean states (Hespanha, (6.2)). -/
@[blueprint "thm:continuousLTI-stateTransition-toLTV"
  (title := "The LTI state transition operator is $e^{A(t-t_{0})}$")
  (statement := /-- For an LTI system, $\Phi(t, t_0) = e^{A(t-t_0)}$, acting on Euclidean states.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 6, equation (6.2). -/)
  (proof := /-- \cref{thm:stateTransitionMatrix-const} in the algebra of operators, and
    $\exp$ commutes with the continuous algebra map from matrices to operators. -/)]
theorem stateTransition_toLTV (sys : ContinuousLTI X U Y ℝ) (t t₀ : ℝ) :
    sys.toLTV.stateTransition t t₀ =
      toEuclideanCLM (n := X) (𝕜 := ℝ) (NormedSpace.exp ((t - t₀) • sys.A)) := by
  rw [ContinuousLTV.stateTransition,
    show sys.toLTV.A = fun _ => toEuclideanCLM (n := X) (𝕜 := ℝ) sys.A from rfl,
    stateTransitionMatrix_const,
    NormedSpace.map_exp _ continuous_toEuclideanCLM, map_smul]

/-- **LTI uniqueness** (Hespanha, P6.1): every trajectory of the unforced LTI system is
`e^{A(t-t₀)} x(t₀)`. -/
@[blueprint "thm:continuousLTI-eq-exp-of-isTrajectoryOn"
  (title := "Uniqueness of the LTI state response")
  (statement := /-- Let $x$ be a trajectory of the unforced LTI system on $[t_0, t_1]$.  Then
    $x(t) = e^{A(t-t_0)}x(t_0)$ for every $t$ in that interval.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 6, Property P6.1. -/)
  (proof := /-- \cref{thm:eq-homogeneousResponse-of-isTrajectoryOn} at the constant state
    matrix, rewritten by \cref{thm:continuousLTI-stateTransition-toLTV}. -/)]
theorem eq_exp_of_isTrajectoryOn (sys : ContinuousLTI X U Y ℝ) {x : ℝ → EuclideanSpace ℝ X}
    {t₀ t₁ : ℝ} (hx : sys.IsTrajectoryOn 0 x (Set.Icc t₀ t₁)) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    x t = toEuclideanCLM (n := X) (𝕜 := ℝ) (NormedSpace.exp ((t - t₀) • sys.A)) (x t₀) := by
  rw [← stateTransition_toLTV]
  exact sys.toLTV.eq_homogeneousResponse_of_isTrajectoryOn continuous_const hx ht

/-- **Variation of constants, time-invariant case.** For an LTI system the forced response is the
closed form `x(t) = e^{A(t-t₀)} x₀ + ∫ τ in t₀..t, e^{A(t-τ)} B u(τ) dτ`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6. -/
@[blueprint "lem:forcedResponse-timeInvariant"
  (title := "Forced response of a time-invariant system")
  (latexEnv := "lemma")
  (statement := /-- For an LTI system the forced response (\cref{def:forcedResponse}) is
    \[
      x(t) = e^{A(t-t_0)}x_0 + \int_{t_0}^{t} e^{A(t-\tau)}\,B\,u(\tau)\,\mathrm{d}\tau .
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 6.
  -/)
  (proof := /-- \cref{thm:continuousLTI-stateTransition-toLTV}, applied once to the homogeneous
    term and once under the integral sign. -/)]
theorem forcedResponse_toLTV (sys : ContinuousLTI X U Y ℝ) (u : ℝ → EuclideanSpace ℝ U)
    (t₀ : ℝ) (x₀ : EuclideanSpace ℝ X) (t : ℝ) :
    sys.toLTV.forcedResponse u t₀ x₀ t =
      toEuclideanCLM (n := X) (𝕜 := ℝ) (NormedSpace.exp ((t - t₀) • sys.A)) x₀ +
        ∫ τ in t₀..t, toEuclideanCLM (n := X) (𝕜 := ℝ) (NormedSpace.exp ((t - τ) • sys.A))
          (toEuclideanLin sys.B (u τ)) := by
  simp only [ContinuousLTV.forcedResponse, stateTransition_toLTV]
  rfl

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
theorem isTrajectory (sys : ContinuousLTI X U Y ℝ) {u : ℝ → EuclideanSpace ℝ U}
    (hu : Continuous u) (t₀ : ℝ) (x₀ : EuclideanSpace ℝ X) :
    sys.IsTrajectory u (fun t =>
      toEuclideanCLM (n := X) (𝕜 := ℝ) (NormedSpace.exp ((t - t₀) • sys.A)) x₀ +
        ∫ τ in t₀..t, toEuclideanCLM (n := X) (𝕜 := ℝ) (NormedSpace.exp ((t - τ) • sys.A))
          (toEuclideanLin sys.B (u τ))) := by
  convert sys.toLTV.isTrajectory_forcedResponse continuous_const continuous_const hu t₀ x₀
    using 1
  exact funext fun t => (forcedResponse_toLTV sys u t₀ x₀ t).symm

end ContinuousLTI

end LinearSystems

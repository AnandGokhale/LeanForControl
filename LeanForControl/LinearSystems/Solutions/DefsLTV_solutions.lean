import LeanForControl.LinearSystems.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Architect

/-!
# Definitions for continuous-time solutions

Every `def` and `noncomputable def` for the `Solutions` directory lives here, apart from the
theorems proved about them (`LTV_solutions.lean`), per the project convention: definitions live
apart from theorems.

Unlike the rest of `LinearSystems/`, this file is about a genuinely *time-varying* state
matrix `A : ℝ → Matrix (Fin n) (Fin n) ℝ`, not the constant `A` fixed by `Basic.lean`'s
conventions for the LTI-only files.

`Matrix (Fin n) (Fin n) ℝ` carries no default norm instance in Mathlib (there are several
natural choices). We fix the `L∞`-operator norm, `Matrix.Norms.Operator`, throughout this
track: it is the one under which matrix multiplication is submultiplicative
(`‖A * B‖ ≤ ‖A‖ * ‖B‖`), which the Peano-Baker series' convergence proof needs.

* `peanoBakerTerm` — the `k`-th iterated-integral term of the Peano-Baker series.
* `stateTransitionMatrix` — the Peano-Baker series itself,
  `Φ(t, t₀) := ∑' k, peanoBakerTerm A k t t₀`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5.
-/

namespace LinearSystems

open scoped Matrix.Norms.Operator

variable {n : ℕ}

/-- The `k`-th term of the Peano-Baker series for a time-varying state matrix `A`:
`peanoBakerTerm A 0 t t₀ = 1` and
`peanoBakerTerm A (k+1) t t₀ = ∫ s in t₀..t, A s * peanoBakerTerm A k s t₀`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5 (Peano-Baker series). -/
@[blueprint "def:peanoBakerTerm"
  (statement := /-- The $k$-th term of the Peano--Baker series for a time-varying state
    matrix $A(t)$:
    \[
      P_0(t,t_0) := I, \qquad
      P_{k+1}(t,t_0) := \int_{t_0}^{t} A(s)\, P_k(s,t_0)\,\mathrm{d}s.
    \] -/)]
noncomputable def peanoBakerTerm (A : ℝ → Matrix (Fin n) (Fin n) ℝ) :
    ℕ → ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ
  | 0,     _, _  => 1
  | k + 1, t, t₀ => ∫ s in t₀..t, A s * peanoBakerTerm A k s t₀

/-- The *state transition matrix* of a time-varying linear system `ẋ = A(t) x`, given by the
Peano-Baker series `Φ(t, t₀) := ∑' k, peanoBakerTerm A k t t₀`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Theorem 5.1
(Peano-Baker series). -/
@[blueprint "def:stateTransitionMatrix"
  (statement := /-- The \emph{state transition matrix} $\Phi(t,t_0)$, given by the
    Peano--Baker series
    \[
      \Phi(t,t_0) := \sum_{k=0}^{\infty} P_k(t,t_0).
    \] -/)]
noncomputable def stateTransitionMatrix (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (t t₀ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑' k, peanoBakerTerm A k t t₀

end LinearSystems

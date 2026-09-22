import LeanForControl.LinearSystems.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Architect

/-!
# Definitions for discrete-time solutions

Every `def` and `noncomputable def` for the `Solutions` directory's discrete-time track lives
here, apart from the theorems proved about them (`DiscLTV.lean`), per the project convention:
definitions live apart from theorems.

Like `DefsCtsLTV.lean`, this file is about a genuinely *time-varying* state matrix
`A : ℕ → Matrix (Fin n) (Fin n) ℝ`, but now for the discrete-time system `x(t+1) = A(t) x(t)`.

* `discStateTransitionMatrix` — the discrete-time state transition matrix,
  `Φ(t, t₀) := A(t-1) A(t-2) ⋯ A(t₀+1) A(t₀)` for `t > t₀`, `Φ(t₀, t₀) := I`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Section 5.3.
-/

namespace LinearSystems

variable {n : ℕ}

/-- The *discrete-time state transition matrix* of a time-varying linear system
`x(t+1) = A(t) x(t)`:
`Φ(t, t₀) := A(t-1) A(t-2) ⋯ A(t₀+1) A(t₀)` for `t > t₀`, and `Φ(t₀, t₀) := I`. Formalized as the
product, in order, of `A` over `[t₀, t)`; for `t ≤ t₀` this degenerates to the empty product `I`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, equation (5.11). -/
@[blueprint "def:discStateTransitionMatrix"
  (statement := /-- The discrete-time \emph{state transition matrix} $\Phi(t,t_0)$:
    \[
      \Phi(t,t_0) := \begin{cases}
        I & t = t_0 \\
        A(t-1)A(t-2)\cdots A(t_0+1)A(t_0) & t > t_0.
      \end{cases}
    \] -/)]
noncomputable def discStateTransitionMatrix (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (t t₀ : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((List.range (t - t₀)).map (fun k => A (t - 1 - k))).prod

end LinearSystems

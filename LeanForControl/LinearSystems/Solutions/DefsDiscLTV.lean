import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Architect

/-!
# Definitions for discrete-time solutions

Every `def` and `noncomputable def` for the `Solutions` directory's discrete-time track lives
here, apart from the theorems proved about them (`DiscLTV.lean`), per the project convention:
definitions live apart from theorems.

Like `DefsCtsLTV.lean`, this file is about a genuinely *time-varying* state matrix
`A : ℕ → Matrix X X ℝ`, but now for the discrete-time system `x(t+1) = A(t) x(t)`.

* `discStateTransitionMatrix` — the discrete-time state transition matrix,
  `Φ(t, t₀) := A(t-1) A(t-2) ⋯ A(t₀+1) A(t₀)` for `t > t₀`, `Φ(t₀, t₀) := I`.
* `discForcedResponse` — the discrete variation-of-constants formula
  `x(t) = Φ(t, t₀) x₀ + Σ_{τ=t₀}^{t-1} Φ(t, τ+1) B(τ) u(τ)`.
* `discHomogeneousResponse` — its unforced part, `x(t) = Φ(t, t₀) x₀`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Section 5.3.
-/

namespace LinearSystems

open Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The *discrete-time state transition matrix* of a time-varying linear system
`x(t+1) = A(t) x(t)`:
`Φ(t, t₀) := A(t-1) A(t-2) ⋯ A(t₀+1) A(t₀)` for `t > t₀`, and `Φ(t₀, t₀) := I`. Formalized as the
product, in order, of `A` over `[t₀, t)`; for `t ≤ t₀` this degenerates to the empty product `I`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, equation (5.11). -/
@[blueprint "def:discStateTransitionMatrix"
  (title := "Discrete state transition matrix")
  (statement := /-- The discrete-time \emph{state transition matrix} $\Phi(t,t_0)$:
    \[
      \Phi(t,t_0) := \begin{cases}
        A(t-1)A(t-2)\cdots A(t_0+1)A(t_0) & t > t_0, \\
        I & t \le t_0.
      \end{cases}
    \]
    Formally, the ordered product of $A$ over $[t_0, t)$, which for $t \le t_0$ is the empty
    product $I$.  The system runs forward only, so the $t < t_0$ branch carries no meaning; it
    is there to make the definition total.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, equation (5.11).
  -/)]
noncomputable def discStateTransitionMatrix (A : ℕ → Matrix X X ℝ) (t t₀ : ℕ) :
    Matrix X X ℝ :=
  ((List.range (t - t₀)).map (fun k => A (t - 1 - k))).prod

variable {U : Type*} [Fintype U]

/-- The *forced response* of `x(t+1) = A(t) x(t) + B(t) u(t)` from the state `x₀` at time `t₀`,
given by the discrete variation-of-constants formula
`x(t) = Φ(t, t₀) x₀ + Σ_{τ=t₀}^{t-1} Φ(t, τ+1) B(τ) u(τ)`.

It solves the recursion forward from `t₀` only: for `t < t₀` the sum is empty and the value
is `x₀`, which carries no meaning.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Section 5.3. -/
@[blueprint "def:discForcedResponse"
  (title := "Forced response, discrete time")
  (statement := /-- The \emph{forced response} of $x(t+1) = A(t)x(t) + B(t)u(t)$ from the state
    $x_0$ at time $t_0$,
    \[
      x(t) = \Phi(t, t_0)\,x_0 + \sum_{\tau=t_0}^{t-1} \Phi(t, \tau+1)\,B(\tau)\,u(\tau),
    \]
    with $\Phi$ the discrete state transition matrix (\cref{def:discStateTransitionMatrix}).
    It solves the recursion forward from $t_0$ only.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, Section 5.3.
  -/)]
noncomputable def discForcedResponse (A : ℕ → Matrix X X ℝ) (B : ℕ → Matrix X U ℝ)
    (u : ℕ → U → ℝ) (t₀ : ℕ) (x₀ : X → ℝ) : ℕ → X → ℝ :=
  fun t => discStateTransitionMatrix A t t₀ *ᵥ x₀ +
    ∑ τ ∈ Finset.Ico t₀ t, discStateTransitionMatrix A t (τ + 1) *ᵥ (B τ *ᵥ u τ)

/-- The *homogeneous response* of `x(t+1) = A(t) x(t)` from the state `x₀` at time `t₀`,
namely `x(t) = Φ(t, t₀) x₀`: the forced response with the input switched off, and the object
stability is stated about.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Section 5.3. -/
@[blueprint "def:discHomogeneousResponse"
  (title := "Homogeneous response, discrete time")
  (statement := /-- The \emph{homogeneous response} of $x(t+1) = A(t)x(t)$ from the state $x_0$
    at time $t_0$, $x(t) = \Phi(t, t_0)\,x_0$: the forced response
    (\cref{def:discForcedResponse}) with the input switched off.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, Section 5.3.
  -/)]
noncomputable def discHomogeneousResponse (A : ℕ → Matrix X X ℝ) (t₀ : ℕ) (x₀ : X → ℝ) :
    ℕ → X → ℝ :=
  fun t => discStateTransitionMatrix A t t₀ *ᵥ x₀

end LinearSystems

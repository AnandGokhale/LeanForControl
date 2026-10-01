import LeanForControl.LinearSystems.Solutions.DefsCtsLTV
import LeanForControl.Stability.DefsNonAutonomous
import Mathlib.Analysis.CStarAlgebra.Matrix
import Architect

/-!
# `LinearSystems.Stability.Continuous.DefsLyapunovLTV`

The two objects a continuous-time linear time-varying system contributes to the
non-autonomous stability track of `Stability/DefsNonAutonomous.lean`: its vector field, and
its state transition matrix read as an operator on the Euclidean state space.

Nothing here is a stability notion. Hespanha's Lyapunov-stability definition for `(CLTV)` is
*not* re-defined: the point of this pair of files is that his conditions on `Φ(t,t₀)` are
theorems about `StableNA`, `AsymptoticStableNA` and `ExponentiallyStableNA`, proved in
`LyapunovLTV.lean`, rather than a second definition of stability.

## Why the state space changes shape here

`LinearSystems/` works with states in `Fin n → ℝ` under the `L∞` norm, the setting in which
`Matrix.Norms.Operator` makes matrix multiplication submultiplicative. `Stability/` works with
states in `EuclideanSpace ℝ (Fin n)`. The two are the same type up to `WithLp.ofLp`, but carry
different norms, so a matrix acts on the Euclidean side through `Matrix.toEuclideanCLM` — the
same bridge `Stability/LyapunovIndirect/DefsDynamics.lean` already uses for the autonomous
linearization.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8.
-/

namespace LinearSystems

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The time-varying linear vector field `f(t, x) = A(t) x` of the system `ẋ = A(t) x`,
on the repository's Euclidean state convention.

The time-varying counterpart of `affineLinearVectorField`, which fixes `A` and moves the
equilibrium; here the equilibrium is always the origin and it is `A` that moves. -/
@[blueprint "def:linearVectorField"
  (title := "Time-varying linear vector field")
  (statement := /-- For a matrix-valued map $A : \mathbb{R} \to \mathbb{R}^{n \times n}$, the
    \emph{linear vector field} is
    \[
      f(t, x) = A(t)\, x,
    \]
    the right-hand side of the homogeneous time-varying system $\dot x = A(t)x$. -/)]
noncomputable def linearVectorField (A : ℝ → Matrix (Fin n) (Fin n) ℝ) : ℝ → ℝⁿ → ℝⁿ :=
  fun t x => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (A t) x

/-- The state transition matrix `Φ(t, t₀)` of `ẋ = A(t) x`, read as a continuous linear
operator on `ℝⁿ` rather than as a matrix.

Only the *operator* is needed on the stability side: the textbook conditions are bounds on
`‖Φ(t, t₀) x₀‖`, and an operator norm is the right home for them. Taking the operator view
also sidesteps a genuine hazard — `Matrix (Fin n) (Fin n) ℝ` carries several scoped norm
instances, and the `L∞` one that `LinearSystems/Solutions/` fixes is not the one that would
match the Euclidean state norm here. -/
@[blueprint "def:stateTransitionCLM"
  (title := "State transition operator")
  (statement := /-- The state transition matrix $\Phi(t,t_0)$
    (\cref{def:stateTransitionMatrix}) read as a continuous linear operator on
    $\mathbb{R}^{n}$, through the identification of a matrix with an endomorphism of
    Euclidean space. -/)]
noncomputable def stateTransitionCLM (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (t t₀ : ℝ) :
    ℝⁿ →L[ℝ] ℝⁿ :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (stateTransitionMatrix A t t₀)

end LinearSystems

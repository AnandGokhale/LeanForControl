import LeanForControl.LinearSystems.Solutions.DiscLTV
import Architect

/-!
# Discrete-time LTI solutions: matrix powers

Theorems specializing the discrete LTV solution theory (`DiscLTV.lean`) to a *constant* state
matrix `A`: the state transition matrix collapses to the matrix power `Φ(t, t₀) = A^(t - t₀)`,
the discrete counterpart of `Φ(t, t₀) = e^{A(t - t₀)}` in `CtsLTI.lean`.

The unforced time-invariant system is the autonomous map `x ↦ A x`, so its trajectories are the
iterates of that map.  `iterate_mulVec` makes this explicit; it is what connects the linear track
to the autonomous discrete-time stability predicates of `Stability.DefsDiscrete`, which are
stated in terms of iterates `f^[k]`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Section 5.3.
-/

namespace LinearSystems

open Matrix

variable {X : Type*} [Fintype X] [DecidableEq X] (A : Matrix X X ℝ)

/-- For a constant state matrix the discrete state transition matrix is a matrix power,
`Φ(t, t₀) = A^(t - t₀)`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Section 5.3. -/
@[blueprint "thm:discStateTransitionMatrix-const"
  (title := "The discrete state transition matrix of an LTI system")
  (statement := /-- For a constant state matrix $A$, the discrete state transition matrix
    (\cref{def:discStateTransitionMatrix}) is $\Phi(t, t_0) = A^{t - t_0}$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, Section 5.3. -/)
  (proof := /-- $\Phi(t, t_0)$ is the ordered product of $t - t_0$ factors, all equal to
    $A$. -/)]
theorem discStateTransitionMatrix_const (t t₀ : ℕ) :
    discStateTransitionMatrix (fun _ => A) t t₀ = A ^ (t - t₀) := by
  simp [discStateTransitionMatrix, List.map_const', List.prod_replicate]

/-- The homogeneous response of `x(t+1) = A x(t)` is `x(t) = A^(t - t₀) x₀`. -/
@[blueprint "lem:discHomogeneousResponse-timeInvariant"
  (title := "Homogeneous response of a discrete LTI system")
  (latexEnv := "lemma")
  (statement := /-- For a constant state matrix $A$, the homogeneous response
    (\cref{def:discHomogeneousResponse}) is $x(t) = A^{t - t_0} x_0$. -/)
  (proof := /-- \cref{thm:discStateTransitionMatrix-const}. -/)]
theorem discHomogeneousResponse_timeInvariant (t₀ : ℕ) (x₀ : X → ℝ) (t : ℕ) :
    discHomogeneousResponse (fun _ => A) t₀ x₀ t = A ^ (t - t₀) *ᵥ x₀ := by
  simp [discHomogeneousResponse, discStateTransitionMatrix_const]

/-- Iterating the linear map `x ↦ A x` `n` times is multiplication by `Aⁿ`. -/
@[blueprint "lem:iterate-mulVec"
  (title := "Iterates of a linear map are matrix powers")
  (latexEnv := "lemma")
  (statement := /-- The $n$-th iterate of $x \mapsto Ax$ is $x \mapsto A^{n}x$. -/)
  (proof := /-- Induction on $n$, using $A^{n+1} = A\,A^{n}$. -/)]
theorem iterate_mulVec (n : ℕ) (x : X → ℝ) : (fun z => A *ᵥ z)^[n] x = A ^ n *ᵥ x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', Matrix.mulVec_mulVec]

namespace DiscreteLinearSystem.timeInvariant

variable {U Y : Type*} [Fintype U] (B : Matrix X U ℝ) (C : Matrix Y X ℝ) (D : Matrix Y U ℝ)

omit [DecidableEq X] in
/-- Unforced, a time-invariant system is the autonomous map `x ↦ A x`, at every time. -/
@[simp, blueprint "lem:discLinearSystem-timeInvariant-vectorField-zero"
  (title := "The unforced discrete LTI system is autonomous")
  (latexEnv := "lemma")
  (statement := /-- With the input switched off, the state equation of a time-invariant system
    (\cref{def:discLinearSystem-timeInvariant}) is the map $x \mapsto Ax$ at every time $k$. -/)
  (proof := /-- \cref{lem:discLinearSystem-vectorField-zero-input} at constant
    coefficients. -/)]
theorem vectorField_zero (k : ℕ) :
    (timeInvariant A B C D).vectorField 0 k = fun z => A *ᵥ z := by
  simp

/-- Every trajectory of the unforced time-invariant system is `x(t) = A^(t - t₀) x(t₀)`. -/
@[blueprint "thm:discLinearSystem-timeInvariant-eq-pow-mulVec"
  (title := "Unforced trajectories of a discrete LTI system")
  (statement := /-- If $x$ is a trajectory of the unforced time-invariant system on
    $[t_0, \infty)$ (\cref{def:discLinearSystem-isTrajectoryOn}), then
    $x(t) = A^{t - t_0} x(t_0)$ for every $t \ge t_0$. -/)
  (proof := /-- \cref{thm:eq-discHomogeneousResponse-of-isTrajectoryOn}, rewritten by
    \cref{lem:discHomogeneousResponse-timeInvariant}. -/)]
theorem eq_pow_mulVec_of_isTrajectoryOn {x : ℕ → X → ℝ} {t₀ : ℕ}
    (hx : (timeInvariant A B C D).IsTrajectoryOn 0 x (Set.Ici t₀)) {t : ℕ} (ht : t₀ ≤ t) :
    x t = A ^ (t - t₀) *ᵥ x t₀ := by
  rw [eq_discHomogeneousResponse_of_isTrajectoryOn _ hx ht]
  exact discHomogeneousResponse_timeInvariant A t₀ (x t₀) t

end DiscreteLinearSystem.timeInvariant

end LinearSystems

import LeanForControl.LinearSystems.Solutions.CtsLTI
import LeanForControl.LinearSystems.Stability.Continuous.Hurwitz
import LeanForControl.LinearSystems.Stability.Continuous.LyapunovEquation
import LeanForControl.LinearSystems.Stability.Continuous.LyapunovLTV
import Architect

/-!
# `LinearSystems.Stability.Continuous.LyapunovLTI`

Hespanha's Theorem 8.1: for a *time-invariant* system `ẋ = A x`, the stability notions of
Definition 8.1 are eigenvalue conditions on `A`.

`LyapunovLTV.lean` turned every clause of Definition 8.1 into a bound on the state transition
matrix `Φ(t, t₀)`. For a constant `A` that matrix is `e^{A(t-t₀)}`
(`stateTransitionMatrix_const`), and `Hurwitz.lean` says what the Hurwitz condition means for
`e^{At}`. This file is the bridge between them.

## Contents

* **Theorem 8.1(2)** — `ContinuousLinearSystem.timeInvariant.asymptoticStableNA_iff_isHurwitz`:
  asymptotic stability holds exactly when every eigenvalue of `A` has strictly negative real
  part.
* **Theorem 8.1(3)** — `ContinuousLinearSystem.timeInvariant.exponentiallyStableNA_iff_isHurwitz`:
  and so does exponential stability, under the same condition.

Both are in the `ContinuousLinearSystem.timeInvariant` namespace, so that with
`open ContinuousLinearSystem` they read `timeInvariant.asymptoticStableNA_iff_isHurwitz`.

## Scope

Clauses (1) and (4) ask that the Jordan blocks at eigenvalues on the imaginary axis be
`1 × 1`. Mathlib has no Jordan normal form, so those clauses need a Jordan-free
restatement — semisimplicity of `A` on its imaginary-axis spectrum — and are not attempted
here. See `MatrixAlgebra/plan.md`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.1.
-/

namespace LinearSystems

open Matrix Set Filter Topology NormedSpace ContinuousLinearSystem
open scoped Matrix.Norms.Operator

variable {X U Y : Type*} [Fintype X] [DecidableEq X] [Fintype U]

namespace ContinuousLinearSystem.timeInvariant

/-! ## Theorem 8.1(2): asymptotic stability -/

omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.1(2).**
The time-invariant system `ẋ = A x` is asymptotically stable if and only if every eigenvalue
of `A` has strictly negative real part.

That this is the *same* condition as exponential stability (Theorem 8.1(3)) is a genuine
feature of the time-invariant case; for a time-varying `A(t)` the two differ, as
`ẋ = -x / (1 + t)` shows. The equivalence between them is not recorded here — it belongs with
the Lyapunov-equation development of Theorem 8.2.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.1(2). -/
@[blueprint "thm:asymptoticStableNA-iff-isHurwitz"
  (title := "Asymptotic stability of a linear time-invariant system")
  (statement := /-- Consider the time-invariant system $\dot x = Ax$ with $A$ a real square
    matrix.

    The origin is an asymptotically stable equilibrium
    (\cref{def:asymptoticStableNA}) if and only if $A$ is Hurwitz
    (\cref{def:stability-isHurwitz}), that is, every eigenvalue of $A$ has strictly negative
    real part.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.1(2).
  -/)
  (proof := /-- For constant $A$ the state transition matrix is $e^{A(t-t_0)}$
    (\cref{thm:stateTransitionMatrix-const}), so
    \cref{thm:asymptoticStableNA-iff-decayingHomogeneousResponse} turns the statement into one
    about $e^{At}x_0$.

    If the response converges then $A$ is Hurwitz
    (\cref{thm:isHurwitz-of-tendsto-exp-mulVec}).  Conversely a Hurwitz $A$ gives an
    exponentially decaying envelope for $\|e^{At}x_0\|$
    (\cref{thm:isHurwitz-exists-norm-exp-mulVec-le}); the envelope is bounded by $k\|x_0\|$,
    which supplies the stability half, and tends to zero
    (\cref{lem:tendsto-const-mul-exp-neg}), which supplies the attractivity half. -/)]
theorem asymptoticStableNA_iff_isHurwitz
    (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix Y X ℝ) (D : Matrix Y U ℝ) :
    AsymptoticStableNA ((timeInvariant A B C D).vectorField 0) (0 : X → ℝ) ↔
      IsHurwitz A := by
  classical
  have hcoeff : (timeInvariant A B C D).A = fun _ => A := rfl
  have hhr : ∀ (t₀ : ℝ) (x₀ : X → ℝ), homogeneousResponse (fun _ => A) t₀ x₀
      = fun t => exp ((t - t₀) • A) *ᵥ x₀ := by
    intro t₀ x₀
    funext t
    simp [homogeneousResponse, stateTransitionMatrix_const]
  rw [asymptoticStableNA_iff_decayingHomogeneousResponse _ (by simpa using continuous_const)]
  simp only [hcoeff, hhr]
  constructor
  · rintro ⟨-, hconv⟩
    refine isHurwitz_of_tendsto_exp_mulVec A fun x => ?_
    simpa using hconv 0 le_rfl x
  · intro hA
    obtain ⟨k, hk, γ, hγ, hbd⟩ := hA.exists_norm_exp_mulVec_le
    refine ⟨fun t₀ _ x₀ => ⟨k * ‖x₀‖, fun t ht => ?_⟩, fun t₀ _ x₀ => ?_⟩
    · calc ‖exp ((t - t₀) • A) *ᵥ x₀‖
          ≤ k * Real.exp (-γ * (t - t₀)) * ‖x₀‖ := hbd (t - t₀) (by linarith) x₀
        _ ≤ k * 1 * ‖x₀‖ := by
            gcongr
            exact Real.exp_le_one_iff.mpr
              (by simpa [neg_mul] using mul_nonneg hγ.le (sub_nonneg.2 ht))
        _ = k * ‖x₀‖ := by ring
    · refine squeeze_zero_norm' ?_ (tendsto_const_mul_exp_neg (k * ‖x₀‖) t₀ hγ)
      filter_upwards [eventually_ge_atTop t₀] with t ht
      simpa [mul_comm, mul_assoc, mul_left_comm] using hbd (t - t₀) (by linarith) x₀

/-! ## Theorem 8.1(3): exponential stability -/

-- `DecidableEq X` is needed only by the `L∞` operator norm inside the proof, not by the
-- statement, so it is reinstated there with `classical`.
omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.1(3).**
The time-invariant system `ẋ = A x` is exponentially stable if and only if every eigenvalue
of `A` has strictly negative real part.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.1(3). -/
@[blueprint "thm:exponentiallyStableNA-iff-isHurwitz"
  (title := "Exponential stability of a linear time-invariant system")
  (statement := /-- Consider the time-invariant system $\dot x = Ax$ with $A$ a real square
    matrix.

    The origin is an exponentially stable equilibrium
    (\cref{def:exponentiallyStableNA}) if and only if $A$ is Hurwitz
    (\cref{def:stability-isHurwitz}).

    Together with \cref{thm:asymptoticStableNA-iff-isHurwitz} this says the two notions
    coincide for a time-invariant system — a genuine feature of constant $A$, not of linearity:
    for time-varying $A(t)$ they differ, as $\dot x = -x/(1+t)$ shows.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.1(3).
  -/)
  (proof := /-- As for \cref{thm:asymptoticStableNA-iff-isHurwitz}, but against
    \cref{thm:exponentiallyStableNA-iff-decayingStateTransition}, which already asks for an
    exponential envelope.  The forward direction squeezes $\|e^{At}x\|$ to zero under that
    envelope and applies \cref{thm:isHurwitz-of-tendsto-exp-mulVec}; the converse is
    \cref{thm:isHurwitz-exists-norm-exp-mulVec-le} re-anchored from $0$ to $t_0$. -/)]
theorem exponentiallyStableNA_iff_isHurwitz
    (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix Y X ℝ) (D : Matrix Y U ℝ) :
    ExponentiallyStableNA ((timeInvariant A B C D).vectorField 0) (0 : X → ℝ) ↔
      IsHurwitz A := by
  classical
  have hcoeff : (timeInvariant A B C D).A = fun _ => A := rfl
  rw [exponentiallyStableNA_iff_decayingStateTransition _ (by simpa using continuous_const)]
  simp only [hcoeff, stateTransitionMatrix_const]
  constructor
  · rintro ⟨k, hk, γ, hγ, hbd⟩
    refine isHurwitz_of_tendsto_exp_mulVec A fun x => ?_
    refine squeeze_zero_norm' ?_ (by simpa using tendsto_const_mul_exp_neg (k * ‖x‖) 0 hγ)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simpa [mul_comm, mul_assoc, mul_left_comm] using hbd 0 le_rfl t ht x
  · intro heig
    obtain ⟨k, hk, γ, hγ, hbd⟩ := heig.exists_norm_exp_mulVec_le
    exact ⟨k, hk, γ, hγ, fun t₀ _ t ht x => hbd (t - t₀) (by linarith) x⟩

/-! ## Theorem 8.2: Lyapunov stability -/

-- `DecidableEq X` is needed by the clauses' proofs, not by the statement.
set_option linter.unusedDecidableInType false in
/-- **Hespanha, Theorem 8.2 (Lyapunov stability).**
For the time-invariant system `ẋ = A x` the following are equivalent:

1. asymptotic stability,
2. exponential stability,
3. every eigenvalue of `A` has strictly negative real part,
4. every positive-definite `Q` admits a positive-definite solution `P` of `PA + AᵀP = -Q`,
   unique among all matrix solutions,
5. some positive-definite `P` makes `-(PA + AᵀP)` positive definite,
6. some positive-definite `P` and rate `c > 0` satisfy `PA + AᵀP ≼ -2c P`.

Clause 6 is not in Hespanha's list. It is the rate-carrying form of clause 5 — along a
trajectory it gives `V̇ ≤ -2c V` for `V = xᵀPx` — and it is the shape every contraction and
guaranteed-decay-rate condition is written in.

Each edge is proved separately — clauses 1 and 2 against `IsHurwitz` here, clauses 4, 5 and 6
in `LyapunovEquation.lean` — and this records the textbook statement they add up to.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.2. -/
@[blueprint "thm:lyapunovStability-tfae"
  (title := "Hespanha's Theorem 8.2")
  (statement := /-- For the time-invariant system $\dot x = Ax$ the following are equivalent.
    \begin{enumerate}
      \item The origin is asymptotically stable (\cref{def:asymptoticStableNA}).
      \item The origin is exponentially stable (\cref{def:exponentiallyStableNA}).
      \item $A$ is Hurwitz (\cref{def:stability-isHurwitz}).
      \item For every positive definite $Q$ there is a positive definite $P$ with
        $PA + A^{\mathsf T}P = -Q$ (\cref{def:continuousLyapunovEquation}), and this $P$ is
        the unique matrix solution.
      \item There is a positive definite $P$ with $-(PA + A^{\mathsf T}P)$ positive definite.
      \item There are a positive definite $P$ and a rate $c > 0$ with
        $PA + A^{\mathsf T}P \preceq -2cP$.
    \end{enumerate}

    Clause 6 is not in Hespanha's list.  It is the rate-carrying form of clause 5: along a
    trajectory it gives $\dot V \le -2cV$ for $V = x^{\mathsf T}Px$, hence
    $V(t) \le V(0)e^{-2ct}$, and it is the shape every contraction and guaranteed-decay-rate
    condition is written in.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.2.
  -/)
  (proof := /-- Every clause is tied to clause 3 and the cycle is closed by transitivity:
    $1 \Leftrightarrow 3$ is \cref{thm:asymptoticStableNA-iff-isHurwitz},
    $2 \Leftrightarrow 3$ is \cref{thm:exponentiallyStableNA-iff-isHurwitz},
    $3 \Leftrightarrow 4$ is \cref{thm:isHurwitz-iff-forall-posDef-exists-solution},
    $3 \Leftrightarrow 5$ is \cref{thm:isHurwitz-iff-exists-posDef-lyapunovResidual}, and
    $3 \Leftrightarrow 6$ is \cref{thm:isHurwitz-iff-exists-posDef-lyapunovRate}. -/)]
theorem lyapunovStability_tfae
    (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix Y X ℝ) (D : Matrix Y U ℝ) :
    [ AsymptoticStableNA ((timeInvariant A B C D).vectorField 0) (0 : X → ℝ),
      ExponentiallyStableNA ((timeInvariant A B C D).vectorField 0) (0 : X → ℝ),
      IsHurwitz A,
      ∀ R : Matrix X X ℝ, R.PosDef →
        ∃ S : Matrix X X ℝ, S.PosDef ∧ ContinuousLyapunovEquation A S R ∧
          ∀ T : Matrix X X ℝ, ContinuousLyapunovEquation A T R → T = S,
      ∃ S : Matrix X X ℝ, S.PosDef ∧ (-(S * A + Aᵀ * S)).PosDef,
      ∃ (S : Matrix X X ℝ) (c : ℝ), 0 < c ∧ S.PosDef ∧
        (-(S * A + Aᵀ * S) - (2 * c) • S).PosSemidef ].TFAE := by
  tfae_have 1 ↔ 3 := asymptoticStableNA_iff_isHurwitz A B C D
  tfae_have 2 ↔ 3 := exponentiallyStableNA_iff_isHurwitz A B C D
  tfae_have 3 ↔ 4 := isHurwitz_iff_forall_posDef_exists_solution A
  tfae_have 3 ↔ 5 := isHurwitz_iff_exists_posDef_lyapunovResidual A
  tfae_have 3 ↔ 6 := isHurwitz_iff_exists_posDef_lyapunovRate A
  tfae_finish

end ContinuousLinearSystem.timeInvariant

end LinearSystems

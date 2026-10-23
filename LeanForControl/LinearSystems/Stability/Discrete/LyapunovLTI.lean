import LeanForControl.LinearSystems.Stability.Discrete.LyapunovEquation
import LeanForControl.LinearSystems.Stability.Discrete.LyapunovLTV
import LeanForControl.LinearSystems.Stability.Discrete.Schur
import Architect

/-!
# `LinearSystems.Stability.Discrete.LyapunovLTI`

Hespanha's Theorems 8.3 and 8.4: for a *time-invariant* discrete-time system `x⁺ = A x`, the
stability notions of Definition 8.2 are eigenvalue conditions on `A`, and the Lyapunov equation
`AᵀPA - P = -Q`.  The discrete-time counterpart of
`LinearSystems/Stability/Continuous/LyapunovLTI.lean`.

`Discrete/LyapunovLTV.lean` turned every clause of Definition 8.2 into a bound on the state
transition matrix `Φ(t, t₀)`; for a constant `A` that matrix is `A^(t - t₀)`
(`discStateTransitionMatrix_const`), and `Discrete/Schur.lean` says what the Schur condition
means for the powers of `A`.

* **Theorem 8.3(2)** — `DiscreteLTI.locallyAsymptoticallyStable_iff_isSchur` and
  `DiscreteLTI.locallyExponentiallyStable_iff_isSchur`.
* **Theorem 8.4** — `DiscreteLTI.lyapunovStability_tfae`.

## Scope

Clauses (1) and (3) of Theorem 8.3 ask that the Jordan blocks at eigenvalues of magnitude `1` be
`1 × 1`.  Mathlib has no Jordan normal form, so, as for clauses (1) and (4) of the continuous
Theorem 8.1, they are not attempted here.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorems 8.3 and 8.4.
-/

namespace LinearSystems

open Matrix Set Filter Topology
open scoped Matrix.Norms.Operator

variable {X U Y : Type*} [Fintype X] [DecidableEq X] [Fintype U]

namespace DiscreteLTI

omit [Fintype U] in
/-- The state transition matrix of an LTI system is a matrix power. -/
private lemma discStateTransitionMatrix_toLTV (sys : DiscreteLTI X U Y ℝ) (t t₀ : ℕ) :
    discStateTransitionMatrix sys.toLTV.A t t₀ = sys.A ^ (t - t₀) :=
  discStateTransitionMatrix_const sys.A t t₀

/-! ## Theorem 8.3(2) -/

omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.3(2), asymptotic stability.**  The time-invariant system `x⁺ = A x` is
asymptotically stable if and only if every eigenvalue of `A` has magnitude strictly below `1`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.3(2). -/
@[blueprint "thm:discreteLTI-locallyAsymptoticallyStable-iff-isSchur"
  (title := "Asymptotic stability of a discrete-time linear time-invariant system")
  (statement := /-- For the time-invariant system $x^{+} = Ax$, the origin is locally
    asymptotically stable (\cref{def:discreteSystem-locallyAsymptoticallyStable}) if and only if
    $A$ is Schur (\cref{def:stability-isSchur}): every eigenvalue of $A$ has magnitude strictly
    smaller than $1$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.3(2).
  -/)
  (proof := /-- For constant $A$ the state transition matrix is $A^{t - t_0}$
    (\cref{thm:discStateTransitionMatrix-const}), so
    \cref{thm:discreteLTV-locallyAsymptoticallyStable-iff-decayingHomogeneousResponse} turns the
    statement into one about $A^{k}x_0$.  If the responses converge then $A$ is Schur
    (\cref{thm:isSchur-of-tendsto-pow-mulVec}); conversely a Schur $A$ has a geometric envelope
    $\|A^{k}x\| \le C\rho^{k}\|x\|$ (\cref{thm:isSchur-exists-norm-pow-mulVec-le}), which bounds
    the responses and makes them vanish. -/)]
theorem locallyAsymptoticallyStable_iff_isSchur (sys : DiscreteLTI X U Y ℝ) :
    sys.toDiscreteSystem.zeroInput.LocallyAsymptoticallyStable (0 : X → ℝ) ↔ IsSchur sys.A := by
  classical
  have hhr : ∀ (t₀ : ℕ) (x₀ : X → ℝ), discHomogeneousResponse sys.toLTV.A t₀ x₀ =
      fun t => sys.A ^ (t - t₀) *ᵥ x₀ := fun t₀ x₀ => by
    funext t
    simp [discHomogeneousResponse, discStateTransitionMatrix_toLTV]
  rw [DiscreteLTV.locallyAsymptoticallyStable_iff_decayingHomogeneousResponse]
  simp only [hhr]
  constructor
  · rintro ⟨-, hconv⟩
    exact isSchur_of_tendsto_pow_mulVec sys.A fun x => by simpa using hconv 0 x
  · intro hA
    obtain ⟨C, hC, ρ, hρ0, hρ1, hbd⟩ := hA.exists_norm_pow_mulVec_le
    refine ⟨fun t₀ x₀ => ⟨C * ‖x₀‖, fun t _ => ?_⟩, fun t₀ x₀ => ?_⟩
    · calc ‖sys.A ^ (t - t₀) *ᵥ x₀‖ ≤ C * ρ ^ (t - t₀) * ‖x₀‖ := hbd _ x₀
        _ ≤ C * 1 * ‖x₀‖ := by gcongr; exact pow_le_one₀ hρ0 hρ1.le
        _ = C * ‖x₀‖ := by ring
    · refine squeeze_zero_norm (fun t => hbd (t - t₀) x₀) ?_
      have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
        (tendsto_sub_atTop_nat t₀)).const_mul C
      simpa [Function.comp_def] using h.mul_const ‖x₀‖

omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.3(2), exponential stability.**  The time-invariant system `x⁺ = A x`
is exponentially stable if and only if every eigenvalue of `A` has magnitude strictly below `1`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.3(2). -/
@[blueprint "thm:discreteLTI-locallyExponentiallyStable-iff-isSchur"
  (title := "Exponential stability of a discrete-time linear time-invariant system")
  (statement := /-- For the time-invariant system $x^{+} = Ax$, the origin is locally
    exponentially stable (\cref{def:discreteSystem-locallyExponentiallyStable}) if and only if
    $A$ is Schur (\cref{def:stability-isSchur}).

    Together with \cref{thm:discreteLTI-locallyAsymptoticallyStable-iff-isSchur} this says the
    two notions coincide for a time-invariant system.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.3(2).
  -/)
  (proof := /-- Against
    \cref{thm:discreteLTV-locallyExponentiallyStable-iff-decayingStateTransition}, which already
    asks for a geometric envelope $\|A^{t - t_0}x\| \le c\rho^{t - t_0}\|x\|$.  Forwards, at
    $t_0 = 0$ the envelope makes $A^{k}x \to 0$, so $A$ is Schur
    (\cref{thm:isSchur-of-tendsto-pow-mulVec}); backwards is
    \cref{thm:isSchur-exists-norm-pow-mulVec-le}. -/)]
theorem locallyExponentiallyStable_iff_isSchur (sys : DiscreteLTI X U Y ℝ) :
    sys.toDiscreteSystem.zeroInput.LocallyExponentiallyStable (0 : X → ℝ) ↔ IsSchur sys.A := by
  classical
  rw [DiscreteLTV.locallyExponentiallyStable_iff_decayingStateTransition]
  simp only [discStateTransitionMatrix_toLTV]
  constructor
  · rintro ⟨c, -, ρ, hρ0, hρ1, hbd⟩
    refine isSchur_of_tendsto_pow_mulVec sys.A fun x => ?_
    refine squeeze_zero_norm (fun k => by simpa using hbd 0 k (Nat.zero_le k) x) ?_
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul c).mul_const ‖x‖
  · intro hA
    obtain ⟨C, hC, ρ, hρ0, hρ1, hbd⟩ := hA.exists_norm_pow_mulVec_le
    exact ⟨C, hC, ρ, hρ0, hρ1, fun t₀ t _ x => hbd (t - t₀) x⟩

/-! ## Theorem 8.4 -/

omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.4 (Lyapunov stability in discrete time).**  For the time-invariant
system `x⁺ = A x` the following are equivalent:

1. asymptotic stability,
2. exponential stability,
3. every eigenvalue of `A` has magnitude strictly smaller than `1`,
4. every positive definite `Q` admits a positive definite solution `P` of `AᵀPA - P = -Q`,
   unique among all matrix solutions,
5. some positive definite `P` makes `-(AᵀPA - P)` positive definite.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.4. -/
@[blueprint "thm:discreteLTI-lyapunovStability-tfae"
  (title := "Hespanha's Theorem 8.4")
  (statement := /-- For the time-invariant system $x^{+} = Ax$ the following are equivalent.
    \begin{enumerate}
      \item The origin is asymptotically stable
        (\cref{def:discreteSystem-locallyAsymptoticallyStable}).
      \item The origin is exponentially stable
        (\cref{def:discreteSystem-locallyExponentiallyStable}).
      \item $A$ is Schur (\cref{def:stability-isSchur}).
      \item For every positive definite $Q$ there is a positive definite $P$ with
        $A^{\mathsf T}PA - P = -Q$ (\cref{def:discreteLyapunovEquation}), and this $P$ is the
        unique matrix solution.
      \item There is a positive definite $P$ with $-(A^{\mathsf T}PA - P)$ positive definite.
    \end{enumerate}

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.4.
  -/)
  (proof := /-- Every clause is tied to clause 3:
    $1 \Leftrightarrow 3$ is \cref{thm:discreteLTI-locallyAsymptoticallyStable-iff-isSchur},
    $2 \Leftrightarrow 3$ is \cref{thm:discreteLTI-locallyExponentiallyStable-iff-isSchur},
    $3 \Leftrightarrow 4$ is \cref{thm:isSchur-iff-forall-posDef-exists-discrete-solution}, and
    $3 \Leftrightarrow 5$ is \cref{thm:isSchur-iff-exists-posDef-discreteLyapunovResidual}. -/)]
theorem lyapunovStability_tfae (sys : DiscreteLTI X U Y ℝ) :
    [ sys.toDiscreteSystem.zeroInput.LocallyAsymptoticallyStable (0 : X → ℝ),
      sys.toDiscreteSystem.zeroInput.LocallyExponentiallyStable (0 : X → ℝ),
      IsSchur sys.A,
      ∀ R : Matrix X X ℝ, R.PosDef →
        ∃ S : Matrix X X ℝ, S.PosDef ∧ DiscreteLyapunovEquation sys.A S R ∧
          ∀ T : Matrix X X ℝ, DiscreteLyapunovEquation sys.A T R → T = S,
      ∃ S : Matrix X X ℝ, S.PosDef ∧ (-(sys.Aᵀ * S * sys.A - S)).PosDef ].TFAE := by
  classical
  tfae_have 1 ↔ 3 := locallyAsymptoticallyStable_iff_isSchur sys
  tfae_have 2 ↔ 3 := locallyExponentiallyStable_iff_isSchur sys
  tfae_have 3 ↔ 4 := isSchur_iff_forall_posDef_exists_discrete_solution sys.A
  tfae_have 3 ↔ 5 := isSchur_iff_exists_posDef_discreteLyapunovResidual sys.A
  tfae_finish

end DiscreteLTI

end LinearSystems

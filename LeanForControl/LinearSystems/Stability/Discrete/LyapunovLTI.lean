import LeanForControl.LinearSystems.Solutions.DiscLTI
import LeanForControl.LinearSystems.Stability.DefsStability
import LeanForControl.MatrixAlgebra.QuadraticForm
import LeanForControl.Stability.LyapunovDiscrete
import Architect

/-!
# Lyapunov stability of discrete-time LTI systems

A positive-definite solution of the discrete-time Lyapunov equation `Aᵀ P A - P = -Q` makes
`V(x) = xᵀ P x` a quadratic Lyapunov function for `x(k+1) = A x(k)`.  The general direct method
(`globallyExponentiallyStableDT_of_lyapunov`, Theorem 2 row 4 of Jungers and van de Wouw) then
gives global exponential stability, with no matrix-specific argument beyond the identity
`V(A x) - V(x) = -xᵀ Q x`.

## Main results

* `DiscreteLyapunovEquation.dotProduct_mulVec_sub` — along `x ↦ A x`, a solution's quadratic
  form decreases by exactly `xᵀ Q x`.
* `DiscreteLinearSystem.timeInvariant.globallyExponentiallyStableDT_of_discreteLyapunovEquation`
  — a positive-definite solution for some positive-definite `Q` makes the origin of the unforced
  time-invariant system globally exponentially stable.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8; Jungers and van de Wouw,
*Discrete-time nonlinear control systems* (2026), Theorem 2.
-/

namespace LinearSystems

open Matrix MatrixAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- Along `x ↦ A x`, the quadratic form of a solution of the discrete Lyapunov equation
decreases by exactly `xᵀ Q x`. -/
@[blueprint "lem:discreteLyapunovEquation-dotProduct-mulVec-sub"
  (title := "Decrease of the quadratic form along a discrete LTI system")
  (latexEnv := "lemma")
  (statement := /-- If $A^{\mathsf T}PA - P = -Q$ (\cref{def:discreteLyapunovEquation}), then
    for every $x$,
    \[
      (Ax)^{\mathsf T} P (Ax) - x^{\mathsf T} P x = -x^{\mathsf T} Q x.
    \] -/)
  (proof := /-- $(Ax)^{\mathsf T}P(Ax) = x^{\mathsf T}(A^{\mathsf T}PA)x$, and
    $A^{\mathsf T}PA = P - Q$. -/)]
theorem DiscreteLyapunovEquation.dotProduct_mulVec_sub {A P Q : Matrix X X ℝ}
    (h : DiscreteLyapunovEquation A P Q) (x : X → ℝ) :
    (A *ᵥ x) ⬝ᵥ (P *ᵥ (A *ᵥ x)) - x ⬝ᵥ (P *ᵥ x) = -(x ⬝ᵥ (Q *ᵥ x)) := by
  -- `Aᵀ P A = P - Q`, rearranging the equation
  have hAPA : Aᵀ * (P * A) = P - Q := by
    rw [← Matrix.mul_assoc]
    calc Aᵀ * P * A = (Aᵀ * P * A - P) + P := by abel
      _ = P - Q := by rw [show Aᵀ * P * A - P = -Q from h]; abel
  -- move `A` across the dot product: `(A x)ᵀ P (A x) = xᵀ (Aᵀ P A) x`
  have h_move : (A *ᵥ x) ⬝ᵥ (P *ᵥ (A *ᵥ x)) = x ⬝ᵥ ((Aᵀ * (P * A)) *ᵥ x) := by
    conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  rw [h_move, hAPA, Matrix.sub_mulVec, dotProduct_sub]
  ring

omit [DecidableEq X] in
/-- **Discrete-time Lyapunov theorem for LTI systems.**  If the discrete Lyapunov equation
`Aᵀ P A - P = -Q` has a positive-definite solution `P` for a positive-definite `Q`, the origin of
the unforced time-invariant system `x(k+1) = A x(k)` is globally exponentially stable.

`V(x) = xᵀ P x` satisfies `c₁ ‖x‖² ≤ V(x) ≤ c₂ ‖x‖²` and `ΔV(x) = -xᵀ Q x ≤ -c₃ V(x)`, which is
row 4 of Theorem 2 of Jungers and van de Wouw with `p = 2`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8; Jungers and van de Wouw,
*Discrete-time nonlinear control systems* (2026), Theorem 2. -/
@[blueprint "thm:globallyExponentiallyStableDT-of-discreteLyapunovEquation"
  (title := "Discrete Lyapunov equation implies global exponential stability")
  (statement := /-- Let $P$ and $Q$ be positive definite with $A^{\mathsf T}PA - P = -Q$
    (\cref{def:discreteLyapunovEquation}).  Then the origin of the unforced time-invariant system
    $x(k+1) = Ax(k)$ (\cref{def:discLinearSystem-timeInvariant}) is globally exponentially stable
    (\cref{def:globallyExponentiallyStableDT}).

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8. -/)
  (proof := /-- Take $V(x) = x^{\mathsf T}Px$.  By
    \cref{lem:exists-norm-sq-bounds-dotProduct-mulVec} there are $0 < c_1 \le c_2$ with
    $c_1\|x\|^{2} \le V(x) \le c_2\|x\|^{2}$, and $q > 0$ with $x^{\mathsf T}Qx \ge q\|x\|^{2}$.
    By \cref{lem:discreteLyapunovEquation-dotProduct-mulVec-sub},
    $\Delta V(x) = -x^{\mathsf T}Qx \le -q\|x\|^{2} \le -(q/c_2)V(x)$, so with
    $c_3 = \min(q/c_2, 1/2)$ the hypotheses of
    \cref{thm:globallyExponentiallyStableDT-of-lyapunov} hold with $p = 2$. -/)]
theorem DiscreteLinearSystem.timeInvariant.globallyExponentiallyStableDT_of_discreteLyapunovEquation
    {U Y : Type*} [Fintype U] {A P Q : Matrix X X ℝ} (B : Matrix X U ℝ) (C : Matrix Y X ℝ)
    (D : Matrix Y U ℝ) (hP : P.PosDef) (hQ : Q.PosDef) (h : DiscreteLyapunovEquation A P Q) :
    GloballyExponentiallyStableDT ((DiscreteLinearSystem.timeInvariant A B C D).vectorField 0 0)
      0 := by
  /- `V(x) = xᵀ P x` is sandwiched by `‖x‖²`, and decreases by `xᵀ Q x ≥ q ‖x‖² ≥ (q / c₂) V`,
     so the direct method applies with `p = 2` and `c₃ = min (q / c₂) (1 / 2)`. -/
  rw [DiscreteLinearSystem.timeInvariant.vectorField_zero]
  -- Step 1. Quadratic bounds for `V` and a lower bound for `xᵀ Q x`.
  obtain ⟨c₁, c₂, hc₁, hc₁₂, hV_bd⟩ := exists_norm_sq_bounds_dotProduct_mulVec P hP
  obtain ⟨q, _, hq, -, hQ_bd⟩ := exists_norm_sq_bounds_dotProduct_mulVec Q hQ
  have hc₂ : 0 < c₂ := hc₁.trans_le hc₁₂
  set c₃ := min (q / c₂) (1 / 2) with hc₃_def
  -- Step 2. Apply the direct method with `V(x) = xᵀ P x` and `p = 2`.
  refine globallyExponentiallyStableDT_of_lyapunov (V := fun x => x ⬝ᵥ (P *ᵥ x)) (c₃ := c₃)
    (p := 2)
    hc₁ hc₁₂ two_pos (lt_min (div_pos hq hc₂) (by norm_num))
    ((min_le_right _ _).trans_lt (by norm_num)) (fun x => ?_) (fun x => ?_) (fun x => ?_)
  · -- lower sandwich
    simpa [Real.rpow_two] using (hV_bd x).1
  · -- upper sandwich
    simpa [Real.rpow_two] using (hV_bd x).2
  · -- decrease: `ΔV = -xᵀ Q x ≤ -q ‖x‖² ≤ -(q / c₂) V ≤ -c₃ V`
    change (A *ᵥ x) ⬝ᵥ (P *ᵥ (A *ᵥ x)) - x ⬝ᵥ (P *ᵥ x) ≤ -c₃ * (x ⬝ᵥ (P *ᵥ x))
    rw [h.dotProduct_mulVec_sub x]
    have hV_nonneg : 0 ≤ x ⬝ᵥ (P *ᵥ x) := (by positivity : (0 : ℝ) ≤ c₁ * ‖x‖ ^ 2).trans
      (hV_bd x).1
    -- `V ≤ c₂ ‖x‖²` turns the bound on `xᵀ Q x` into one on `V`
    have h_Q_ge_V : q / c₂ * (x ⬝ᵥ (P *ᵥ x)) ≤ x ⬝ᵥ (Q *ᵥ x) := by
      calc q / c₂ * (x ⬝ᵥ (P *ᵥ x)) ≤ q / c₂ * (c₂ * ‖x‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (hV_bd x).2 (div_pos hq hc₂).le
        _ = q * ‖x‖ ^ 2 := by field_simp
        _ ≤ x ⬝ᵥ (Q *ᵥ x) := (hQ_bd x).1
    have h_c₃_le : c₃ * (x ⬝ᵥ (P *ᵥ x)) ≤ q / c₂ * (x ⬝ᵥ (P *ᵥ x)) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hV_nonneg
    linarith

end LinearSystems

import LeanForControl.LinearSystems.Solutions.CtsLTV
import LeanForControl.Contraction.Norms.LogNorm
import Architect

/-!
# Log-norm bounds on the solutions of linear systems

For `ẋ = A(t) x` on a normed space, the log norm bounds the growth of every solution:

* `ContinuousLTV.norm_stateTransition_le`, `ContinuousLTV.le_norm_stateTransition` — Coppel's
  inequalities, `exp (-∫_{t₀}^t μ(-A(τ)) dτ) ≤ ‖Φ(t, t₀)‖ ≤ exp (∫_{t₀}^t μ(A(τ)) dτ)` for
  `t₀ ≤ t`.
* `ContinuousLTV.norm_forcedResponse_le` — the forced response from `x₀`,
  `‖x(t)‖ ≤ e^{∫_{t₀}^t μ(A)} ‖x₀‖ + ∫_{t₀}^t e^{∫_τ^t μ(A)} ‖B(τ) u(τ)‖ dτ`.
* `ContinuousLTV.norm_stateTransition_le_of_const`,
  `ContinuousLTV.norm_forcedResponse_le_of_const` — for a constant `A`:
  `‖Φ(t, t₀)‖ ≤ e^{μ(A)(t - t₀)}`, and, when `μ(A) < 0` and `‖B(τ) u(τ)‖ ≤ β`,
  `‖x(t)‖ ≤ e^{μ(A)(t - t₀)} ‖x₀‖ + β / (-μ(A))`.

References: F. Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), Section 2.4;
W. A. Coppel, *Stability and Asymptotic Behavior of Differential Equations* (1965), Chapter III.
-/

open Set Real MeasureTheory
open scoped LogNorm

namespace LinearSystems

namespace ContinuousLTV

variable {E U Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **Coppel's inequality**: `‖Φ(t, t₀)‖ ≤ exp (∫_{t₀}^t μ(A(τ)) dτ)` for `t₀ ≤ t`. -/
@[blueprint "thm:continuousLTV-norm-stateTransition-le"
  (title := "Coppel's inequality")
  (statement := /-- For $A$ continuous and $t_0 \le t$, the state transition operator
    (\cref{def:continuousLTV-stateTransition}) satisfies
    \[ \|\Phi(t, t_0)\| \le \exp\Bigl( \int_{t_0}^{t} \mu(A(\tau)) \, d\tau \Bigr), \]
    for the log norm (\cref{def:logNorm}) of any norm on the state space.

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Section 2.4. -/)
  (proof := /-- Let $x(r) = \Phi(r, t_0) x_0$ and $M(r) = \int_{t_0}^r \mu(A(\tau)) d\tau$.  By the
    curve norm derivative (\cref{lem:hasDerivWithinAt-norm-sq}) and Lumer's inequality
    (\cref{thm:regularPairing-pairing-le-logNorm}), the right derivative of $\|x\|^2$ is
    $2 \pair{A x}{x} \le 2 \mu(A) \|x\|^2$, so $e^{-2M} \|x\|^2$ has a nonpositive right
    derivative and is nonincreasing.  Hence $\|x(t)\| \le e^{M(t)} \|x_0\|$. -/)]
theorem norm_stateTransition_le (s : ContinuousLTV E U Y) (hA : Continuous s.A) {t₀ t : ℝ}
    (ht : t₀ ≤ t) : ‖s.stateTransition t t₀‖ ≤ exp (∫ τ in t₀..t, μ (s.A τ)) := by
  have hμ : Continuous fun τ => μ (s.A τ) := continuous_logNorm.comp hA
  set M : ℝ → ℝ := fun r => ∫ τ in t₀..r, μ (s.A τ)
  refine ContinuousLinearMap.opNorm_le_bound _ (exp_pos _).le fun x₀ => ?_
  set x : ℝ → E := fun r => s.stateTransition r t₀ x₀
  have hx (r : ℝ) : HasDerivAt x (s.A r (x r)) r := by
    simpa using (s.hasDerivAt_stateTransition hA r t₀).clm_apply (hasDerivAt_const r x₀)
  -- `g = e^{-2M} ‖x‖²` has a nonpositive right derivative, so `g t ≤ g t₀ = ‖x₀‖²`
  set g : ℝ → ℝ := fun r => exp (-(2 * M r)) * ‖x r‖ ^ 2
  have hg (r : ℝ) : HasDerivWithinAt g
      (exp (-(2 * M r)) * (-(2 * μ (s.A r))) * ‖x r‖ ^ 2 +
        exp (-(2 * M r)) * (2 * RegularPairing.ofNorm E (s.A r (x r)) (x r))) (Ici r) r := by
    have hM := ((hμ.integral_hasStrictDerivAt t₀ r).hasDerivAt.const_mul 2).neg.exp
    exact hM.hasDerivWithinAt.mul
      (hasDerivWithinAt_Ioi_iff_Ici.1 (RegularPairing.hasDerivWithinAt_norm_sq
        (hx r).hasDerivWithinAt))
  have hle := image_le_of_deriv_right_le_deriv_boundary (f := g) (B := fun _ => ‖x₀‖ ^ 2)
    (B' := fun _ => 0) (a := t₀) (b := t)
    (fun r _ => ((((hμ.integral_hasStrictDerivAt t₀ r).hasDerivAt.const_mul 2).neg.exp
      ).continuousAt.mul ((hx r).continuousAt.norm.pow 2)).continuousWithinAt)
    (fun r _ => hg r) (by simp [g, M, x]) continuousOn_const
    (fun r _ => hasDerivWithinAt_const _ _ _) (fun r _ => by
      have h := (RegularPairing.ofNorm E).pairing_le_logNorm (s.A r) (x r)
      have he := exp_pos (-(2 * M r))
      nlinarith) (right_mem_Icc.2 ht)
  -- `‖x t‖² ≤ e^{2 M t} ‖x₀‖²`
  have hsq : ‖x t‖ ^ 2 ≤ (exp (M t) * ‖x₀‖) ^ 2 := by
    have h2 : exp (-(2 * M t)) * exp (M t) ^ 2 = 1 := by
      rw [← exp_nat_mul, ← exp_add]; norm_num
    have he := exp_pos (-(2 * M t))
    simp only [g] at hle
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **Coppel's lower inequality**: `exp (-∫_{t₀}^t μ(-A(τ)) dτ) ≤ ‖Φ(t, t₀)‖` for `t₀ ≤ t`. -/
@[blueprint "thm:continuousLTV-le-norm-stateTransition"
  (title := "Coppel's lower inequality")
  (statement := /-- For $A$ continuous, $t_0 \le t$ and a nonzero state space,
    \[ \exp\Bigl( -\int_{t_0}^{t} \mu(-A(\tau)) \, d\tau \Bigr) \le \|\Phi(t, t_0)\|. \]

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Section 2.4. -/)
  (proof := /-- As for \cref{thm:continuousLTV-norm-stateTransition-le}, with
    $\pair{Ax}{x} \ge -\pair{-Ax}{x} \ge -\mu(-A) \|x\|^2$ (subadditivity of the pairing):
    $e^{2N} \|x\|^2$ is nondecreasing, for
    $N(r) = \int_{t_0}^r \mu(-A(\tau)) d\tau$. -/)]
theorem le_norm_stateTransition [Nontrivial E] (s : ContinuousLTV E U Y) (hA : Continuous s.A)
    {t₀ t : ℝ} (ht : t₀ ≤ t) : exp (-∫ τ in t₀..t, μ (-s.A τ)) ≤ ‖s.stateTransition t t₀‖ := by
  have hμ : Continuous fun τ => μ (-s.A τ) := continuous_logNorm.comp hA.neg
  set N : ℝ → ℝ := fun r => ∫ τ in t₀..r, μ (-s.A τ)
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
  set x : ℝ → E := fun r => s.stateTransition r t₀ x₀
  have hx (r : ℝ) : HasDerivAt x (s.A r (x r)) r := by
    simpa using (s.hasDerivAt_stateTransition hA r t₀).clm_apply (hasDerivAt_const r x₀)
  have hN (r : ℝ) : HasDerivAt (fun r => exp (2 * N r)) (exp (2 * N r) * (2 * μ (-s.A r))) r :=
    ((hμ.integral_hasStrictDerivAt t₀ r).hasDerivAt.const_mul 2).exp
  -- `-e^{2N} ‖x‖²` has a nonpositive right derivative, so `e^{2N t} ‖x t‖² ≥ ‖x₀‖²`
  have hle := image_le_of_deriv_right_le_deriv_boundary
    (f := fun r => -(exp (2 * N r) * ‖x r‖ ^ 2)) (B := fun _ => -‖x₀‖ ^ 2) (B' := fun _ => 0)
    (a := t₀) (b := t)
    (fun r _ => ((hN r).continuousAt.mul ((hx r).continuousAt.norm.pow 2)).neg.continuousWithinAt)
    (fun r _ => ((hN r).hasDerivWithinAt.mul (hasDerivWithinAt_Ioi_iff_Ici.1
      (RegularPairing.hasDerivWithinAt_norm_sq (hx r).hasDerivWithinAt))).neg)
    (by simp [N, x]) continuousOn_const (fun r _ => hasDerivWithinAt_const _ _ _) (fun r _ => by
      have h₁ := (RegularPairing.ofNorm E).pairing_le_logNorm (-s.A r) (x r)
      have h₂ := (RegularPairing.ofNorm E).neg_ofNorm_neg_le (s.A r (x r)) (x r)
      have he := exp_pos (2 * N r)
      simp only [ContinuousLinearMap.neg_apply] at h₁
      nlinarith) (right_mem_Icc.2 ht)
  -- `e^{-N t} ‖x₀‖ ≤ ‖x t‖ ≤ ‖Φ(t, t₀)‖ ‖x₀‖`
  have hsq : (exp (-N t) * ‖x₀‖) ^ 2 ≤ ‖x t‖ ^ 2 := by
    have h2 : exp (2 * N t) * exp (-N t) ^ 2 = 1 := by
      rw [← exp_nat_mul, ← exp_add]; norm_num
    have he := exp_pos (2 * N t)
    simp only at hle
    nlinarith
  have hxt := (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hsq
  exact le_of_mul_le_mul_right (hxt.trans ((s.stateTransition t t₀).le_opNorm x₀))
    (norm_pos_iff.2 hx₀)

/-- **The forced response under a log-norm bound**:
`‖x(t)‖ ≤ e^{∫_{t₀}^t μ(A)} ‖x₀‖ + ∫_{t₀}^t e^{∫_τ^t μ(A)} ‖B(τ) u(τ)‖ dτ` for `t₀ ≤ t`. -/
@[blueprint "thm:continuousLTV-norm-forcedResponse-le"
  (title := "Log-norm bound on the forced response")
  (statement := /-- For $A$, $B$ and $u$ continuous and $t_0 \le t$, the forced response
    (\cref{def:forcedResponse}) from $x_0$ satisfies
    \[ \|x(t)\| \le e^{\int_{t_0}^t \mu(A)} \|x_0\|
      + \int_{t_0}^t e^{\int_\tau^t \mu(A)} \|B(\tau) u(\tau)\| \, d\tau. \]

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Section 2.4. -/)
  (proof := /-- The variation-of-constants formula and
    \cref{thm:continuousLTV-norm-stateTransition-le} for $\Phi(t, t_0)$ and each
    $\Phi(t, \tau)$. -/)]
theorem norm_forcedResponse_le (s : ContinuousLTV E U Y) (hA : Continuous s.A)
    (hB : Continuous s.B) {u : ℝ → U} (hu : Continuous u) {t₀ t : ℝ} (ht : t₀ ≤ t) (x₀ : E) :
    ‖s.forcedResponse u t₀ x₀ t‖ ≤ exp (∫ τ in t₀..t, μ (s.A τ)) * ‖x₀‖ +
      ∫ τ in t₀..t, exp (∫ σ in τ..t, μ (s.A σ)) * ‖s.B τ (u τ)‖ := by
  have hμ : Continuous fun τ => μ (s.A τ) := continuous_logNorm.comp hA
  -- `τ ↦ ∫_τ^t μ(A)` is continuous
  have hI : Continuous fun τ => ∫ σ in τ..t, μ (s.A σ) := by
    rw [show (fun τ => ∫ σ in τ..t, μ (s.A σ)) = fun τ => -∫ σ in t..τ, μ (s.A σ) from
      funext fun τ => intervalIntegral.integral_symm _ _]
    exact (continuous_iff_continuousAt.2 fun τ =>
      (hμ.integral_hasStrictDerivAt t τ).hasDerivAt.continuousAt).neg
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact ((s.stateTransition t t₀).le_opNorm x₀).trans
      (mul_le_mul_of_nonneg_right (s.norm_stateTransition_le hA ht) (norm_nonneg _))
  · refine intervalIntegral.norm_integral_le_of_norm_le ht (ae_of_all _ fun τ hτ => ?_)
      ((hI.rexp.mul (hB.clm_apply hu).norm).intervalIntegrable _ _)
    exact ((s.stateTransition t τ).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (s.norm_stateTransition_le hA hτ.2) (norm_nonneg _))

/-- **Coppel's inequality for a constant `A`**: `‖Φ(t, t₀)‖ ≤ e^{μ(A)(t - t₀)}` for `t₀ ≤ t`. -/
theorem norm_stateTransition_le_of_const (s : ContinuousLTV E U Y) {A : E →L[ℝ] E}
    (hA : ∀ τ, s.A τ = A) {t₀ t : ℝ} (ht : t₀ ≤ t) :
    ‖s.stateTransition t t₀‖ ≤ exp (μ A * (t - t₀)) := by
  have hc : Continuous s.A := by rw [show s.A = fun _ => A from funext hA]; exact continuous_const
  have h := s.norm_stateTransition_le hc ht
  simpa [hA, mul_comm] using h

/-- **The forced response for a constant `A` with `μ(A) < 0`**: if `‖B(τ) u(τ)‖ ≤ β` on
`[t₀, t]`, then `‖x(t)‖ ≤ e^{μ(A)(t - t₀)} ‖x₀‖ + β / (-μ(A))`. -/
@[blueprint "thm:continuousLTV-norm-forcedResponse-le-of-const"
  (title := "Input-to-state bound for a contracting linear system")
  (statement := /-- For a constant $A$ with $\mu(A) < 0$, $B$ and $u$ continuous, and
    $\|B(\tau) u(\tau)\| \le \beta$ on $[t_0, t]$, the forced response from $x_0$ satisfies
    \[ \|x(t)\| \le e^{\mu(A)(t - t_0)} \|x_0\| + \frac{\beta}{-\mu(A)}. \]

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Section 2.4. -/)
  (proof := /-- \cref{thm:continuousLTV-norm-forcedResponse-le}, with
    $\int_{t_0}^t e^{\mu(A)(t - \tau)} \beta \, d\tau
      = \beta \, \frac{1 - e^{\mu(A)(t - t_0)}}{-\mu(A)} \le \frac{\beta}{-\mu(A)}$. -/)]
theorem norm_forcedResponse_le_of_const (s : ContinuousLTV E U Y) {A : E →L[ℝ] E}
    (hA : ∀ τ, s.A τ = A) (hμ : μ A < 0) (hB : Continuous s.B) {u : ℝ → U} (hu : Continuous u)
    {β : ℝ} {t₀ t : ℝ} (ht : t₀ ≤ t) (hβ : ∀ τ ∈ Icc t₀ t, ‖s.B τ (u τ)‖ ≤ β) (x₀ : E) :
    ‖s.forcedResponse u t₀ x₀ t‖ ≤ exp (μ A * (t - t₀)) * ‖x₀‖ + β / (-μ A) := by
  have hc : Continuous s.A := by rw [show s.A = fun _ => A from funext hA]; exact continuous_const
  have h := s.norm_forcedResponse_le hc hB hu ht x₀
  simp only [hA, intervalIntegral.integral_const, smul_eq_mul] at h
  refine h.trans (add_le_add (by rw [mul_comm (t - t₀)]) ?_)
  -- `∫_{t₀}^t e^{μ (t - τ)} ‖B u‖ ≤ β ∫_{t₀}^t e^{μ (t - τ)} = β (1 - e^{μ (t - t₀)}) / (-μ)`
  have hint : ∫ τ in t₀..t, exp ((t - τ) * μ A) = (1 - exp ((t - t₀) * μ A)) / (-μ A) := by
    have hd (τ : ℝ) : HasDerivAt (fun τ => exp ((t - τ) * μ A) / (-μ A))
        (exp ((t - τ) * μ A)) τ := by
      have hne : μ A ≠ 0 := hμ.ne
      have := (((hasDerivAt_id' τ).const_sub t).mul_const (μ A)).exp.div_const (-μ A)
      convert this using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hd τ)
      ((by fun_prop : Continuous fun τ => exp ((t - τ) * μ A)).intervalIntegrable _ _)]
    simp only [sub_self, zero_mul, exp_zero]
    ring
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ t₀ (left_mem_Icc.2 ht))
  calc ∫ τ in t₀..t, exp ((t - τ) * μ A) * ‖s.B τ (u τ)‖
      ≤ ∫ τ in t₀..t, exp ((t - τ) * μ A) * β := by
        refine intervalIntegral.integral_mono_on ht
          ((by fun_prop : Continuous fun τ => exp ((t - τ) * μ A)).mul
            (hB.clm_apply hu).norm |>.intervalIntegrable _ _)
          ((by fun_prop : Continuous fun τ => exp ((t - τ) * μ A) * β).intervalIntegrable _ _)
          fun τ hτ => mul_le_mul_of_nonneg_left (hβ τ hτ) (exp_pos _).le
    _ = β * ((1 - exp ((t - t₀) * μ A)) / (-μ A)) := by
        rw [intervalIntegral.integral_mul_const, hint, mul_comm]
    _ ≤ β / (-μ A) := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right (neg_pos.2 hμ)]
        nlinarith [exp_pos ((t - t₀) * μ A)]

end ContinuousLTV

end LinearSystems

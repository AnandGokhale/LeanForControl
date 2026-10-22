import LeanForControl.Stability.Continuous.Boundedness
import Architect

/-!
# `Stability.Continuous.ISS` — input-to-state stability

A system with input is *input-to-state stable* when every trajectory obeys
`‖x(t) - x_eq‖ ≤ β(‖x(t₀) - x_eq‖, t - t₀) + γ(M)` for any bound `M` on the input over
`[t₀, t]`: the effect of the initial state decays, and the input contributes at most a gain of
its size.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Section 4.9, Definition 4.7 and Theorem 4.19;
Sontag, *Input to state stability: basic concepts and results*, in *Nonlinear and Optimal Control
Theory*, Lecture Notes in Mathematics 1932, Springer (2008).

## Main results

* `InputToStateStable` — Khalil's Definition 4.7, with a class `K∞` gain.
* `norm_le_of_isISSLyapunov` — the estimate of Khalil's Theorem 4.19, for a merely monotone `ρ`:
  `‖x(t) - x_c‖ ≤ β(‖x(t₀) - x_c‖, t - t₀) + α₁⁻¹(α₂(ρ(M)))`.
* `inputToStateStable_of_isISSLyapunov` — Theorem 4.19 itself, with `ρ` of class `K∞`.
* `InputToStateStable.globallyUniformlyAsymptoticallyStable` — the unforced system of an
  input-to-state stable system is globally uniformly asymptotically stable.

## The argument

Fix an input `u` and a time `t`, and freeze `u` into the system: `ẋ = F(τ, x, u(τ))` is an
unforced time-varying system.  Clamping `u` to `[t₀, t]` keeps the decrease condition
`V̇ ≤ -W₃(x)` for `‖x - x_c‖ ≥ ρ(M)` at every time.  The global ultimate boundedness theorem then
applies with `μ = ρ(M)`, and its class `KL` function `β` depends neither on the system nor on `μ`,
so the same `β` serves every input.

## Differences from Khalil

* The input enters through any bound `M` on `‖u‖` over `[t₀, t]` rather than its supremum; the
  two are equivalent, taking `M` to be the supremum, and a bound avoids the junk value of `sSup`
  on an unbounded set.
* The gain `γ` is class `K∞` rather than class `K`, as in Sontag.  Nothing is lost: a class `K`
  gain `γ` is dominated by `γ + id`, of class `K∞`.  Theorem 4.19 accordingly asks for `ρ` of
  class `K∞`, also no loss, since enlarging `ρ` only weakens its hypothesis;
  `norm_le_of_isISSLyapunov` keeps Khalil's exact gain `α₁⁻¹ ∘ α₂ ∘ ρ` for any monotone `ρ`.
* As for every bound in this library, trajectories are quantified on segments: solutions are not
  required to exist for all time.  A global bound rules out escape in finite time.
-/

open Set Filter Topology Metric

namespace ContinuousSystem

variable {E U Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup U]

/-- The system is **input-to-state stable** about `x_eq`: there are a global class `KL` function
`β` and a class `K∞` gain `γ` with `‖x(t) - x_eq‖ ≤ β(‖x(t₀) - x_eq‖, t - t₀) + γ(M)` along every
trajectory, whenever `M` bounds `‖u‖` on `[t₀, t]`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.7; Sontag (2008), for the class
`K∞` gain. -/
@[blueprint "def:continuousSystem-inputToStateStable"
  (title := "Input-to-state stability")
  (statement := /-- A continuous-time system with input is \emph{input-to-state stable} about
    $x_{\mathrm{eq}}$ when there are a global class $\mathcal{KL}$ function $\beta$
    (\cref{def:isClassKLGlobal}) and a class $\mathcal{K}_{\infty}$ function $\gamma$
    (\cref{def:isClassKInfty}) such that every trajectory on a segment $[t_0, t_1]$,
    $t_0 \ge 0$, under any input $u$ satisfies
    \[
      \|x(t) - x_{\mathrm{eq}}\| \le \beta(\|x(t_0) - x_{\mathrm{eq}}\|, t - t_0) + \gamma(M)
      \qquad \forall\, t \in [t_0, t_1]
    \]
    whenever $\|u(\tau)\| \le M$ for all $\tau \in [t_0, t]$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.7.  Differences:
    \begin{itemize} \item Any bound $M$ on the input replaces its supremum, which is equivalent.
    \item $\gamma$ is class $\mathcal{K}_{\infty}$, as in Sontag, rather than class
    $\mathcal{K}$; a class $\mathcal{K}$ gain $\gamma$ is dominated by $\gamma + \mathrm{id}$.
    \item Solutions are not required to exist for all time. \end{itemize} -/)]
def InputToStateStable (s : ContinuousSystem E U Y) (x_eq : E) : Prop :=
  ∃ β : ClassKLGlobal, ∃ γ : ClassKInfty, ∀ t₀ : ℝ, 0 ≤ t₀ →
    ∀ (t₁ : ℝ) (u : ℝ → U) (x : ℝ → E), s.IsTrajectoryOn u x (Icc t₀ t₁) →
      ∀ t ∈ Icc t₀ t₁, ∀ M : ℝ, (∀ τ ∈ Icc t₀ t, ‖u τ‖ ≤ M) →
        ‖x t - x_eq‖ ≤ β.toFun ‖x t₀ - x_eq‖ (t - t₀) + γ.toFun M

/-- **Input-to-state stability implies global uniform asymptotic stability of the unforced
system**: with `u ≡ 0` and `M = 0` the estimate is a global class `KL` bound.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Section 4.9, after Definition 4.7. -/
@[blueprint "thm:continuousSystem-inputToStateStable-globallyUniformlyAsymptoticallyStable"
  (title := "Input-to-state stability implies global uniform asymptotic stability")
  (statement := /-- If $s$ is input-to-state stable about $x_{\mathrm{eq}}$
    (\cref{def:continuousSystem-inputToStateStable}), then $x_{\mathrm{eq}}$ is a globally
    uniformly asymptotically stable equilibrium of the unforced system $\dot x = F(t, x, 0)$
    (\cref{def:continuousSystem-globallyUniformlyAsymptoticallyStable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Section 4.9. -/)
  (proof := /-- With $u \equiv 0$ and $M = 0$, $\gamma(M) = 0$ and the estimate is
    $\|x(t) - x_{\mathrm{eq}}\| \le \beta(\|x(t_0) - x_{\mathrm{eq}}\|, t - t_0)$.  The bound
    $\beta(r, s) + r e^{-s}$ is again global class $\mathcal{KL}$, now also radially unbounded,
    and \cref{lem:continuousSystem-globallyUniformlyAsymptoticallyStable-iff-classKL}
    concludes. -/)]
theorem InputToStateStable.globallyUniformlyAsymptoticallyStable {s : ContinuousSystem E U Y}
    {x_eq : E} (h : s.InputToStateStable x_eq) :
    s.zeroInput.GloballyUniformlyAsymptoticallyStable x_eq := by
  obtain ⟨β, γ, hβ⟩ := h
  -- `β(r, s) + r e^{-s}`: adding `r e^{-s}` makes `β(·, 0)` radially unbounded.
  refine (globallyUniformlyAsymptoticallyStable_iff_classKL _ _).mpr
    ⟨fun r σ => β.toFun r σ + r * Real.exp (-σ), fun σ hσ => by simp [β.map_zero σ hσ],
      β.continuous.add (continuous_fst.mul (continuous_snd.neg.rexp)).continuousOn,
      fun σ hσ a ha b hb hab =>
        add_lt_add (β.strict_mono_r σ hσ ha hb hab) (mul_lt_mul_of_pos_right hab (Real.exp_pos _)),
      ?_, fun r hr => (β.anti_s r hr).add fun a _ b _ hab =>
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hab)) hr,
      fun r hr => by
        simpa using (β.tendsto_zero r hr).add
          (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul r),
      fun t₀ ht₀ t₁ x hx t ht => ?_⟩
  · simpa using tendsto_atTop_add_left_of_le' atTop 0
      ((eventually_ge_atTop 0).mono fun r hr => β.nonneg r hr 0 le_rfl) tendsto_id
  · -- With `u ≡ 0` and `M = 0`, `γ(M) = 0`.
    have h := hβ t₀ ht₀ t₁ (fun _ => 0) x hx t ht 0 fun _ _ => by simp
    rw [γ.map_zero, add_zero] at h
    exact h.trans (le_add_of_nonneg_right
      (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le))

section ISSLyapunov

universe u

variable {U' Y' : Type u} [NormedAddCommGroup U'] {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- **The input-to-state estimate of an ISS-Lyapunov function.**  Let
`α₁(‖x - x_c‖) ≤ V(t, x) ≤ α₂(‖x - x_c‖)` with `α₁, α₂` of class `K∞`, and `V̇ ≤ -W₃(x)`
whenever `‖x - x_c‖ ≥ ρ(‖u‖)`, with `W₃` positive definite and `ρ` nonnegative and monotone.
Then `‖x(t) - x_c‖ ≤ β(‖x(t₀) - x_c‖, t - t₀) + α₁⁻¹(α₂(ρ(M)))` whenever `M` bounds `‖u‖` on
`[t₀, t]`, for a single global class `KL` function `β`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.19 and its proof. -/
@[blueprint "thm:continuousSystem-norm-le-of-isISSLyapunov"
  (title := "Input-to-state estimate from an ISS-Lyapunov function")
  (statement := /-- Let the state space be $\mathbb{R}^n$, $V$ differentiable, $\alpha_1,
    \alpha_2$ class $\mathcal{K}_{\infty}$, $W_3$ positive definite about $x_c$ on
    $\mathbb{R}^n$ (\cref{def:isPositiveDefiniteOn}), and $\rho : [0, \infty) \to [0, \infty)$
    nondecreasing, with
    \[
      \alpha_1(\|x - x_c\|) \le V(t, x) \le \alpha_2(\|x - x_c\|), \qquad
      \dot V(t, x, u) \le -W_3(x) \quad \text{for } \|x - x_c\| \ge \rho(\|u\|)
    \]
    for all $t \ge 0$, $x$ and $u$.  Then there is a global class $\mathcal{KL}$ function
    $\beta$ such that every trajectory on a segment $[t_0, t_1]$, $t_0 \ge 0$, satisfies
    \[
      \|x(t) - x_c\| \le \beta(\|x(t_0) - x_c\|, t - t_0) + \alpha_1^{-1}(\alpha_2(\rho(M)))
    \]
    for $t \in [t_0, t_1]$, whenever $\|u(\tau)\| \le M$ for all $\tau \in [t_0, t]$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.19, whose $\rho$ is class
    $\mathcal{K}$; only its monotonicity is used. -/)
  (proof := /-- Fix the input and $t$.  Freeze the input, clamped to $[t_0, t]$, into the
    system: $\dot x = F(\tau, x, u(\tau))$ is an unforced system with the same trajectories on
    $[t_0, t]$, and since $\|u(\tau)\| \le M$ and $\rho$ is nondecreasing, $\dot V \le -W_3$
    wherever $\|x - x_c\| \ge \rho(M)$.  Apply
    \cref{thm:continuousSystem-exists-classKLGlobal-ultimateBound-of-lyapunov} with
    $\mu = \rho(M)$; its $\beta$ does not depend on the system or on $\mu$, so it is the same for
    every input.  Finally $\max\{a, b\} \le a + b$ for $a, b \ge 0$. -/)]
theorem norm_le_of_isISSLyapunov [NeZero n] {s : ContinuousSystem ℝⁿ U' Y'}
    {V : ℝ → ℝⁿ → ℝ} {x_c : ℝⁿ} (α₁ α₂ : ClassKInfty) {W₃ : ℝⁿ → ℝ} {ρ : ℝ → ℝ}
    (hV : Differentiable ℝ (Function.uncurry V))
    (hV_bd : ∀ t : ℝ, 0 ≤ t → ∀ y : ℝⁿ,
      α₁.toFun ‖y - x_c‖ ≤ V t y ∧ V t y ≤ α₂.toFun ‖y - x_c‖)
    (hW₃ : IsPositiveDefiniteOn W₃ x_c univ)
    (hρ_mono : MonotoneOn ρ (Ici 0)) (hρ_nonneg : ∀ r, 0 ≤ r → 0 ≤ ρ r)
    (hlie : ∀ t : ℝ, 0 ≤ t → ∀ (y : ℝⁿ) (w : U'), ρ ‖w‖ ≤ ‖y - x_c‖ →
      s.lieDerivative V t y w ≤ -W₃ y) :
    ∃ β : ClassKLGlobal, ∀ t₀ : ℝ, 0 ≤ t₀ →
      ∀ (t₁ : ℝ) (u : ℝ → U') (x : ℝ → ℝⁿ), s.IsTrajectoryOn u x (Icc t₀ t₁) →
        ∀ t ∈ Icc t₀ t₁, ∀ M : ℝ, (∀ τ ∈ Icc t₀ t, ‖u τ‖ ≤ M) →
          ‖x t - x_c‖ ≤ β.toFun ‖x t₀ - x_c‖ (t - t₀) + α₁.invFun (α₂.toFun (ρ M)) := by
  -- `β` is chosen once, before the input.
  obtain ⟨β, hβ⟩ := exists_classKLGlobal_ultimateBound_of_lyapunov.{u} α₁ α₂ hW₃
  refine ⟨β, fun t₀ ht₀ t₁ u x hx t ht M hM => ?_⟩
  have hM_nonneg : 0 ≤ M := (norm_nonneg _).trans (hM t₀ ⟨le_rfl, ht.1⟩)
  -- Step 1. Freeze the input, clamped to `[t₀, t]`, into an unforced system.
  let clamp : ℝ → ℝ := fun τ => max t₀ (min τ t)
  have h_clamp_mem : ∀ τ, clamp τ ∈ Icc t₀ t := fun τ =>
    ⟨le_max_left _ _, max_le ht.1 (min_le_right _ _)⟩
  have h_clamp_eq : ∀ τ ∈ Icc t₀ t, clamp τ = τ := fun τ hτ => by
    simp only [clamp, min_eq_left hτ.2, max_eq_right hτ.1]
  let s' : ContinuousSystem ℝⁿ Unit Y' :=
    autonomous (fun τ y => s.F τ y (u (clamp τ))) (fun τ y => s.h τ y (u (clamp τ)))
  -- On `[t₀, t]` the frozen system has the same trajectories ...
  have hx' : s'.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t) := fun τ hτ => by
    simpa [s', vectorField, h_clamp_eq τ hτ] using
      (hx τ ⟨hτ.1, hτ.2.trans ht.2⟩).mono (Icc_subset_Icc_right ht.2)
  -- ... and `V̇ ≤ -W₃` outside the ball of radius `ρ(M)`, as `ρ(‖u‖) ≤ ρ(M)` at every time.
  have hlie' : ∀ τ : ℝ, 0 ≤ τ → ∀ y : ℝⁿ, ρ M ≤ ‖y - x_c‖ →
      s'.lieDerivative V τ y () ≤ -W₃ y := fun τ hτ y hy =>
    hlie τ hτ y (u (clamp τ)) ((hρ_mono (norm_nonneg _) hM_nonneg
      (hM _ (h_clamp_mem τ))).trans hy)
  -- Step 2. The global ultimate bound with `μ = ρ(M)`, and `max ≤ sum`.
  have h := hβ hV hV_bd hlie' (hρ_nonneg M hM_nonneg) t₀ ht₀ t x hx' t ⟨ht.1, le_rfl⟩
  exact h.trans (max_le_add_of_nonneg (β.nonneg _ (norm_nonneg _) _ (sub_nonneg.mpr ht.1))
    (α₁.inv_maps_to (α₂.maps_to (hρ_nonneg M hM_nonneg))))

/-- **ISS-Lyapunov functions certify input-to-state stability**, with gain
`γ = α₁⁻¹ ∘ α₂ ∘ ρ`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.19. -/
@[blueprint "thm:continuousSystem-inputToStateStable-of-isISSLyapunov"
  (title := "ISS-Lyapunov theorem")
  (statement := /-- Under the hypotheses of \cref{thm:continuousSystem-norm-le-of-isISSLyapunov}
    with $\rho$ class $\mathcal{K}_{\infty}$, the system is input-to-state stable about $x_c$
    (\cref{def:continuousSystem-inputToStateStable}) with gain
    $\gamma = \alpha_1^{-1} \circ \alpha_2 \circ \rho$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.19, with $\rho$ of class
    $\mathcal{K}$; a class $\mathcal{K}$ $\rho$ can be replaced by $\rho + \mathrm{id}$, which
    only weakens the hypothesis. -/)
  (proof := /-- \cref{thm:continuousSystem-norm-le-of-isISSLyapunov}, with
    $\alpha_1^{-1} \circ \alpha_2 \circ \rho$ class $\mathcal{K}_{\infty}$
    (\cref{lem:classKInfty-symm}, \cref{lem:classKInfty-comp}). -/)]
theorem inputToStateStable_of_isISSLyapunov [NeZero n] {s : ContinuousSystem ℝⁿ U' Y'}
    {V : ℝ → ℝⁿ → ℝ} {x_c : ℝⁿ} (α₁ α₂ ρ : ClassKInfty) {W₃ : ℝⁿ → ℝ}
    (hV : Differentiable ℝ (Function.uncurry V))
    (hV_bd : ∀ t : ℝ, 0 ≤ t → ∀ y : ℝⁿ,
      α₁.toFun ‖y - x_c‖ ≤ V t y ∧ V t y ≤ α₂.toFun ‖y - x_c‖)
    (hW₃ : IsPositiveDefiniteOn W₃ x_c univ)
    (hlie : ∀ t : ℝ, 0 ≤ t → ∀ (y : ℝⁿ) (w : U'), ρ.toFun ‖w‖ ≤ ‖y - x_c‖ →
      s.lieDerivative V t y w ≤ -W₃ y) :
    s.InputToStateStable x_c := by
  obtain ⟨β, hβ⟩ := norm_le_of_isISSLyapunov α₁ α₂ hV hV_bd hW₃ ρ.strict_mono.monotoneOn
    (fun r hr => ρ.maps_to hr) hlie
  exact ⟨β, α₁.symm.comp (α₂.comp ρ), hβ⟩

end ISSLyapunov

end ContinuousSystem

import LeanForControl.Stability.Continuous.ISS
import LeanForControl.Stability.Continuous.KLCharacterization
import LeanForControl.Analysis.Norm
import Architect

/-!
# `Stability.Continuous.Cascade` — cascades of input-to-state stable systems

In the cascade `ẋ₁ = f₁(t, x₁, x₂)`, `ẋ₂ = f₂(t, x₂)`, the second system drives the first.  If the
driven system is input-to-state stable with `x₂` as its input and the driving system is globally
uniformly asymptotically stable, the cascade is globally uniformly asymptotically stable: `x₂`
decays, and with it its effect on `x₁`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Section 4.9, Lemma 4.7.

## Main results

* `cascade_globallyUniformlyAsymptoticallyStable` — Khalil's Lemma 4.7.
* `cascade_inputToStateStable` — a cascade of input-to-state stable systems is input-to-state
  stable.

## Differences from Khalil

* No regularity is assumed of `f₁` or `f₂`: input-to-state stability and global uniform asymptotic
  stability are estimates on trajectories, and the lemmas are statements about trajectories.
* The equilibria are a general `(x_c, x_e)`.  The driven system is input-to-state stable about
  `(x_c, x_e)`: its input, the driving state, is measured from `x_e`.

## The class `KL` bound

Both lemmas bound the cascade by
`β(r, s) = β₁(c(β₁(r, s/2) + γ₁(cβ₂(r, 0))), s/2) + γ₁(cβ₂(r, s/2)) + β₂(r, s)`, Khalil's with
`c = 1`; with an input, `c = 2` leaves room to split off the input's contribution
(`f(a + b) ≤ f(2a) + f(2b)`).
-/

open Set Filter Topology

namespace ContinuousSystem

/-- **The class `KL` bound of a cascade**:
`β(r, s) = β₁(c(β₁(r, s/2) + γ₁(cβ₂(r, 0))), s/2) + γ₁(cβ₂(r, s/2)) + β₂(r, s)`. -/
private noncomputable def cascadeKL (β₁ : ClassKLGlobal) (γ₁ : ClassKInfty) (β₂ : ClassKLGlobal)
    {c : ℝ} (hc : 0 < c) : ClassKLGlobal :=
  -- `κ(r, s) = γ₁(cβ₂(r, s))`, and `a(r, σ) = c(β₁(r, σ/2) + κ(r, 0))` bounds the driven state
  -- at the midpoint.
  let κ := (β₂.smul c hc).comp_left γ₁
  let β₁' := β₁.timeScale 2 two_pos
  (β₁'.comp_antitone (fun r σ => c * (β₁'.toFun r σ + κ.toFun r 0))
    (fun σ hσ => by simp [β₁'.map_zero σ hσ, κ.map_zero 0 le_rfl])
    (continuousOn_const.mul (β₁'.continuous.add (κ.continuous.comp
      (continuousOn_fst.prodMk continuousOn_const) fun p hp => ⟨hp.1, mem_Ici.2 le_rfl⟩)))
    (fun σ hσ r hr r' hr' h => mul_lt_mul_of_pos_left (add_lt_add_of_lt_of_le
      (β₁'.strict_mono_r σ hσ hr hr' h) (κ.mono_r hr le_rfl h.le)) hc)
    (fun r hr σ hσ σ' hσ' h => mul_le_mul_of_nonneg_left
      (add_le_add (β₁'.anti_s r hr hσ hσ' h) le_rfl) hc.le)).add
    ((β₂.timeScale 2 two_pos).smul c hc |>.comp_left γ₁) |>.add β₂

/-- **The driven state of a cascade.**  Let `s₁` be input-to-state stable about `(x_c, x_e)` with
data `β₁, γ₁`, and let the driving state obey
`‖x₂(τ) - x_e‖ ≤ β₂(r, τ - t₀) + g` on `[t₀, t]`, with `‖x₁(t₀) - x_c‖ ≤ r`.  Then, applying
input-to-state stability on `[t₀, m]` and on `[m, t]`, `m = (t₀ + t)/2`,
`‖x₁(t) - x_c‖ ≤ β₁(β₁(r, s/2) + γ₁(β₂(r, 0) + g), s/2) + γ₁(β₂(r, s/2) + g)`, `s = t - t₀`. -/
private lemma norm_fst_sub_le_of_cascade {E₁ E₂ Y₁ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {s₁ : ContinuousSystem E₁ E₂ Y₁} {x_c : E₁} {x_e : E₂} {β₁ : ClassKLGlobal}
    {γ₁ : ClassKInfty}
    (hISS : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (u : ℝ → E₂) (x : ℝ → E₁),
      s₁.IsRightTrajectoryOn u x (Icc t₀ t₁) →
        ∀ t ∈ Icc t₀ t₁, ∀ M : ℝ, (∀ τ ∈ Icc t₀ t, ‖u τ - x_e‖ ≤ M) →
          ‖x t - x_c‖ ≤ β₁.toFun ‖x t₀ - x_c‖ (t - t₀) + γ₁.toFun M)
    {β₂ : ClassKLGlobal} {g r t₀ t₁ t : ℝ} (ht₀ : 0 ≤ t₀) (ht : t ∈ Icc t₀ t₁)
    {x₁ : ℝ → E₁} {x₂ : ℝ → E₂} (hx₁ : s₁.IsRightTrajectoryOn x₂ x₁ (Icc t₀ t₁))
    (hr₁ : ‖x₁ t₀ - x_c‖ ≤ r) (h_x₂ : ∀ τ ∈ Icc t₀ t, ‖x₂ τ - x_e‖ ≤ β₂.toFun r (τ - t₀) + g) :
    ‖x₁ t - x_c‖ ≤ β₁.toFun (β₁.toFun r ((t - t₀) / 2) + γ₁.toFun (β₂.toFun r 0 + g))
      ((t - t₀) / 2) + γ₁.toFun (β₂.toFun r ((t - t₀) / 2) + g) := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hr₁
  set m := (t₀ + t) / 2
  have hσ : 0 ≤ (t - t₀) / 2 := by linarith [ht.1]
  have hm₀ : t₀ ≤ m := by simp only [m]; linarith [ht.1]
  have hm : m ≤ t := by simp only [m]; linarith [ht.1]
  have h_half : m - t₀ = (t - t₀) / 2 := by simp only [m]; ring
  have h_half' : t - m = (t - t₀) / 2 := by simp only [m]; ring
  -- On `[t₀, m]` the input is at most `β₂(r, 0) + g`.
  have h_mid : ‖x₁ m - x_c‖ ≤ β₁.toFun r ((t - t₀) / 2) + γ₁.toFun (β₂.toFun r 0 + g) := by
    have h := hISS t₀ ht₀ t₁ _ x₁ hx₁ m ⟨hm₀, hm.trans ht.2⟩ (β₂.toFun r 0 + g)
      fun τ hτ => (h_x₂ τ ⟨hτ.1, hτ.2.trans hm⟩).trans
        (add_le_add (β₂.anti_s_mono hr le_rfl (by linarith [hτ.1])) le_rfl)
    rw [h_half] at h
    exact h.trans (add_le_add (β₁.mono_r (norm_nonneg _) hσ hr₁) le_rfl)
  -- On `[m, t]` the input is at most `β₂(r, (t - t₀)/2) + g`.
  have h := hISS m (ht₀.trans hm₀) t₁ _ x₁ (hx₁.mono (Icc_subset_Icc_left hm₀)) t ⟨hm, ht.2⟩
    (β₂.toFun r ((t - t₀) / 2) + g) fun τ hτ => (h_x₂ τ ⟨hm₀.trans hτ.1, hτ.2⟩).trans
      (add_le_add (β₂.anti_s_mono hr hσ (by linarith [hτ.1])) le_rfl)
  rw [h_half'] at h
  exact h.trans (add_le_add (β₁.mono_r (norm_nonneg _) hσ h_mid) le_rfl)

variable {E₁ E₂ Y₁ Y₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- **A cascade of an input-to-state stable system and a globally uniformly asymptotically stable
one is globally uniformly asymptotically stable.**  If `s₁`, with the state of `s₂` as its input,
is input-to-state stable about `(x_c, x_e)`, and `x_e` is globally uniformly
asymptotically stable for `s₂`, then `(x_c, x_e)` is globally uniformly asymptotically stable
for the cascade.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.7.  Differences: no regularity of the
fields is assumed; the equilibria are general, with `s₁`'s input measured from `x_e`. -/
@[blueprint "lem:continuousSystem-cascade-globallyUniformlyAsymptoticallyStable"
  (title := "Cascades of input-to-state stable systems")
  (latexEnv := "lemma")
  (statement := /-- Let $s_1$, with input $x_2$, be input-to-state stable about $(x_c, x_e)$
    (\cref{def:continuousSystem-inputToStateStable}), and let $x_e$ be globally uniformly
    asymptotically stable for $s_2$
    (\cref{def:continuousSystem-globallyUniformlyAsymptoticallyStable}).  Then $(x_c, x_e)$ is
    globally uniformly asymptotically stable for the cascade
    (\cref{def:continuousSystem-cascade}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.7.  Differences: no
    regularity of the fields is assumed, since both hypotheses are estimates on trajectories;
    the equilibria are general, with the input of $s_1$ measured from $x_e$. -/)
  (proof := /-- Let $\beta_1, \gamma_1$ be the input-to-state stability data of $s_1$ and
    $\beta_2$ a class $\mathcal{KL}$ bound for $s_2$
    (\cref{lem:continuousSystem-globallyUniformlyAsymptoticallyStable-iff-classKL}).  With
    $r = \|x(t_0) - (x_c, x_e)\|$, $s = t - t_0$ and $m = (t_0 + t)/2$, input-to-state stability
    on $[t_0, m]$ and on $[m, t]$, with the input bounded by $\beta_2(r, 0)$ and by
    $\beta_2(r, s/2)$, gives
    \[
      \|x_1(t) - x_c\| \le \beta_1\bigl(\beta_1(r, s/2) + \gamma_1(\beta_2(r, 0)), s/2\bigr)
        + \gamma_1(\beta_2(r, s/2)),
    \]
    and $\|x_2(t) - x_e\| \le \beta_2(r, s)$.  The sum $\beta(r, s)$ of the right-hand sides is
    class $\mathcal{KL}$, and bounds
    $\|x(t) - (x_c, x_e)\| = \max(\|x_1 - x_c\|, \|x_2 - x_e\|)$. -/)]
theorem cascade_globallyUniformlyAsymptoticallyStable {s₁ : ContinuousSystem E₁ E₂ Y₁}
    {s₂ : ContinuousSystem E₂ Unit Y₂} {x_c : E₁} {x_e : E₂}
    (h₁ : s₁.InputToStateStable x_c x_e) (h₂ : s₂.GloballyUniformlyAsymptoticallyStable x_e) :
    (cascade s₁ s₂).GloballyUniformlyAsymptoticallyStable (x_c, x_e) := by
  obtain ⟨β₁, γ₁, hISS⟩ := h₁
  obtain ⟨β₂, hβ₂⟩ := (globallyUniformlyAsymptoticallyStable_iff_classKL s₂ x_e).1 h₂
  set β := cascadeKL β₁ γ₁ β₂ one_pos
  have hβ : ∀ r σ, β.toFun r σ =
      β₁.toFun (β₁.toFun r (σ / 2) + γ₁.toFun (β₂.toFun r 0)) (σ / 2) +
        γ₁.toFun (β₂.toFun r (σ / 2)) + β₂.toFun r σ := fun r σ => by
      simp [β, cascadeKL, ClassKLGlobal.add, ClassKLGlobal.smul, ClassKLGlobal.timeScale,
        ClassKLGlobal.comp_left, ClassKLGlobal.comp_antitone]
  refine (globallyUniformlyAsymptoticallyStable_iff_classKL _ _).2 ⟨β, ?_⟩
  -- The estimate along a trajectory.
  intro t₀ ht₀ t₁ x hx t ht
  obtain ⟨hx₁, hx₂⟩ := cascade_isTrajectoryOn_iff.1 hx
  set r := ‖x t₀ - (x_c, x_e)‖
  have hr₁ : ‖(x t₀).1 - x_c‖ ≤ r := norm_fst_le (x t₀ - (x_c, x_e))
  have hr₂ : ‖(x t₀).2 - x_e‖ ≤ r := norm_snd_le (x t₀ - (x_c, x_e))
  have h_x₂ : ∀ τ ∈ Icc t₀ t₁, ‖(x τ).2 - x_e‖ ≤ β₂.toFun r (τ - t₀) + 0 := fun τ hτ => by
    rw [add_zero]
    exact (hβ₂ t₀ ht₀ t₁ (fun τ => (x τ).2) hx₂ τ hτ).trans
      (β₂.mono_r (norm_nonneg _) (by linarith [hτ.1]) hr₂)
  have h_x₁ := norm_fst_sub_le_of_cascade hISS ht₀ ht (IsTrajectoryOn.isRightTrajectoryOn hx₁) hr₁
    fun τ hτ => h_x₂ τ ⟨hτ.1, hτ.2.trans ht.2⟩
  simp only [add_zero] at h_x₁
  calc ‖x t - (x_c, x_e)‖
      ≤ ‖(x t).1 - x_c‖ + ‖(x t).2 - x_e‖ := Prod.norm_le_norm_fst_add_norm_snd _
    _ ≤ (β₁.toFun (β₁.toFun r ((t - t₀) / 2) + γ₁.toFun (β₂.toFun r 0)) ((t - t₀) / 2) +
          γ₁.toFun (β₂.toFun r ((t - t₀) / 2))) + (β₂.toFun r (t - t₀) + 0) :=
        add_le_add h_x₁ (h_x₂ t ht)
    _ = β.toFun r (t - t₀) := by rw [hβ, add_zero]

/-- **A cascade of input-to-state stable systems is input-to-state stable.**  If `s₁`, with the
state of `s₂` as its input, is input-to-state stable about `(x_c, x_e)`, and `s₂` is
input-to-state stable about `(x_e, w_eq)`, the cascade is input-to-state stable about
`((x_c, x_e), w_eq)`.

The proof is that of `cascade_globallyUniformlyAsymptoticallyStable`, with the input's
contribution `g = γ₂(M)` carried through and split off by `f(a + b) ≤ f(2a) + f(2b)`
(`MonotoneOn.weak_triangle`).

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Section 4.9, after Lemma 4.7; Sontag (2008). -/
@[blueprint "lem:continuousSystem-cascade-inputToStateStable"
  (title := "Cascades of input-to-state stable systems are input-to-state stable")
  (latexEnv := "lemma")
  (statement := /-- Let $s_1$, with input $x_2$, be input-to-state stable about $(x_c, x_e)$,
    and let $s_2$, with input $w$, be input-to-state stable about $(x_e, w_{\mathrm{eq}})$
    (\cref{def:continuousSystem-inputToStateStable}).  Then the cascade
    (\cref{def:continuousSystem-cascade}), with input $w$, is input-to-state stable about
    $((x_c, x_e), w_{\mathrm{eq}})$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Section 4.9; Sontag (2008). -/)
  (proof := /-- As in \cref{lem:continuousSystem-cascade-globallyUniformlyAsymptoticallyStable},
    with $\|x_2(\tau) - x_e\| \le \beta_2(r, \tau - t_0) + g$, $g = \gamma_2(M)$, carried
    through.  Splitting with $f(a + b) \le f(2a) + f(2b)$ for nondecreasing $f \ge 0$
    (\cref{lem:monotoneOn-weak-triangle}) gives
    $\|x(t) - (x_c, x_e)\| \le \beta(r, t - t_0) + \gamma(M)$, with $\beta$ the cascade bound for
    $c = 2$ and
    $\gamma(M) = \beta_1(2\gamma_1(2\gamma_2(M)), 0) + \gamma_1(2\gamma_2(M)) + \gamma_2(M)$,
    class $\mathcal{K}_\infty$ by \cref{lem:classKInfty-addMonotone}. -/)]
theorem cascade_inputToStateStable {W : Type*} [NormedAddCommGroup W]
    {s₁ : ContinuousSystem E₁ E₂ Y₁} {s₂ : ContinuousSystem E₂ W Y₂} {x_c : E₁} {x_e : E₂}
    {w_eq : W} (h₁ : s₁.InputToStateStable x_c x_e) (h₂ : s₂.InputToStateStable x_e w_eq) :
    (cascade s₁ s₂).InputToStateStable (x_c, x_e) w_eq := by
  obtain ⟨β₁, γ₁, hISS₁⟩ := h₁
  obtain ⟨β₂, γ₂, hISS₂⟩ := h₂
  -- The gain `γ(M) = γ₂(M) + γ₁(2γ₂(M)) + β₁(δ(M), 0)`, with `δ(M) = 2γ₁(2γ₂(M))`.
  let δ := (γ₁.comp (γ₂.smul 2 two_pos)).smul 2 two_pos
  let γ := (γ₂.add (γ₁.comp (γ₂.smul 2 two_pos))).addMonotone (fun M => β₁.toFun (δ M) 0)
    (by simp [δ.map_zero, β₁.map_zero 0 le_rfl])
    (β₁.continuous.comp (δ.continuous.prodMk continuousOn_const) fun M hM =>
      ⟨δ.maps_to hM, mem_Ici.2 le_rfl⟩)
    (fun a ha b hb h => β₁.mono_r (δ.maps_to ha) le_rfl (δ.strict_mono.monotoneOn ha hb h))
  have h_split : ∀ a b, 0 ≤ a → 0 ≤ b → γ₁.toFun (a + b) ≤ γ₁.toFun (2 * a) + γ₁.toFun (2 * b) :=
    fun _ _ => γ₁.strict_mono.monotoneOn.weak_triangle fun y hy => γ₁.maps_to hy
  refine ⟨cascadeKL β₁ γ₁ β₂ two_pos, γ, fun t₀ ht₀ t₁ w x hx t ht M hM => ?_⟩
  obtain ⟨hx₁, hx₂⟩ := cascade_isRightTrajectoryOn_iff.1 hx
  set r := ‖x t₀ - (x_c, x_e)‖
  have hr : 0 ≤ r := norm_nonneg _
  have hr₂ : ‖(x t₀).2 - x_e‖ ≤ r := norm_snd_le (x t₀ - (x_c, x_e))
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM t₀ ⟨le_rfl, ht.1⟩)
  set g := γ₂.toFun M
  have hg : 0 ≤ g := γ₂.maps_to hM₀
  -- The driving state, from its own input-to-state stability.
  have h_x₂ : ∀ τ ∈ Icc t₀ t, ‖(x τ).2 - x_e‖ ≤ β₂.toFun r (τ - t₀) + g := fun τ hτ =>
    (hISS₂ t₀ ht₀ t₁ w (fun τ => (x τ).2) hx₂ τ ⟨hτ.1, hτ.2.trans ht.2⟩ M
      fun σ hσ => hM σ ⟨hσ.1, hσ.2.trans hτ.2⟩).trans
      (add_le_add (β₂.mono_r (norm_nonneg _) (by linarith [hτ.1]) hr₂) le_rfl)
  have h_x₁ := norm_fst_sub_le_of_cascade hISS₁ ht₀ ht hx₁ (norm_fst_le (x t₀ - (x_c, x_e))) h_x₂
  -- Split off the input's contribution.
  set s := (t - t₀) / 2
  have hs : 0 ≤ s := by simp only [s]; linarith [ht.1]
  have hβ₂r : ∀ σ, 0 ≤ σ → 0 ≤ β₂.toFun r σ := fun σ hσ => β₂.nonneg r hr σ hσ
  have h_inner : β₁.toFun r s + γ₁.toFun (β₂.toFun r 0 + g) ≤
      (β₁.toFun r s + γ₁.toFun (2 * β₂.toFun r 0)) + γ₁.toFun (2 * g) := by
    rw [add_assoc]
    exact add_le_add le_rfl (h_split _ _ (hβ₂r 0 le_rfl) hg)
  have h_term₁ : β₁.toFun (β₁.toFun r s + γ₁.toFun (β₂.toFun r 0 + g)) s ≤
      β₁.toFun (2 * (β₁.toFun r s + γ₁.toFun (2 * β₂.toFun r 0))) s +
        β₁.toFun (2 * γ₁.toFun (2 * g)) 0 :=
    calc β₁.toFun (β₁.toFun r s + γ₁.toFun (β₂.toFun r 0 + g)) s
        ≤ β₁.toFun ((β₁.toFun r s + γ₁.toFun (2 * β₂.toFun r 0)) + γ₁.toFun (2 * g)) s :=
          β₁.mono_r (add_nonneg (β₁.nonneg r hr s hs) (γ₁.maps_to (add_nonneg (hβ₂r 0 le_rfl) hg)))
            hs h_inner
      _ ≤ β₁.toFun (2 * (β₁.toFun r s + γ₁.toFun (2 * β₂.toFun r 0))) s +
            β₁.toFun (2 * γ₁.toFun (2 * g)) s :=
          (β₁.strict_mono_r s hs).monotoneOn.weak_triangle (fun y hy => β₁.nonneg y hy s hs)
            (add_nonneg (β₁.nonneg r hr s hs) (γ₁.maps_to (mul_nonneg two_pos.le (hβ₂r 0 le_rfl))))
            (γ₁.maps_to (mul_nonneg two_pos.le hg))
      _ ≤ β₁.toFun (2 * (β₁.toFun r s + γ₁.toFun (2 * β₂.toFun r 0))) s +
            β₁.toFun (2 * γ₁.toFun (2 * g)) 0 :=
          add_le_add le_rfl (β₁.anti_s_mono
            (mul_nonneg two_pos.le (γ₁.maps_to (mul_nonneg two_pos.le hg))) le_rfl hs)
  calc ‖x t - (x_c, x_e)‖
      ≤ ‖(x t).1 - x_c‖ + ‖(x t).2 - x_e‖ := Prod.norm_le_norm_fst_add_norm_snd _
    _ ≤ (β₁.toFun (β₁.toFun r s + γ₁.toFun (β₂.toFun r 0 + g)) s +
          γ₁.toFun (β₂.toFun r s + g)) + (β₂.toFun r (t - t₀) + g) :=
        add_le_add h_x₁ (h_x₂ t ⟨ht.1, le_rfl⟩)
    _ ≤ (β₁.toFun (2 * (β₁.toFun r s + γ₁.toFun (2 * β₂.toFun r 0))) s +
          β₁.toFun (2 * γ₁.toFun (2 * g)) 0 + (γ₁.toFun (2 * β₂.toFun r s) +
            γ₁.toFun (2 * g))) + (β₂.toFun r (t - t₀) + g) :=
        add_le_add (add_le_add h_term₁ (h_split _ _ (hβ₂r s hs) hg)) le_rfl
    _ = (cascadeKL β₁ γ₁ β₂ two_pos).toFun r (t - t₀) + γ.toFun M := by
        simp only [γ, δ, cascadeKL, ClassKLGlobal.add, ClassKLGlobal.smul,
          ClassKLGlobal.timeScale, ClassKLGlobal.comp_left, ClassKLGlobal.comp_antitone,
          ClassKInfty.addMonotone_apply, ClassKInfty.add,
          ClassKInfty.comp, ClassKInfty.smul, ClassKInfty.of_strictMono, Function.comp_apply, s, g]
        ring

end ContinuousSystem

import LeanForControl.Stability.Continuous.ISS
import LeanForControl.Stability.Continuous.KLCharacterization
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
* The equilibria are a general `(x_c, x_e)`.  The driven system's input-to-state stability is
  measured from `x_e` (`shiftInput`); for `x_e = 0` this is input-to-state stability itself
  (`shiftInput_zero`).

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
  -- `a(r, σ)` bounds the driven state at the midpoint.
  have ha_nonneg : ∀ r, 0 ≤ r → ∀ σ, 0 ≤ σ →
      0 ≤ c * (β₁.toFun r (σ / 2) + γ₁.toFun (c * β₂.toFun r 0)) := fun r hr σ hσ =>
    mul_nonneg hc.le (add_nonneg (β₁.nonneg r hr _ (by positivity))
      (γ₁.maps_to (mul_nonneg hc.le (β₂.nonneg r hr 0 le_rfl))))
  have ha_le_s : ∀ r, 0 ≤ r → ∀ σ σ', 0 ≤ σ → σ ≤ σ' →
      c * (β₁.toFun r (σ' / 2) + γ₁.toFun (c * β₂.toFun r 0)) ≤
        c * (β₁.toFun r (σ / 2) + γ₁.toFun (c * β₂.toFun r 0)) := fun r hr σ σ' hσ h =>
    mul_le_mul_of_nonneg_left (add_le_add (β₁.anti_s_mono hr (by positivity) (by linarith))
      le_rfl) hc.le
  { toFun := fun r σ => β₁.toFun (c * (β₁.toFun r (σ / 2) + γ₁.toFun (c * β₂.toFun r 0))) (σ / 2) +
      γ₁.toFun (c * β₂.toFun r (σ / 2)) + β₂.toFun r σ
    map_zero := fun σ hσ => by
      simp only [β₂.map_zero 0 le_rfl, β₂.map_zero _ (by positivity : (0 : ℝ) ≤ σ / 2),
        β₂.map_zero σ hσ, mul_zero, γ₁.map_zero, β₁.map_zero _ (by positivity : (0 : ℝ) ≤ σ / 2),
        add_zero]
    continuous := by
      have h_half : ContinuousOn (fun p : ℝ × ℝ => p.2 / 2) (Ici 0 ×ˢ Ici 0) :=
        continuousOn_snd.div_const 2
      have h_mem : ∀ p ∈ Ici (0 : ℝ) ×ˢ Ici 0, p.2 / 2 ∈ Ici (0 : ℝ) := fun p hp =>
        mem_Ici.2 (by have := mem_Ici.1 hp.2; positivity)
      have h_β₂ : ContinuousOn (fun p : ℝ × ℝ => β₂.toFun p.1 (p.2 / 2)) (Ici 0 ×ˢ Ici 0) :=
        β₂.continuous.comp (continuousOn_fst.prodMk h_half) fun p hp => ⟨hp.1, h_mem p hp⟩
      have h_β₂0 : ContinuousOn (fun p : ℝ × ℝ => β₂.toFun p.1 0) (Ici 0 ×ˢ Ici 0) :=
        β₂.continuous.comp (continuousOn_fst.prodMk continuousOn_const)
          fun p hp => ⟨hp.1, mem_Ici.2 le_rfl⟩
      have h_a : ContinuousOn (fun p : ℝ × ℝ =>
          c * (β₁.toFun p.1 (p.2 / 2) + γ₁.toFun (c * β₂.toFun p.1 0))) (Ici 0 ×ˢ Ici 0) :=
        continuousOn_const.mul ((β₁.continuous.comp (continuousOn_fst.prodMk h_half)
          fun p hp => ⟨hp.1, h_mem p hp⟩).add (γ₁.continuous.comp (continuousOn_const.mul h_β₂0)
            fun p hp => mem_Ici.2 (mul_nonneg hc.le (β₂.nonneg _ hp.1 0 le_rfl))))
      exact ((β₁.continuous.comp (h_a.prodMk h_half) fun p hp =>
        ⟨mem_Ici.2 (ha_nonneg _ hp.1 _ hp.2), h_mem p hp⟩).add
        (γ₁.continuous.comp (continuousOn_const.mul h_β₂) fun p hp =>
          mem_Ici.2 (mul_nonneg hc.le (β₂.nonneg _ hp.1 _ (h_mem p hp))))).add β₂.continuous
    strict_mono_r := fun σ hσ r hr r' hr' h => by
      have hr₀ : (0 : ℝ) ≤ r := hr
      exact add_lt_add_of_le_of_lt (add_le_add
        (β₁.mono_r (ha_nonneg r hr₀ σ hσ) (by positivity) (mul_le_mul_of_nonneg_left
          (add_le_add (β₁.mono_r hr₀ (by positivity) h.le)
            (γ₁.mono (mul_nonneg hc.le (β₂.nonneg r hr₀ 0 le_rfl))
              (mul_le_mul_of_nonneg_left (β₂.mono_r hr₀ le_rfl h.le) hc.le))) hc.le))
        (γ₁.mono (mul_nonneg hc.le (β₂.nonneg r hr₀ _ (by positivity)))
          (mul_le_mul_of_nonneg_left (β₂.mono_r hr₀ (by positivity) h.le) hc.le)))
        (β₂.strict_mono_r σ hσ hr hr' h)
    nonneg := fun r hr σ hσ =>
      add_nonneg (add_nonneg (β₁.nonneg _ (ha_nonneg r hr σ hσ) _ (by positivity))
        (γ₁.maps_to (mul_nonneg hc.le (β₂.nonneg r hr _ (by positivity))))) (β₂.nonneg r hr σ hσ)
    anti_s := fun r hr σ hσ σ' hσ' h => by
      have hσ₀ : (0 : ℝ) ≤ σ := hσ
      exact add_le_add (add_le_add
        ((β₁.mono_r (ha_nonneg r hr σ' (hσ₀.trans h)) (by linarith)
          (ha_le_s r hr σ σ' hσ₀ h)).trans
          (β₁.anti_s_mono (ha_nonneg r hr σ hσ₀) (by positivity) (by linarith)))
        (γ₁.mono (mul_nonneg hc.le (β₂.nonneg r hr _ (by linarith)))
          (mul_le_mul_of_nonneg_left (β₂.anti_s_mono hr (by positivity) (by linarith)) hc.le)))
        (β₂.anti_s_mono hr hσ₀ h)
    tendsto_zero := fun r hr => by
      have h_half : Tendsto (fun σ : ℝ => σ / 2) atTop atTop :=
        tendsto_id.atTop_div_const two_pos
      -- The first term: its first argument is at most its value at `σ = 0`.
      have h₁ : Tendsto (fun σ => β₁.toFun
          (c * (β₁.toFun r (σ / 2) + γ₁.toFun (c * β₂.toFun r 0))) (σ / 2)) atTop (nhds 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
          ((β₁.tendsto_zero _ (ha_nonneg r hr 0 le_rfl)).comp h_half) ?_ ?_
        · filter_upwards [eventually_ge_atTop 0] with σ hσ
          exact β₁.nonneg _ (ha_nonneg r hr σ hσ) _ (by positivity)
        · filter_upwards [eventually_ge_atTop 0] with σ hσ
          simpa using β₁.mono_r (ha_nonneg r hr σ hσ) (by positivity)
            (ha_le_s r hr 0 σ le_rfl hσ)
      -- The second term: `γ₁` is continuous at `0`.
      have h₂ : Tendsto (fun σ => γ₁.toFun (c * β₂.toFun r (σ / 2))) atTop (nhds 0) := by
        have h_in : Tendsto (fun σ => c * β₂.toFun r (σ / 2)) atTop (𝓝[Ici 0] 0) :=
          tendsto_nhdsWithin_iff.2 ⟨by simpa using ((β₂.tendsto_zero r hr).comp h_half).const_mul c,
            by
              filter_upwards [eventually_ge_atTop 0] with σ hσ
              exact mul_nonneg hc.le (β₂.nonneg r hr _ (by positivity))⟩
        simpa [γ₁.map_zero] using (γ₁.continuous 0 (mem_Ici.2 le_rfl)).tendsto.comp h_in
      simpa using (h₁.add h₂).add (β₂.tendsto_zero r hr) }

/-- **The driven state of a cascade.**  Let `s₁`, with its input measured from `x_e`, be
input-to-state stable with data `β₁, γ₁`, and let the driving state obey
`‖x₂(τ) - x_e‖ ≤ β₂(r, τ - t₀) + g` on `[t₀, t]`, with `‖x₁(t₀) - x_c‖ ≤ r`.  Then, applying
input-to-state stability on `[t₀, m]` and on `[m, t]`, `m = (t₀ + t)/2`,
`‖x₁(t) - x_c‖ ≤ β₁(β₁(r, s/2) + γ₁(β₂(r, 0) + g), s/2) + γ₁(β₂(r, s/2) + g)`, `s = t - t₀`. -/
private lemma norm_fst_sub_le_of_cascade {E₁ E₂ Y₁ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {s₁ : ContinuousSystem E₁ E₂ Y₁} {x_c : E₁} {x_e : E₂} {β₁ : ClassKLGlobal}
    {γ₁ : ClassKInfty}
    (hISS : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (u : ℝ → E₂) (x : ℝ → E₁),
      (s₁.shiftInput x_e).IsTrajectoryOn u x (Icc t₀ t₁) →
        ∀ t ∈ Icc t₀ t₁, ∀ M : ℝ, (∀ τ ∈ Icc t₀ t, ‖u τ‖ ≤ M) →
          ‖x t - x_c‖ ≤ β₁.toFun ‖x t₀ - x_c‖ (t - t₀) + γ₁.toFun M)
    {β₂ : ClassKLGlobal} {g r t₀ t₁ t : ℝ} (ht₀ : 0 ≤ t₀) (ht : t ∈ Icc t₀ t₁)
    {x₁ : ℝ → E₁} {x₂ : ℝ → E₂} (hx₁ : s₁.IsTrajectoryOn x₂ x₁ (Icc t₀ t₁))
    (hr₁ : ‖x₁ t₀ - x_c‖ ≤ r) (h_x₂ : ∀ τ ∈ Icc t₀ t, ‖x₂ τ - x_e‖ ≤ β₂.toFun r (τ - t₀) + g) :
    ‖x₁ t - x_c‖ ≤ β₁.toFun (β₁.toFun r ((t - t₀) / 2) + γ₁.toFun (β₂.toFun r 0 + g))
      ((t - t₀) / 2) + γ₁.toFun (β₂.toFun r ((t - t₀) / 2) + g) := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hr₁
  -- `x₁` is a trajectory of the shifted system under `x₂ - x_e`.
  have hx₁' : (s₁.shiftInput x_e).IsTrajectoryOn (fun τ => x₂ τ - x_e) x₁ (Icc t₀ t₁) := by
    rw [shiftInput_isTrajectoryOn_iff]
    simpa only [sub_add_cancel] using hx₁
  set m := (t₀ + t) / 2
  have hσ : 0 ≤ (t - t₀) / 2 := by linarith [ht.1]
  have hm₀ : t₀ ≤ m := by simp only [m]; linarith [ht.1]
  have hm : m ≤ t := by simp only [m]; linarith [ht.1]
  have h_half : m - t₀ = (t - t₀) / 2 := by simp only [m]; ring
  have h_half' : t - m = (t - t₀) / 2 := by simp only [m]; ring
  -- On `[t₀, m]` the input is at most `β₂(r, 0) + g`.
  have h_mid : ‖x₁ m - x_c‖ ≤ β₁.toFun r ((t - t₀) / 2) + γ₁.toFun (β₂.toFun r 0 + g) := by
    have h := hISS t₀ ht₀ t₁ _ x₁ hx₁' m ⟨hm₀, hm.trans ht.2⟩ (β₂.toFun r 0 + g)
      fun τ hτ => (h_x₂ τ ⟨hτ.1, hτ.2.trans hm⟩).trans
        (add_le_add (β₂.anti_s_mono hr le_rfl (by linarith [hτ.1])) le_rfl)
    rw [h_half] at h
    exact h.trans (add_le_add (β₁.mono_r (norm_nonneg _) hσ hr₁) le_rfl)
  -- On `[m, t]` the input is at most `β₂(r, (t - t₀)/2) + g`.
  have h := hISS m (ht₀.trans hm₀) t₁ _ x₁ (hx₁'.mono (Icc_subset_Icc_left hm₀)) t ⟨hm, ht.2⟩
    (β₂.toFun r ((t - t₀) / 2) + g) fun τ hτ => (h_x₂ τ ⟨hm₀.trans hτ.1, hτ.2⟩).trans
      (add_le_add (β₂.anti_s_mono hr hσ (by linarith [hτ.1])) le_rfl)
  rw [h_half'] at h
  exact h.trans (add_le_add (β₁.mono_r (norm_nonneg _) hσ h_mid) le_rfl)

/-- The norm of a pair is at most the sum of the norms of its components. -/
private lemma norm_sub_pair_le {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    (p q : E₁ × E₂) : ‖p - q‖ ≤ ‖p.1 - q.1‖ + ‖p.2 - q.2‖ :=
  calc ‖p - q‖
      = max ‖p.1 - q.1‖ ‖p.2 - q.2‖ := by simp [Prod.norm_def]
    _ ≤ ‖p.1 - q.1‖ + ‖p.2 - q.2‖ := max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)

variable {E₁ E₂ Y₁ Y₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- **A cascade of an input-to-state stable system and a globally uniformly asymptotically stable
one is globally uniformly asymptotically stable.**  If `s₁`, with the state of `s₂` as its input
measured from `x_e`, is input-to-state stable about `x_c`, and `x_e` is globally uniformly
asymptotically stable for `s₂`, then `(x_c, x_e)` is globally uniformly asymptotically stable
for the cascade.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.7.  Differences: no regularity of the
fields is assumed; the equilibria are general, with `s₁`'s input measured from `x_e`
(for `x_e = 0`, `shiftInput_zero`). -/
@[blueprint "lem:continuousSystem-cascade-globallyUniformlyAsymptoticallyStable"
  (title := "Cascades of input-to-state stable systems")
  (latexEnv := "lemma")
  (statement := /-- Let $s_1$, with input $x_2$ measured from $x_e$
    (\cref{def:continuousSystem-shiftInput}), be input-to-state stable about $x_c$
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
    (h₁ : (s₁.shiftInput x_e).InputToStateStable x_c)
    (h₂ : s₂.GloballyUniformlyAsymptoticallyStable x_e) :
    (cascade s₁ s₂).GloballyUniformlyAsymptoticallyStable (x_c, x_e) := by
  obtain ⟨β₁, γ₁, hISS⟩ := h₁
  obtain ⟨β₂, hβ₂⟩ := (globallyUniformlyAsymptoticallyStable_iff_classKL s₂ x_e).1 h₂
  set β := cascadeKL β₁ γ₁ β₂ one_pos
  have hβ : ∀ r σ, β.toFun r σ =
      β₁.toFun (β₁.toFun r (σ / 2) + γ₁.toFun (β₂.toFun r 0)) (σ / 2) +
        γ₁.toFun (β₂.toFun r (σ / 2)) + β₂.toFun r σ := fun r σ => by simp [β, cascadeKL]
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
  have h_x₁ := norm_fst_sub_le_of_cascade hISS ht₀ ht hx₁ hr₁
    fun τ hτ => h_x₂ τ ⟨hτ.1, hτ.2.trans ht.2⟩
  simp only [add_zero] at h_x₁
  calc ‖x t - (x_c, x_e)‖
      ≤ ‖(x t).1 - x_c‖ + ‖(x t).2 - x_e‖ := norm_sub_pair_le _ _
    _ ≤ (β₁.toFun (β₁.toFun r ((t - t₀) / 2) + γ₁.toFun (β₂.toFun r 0)) ((t - t₀) / 2) +
          γ₁.toFun (β₂.toFun r ((t - t₀) / 2))) + (β₂.toFun r (t - t₀) + 0) :=
        add_le_add h_x₁ (h_x₂ t ht)
    _ = β.toFun r (t - t₀) := by rw [hβ, add_zero]

/-- **A cascade of input-to-state stable systems is input-to-state stable.**  If `s₁`, with the
state of `s₂` as its input measured from `x_e`, is input-to-state stable about `x_c`, and `s₂` is
input-to-state stable about `x_e` with input `w`, the cascade is input-to-state stable about
`(x_c, x_e)` with input `w`.

The proof is that of `cascade_globallyUniformlyAsymptoticallyStable`, with the input's
contribution `g = γ₂(M)` carried through and split off by `f(a + b) ≤ f(2a) + f(2b)`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Section 4.9, after Lemma 4.7; Sontag (2008). -/
@[blueprint "lem:continuousSystem-cascade-inputToStateStable"
  (title := "Cascades of input-to-state stable systems are input-to-state stable")
  (latexEnv := "lemma")
  (statement := /-- Let $s_1$, with input $x_2$ measured from $x_e$
    (\cref{def:continuousSystem-shiftInput}), be input-to-state stable about $x_c$, and let
    $s_2$, with input $w$, be input-to-state stable about $x_e$
    (\cref{def:continuousSystem-inputToStateStable}).  Then the cascade
    (\cref{def:continuousSystem-cascade}), with input $w$, is input-to-state stable about
    $(x_c, x_e)$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Section 4.9; Sontag (2008). -/)
  (proof := /-- As in \cref{lem:continuousSystem-cascade-globallyUniformlyAsymptoticallyStable},
    with $\|x_2(\tau) - x_e\| \le \beta_2(r, \tau - t_0) + g$, $g = \gamma_2(M)$, carried
    through.  Splitting with $f(a + b) \le f(2a) + f(2b)$ for nondecreasing $f \ge 0$ gives
    $\|x(t) - (x_c, x_e)\| \le \beta(r, t - t_0) + \gamma(M)$, with $\beta$ the cascade bound for
    $c = 2$ and
    $\gamma(M) = \beta_1(2\gamma_1(2\gamma_2(M)), 0) + \gamma_1(2\gamma_2(M)) + \gamma_2(M)$,
    class $\mathcal{K}_\infty$. -/)]
theorem cascade_inputToStateStable {W : Type*} [NormedAddCommGroup W]
    {s₁ : ContinuousSystem E₁ E₂ Y₁} {s₂ : ContinuousSystem E₂ W Y₂} {x_c : E₁} {x_e : E₂}
    (h₁ : (s₁.shiftInput x_e).InputToStateStable x_c) (h₂ : s₂.InputToStateStable x_e) :
    (cascade s₁ s₂).InputToStateStable (x_c, x_e) := by
  obtain ⟨β₁, γ₁, hISS₁⟩ := h₁
  obtain ⟨β₂, γ₂, hISS₂⟩ := h₂
  -- `f(a + b) ≤ f(2a) + f(2b)` for nondecreasing nonnegative `f`.
  have h_split : ∀ f : ℝ → ℝ, MonotoneOn f (Ici 0) → (∀ y, 0 ≤ y → 0 ≤ f y) →
      ∀ a b, 0 ≤ a → 0 ≤ b → f (a + b) ≤ f (2 * a) + f (2 * b) := by
    intro f hf hf0 a b ha hb
    rcases le_total a b with h | h
    · exact (hf (mem_Ici.2 (add_nonneg ha hb)) (mem_Ici.2 (by positivity)) (by linarith)).trans
        (le_add_of_nonneg_left (hf0 _ (by positivity)))
    · exact (hf (mem_Ici.2 (add_nonneg ha hb)) (mem_Ici.2 (by positivity)) (by linarith)).trans
        (le_add_of_nonneg_right (hf0 _ (by positivity)))
  have h_split_γ₁ := h_split γ₁.toFun γ₁.strict_mono.monotoneOn fun y hy => γ₁.maps_to hy
  have h_split_β₁ : ∀ σ, 0 ≤ σ → ∀ a b, 0 ≤ a → 0 ≤ b →
      β₁.toFun (a + b) σ ≤ β₁.toFun (2 * a) σ + β₁.toFun (2 * b) σ := fun σ hσ =>
    h_split (fun y => β₁.toFun y σ) (β₁.strict_mono_r σ hσ).monotoneOn
      fun y hy => β₁.nonneg y hy σ hσ
  -- The bound of the cascade and its gain.
  set β := cascadeKL β₁ γ₁ β₂ two_pos
  set γf : ℝ → ℝ := fun M => β₁.toFun (2 * γ₁.toFun (2 * γ₂.toFun M)) 0 +
    γ₁.toFun (2 * γ₂.toFun M) + γ₂.toFun M
  have hγ₂_nonneg : ∀ M, 0 ≤ M → 0 ≤ γ₂.toFun M := fun M hM => γ₂.maps_to hM
  have hγ₂₁ : ∀ M, 0 ≤ M → 0 ≤ 2 * γ₁.toFun (2 * γ₂.toFun M) := fun M hM =>
    mul_nonneg two_pos.le (γ₁.maps_to (mul_nonneg two_pos.le (hγ₂_nonneg M hM)))
  let γ : ClassKInfty := ClassKInfty.of_strictMono γf
    (by simp [γf, γ₂.map_zero, γ₁.map_zero, β₁.map_zero 0 le_rfl])
    (((β₁.continuous.comp ((continuousOn_const.mul (γ₁.continuous.comp
      (continuousOn_const.mul γ₂.continuous) fun M hM => mem_Ici.2 (mul_nonneg two_pos.le
        (hγ₂_nonneg M hM)))).prodMk continuousOn_const) fun M hM =>
          ⟨mem_Ici.2 (hγ₂₁ M hM), mem_Ici.2 le_rfl⟩).add (γ₁.continuous.comp
            (continuousOn_const.mul γ₂.continuous) fun M hM => mem_Ici.2 (mul_nonneg two_pos.le
              (hγ₂_nonneg M hM)))).add γ₂.continuous)
    (fun M hM M' hM' h => by
      have hγ₂ := (γ₂.strict_mono hM hM' h)
      have hM₀ : (0 : ℝ) ≤ M := hM
      exact add_lt_add_of_le_of_lt (add_le_add
        (β₁.mono_r (hγ₂₁ M hM₀) le_rfl (mul_le_mul_of_nonneg_left (γ₁.mono
          (mul_nonneg two_pos.le (hγ₂_nonneg M hM₀)) (by linarith)) two_pos.le))
        (γ₁.mono (mul_nonneg two_pos.le (hγ₂_nonneg M hM₀)) (by linarith))) hγ₂)
    (by
      refine tendsto_atTop_mono' _ ?_ γ₂.tendsto_atTop
      filter_upwards [eventually_ge_atTop 0] with M hM
      exact le_add_of_nonneg_left (add_nonneg (β₁.nonneg _ (hγ₂₁ M hM) 0 le_rfl)
        (γ₁.maps_to (mul_nonneg two_pos.le (hγ₂_nonneg M hM)))))
  refine ⟨β, γ, fun t₀ ht₀ t₁ w x hx t ht M hM => ?_⟩
  obtain ⟨hx₁, hx₂⟩ := cascade_isTrajectoryOn_iff.1 hx
  set r := ‖x t₀ - (x_c, x_e)‖
  have hr : 0 ≤ r := norm_nonneg _
  have hr₁ : ‖(x t₀).1 - x_c‖ ≤ r := norm_fst_le (x t₀ - (x_c, x_e))
  have hr₂ : ‖(x t₀).2 - x_e‖ ≤ r := norm_snd_le (x t₀ - (x_c, x_e))
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM t₀ ⟨le_rfl, ht.1⟩)
  set g := γ₂.toFun M
  have hg : 0 ≤ g := hγ₂_nonneg M hM₀
  -- The driving state, from its own input-to-state stability.
  have h_x₂ : ∀ τ ∈ Icc t₀ t, ‖(x τ).2 - x_e‖ ≤ β₂.toFun r (τ - t₀) + g := fun τ hτ =>
    (hISS₂ t₀ ht₀ t₁ w (fun τ => (x τ).2) hx₂ τ ⟨hτ.1, hτ.2.trans ht.2⟩ M
      fun σ hσ => hM σ ⟨hσ.1, hσ.2.trans hτ.2⟩).trans
      (add_le_add (β₂.mono_r (norm_nonneg _) (by linarith [hτ.1]) hr₂) le_rfl)
  have h_x₁ := norm_fst_sub_le_of_cascade hISS₁ ht₀ ht hx₁ hr₁ h_x₂
  -- Split off the input's contribution.
  set s := (t - t₀) / 2
  have hs : 0 ≤ s := by simp only [s]; linarith [ht.1]
  have hβ₂r : ∀ σ, 0 ≤ σ → 0 ≤ β₂.toFun r σ := fun σ hσ => β₂.nonneg r hr σ hσ
  have h_inner : β₁.toFun r s + γ₁.toFun (β₂.toFun r 0 + g) ≤
      (β₁.toFun r s + γ₁.toFun (2 * β₂.toFun r 0)) + γ₁.toFun (2 * g) := by
    rw [add_assoc]
    exact add_le_add le_rfl (h_split_γ₁ _ _ (hβ₂r 0 le_rfl) hg)
  have hA : 0 ≤ β₁.toFun r s + γ₁.toFun (2 * β₂.toFun r 0) :=
    add_nonneg (β₁.nonneg r hr s hs) (γ₁.maps_to (mul_nonneg two_pos.le (hβ₂r 0 le_rfl)))
  have hC : 0 ≤ γ₁.toFun (2 * g) := γ₁.maps_to (mul_nonneg two_pos.le hg)
  have h_term₁ : β₁.toFun (β₁.toFun r s + γ₁.toFun (β₂.toFun r 0 + g)) s ≤
      β₁.toFun (2 * (β₁.toFun r s + γ₁.toFun (2 * β₂.toFun r 0))) s +
        β₁.toFun (2 * γ₁.toFun (2 * g)) 0 :=
    calc β₁.toFun (β₁.toFun r s + γ₁.toFun (β₂.toFun r 0 + g)) s
        ≤ β₁.toFun ((β₁.toFun r s + γ₁.toFun (2 * β₂.toFun r 0)) + γ₁.toFun (2 * g)) s :=
          β₁.mono_r (add_nonneg (β₁.nonneg r hr s hs) (γ₁.maps_to (add_nonneg (hβ₂r 0 le_rfl) hg)))
            hs h_inner
      _ ≤ β₁.toFun (2 * (β₁.toFun r s + γ₁.toFun (2 * β₂.toFun r 0))) s +
            β₁.toFun (2 * γ₁.toFun (2 * g)) s := h_split_β₁ s hs _ _ hA hC
      _ ≤ β₁.toFun (2 * (β₁.toFun r s + γ₁.toFun (2 * β₂.toFun r 0))) s +
            β₁.toFun (2 * γ₁.toFun (2 * g)) 0 :=
          add_le_add le_rfl (β₁.anti_s_mono (by positivity) le_rfl hs)
  have h_term₂ : γ₁.toFun (β₂.toFun r s + g) ≤ γ₁.toFun (2 * β₂.toFun r s) + γ₁.toFun (2 * g) :=
    h_split_γ₁ _ _ (hβ₂r s hs) hg
  calc ‖x t - (x_c, x_e)‖
      ≤ ‖(x t).1 - x_c‖ + ‖(x t).2 - x_e‖ := norm_sub_pair_le _ _
    _ ≤ (β₁.toFun (β₁.toFun r s + γ₁.toFun (β₂.toFun r 0 + g)) s +
          γ₁.toFun (β₂.toFun r s + g)) + (β₂.toFun r (t - t₀) + g) :=
        add_le_add h_x₁ (h_x₂ t ⟨ht.1, le_rfl⟩)
    _ ≤ (β₁.toFun (2 * (β₁.toFun r s + γ₁.toFun (2 * β₂.toFun r 0))) s +
          β₁.toFun (2 * γ₁.toFun (2 * g)) 0 + (γ₁.toFun (2 * β₂.toFun r s) +
            γ₁.toFun (2 * g))) + (β₂.toFun r (t - t₀) + g) := by gcongr
    _ = β.toFun r (t - t₀) + γ.toFun M := by
        simp only [β, γ, γf, cascadeKL, ClassKInfty.of_strictMono, s, g]
        ring

end ContinuousSystem

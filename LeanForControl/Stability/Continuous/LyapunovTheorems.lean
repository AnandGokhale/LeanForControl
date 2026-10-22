import LeanForControl.Stability.Continuous.LyapunovFunctions
import LeanForControl.Stability.Continuous.KLCharacterization
import LeanForControl.Comparison.PositiveDefiniteBounds
import LeanForControl.Comparison.DecaySystem
import LeanForControl.Analysis.Continuity
import LeanForControl.Analysis.DiniDeriv
import Architect

/-!
# `Stability.Continuous.LyapunovTheorems` — what the Lyapunov certificates certify

Lyapunov's direct method for `ẋ = f(t, x)`: the certificates of
`Stability.Continuous.LyapunovFunctions` imply the stability notions of
`Stability.Continuous.Defs`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorems 4.8 and 4.9.

## Main results

* `IsUniformLyapunovFunction.uniformlyStable` — a uniform Lyapunov function certifies uniform
  stability (Khalil, Theorem 4.8).
* `IsStrictUniformLyapunovFunction.uniformlyAsymptoticallyStable` — a strict uniform Lyapunov
  function certifies uniform asymptotic stability (Khalil, Theorem 4.9).

## The two arguments

* **Trapping.**  `V` does not increase along a trajectory, and `W₁(x) ≤ V(t, x) ≤ W₂(x)` with
  `W₁, W₂` independent of `t`.  A trajectory starting where `W₂` is small therefore keeps `V`
  small, and so `W₁` small: it cannot reach a sphere on which `W₁` is large.  This gives uniform
  stability directly: to stay in the `ε`-ball, run the argument on a radius below `ε`.
* **Decay.**  With `V̇ ≤ -W₃`, the sandwich turns this into the scalar inequality
  `D⁺v ≤ -α(v)` for `v(t) = V(t, x(t))` and a class `K` function `α`.  The comparison lemma bounds
  `v` by a class `KL` function, and the sandwich turns that into a class `KL` bound on
  `‖x(t) - x_eq‖`, from which the uniform convergence time follows.

Only segment trajectories are used, so no solution is assumed to exist for all time.  The state
space is `ℝⁿ`, because the class `K` bounds on positive definite functions
(`IsPositiveDefiniteOn.exists_classK_bounds`) use compactness of its spheres.
-/

open Set Filter Topology Metric

namespace ContinuousSystem

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Lyapunov's exponential stability theorem -/

/-- Taking `a`-th roots: `u^a ≤ C w^a` gives `u ≤ C^{1/a} w`, for nonnegative `u, w, C`. -/
private lemma le_rpow_inv_mul {u w C a : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) (hC : 0 ≤ C) (ha : 0 < a)
    (h : u ^ a ≤ C * w ^ a) : u ≤ C ^ (1 / a) * w := by
  have h_root := Real.rpow_le_rpow (Real.rpow_nonneg hu a) h (one_div_nonneg.mpr ha.le)
  rwa [← Real.rpow_mul hu, mul_one_div_cancel ha.ne', Real.rpow_one,
    Real.mul_rpow hC (Real.rpow_nonneg hw a), ← Real.rpow_mul hw, mul_one_div_cancel ha.ne',
    Real.rpow_one] at h_root

/-- **The exponential estimate** of an exponential Lyapunov function, along any trajectory segment
that stays in its region `D`: `‖x(t) - x_eq‖ ≤ K ‖x(t₀) - x_eq‖ e^{-γ(t - t₀)}` with
`K = (k₂/k₁)^{1/a}` and `γ = k₃/(a k₂)`. -/
private lemma IsExponentialLyapunovFunction.exists_estimate {s : ContinuousSystem E Unit Y}
    {V : ℝ → E → ℝ} {x_eq : E} {D : Set E} {a : ℝ}
    (hV : s.IsExponentialLyapunovFunction V x_eq D a) :
    ∃ K > 0, ∃ γ > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
      s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → (∀ τ ∈ Icc t₀ t₁, x τ ∈ D) →
        ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ K * ‖x t₀ - x_eq‖ * Real.exp (-γ * (t - t₀)) := by
  obtain ⟨k₁, hk₁, k₂, hk₂, k₃, hk₃, hb⟩ := hV.bounds
  have ha := hV.exponent_pos
  refine ⟨(k₂ / k₁) ^ (1 / a), Real.rpow_pos_of_pos (div_pos hk₂ hk₁) _, k₃ / k₂ / a,
    div_pos (div_pos hk₃ hk₂) ha, fun t₀ ht₀ t₁ x hx h_in t ht => ?_⟩
  set c := k₃ / k₂
  -- `V ≤ k₂ ‖x - x_eq‖ᵃ` turns `V̇ ≤ -k₃ ‖x - x_eq‖ᵃ` into `V̇ ≤ -(k₃/k₂) V`.
  have h_decay := IsIntegralCurveOn.le_exp_mul_of_lieDerivative_le (c := c) hx
    (fun τ hτ => hV.differentiableAt τ (ht₀.trans hτ.1) _ (h_in τ hτ))
    (fun τ hτ => by
      change s.lieDerivative V τ (x τ) () ≤ -c * V τ (x τ)
      obtain ⟨-, h_up, h_lie⟩ := hb τ (ht₀.trans hτ.1.le) (x τ) (h_in τ (Ioo_subset_Icc_self hτ))
      have h_cV : c * V τ (x τ) ≤ k₃ * ‖x τ - x_eq‖ ^ a := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hk₂]
        nlinarith [h_up]
      linarith) t ht
  -- `k₁ ‖x(t) - x_eq‖ᵃ ≤ V(t, x(t)) ≤ e^{-c(t - t₀)} V(t₀, x(t₀))`
  -- `≤ e^{-c(t - t₀)} k₂ ‖x(t₀) - x_eq‖ᵃ`.
  obtain ⟨h_low, -, -⟩ := hb t (ht₀.trans ht.1) (x t) (h_in t ht)
  obtain ⟨-, h_up, -⟩ := hb t₀ ht₀ (x t₀) (h_in t₀ ⟨le_rfl, ht.1.trans ht.2⟩)
  have h_main : k₁ * ‖x t - x_eq‖ ^ a ≤ Real.exp (-c * (t - t₀)) * (k₂ * ‖x t₀ - x_eq‖ ^ a) :=
    h_low.trans (h_decay.trans (mul_le_mul_of_nonneg_left h_up (Real.exp_pos _).le))
  have h_pow : ‖x t - x_eq‖ ^ a ≤ k₂ / k₁ * Real.exp (-c * (t - t₀)) * ‖x t₀ - x_eq‖ ^ a := by
    have h_eq : k₁ * (k₂ / k₁ * Real.exp (-c * (t - t₀)) * ‖x t₀ - x_eq‖ ^ a) =
        Real.exp (-c * (t - t₀)) * (k₂ * ‖x t₀ - x_eq‖ ^ a) := by
      field_simp
    exact le_of_mul_le_mul_left (h_main.trans_eq h_eq.symm) hk₁
  -- Take `a`-th roots.
  have h_root := le_rpow_inv_mul (norm_nonneg _) (norm_nonneg _)
    (mul_nonneg (div_pos hk₂ hk₁).le (Real.exp_pos _).le) ha h_pow
  rw [Real.mul_rpow (div_pos hk₂ hk₁).le (Real.exp_pos _).le, ← Real.exp_mul] at h_root
  calc ‖x t - x_eq‖ ≤ _ := h_root
    _ = (k₂ / k₁) ^ (1 / a) * ‖x t₀ - x_eq‖ * Real.exp (-(c / a) * (t - t₀)) := by
      rw [show -c * (t - t₀) * (1 / a) = -(c / a) * (t - t₀) by ring]
      ring

/-- **Lyapunov's exponential stability theorem**: an exponential Lyapunov function certifies local
exponential stability, with
`‖x(t) - x_eq‖ ≤ (k₂/k₁)^{1/a} ‖x(t₀) - x_eq‖ e^{-(k₃/(a k₂))(t - t₀)}` near `x_eq`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.10. -/
@[blueprint "thm:continuousSystem-isExponentialLyapunovFunction-locallyExponentiallyStable"
  (title := "Lyapunov's exponential stability theorem")
  (statement := /-- If $V$ is an exponential Lyapunov function for $x_{\mathrm{eq}}$
    (\cref{def:continuousSystem-isExponentialLyapunovFunction}), then $x_{\mathrm{eq}}$ is locally
    exponentially stable (\cref{def:continuousSystem-locallyExponentiallyStable}): near
    $x_{\mathrm{eq}}$,
    \[
      \|x(t) - x_{\mathrm{eq}}\| \le \Bigl(\frac{k_2}{k_1}\Bigr)^{1/a}
        \|x(t_0) - x_{\mathrm{eq}}\|\, e^{-(k_3/(a k_2))(t - t_0)}.
    \]
    The state space is any normed space.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.10. -/)
  (proof := /-- The bounds give $\dot V \le -(k_3/k_2) V$, so $e^{(k_3/k_2)t} V(t, x(t))$ does not
    increase and $V(t, x(t)) \le V(t_0, x(t_0))\, e^{-(k_3/k_2)(t - t_0)}$ while the trajectory
    stays in $D$; the sandwich and an $a$-th root give the estimate.  To stay in $D$, start
    within $r/(K + 1)$ of $x_{\mathrm{eq}}$, where $\overline{B}(x_{\mathrm{eq}}, r) \subseteq D$
    and $K = (k_2/k_1)^{1/a}$: at the first time the trajectory reached the sphere of radius $r$
    the estimate would put it strictly inside. -/)]
theorem IsExponentialLyapunovFunction.locallyExponentiallyStable {s : ContinuousSystem E Unit Y}
    {V : ℝ → E → ℝ} {x_eq : E} {D : Set E} {a : ℝ}
    (hV : s.IsExponentialLyapunovFunction V x_eq D a) :
    s.LocallyExponentiallyStable x_eq := by
  obtain ⟨K, hK, γ, hγ, h_est⟩ := hV.exists_estimate
  obtain ⟨r, hr, hrD⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hV.nhds
  have hD : ∀ y : E, ‖y - x_eq‖ ≤ r → y ∈ D := fun y hy => hrD (mem_closedBall_iff_norm.mpr hy)
  have hρ : 0 < r / (K + 1) := div_pos hr (by linarith)
  have hKρ : K * (r / (K + 1)) < r := by
    calc K * (r / (K + 1)) < (K + 1) * (r / (K + 1)) := mul_lt_mul_of_pos_right (lt_add_one K) hρ
      _ = r := mul_div_cancel₀ r (by linarith)
  refine ⟨r / (K + 1), hρ, K, hK, γ, hγ, fun t₀ ht₀ t₁ x hx h_init => ?_⟩
  -- The trajectory never reaches the sphere of radius `r`, so it stays in `D`.
  have h_trap : ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ < r := by
    intro t ht
    by_contra h_out
    push Not at h_out
    have h_start : ‖x t₀ - x_eq‖ < r := h_init.trans (div_lt_self hr (by linarith))
    obtain ⟨τ, hτ, hτ_eq, h_before⟩ := exists_first_sphere_hit
      ((IsIntegralCurveOn.continuousOn hx).mono (Icc_subset_Icc_right ht.2)) h_start
      ⟨ht.1, le_rfl⟩ h_out
    have h_seg := h_est t₀ ht₀ τ x
      (IsIntegralCurveOn.mono hx (Icc_subset_Icc_right (hτ.2.trans ht.2)))
      (fun u hu => hD _ (h_before u hu)) τ ⟨hτ.1, le_rfl⟩
    have h_exp : Real.exp (-γ * (τ - t₀)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hτ.1]))
    have h_inside : ‖x τ - x_eq‖ < r :=
      calc ‖x τ - x_eq‖ ≤ K * ‖x t₀ - x_eq‖ * Real.exp (-γ * (τ - t₀)) := h_seg
        _ ≤ K * ‖x t₀ - x_eq‖ := mul_le_of_le_one_right (by positivity) h_exp
        _ < K * (r / (K + 1)) := mul_lt_mul_of_pos_left h_init hK
        _ < r := hKρ
    exact h_inside.ne hτ_eq
  exact h_est t₀ ht₀ t₁ x hx (fun u hu => hD _ (h_trap u hu).le)

/-- **Lyapunov's global exponential stability theorem**: an exponential Lyapunov function on the
whole space certifies global exponential stability; no trapping is needed.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.10, global case. -/
@[blueprint "thm:continuousSystem-isExponentialLyapunovFunction-globallyExponentiallyStable"
  (title := "Lyapunov's global exponential stability theorem")
  (statement := /-- If $V$ is an exponential Lyapunov function for $x_{\mathrm{eq}}$ on the whole
    space (\cref{def:continuousSystem-isExponentialLyapunovFunction} with $D = E$), then
    $x_{\mathrm{eq}}$ is globally exponentially stable
    (\cref{def:continuousSystem-globallyExponentiallyStable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.10, global case. -/)
  (proof := /-- The estimate of
    \cref{thm:continuousSystem-isExponentialLyapunovFunction-locallyExponentiallyStable} holds on
    every trajectory segment, since every segment stays in $D = E$. -/)]
theorem IsExponentialLyapunovFunction.globallyExponentiallyStable {s : ContinuousSystem E Unit Y}
    {V : ℝ → E → ℝ} {x_eq : E} {a : ℝ} (hV : s.IsExponentialLyapunovFunction V x_eq univ a) :
    s.GloballyExponentiallyStable x_eq := by
  obtain ⟨K, hK, γ, hγ, h_est⟩ := hV.exists_estimate
  exact ⟨K, hK, γ, hγ, fun t₀ ht₀ t₁ x hx => h_est t₀ ht₀ t₁ x hx fun _ _ => mem_univ _⟩

section Euclidean

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Comparison-function setup -/

/-- The level and radius both Lyapunov proofs work at: a level `d > 0` below `b₁` and `b₂`
(the ranges of the class `K` bounds `α₁` on `W₁` and `α₂` on `W₂`), and the radius
`c = α₂⁻¹(d)`, which lies in `(0, r)` and satisfies `α₂(c) = d`. -/
private lemma exists_sandwich_level {r b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (α₂ : ClassK r b₂) :
    ∃ d : ℝ, 0 < d ∧ d < b₁ ∧ d < b₂ ∧
      0 < α₂.invFun d ∧ α₂.invFun d < r ∧ α₂.toFun (α₂.invFun d) = d := by
  set d := min (b₁ / 2) (b₂ / 2)
  have hd_pos : 0 < d := lt_min (half_pos hb₁) (half_pos α₂.hb)
  have hd_lt_b₁ : d < b₁ := (min_le_left ..).trans_lt (half_lt_self hb₁)
  have hd_lt_b₂ : d < b₂ := (min_le_right ..).trans_lt (half_lt_self α₂.hb)
  have hd_mem : d ∈ Ico 0 b₂ := ⟨hd_pos.le, hd_lt_b₂⟩
  have hc_pos : 0 < α₂.invFun d :=
    calc 0 = α₂.invFun 0 := α₂.symm.map_zero.symm
         _ < α₂.invFun d := α₂.symm.strict_mono ⟨le_rfl, α₂.hb⟩ hd_mem hd_pos
  exact ⟨d, hd_pos, hd_lt_b₁, hd_lt_b₂, hc_pos, (α₂.inv_maps_to hd_mem).2, α₂.right_inv hd_mem⟩

/-! ## Trapping -/

/-- **Trapping by a level set.**  Let `x` be a trajectory on `[t₀, t₁]` starting strictly inside
the `ρ`-sphere about `x_c`, on which `V ≥ d`.  If `V̇ ≤ 0` wherever the trajectory is inside the
sphere and above a level `η`, and `V(t₀, x(t₀))` and `η` are both below `d`, the trajectory never
reaches the sphere.

At the first time it did, `V` would be at least `d`; but up to then `V` can only fall while above
`η`, so it is at most `max (V(t₀, x(t₀))) η < d`. -/
lemma norm_lt_of_level_lt {s : ContinuousSystem ℝⁿ Unit Y} {V : ℝ → ℝⁿ → ℝ} {x_c : ℝⁿ}
    {ρ d η t₀ t₁ : ℝ} {x : ℝ → ℝⁿ} (hx : s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁))
    (hV : ∀ τ ∈ Icc t₀ t₁, ‖x τ - x_c‖ ≤ ρ → DifferentiableAt ℝ (Function.uncurry V) (τ, x τ))
    (h_start : ‖x t₀ - x_c‖ < ρ)
    (h_level : max (V t₀ (x t₀)) η < d)
    (h_sphere : ∀ τ ∈ Icc t₀ t₁, ‖x τ - x_c‖ = ρ → d ≤ V τ (x τ))
    (h_dec : ∀ τ ∈ Ico t₀ t₁, ‖x τ - x_c‖ ≤ ρ → η < V τ (x τ) →
      s.lieDerivative V τ (x τ) () ≤ 0) :
    ∀ t ∈ Icc t₀ t₁, ‖x t - x_c‖ < ρ := by
  intro t ht
  by_contra h_out
  -- The first time `τ ∈ [t₀, t]` at which `x` reaches the `ρ`-sphere.
  obtain ⟨τ, hτ, hτ_norm, h_before⟩ := exists_first_sphere_hit
    ((IsIntegralCurveOn.continuousOn hx).mono (Icc_subset_Icc_right ht.2)) h_start
    ⟨ht.1, le_rfl⟩ (not_lt.mp h_out)
  have hτ_mem : τ ∈ Icc t₀ t₁ := ⟨hτ.1, hτ.2.trans ht.2⟩
  -- Up to `τ`, `V` falls whenever it is above `η`, so it stays below `d`.
  have hx_τ := IsIntegralCurveOn.mono hx (Icc_subset_Icc_right hτ_mem.2)
  have hV_τ : ∀ u ∈ Icc t₀ τ, DifferentiableAt ℝ (Function.uncurry V) (u, x u) := fun u hu =>
    hV u ⟨hu.1, hu.2.trans hτ_mem.2⟩ (h_before u hu)
  have h_le := le_max_of_hasDerivWithinAt_nonpos_above
    (IsIntegralCurveOn.continuousOn_comp hx_τ hV_τ)
    (fun u hu => (IsIntegralCurveOn.hasDerivWithinAt_lieDerivative hx_τ hV_τ
      (Ico_subset_Icc_self hu)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hu))
    (fun u hu => h_dec u ⟨hu.1, hu.2.trans_le hτ_mem.2⟩ (h_before u (Ico_subset_Icc_self hu)))
    τ ⟨hτ.1, le_rfl⟩
  exact (h_le.trans_lt h_level).not_ge (h_sphere τ hτ_mem hτ_norm)

/-- **Trapping.**  Let `V` be a Lyapunov function on `D`, with `W₁(x) ≤ V(t, x)` on `D` and
`α₁(‖x - x_eq‖) ≤ W₁(x)` on a closed `r`-ball inside `D`, and pick a level `d` with
`α₁⁻¹(d) < r`.  A trajectory on `[t₀, t₁]` that starts inside the ball with
`V(t₀, x(t₀)) < d` stays inside the ball.

On a sphere `‖x - x_eq‖ = ρ` with `α₁⁻¹(d) < ρ < r`, `V ≥ W₁ ≥ α₁(ρ) > d`, and `V̇ ≤ 0` inside
it, so `norm_lt_of_level_lt` keeps the trajectory inside that sphere. -/
private lemma norm_lt_of_trapped {s : ContinuousSystem ℝⁿ Unit Y} {V : ℝ → ℝⁿ → ℝ}
    {W₁ : ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ} (hV : s.IsLyapunovFunction V x_eq D)
    (hV_lb : ∀ t : ℝ, 0 ≤ t → ∀ y ∈ D, W₁ y ≤ V t y)
    {r b₁ : ℝ} (hrD : closedBall x_eq r ⊆ D) {α₁ : ClassK r b₁}
    (hW₁ : ∀ y : ℝⁿ, ‖y - x_eq‖ < r → α₁.toFun ‖y - x_eq‖ ≤ W₁ y) {d : ℝ} (hd : d ∈ Ico 0 b₁)
    {t₀ t₁ : ℝ} {x : ℝ → ℝⁿ} (hx : s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁))
    (ht₀ : 0 ≤ t₀) (h_start : ‖x t₀ - x_eq‖ < r) (hV_start : V t₀ (x t₀) < d) :
    ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ < r := by
  have hD : ∀ y : ℝⁿ, ‖y - x_eq‖ ≤ r → y ∈ D := fun y hy => hrD (mem_closedBall_iff_norm.mpr hy)
  -- Step 1. An intermediate radius `ρ`, strictly between `α₁⁻¹(d)` and `r`.
  have hd_inv_mem : α₁.invFun d ∈ Ico 0 r := α₁.inv_maps_to hd
  obtain ⟨ρ, hρ_gt, hρ_lt⟩ := exists_between hd_inv_mem.2
  -- Step 2. The trajectory starts inside the `ρ`-ball: `α₁(‖x t₀ - x_eq‖) ≤ W₁ ≤ V < d`.
  have h_α₁_start : α₁.toFun ‖x t₀ - x_eq‖ < α₁.toFun (α₁.invFun d) := by
    rw [α₁.right_inv hd]
    exact (hW₁ _ h_start).trans_lt ((hV_lb t₀ ht₀ _ (hD _ h_start.le)).trans_lt hV_start)
  have h_start_ρ : ‖x t₀ - x_eq‖ < ρ :=
    ((α₁.strict_mono_iff ⟨norm_nonneg _, h_start⟩ hd_inv_mem).mp h_α₁_start).trans hρ_gt
  -- Step 3. On the `ρ`-sphere `V ≥ W₁ ≥ α₁(ρ) > α₁(α₁⁻¹(d)) = d`, and inside it `V̇ ≤ 0`.
  have h_sphere : ∀ τ ∈ Icc t₀ t₁, ‖x τ - x_eq‖ = ρ → d ≤ V τ (x τ) := fun τ hτ hτ_norm => by
    have hτ_lt_r : ‖x τ - x_eq‖ < r := hτ_norm ▸ hρ_lt
    calc d = α₁.toFun (α₁.invFun d) := (α₁.right_inv hd).symm
      _ ≤ α₁.toFun ‖x τ - x_eq‖ :=
          (α₁.strict_mono hd_inv_mem ⟨norm_nonneg _, hτ_lt_r⟩ (hτ_norm ▸ hρ_gt)).le
      _ ≤ W₁ (x τ) := hW₁ _ hτ_lt_r
      _ ≤ V τ (x τ) := hV_lb τ (ht₀.trans hτ.1) _ (hD _ hτ_lt_r.le)
  intro t ht
  exact (norm_lt_of_level_lt (η := V t₀ (x t₀)) hx
    (fun τ hτ hτ_norm => hV.differentiableAt τ (ht₀.trans hτ.1) _ (hD _ (hτ_norm.trans hρ_lt.le)))
    h_start_ρ (by rwa [max_self]) h_sphere
    (fun τ hτ hτ_norm _ => hV.lie_nonpos τ (ht₀.trans hτ.1) _ (hD _ (hτ_norm.trans hρ_lt.le)))
    t ht).trans hρ_lt

/-- The bound `V(t, y) < d = α₂(c)` from the `c`-ball: `V ≤ W₂ ≤ α₂(‖y - x_eq‖) < α₂(c)`. -/
private lemma lt_level_of_norm_lt {V : ℝ → ℝⁿ → ℝ} {W₂ : ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ}
    (hV_ub : ∀ t : ℝ, 0 ≤ t → ∀ y ∈ D, V t y ≤ W₂ y)
    {r b₂ : ℝ} (hrD : closedBall x_eq r ⊆ D) {α₂ : ClassK r b₂}
    (hW₂ : ∀ y : ℝⁿ, ‖y - x_eq‖ < r → W₂ y ≤ α₂.toFun ‖y - x_eq‖)
    {c d : ℝ} (hc_lt_r : c < r) (h_α₂_c : α₂.toFun c = d)
    {t : ℝ} (ht : 0 ≤ t) {y : ℝⁿ} (hy : ‖y - x_eq‖ < c) :
    V t y < d := by
  have hy_r : ‖y - x_eq‖ < r := hy.trans hc_lt_r
  calc V t y
      ≤ W₂ y                   := hV_ub t ht y (hrD (mem_closedBall_iff_norm.mpr hy_r.le))
    _ ≤ α₂.toFun ‖y - x_eq‖    := hW₂ y hy_r
    _ < α₂.toFun c             := α₂.strict_mono ⟨norm_nonneg _, hy_r⟩
                                    ⟨(norm_nonneg _).trans hy.le, hc_lt_r⟩ hy
    _ = d                      := h_α₂_c

/-! ## Lyapunov's uniform stability theorem -/

/-- **Lyapunov's uniform stability theorem**: a uniform Lyapunov function certifies uniform
stability.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.8. -/
@[blueprint "thm:continuousSystem-isUniformLyapunovFunction-uniformlyStable"
  (title := "Lyapunov's uniform stability theorem")
  (statement := /-- If $V$ is a uniform Lyapunov function for $x_{\mathrm{eq}}$
    (\cref{def:continuousSystem-isUniformLyapunovFunction}) on a system with state space
    $\mathbb{R}^n$, then $x_{\mathrm{eq}}$ is uniformly stable
    (\cref{def:continuousSystem-uniformlyStable}).

    The sandwich $W_1(x) \le V(t, x) \le W_2(x)$ is what makes the conclusion uniform in $t_0$:
    $W_1$ and $W_2$ do not depend on $t$, so neither does the $\delta(\varepsilon)$ extracted
    from them.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.8. -/)
  (proof := /-- Given $\varepsilon$, work on a radius $r \le \varepsilon$ whose closed ball lies
    in the region of the certificate.  Bound $W_1$ below and $W_2$ above by class $\mathcal{K}$
    functions $\alpha_1, \alpha_2$ on it (\cref{thm:lyapunov-class-K-bounds}), fix a level $d$
    below both ranges, and take $\delta = \alpha_2^{-1}(d)$: starting within $\delta$ of
    $x_{\mathrm{eq}}$ forces $V(t_0, x(t_0)) < d$.  To leave the $r$-ball the trajectory would
    first cross a sphere on which $W_1 > d$; up to that time $V$ has not increased
    (\cref{lem:isIntegralCurveOn-antitoneOn-of-lieDerivative-nonpos}), so it is
    still below $d$, a contradiction. -/)]
theorem IsUniformLyapunovFunction.uniformlyStable [NeZero n] {s : ContinuousSystem ℝⁿ Unit Y}
    {V : ℝ → ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ} (hV : s.IsUniformLyapunovFunction V x_eq D) :
    s.UniformlyStable x_eq := by
  obtain ⟨W₁, hW₁, hV_lb⟩ := hV.lower
  obtain ⟨W₂, hW₂, hV_ub⟩ := hV.upper
  obtain ⟨R, hR, hRD⟩ := nhds_basis_closedBall.mem_iff.mp hV.nhds
  intro ε hε
  -- Step 1. Work on a radius `r ≤ ε` whose closed ball lies in `D`.
  set r := min ε R
  have hr : 0 < r := lt_min hε hR
  have hrD : closedBall x_eq r ⊆ D := (closedBall_subset_closedBall (min_le_right ε R)).trans hRD
  -- Step 2. Class `K` bounds for `W₁` and `W₂`, a level `d`, and the radius `δ = α₂⁻¹(d)`.
  obtain ⟨b₁, _, α₁, _, hW₁_bd⟩ := hW₁.exists_classK_bounds hr hrD
  obtain ⟨_, b₂, _, α₂, hW₂_bd⟩ := hW₂.exists_classK_bounds hr hrD
  obtain ⟨d, hd_pos, hd_lt_b₁, -, hδ_pos, hδ_lt_r, h_α₂_δ⟩ := exists_sandwich_level α₁.hb α₂
  -- Step 3. Trajectories from the `δ`-ball are trapped in the `r`-ball, inside the `ε`-ball.
  refine ⟨α₂.invFun d, hδ_pos, fun t₀ ht₀ t₁ x hx h_init t ht => ?_⟩
  have h_trapped := norm_lt_of_trapped hV.toIsLyapunovFunction hV_lb hrD
    (fun y hy => (hW₁_bd y hy).1) ⟨hd_pos.le, hd_lt_b₁⟩ hx ht₀ (h_init.trans hδ_lt_r)
    (lt_level_of_norm_lt hV_ub hrD (fun y hy => (hW₂_bd y hy).2) hδ_lt_r h_α₂_δ ht₀ h_init)
  exact (h_trapped t ht).trans_le (min_le_left ε R)

/-! ## The comparison lemma along a trajectory -/

/-- **The comparison lemma along a trajectory.**  Let `σ` be the class `KL` bound that
`ClassK.exists_classKL_bound_of_subsolution` attaches to a class `K` function `α`.  If
`v(τ) = V(τ, x(τ))` stays in `[0, d)` on `[t₀, t]` and `V̇ ≤ -α(V)` there, then `v` is a
subsolution of the decay system of `α`, so `V(t, x(t)) ≤ σ(V(t₀, x(t₀)), t - t₀)`.

This only checks the side conditions: `v` is continuous, its Dini derivative is the derivative
along the system, and its difference quotients are bounded. -/
private lemma comp_trajectory_le_classKL {s : ContinuousSystem ℝⁿ Unit Y} {V : ℝ → ℝⁿ → ℝ}
    {d e : ℝ} {α : ClassK d e} {σ : ClassKL d}
    (hσ : ∀ {t₀ t : ℝ}, t₀ ≤ t → ∀ (v : ℝ → ℝ), ContinuousOn v (Icc t₀ t) →
        v t₀ ∈ Ico 0 d →
        (∀ s ∈ Ico t₀ t, v s ∈ Ico 0 d) →
        (∀ s ∈ Ico t₀ t, D⁺ v s ≤ α.decaySystem.F s (v s) ()) →
        (∀ s ∈ Ico t₀ t,
            IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (v (s + h) - v s) / h)) →
        v t ≤ σ.toFun (v t₀) (t - t₀))
    {x : ℝ → ℝⁿ} {t₀ t₁ t : ℝ} (hx : s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁))
    (hV : ∀ τ ∈ Icc t₀ t₁, DifferentiableAt ℝ (Function.uncurry V) (τ, x τ))
    (ht : t ∈ Icc t₀ t₁)
    (hv_range : ∀ τ ∈ Icc t₀ t, V τ (x τ) ∈ Ico 0 d)
    (hlie : ∀ τ ∈ Ico t₀ t, s.lieDerivative V τ (x τ) () ≤ -α.toFun (V τ (x τ))) :
    V t (x t) ≤ σ.toFun (V t₀ (x t₀)) (t - t₀) := by
  -- Before `t ≤ t₁`, the derivative within `[t₀, t₁]` is a right derivative.
  have hderiv : ∀ τ ∈ Ico t₀ t, HasDerivWithinAt (fun u => V u (x u))
      (s.lieDerivative V τ (x τ) ()) (Ici τ) τ := fun τ hτ =>
    (IsIntegralCurveOn.hasDerivWithinAt_lieDerivative hx hV
      ⟨hτ.1, hτ.2.le.trans ht.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hτ.1, hτ.2.trans_le ht.2⟩)
  have hv_cont : ContinuousOn (fun u => V u (x u)) (Icc t₀ t) :=
    (IsIntegralCurveOn.continuousOn_comp hx hV).mono (Icc_subset_Icc_right ht.2)
  exact hσ ht.1 (fun u => V u (x u)) hv_cont (hv_range t₀ ⟨le_rfl, ht.1⟩)
    (fun τ hτ => hv_range τ (Ico_subset_Icc_self hτ))
    (fun τ hτ => by rw [diniDerivRight_of_hasDerivWithinAt (hderiv τ hτ)]; exact hlie τ hτ)
    (fun τ hτ => (hderiv τ hτ).tendsto_forward_slope.isBoundedUnder_le)

/-! ## Lyapunov's uniform asymptotic stability theorem -/

/-- **Lyapunov's uniform asymptotic stability theorem**: a strict uniform Lyapunov function
certifies uniform asymptotic stability.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.9.  Khalil's two "moreover" clauses
are not part of this conclusion: the explicit class `KL` bound, which the proof constructs, and
the global case, when `D` is the whole space and `W₁` is radially unbounded. -/
@[blueprint "thm:continuousSystem-isStrictUniformLyapunovFunction-uniformlyAsymptoticallyStable"
  (title := "Lyapunov's uniform asymptotic stability theorem")
  (statement := /-- If $V$ is a strict uniform Lyapunov function for $x_{\mathrm{eq}}$
    (\cref{def:continuousSystem-isStrictUniformLyapunovFunction}) on a system with state space
    $\mathbb{R}^n$, then $x_{\mathrm{eq}}$ is uniformly asymptotically stable
    (\cref{def:continuousSystem-uniformlyAsymptoticallyStable}).

    A strictly negative $\dot V$ alone would not do: $W_3$ must be bounded away from zero on
    each annulus, which is exactly what positive definiteness of a function of $x$ alone buys.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.9.  Khalil's two
    ``moreover'' clauses are not part of this conclusion: the explicit class $\mathcal{KL}$
    bound, which the proof constructs, and the global case. -/)
  (proof := /-- Uniform stability is
    \cref{thm:continuousSystem-isUniformLyapunovFunction-uniformlyStable}.  For convergence,
    take class $\mathcal{K}$ bounds $\alpha_1, \alpha_2, \alpha_3$ for $W_1, W_2, W_3$ on a ball
    in the region of the certificate, and the trapping radius $c$ of that proof.  Along a
    trajectory from the $c$-ball,
    $\dot V \le -W_3(x) \le -\alpha_3(\|x - x_{\mathrm{eq}}\|) \le -\alpha_3(\alpha_2^{-1}(V))$,
    so $v(t) = V(t, x(t))$ satisfies $D^+ v \le -\alpha(v)$ with
    $\alpha = \alpha_3 \circ \alpha_2^{-1}$ of class $\mathcal{K}$.
    \cref{thm:classK-dini-bound} gives a class $\mathcal{KL}$ $\sigma$ with
    $v(t) \le \sigma(v(t_0), t - t_0)$; unwinding the sandwich,
    \[
      \|x(t) - x_{\mathrm{eq}}\| \le
        \alpha_1^{-1}\bigl(\sigma(\alpha_2(\|x(t_0) - x_{\mathrm{eq}}\|), t - t_0)\bigr),
    \]
    a class $\mathcal{KL}$ bound.  Conclude by
    \cref{lem:continuousSystem-hasUniformConvergenceTime-of-classKL}. -/)]
theorem IsStrictUniformLyapunovFunction.uniformlyAsymptoticallyStable [NeZero n]
    {s : ContinuousSystem ℝⁿ Unit Y} {V : ℝ → ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ}
    (hV : s.IsStrictUniformLyapunovFunction V x_eq D) :
    s.UniformlyAsymptoticallyStable x_eq := by
  /- Along a trajectory `v(t) = V(t, x(t))` obeys `D⁺v ≤ -α₃(α₂⁻¹(v))`, so the comparison lemma
     bounds it by a class KL `σ(v(t₀), t - t₀)`; the sandwich turns this into the class KL
     bound `‖x(t) - x_eq‖ ≤ α₁⁻¹(σ(α₂(‖x(t₀) - x_eq‖), t - t₀))`. -/
  refine ⟨hV.toIsUniformLyapunovFunction.uniformlyStable, ?_⟩
  obtain ⟨W₁, hW₁, hV_lb⟩ := hV.lower
  obtain ⟨W₂, hW₂, hV_ub⟩ := hV.upper
  obtain ⟨W₃, hW₃, hV_strict⟩ := hV.strict
  -- Step 1. A ball in `D`, and class `K` bounds for `W₁`, `W₂`, `W₃` on it.
  obtain ⟨r, hr, hrD⟩ := nhds_basis_closedBall.mem_iff.mp hV.nhds
  have hD : ∀ y : ℝⁿ, ‖y - x_eq‖ ≤ r → y ∈ D := fun y hy => hrD (mem_closedBall_iff_norm.mpr hy)
  obtain ⟨b₁, _, α₁, _, hW₁_bd⟩ := hW₁.exists_classK_bounds hr hrD
  obtain ⟨_, b₂, _, α₂, hW₂_bd⟩ := hW₂.exists_classK_bounds hr hrD
  obtain ⟨_, _, α₃, _, hW₃_bd⟩ := hW₃.exists_classK_bounds hr hrD
  -- Step 2. The level `d` and trapping radius `c = α₂⁻¹(d)` of the uniform-stability proof.
  obtain ⟨d, hd_pos, hd_lt_b₁, hd_lt_b₂, hc_pos, hc_lt_r, h_α₂_c⟩ :=
    exists_sandwich_level α₁.hb α₂
  set c := α₂.invFun d
  have hV_lt_d : ∀ t : ℝ, 0 ≤ t → ∀ y : ℝⁿ, ‖y - x_eq‖ < c → V t y < d := fun t ht y hy =>
    lt_level_of_norm_lt hV_ub hrD (fun y hy => (hW₂_bd y hy).2) hc_lt_r h_α₂_c ht hy
  -- Step 3. A trajectory from the `c`-ball never leaves the `r`-ball ...
  have h_in_ball : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → ℝⁿ),
      s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < c →
        ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ < r := fun t₀ ht₀ t₁ x hx h_init =>
    norm_lt_of_trapped hV.toIsLyapunovFunction hV_lb hrD (fun y hy => (hW₁_bd y hy).1)
      ⟨hd_pos.le, hd_lt_b₁⟩ hx ht₀ (h_init.trans hc_lt_r) (hV_lt_d t₀ ht₀ _ h_init)
  -- ... and keeps `V` in `[0, d)`: it starts below `d` and does not increase.
  have hV_range : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → ℝⁿ),
      s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < c →
        ∀ t ∈ Icc t₀ t₁, V t (x t) ∈ Ico 0 d := fun t₀ ht₀ t₁ x hx h_init t ht => by
    have h_ball := h_in_ball t₀ ht₀ t₁ x hx h_init
    have h_anti := IsIntegralCurveOn.antitoneOn_of_lieDerivative_nonpos hx (convex_Icc _ _)
      (fun u hu => hV.differentiableAt u (ht₀.trans hu.1) _ (hD _ (h_ball u hu).le))
      fun u hu => by
        rw [interior_Icc] at hu
        exact hV.lie_nonpos u (ht₀.trans hu.1.le) (x u)
          (hD _ (h_ball u (Ioo_subset_Icc_self hu)).le)
    have hx_D : x t ∈ D := hD _ (h_ball t ht).le
    exact ⟨(hW₁.nonneg hx_D).trans (hV_lb t (ht₀.trans ht.1) _ hx_D),
      (h_anti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1).trans_lt (hV_lt_d t₀ ht₀ _ h_init)⟩
  -- Step 4. The comparison function `α₃ ∘ α₂⁻¹` on `[0, d)` and its class KL bound `σ`.
  have h_α : ∃ α : ClassK d (α₃.toFun c), ∀ y ∈ Ico 0 d, α.toFun y = α₃.toFun (α₂.invFun y) := by
    -- Compose `α₂⁻¹ : [0, d) → [0, c)` with `α₃` restricted to `[0, c)`.  As `c` is by
    -- definition `α₂⁻¹(d)`, the two domains match definitionally, so `ClassK.comp` needs no
    -- cast and the composite agrees with `α₃ ∘ α₂⁻¹` by `rfl`.
    let α₂_inv_res := α₂.symm.restrict hd_pos hd_lt_b₂
    let α₃_res : ClassK (α₂.symm.toFun d) (α₃.toFun c) := α₃.restrict hc_pos hc_lt_r
    exact ⟨ClassK.comp α₃_res α₂_inv_res, fun _ _ => rfl⟩
  obtain ⟨α, hα_eq⟩ := h_α
  obtain ⟨σ, hσ_zero, hσ⟩ := α.exists_classKL_bound_of_subsolution
  -- In the `r`-ball, `V̇ ≤ -W₃(y) ≤ -α₃(‖y - x_eq‖) ≤ -α₃(α₂⁻¹(V))`.
  have hlie_comp : ∀ t : ℝ, 0 ≤ t → ∀ y : ℝⁿ, ‖y - x_eq‖ < r → V t y ∈ Ico 0 d →
      s.lieDerivative V t y () ≤ -α.toFun (V t y) := fun t ht y hy hVy => by
    have h_le : α.toFun (V t y) ≤ α₃.toFun ‖y - x_eq‖ := by
      rw [hα_eq _ hVy]
      exact α₂.toFun_invFun_le α₃ ⟨norm_nonneg _, hy⟩ ⟨hVy.1, hVy.2.trans hd_lt_b₂⟩
        ((hV_ub t ht y (hD y hy.le)).trans (hW₂_bd y hy).2)
    linarith [hV_strict t ht y (hD y hy.le), (hW₃_bd y hy).1]
  -- Step 5. The class KL bound `β(ρ, s) = α₁⁻¹(σ(α₂(ρ), s))`.
  obtain ⟨β, hβ_eq⟩ := ClassKL.exists_comp_sandwich α₁ α₂ hσ_zero hc_pos hc_lt_r h_α₂_c hd_lt_b₁
  -- Step 6. Every trajectory from the `c`-ball obeys `β`.
  refine ⟨c / 2, half_pos hc_pos, hasUniformConvergenceTime_of_classKL β (half_lt_self hc_pos) ?_⟩
  intro t₀ ht₀ t₁ x hx h_init t ht
  have h_ball := h_in_ball t₀ ht₀ t₁ x hx h_init
  have h_range := hV_range t₀ ht₀ t₁ x hx h_init
  have h_xt_lt_r : ‖x t - x_eq‖ < r := h_ball t ht
  have ht_sub : 0 ≤ t - t₀ := sub_nonneg.mpr ht.1
  have ht₀_mem : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, ht.1.trans ht.2⟩
  -- `V(t, x(t)) ≤ σ(V(t₀, x(t₀)), t - t₀)`, by the comparison lemma.
  have h_σ_bound : V t (x t) ≤ σ.toFun (V t₀ (x t₀)) (t - t₀) :=
    comp_trajectory_le_classKL hσ hx
      (fun u hu => hV.differentiableAt u (ht₀.trans hu.1) _ (hD _ (h_ball u hu).le)) ht
      (fun τ hτ => h_range τ ⟨hτ.1, hτ.2.trans ht.2⟩)
      (fun τ hτ => hlie_comp τ (ht₀.trans hτ.1) _ (h_ball τ ⟨hτ.1, hτ.2.le.trans ht.2⟩)
        (h_range τ ⟨hτ.1, hτ.2.le.trans ht.2⟩))
  -- `V(t₀, x(t₀))` and `α₂(‖x(t₀) - x_eq‖)` lie in `[0, d)`, and `σ(·, t - t₀)` keeps `[0, d)`.
  have hV_t₀_mem : V t₀ (x t₀) ∈ Ico 0 d := h_range t₀ ht₀_mem
  have h_α₂_t₀_mem : α₂.toFun ‖x t₀ - x_eq‖ ∈ Ico 0 d :=
    α₂.toFun_mem_Ico hc_lt_r h_α₂_c ⟨norm_nonneg _, h_init⟩
  have h_σ_mem : σ.toFun (α₂.toFun ‖x t₀ - x_eq‖) (t - t₀) ∈ Ico 0 d :=
    σ.toFun_mem_Ico hσ_zero h_α₂_t₀_mem ht_sub
  -- `α₁(‖x(t) - x_eq‖) ≤ W₁ ≤ V ≤ σ(V(t₀, x(t₀)), t - t₀) ≤ σ(α₂(‖x(t₀) - x_eq‖), t - t₀)`.
  have h_x₀_lt_r : ‖x t₀ - x_eq‖ < r := h_init.trans hc_lt_r
  have h_chain : α₁.toFun ‖x t - x_eq‖ ≤ σ.toFun (α₂.toFun ‖x t₀ - x_eq‖) (t - t₀) :=
    calc α₁.toFun ‖x t - x_eq‖
      _ ≤ W₁ (x t) := (hW₁_bd (x t) h_xt_lt_r).1
      _ ≤ V t (x t) := hV_lb t (ht₀.trans ht.1) (x t) (hD _ h_xt_lt_r.le)
      _ ≤ σ.toFun (V t₀ (x t₀)) (t - t₀) := h_σ_bound
      _ ≤ σ.toFun (α₂.toFun ‖x t₀ - x_eq‖) (t - t₀) :=
            (σ.strict_mono_r (t - t₀) ht_sub).monotoneOn hV_t₀_mem h_α₂_t₀_mem
              ((hV_ub t₀ ht₀ _ (hD _ h_x₀_lt_r.le)).trans (hW₂_bd _ h_x₀_lt_r).2)
  -- Invert `α₁`, which is increasing on `[0, b₁) ⊇ [0, d)`.
  have h_α₁_mem : α₁.toFun ‖x t - x_eq‖ ∈ Ico 0 b₁ := α₁.maps_to ⟨norm_nonneg _, h_xt_lt_r⟩
  have h_σ_mem_b₁ : σ.toFun (α₂.toFun ‖x t₀ - x_eq‖) (t - t₀) ∈ Ico 0 b₁ :=
    ⟨h_σ_mem.1, h_σ_mem.2.trans hd_lt_b₁⟩
  calc ‖x t - x_eq‖
      = α₁.invFun (α₁.toFun ‖x t - x_eq‖) := (α₁.left_inv ⟨norm_nonneg _, h_xt_lt_r⟩).symm
    _ ≤ α₁.invFun (σ.toFun (α₂.toFun ‖x t₀ - x_eq‖) (t - t₀)) :=
        (α₁.inv_mono_iff h_α₁_mem h_σ_mem_b₁).mpr h_chain
    _ = β.toFun ‖x t₀ - x_eq‖ (t - t₀) := (hβ_eq _ _).symm

/-! ## Global asymptotic stability of a time-invariant system -/

/-- A continuous function positive on a compact set is bounded below there by a positive
constant. -/
private lemma exists_pos_le_of_isCompact {K : Set ℝⁿ} (hK : IsCompact K) {g : ℝⁿ → ℝ}
    (hg : ContinuousOn g K) (h_pos : ∀ y ∈ K, 0 < g y) : ∃ m > 0, ∀ y ∈ K, m ≤ g y := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun _ h => h.elim⟩
  obtain ⟨y₀, hy₀, h_min⟩ := hK.exists_isMinOn hne hg
  exact ⟨g y₀, h_pos y₀ hy₀, fun y hy => h_min hy⟩

/-- **Rate-bounded decrease** for a time-invariant system: if `∇V · f ≤ -c` along a trajectory on
`[a, b]`, then `V(x(b)) + c b ≤ V(x(a)) + c a`.  This is monotonicity of `V(x) + c t`, whose Lie
derivative is `∇V · f + c` (`lieDerivative_add_mul`). -/
private lemma add_mul_le_of_lie_le {s : ContinuousSystem ℝⁿ Unit Y} {f : ℝⁿ → ℝⁿ}
    (hF : ∀ t x, s.F t x () = f x) {V : ℝⁿ → ℝ} (hV : Differentiable ℝ V) {c a b : ℝ}
    {x : ℝ → ℝⁿ} (hx : s.IsTrajectoryOn (fun _ => ()) x (Icc a b)) (hab : a ≤ b)
    (hlie : ∀ t ∈ Ioo a b, fderiv ℝ V (x t) (f (x t)) ≤ -c) :
    V (x b) + c * b ≤ V (x a) + c * a :=
  IsIntegralCurveOn.antitoneOn_of_lieDerivative_nonpos (V := fun t y => V y + c * t) hx
    (convex_Icc a b) (fun t _ => ((hV.comp differentiable_snd).add
      (differentiable_fst.const_mul c) : Differentiable ℝ fun p : ℝ × ℝⁿ => V p.2 + c * p.1) _)
    (fun t ht => by
      rw [interior_Icc] at ht
      rw [lieDerivative_add_mul c (hV _)]
      simp only [ContinuousSystem.vectorField_apply, hF]
      linarith [hlie t ht])
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab

/-- **Lyapunov's global asymptotic stability theorem** for a time-invariant system
`ẋ = f(x)`: a `C¹` function `V`, positive definite on the whole space, with compact sublevel sets
and `∇V · f < 0` away from `x_eq`, makes `x_eq` globally uniformly asymptotically stable.

In `ℝⁿ`, compact sublevel sets is radial unboundedness of the continuous `V`.  No hypothesis
`f(x_eq) = 0` is needed: `x_eq` minimizes `V`, so `∇V(x_eq) = 0`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.2. -/
@[blueprint "thm:continuousSystem-globallyUniformlyAsymptoticallyStable-of-lyapunov"
  (title := "Lyapunov's global asymptotic stability theorem")
  (statement := /-- Let the state equation be $\dot x = f(x)$ with $f$ continuous, on
    $\mathbb{R}^n$.  Let $V : \mathbb{R}^n \to \mathbb{R}$ be $C^1$, positive definite about
    $x_{\mathrm{eq}}$ on all of $\mathbb{R}^n$ (\cref{def:isPositiveDefiniteOn}), with compact
    sublevel sets $\{V \le c\}$ (equivalently, radially unbounded) and
    $\nabla V(x) \cdot f(x) < 0$ for $x \ne x_{\mathrm{eq}}$.  Then $x_{\mathrm{eq}}$ is
    globally uniformly asymptotically stable
    (\cref{def:continuousSystem-globallyUniformlyAsymptoticallyStable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.2. -/)
  (proof := /-- $V$ does not increase along trajectories: $\nabla V \cdot f \le 0$ everywhere,
    since $\nabla V(x_{\mathrm{eq}}) = 0$ at the minimum.  So a trajectory starting below every
    value $V$ takes outside the $\varepsilon$-ball never leaves it.  Take $\delta(\varepsilon)$
    the supremum of the radii $\rho \le \varepsilon$ whose closed ball lies strictly below those
    values: it is positive, since $V$ is bounded below by a positive constant outside the
    $\varepsilon$-ball and small near $x_{\mathrm{eq}}$, and it tends to $\infty$, since
    $V$ is bounded on each ball and large far out.  This is global uniform stability.

    For convergence from the $c$-ball, trajectories stay in the compact set $\{V \le M\}$,
    $M = \max_{\overline B(x_{\mathrm{eq}}, c)} V$, on which, outside the
    $\delta(\eta)$-ball, $\nabla V \cdot f \le -\gamma < 0$.  So $V$ falls at rate $\gamma$
    while the trajectory is outside, and since $V \ge 0$ it enters the $\delta(\eta)$-ball by
    time $t_0 + M/\gamma + 1$; from then on it stays in the $\eta$-ball. -/)]
theorem globallyUniformlyAsymptoticallyStable_of_lyapunov [NeZero n]
    {s : ContinuousSystem ℝⁿ Unit Y} {f : ℝⁿ → ℝⁿ} (hF : ∀ t x, s.F t x () = f x)
    (hf : Continuous f) {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hV_c1 : ContDiff ℝ 1 V)
    (hV_pos : IsPositiveDefiniteOn V x_eq univ) (hV_sub : ∀ c, IsCompact {x | V x ≤ c})
    (hV_neg : ∀ x, x ≠ x_eq → fderiv ℝ V x (f x) < 0) :
    s.GloballyUniformlyAsymptoticallyStable x_eq := by
  have hV : Differentiable ℝ V := hV_c1.differentiable one_ne_zero
  have hV_cont : Continuous V := hV.continuous
  have hV_nonneg : ∀ y, 0 ≤ V y := fun y => hV_pos.nonneg (mem_univ y)
  have h_far_closed : ∀ r : ℝ, IsClosed {y : ℝⁿ | r ≤ ‖y - x_eq‖} := fun r =>
    isClosed_le continuous_const (continuous_id.sub continuous_const).norm
  -- Step 1. `x_eq` minimizes `V`, so `∇V(x_eq) = 0` and `∇V · f ≤ 0` everywhere.
  have h_crit : fderiv ℝ V x_eq = 0 :=
    (IsMinOn.isLocalMin (isMinOn_iff.mpr fun y _ => by rw [hV_pos.2.1]; exact hV_nonneg y)
      Filter.univ_mem).fderiv_eq_zero
  have h_nonpos : ∀ y, fderiv ℝ V y (f y) ≤ 0 := fun y => by
    rcases eq_or_ne y x_eq with rfl | hy
    · simp [h_crit]
    · exact (hV_neg y hy).le
  -- `V` does not increase along trajectories.
  have h_dec : ∀ {a b : ℝ} {x : ℝ → ℝⁿ}, s.IsTrajectoryOn (fun _ => ()) x (Icc a b) →
      ∀ t ∈ Icc a b, V (x t) ≤ V (x a) := fun {a b x} hx t ht => by
    simpa using add_mul_le_of_lie_le hF hV (c := 0)
      (IsIntegralCurveOn.mono hx (Icc_subset_Icc_right ht.2)) ht.1
      fun τ _ => by simpa using h_nonpos (x τ)
  -- Step 2. Trapping: a trajectory that starts below every value `V` takes outside the
  -- `ε`-ball never leaves it.
  have h_trap : ∀ {ε a b : ℝ} {x : ℝ → ℝⁿ}, s.IsTrajectoryOn (fun _ => ()) x (Icc a b) →
      (∀ z, ε ≤ ‖z - x_eq‖ → V (x a) < V z) → ∀ t ∈ Icc a b, ‖x t - x_eq‖ < ε :=
    fun hx h_lt t ht => not_le.mp fun h_out => absurd (h_dec hx t ht) (h_lt _ h_out).not_ge
  -- Step 3. `δ(ε)` is the supremum of the radii `ρ ≤ ε` whose closed ball lies strictly below
  -- every value `V` takes outside the `ε`-ball.
  let S : ℝ → Set ℝ := fun ε => {ρ | ρ ∈ Icc 0 ε ∧
    ∀ y z : ℝⁿ, ‖y - x_eq‖ ≤ ρ → ε ≤ ‖z - x_eq‖ → V y < V z}
  have hS_bdd : ∀ ε, BddAbove (S ε) := fun ε => ⟨ε, fun _ hρ => hρ.1.2⟩
  -- Outside the `ε`-ball `V` is bounded below by some `m > 0` ...
  have h_far_pos : ∀ ε > 0, ∃ m > 0, ∀ z : ℝⁿ, ε ≤ ‖z - x_eq‖ → m ≤ V z := fun ε hε => by
    obtain ⟨m₀, hm₀, h_le⟩ := exists_pos_le_of_isCompact ((hV_sub 1).inter_right (h_far_closed ε))
      hV_cont.continuousOn fun z hz => hV_pos.2.2 z (mem_univ z) fun h => by
        subst h
        simp at hz
        linarith [hz.2]
    refine ⟨min m₀ 1, lt_min hm₀ one_pos, fun z hz => ?_⟩
    by_cases hz₁ : V z ≤ 1
    · exact (min_le_left _ _).trans (h_le z ⟨hz₁, hz⟩)
    · exact (min_le_right _ _).trans (not_le.mp hz₁).le
  -- ... so small balls qualify, and `δ(ε) > 0`.
  have hS_pos : ∀ ε > 0, ∃ ρ > 0, ρ ∈ S ε := fun ε hε => by
    obtain ⟨m, hm, h_m⟩ := h_far_pos ε hε
    obtain ⟨ρ₀, hρ₀, h_near⟩ := Metric.continuousAt_iff.mp hV_cont.continuousAt m hm
    have hρ_pos : 0 < min (ρ₀ / 2) ε := lt_min (half_pos hρ₀) hε
    refine ⟨min (ρ₀ / 2) ε, hρ_pos, ⟨hρ_pos.le, min_le_right _ _⟩, fun y z hy hz => ?_⟩
    have h_dist : dist y x_eq < ρ₀ := by
      rw [dist_eq_norm]
      linarith [min_le_left (ρ₀ / 2) ε]
    have h_small := h_near h_dist
    rw [Real.dist_eq, hV_pos.2.1, sub_zero, abs_of_nonneg (hV_nonneg y)] at h_small
    exact h_small.trans_le (h_m z hz)
  let δ : ℝ → ℝ := fun ε => sSup (S ε)
  have hδ_pos : ∀ ε > 0, 0 < δ ε := fun ε hε => by
    obtain ⟨ρ, hρ_pos, hρ⟩ := hS_pos ε hε
    exact hρ_pos.trans_le (le_csSup (hS_bdd ε) hρ)
  -- Starting within `δ(ε)` traps the trajectory in the `ε`-ball, from any initial time.
  have h_trap_δ : ∀ ε > 0, ∀ {a b : ℝ} {x : ℝ → ℝⁿ},
      s.IsTrajectoryOn (fun _ => ()) x (Icc a b) → ‖x a - x_eq‖ < δ ε →
        ∀ t ∈ Icc a b, ‖x t - x_eq‖ < ε := fun ε hε {a b x} hx h_init => by
    obtain ⟨ρ, -, hρ⟩ := hS_pos ε hε
    obtain ⟨ρ', hρ', h_lt⟩ := exists_lt_of_lt_csSup ⟨ρ, hρ⟩ h_init
    exact h_trap hx fun z hz => hρ'.2 _ z h_lt.le hz
  -- `δ(ε) → ∞`: every radius `R` qualifies once `ε` is large, since `V` is bounded on the
  -- `R`-ball and exceeds that bound far out.
  have hδ_tendsto : Tendsto δ atTop atTop := by
    refine tendsto_atTop.mpr fun R => ?_
    obtain ⟨C, hC⟩ :=
      (isCompact_closedBall x_eq (max R 0)).exists_bound_of_continuousOn hV_cont.continuousOn
    obtain ⟨ρ₁, hρ₁⟩ := (hV_sub C).isBounded.subset_closedBall x_eq
    refine eventually_atTop.mpr ⟨max (max R 0) (ρ₁ + 1), fun ε hε => ?_⟩
    have hR_mem : max R 0 ∈ S ε := by
      refine ⟨⟨le_max_right _ _, (le_max_left _ _).trans hε⟩, fun y z hy hz => ?_⟩
      have hVy : V y ≤ C := (Real.le_norm_self _).trans (hC y (mem_closedBall_iff_norm.mpr hy))
      have hVz : C < V z := by
        by_contra h
        have h_in := mem_closedBall_iff_norm.mp (hρ₁ (not_lt.mp h))
        linarith [(le_max_right (max R 0) (ρ₁ + 1)).trans hε]
      exact hVy.trans_lt hVz
    exact (le_max_left R 0).trans (le_csSup (hS_bdd ε) hR_mem)
  refine ⟨⟨δ, hδ_pos, hδ_tendsto, fun ε hε t₀ _ t₁ x hx h_init => h_trap_δ ε hε hx h_init⟩,
    fun c hc η hη => ?_⟩
  -- Step 4. From the `c`-ball, `V ≤ M`, and trajectories stay in the compact `{V ≤ M}` ...
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall x_eq c).exists_bound_of_continuousOn hV_cont.continuousOn
  have hM_ball : ∀ y : ℝⁿ, ‖y - x_eq‖ ≤ c → V y ≤ M := fun y hy =>
    (Real.le_norm_self _).trans (hM y (mem_closedBall_iff_norm.mpr hy))
  have hM_nonneg : 0 ≤ M := (hV_nonneg x_eq).trans (hM_ball x_eq (by simpa using hc.le))
  -- ... on which, outside the `δ(η)`-ball, `∇V · f ≤ -γ < 0`.
  obtain ⟨γ, hγ, h_rate⟩ := exists_pos_le_of_isCompact (g := fun y => -fderiv ℝ V y (f y))
    ((hV_sub M).inter_right (h_far_closed (δ η)))
    ((hV_c1.continuous_fderiv one_ne_zero).clm_apply hf).neg.continuousOn
    fun y hy => neg_pos.mpr (hV_neg y fun h => by
      subst h
      simp at hy
      linarith [hy.2, hδ_pos η hη])
  have hT_pos : 0 < M / γ + 1 := add_pos_of_nonneg_of_pos (div_nonneg hM_nonneg hγ.le) one_pos
  refine ⟨M / γ + 1, hT_pos, fun t₀ _ t₁ x hx h_init t ht => ?_⟩
  have hT_le : t₀ + (M / γ + 1) ≤ t₁ := ht.1.trans ht.2
  have hx_T := IsIntegralCurveOn.mono hx (Icc_subset_Icc_right hT_le)
  -- Step 5. `V` falls at rate `γ` while the trajectory is outside the `δ(η)`-ball, so it has
  -- entered that ball by time `t₀ + M / γ + 1`.
  obtain ⟨τ, hτ, hτ_in⟩ : ∃ τ ∈ Icc t₀ (t₀ + (M / γ + 1)), ‖x τ - x_eq‖ < δ η := by
    by_contra h_never
    push Not at h_never
    have h_drop := add_mul_le_of_lie_le hF hV (c := γ) hx_T (by linarith) fun τ hτ => by
      have hτ' : τ ∈ Icc t₀ (t₀ + (M / γ + 1)) := Ioo_subset_Icc_self hτ
      linarith [show γ ≤ -fderiv ℝ V (x τ) (f (x τ)) from h_rate _
        ⟨(h_dec hx_T τ hτ').trans (hM_ball _ h_init.le), h_never τ hτ'⟩]
    have h_eq : γ * (t₀ + (M / γ + 1)) = γ * t₀ + M + γ := by
      field_simp
      ring
    linarith [hM_ball _ h_init.le, hV_nonneg (x (t₀ + (M / γ + 1)))]
  -- Step 6. From then on the trajectory stays in the `η`-ball.
  exact h_trap_δ η hη (IsIntegralCurveOn.mono hx (Icc_subset_Icc_left hτ.1)) hτ_in t
    ⟨hτ.2.trans ht.1, ht.2⟩

end Euclidean

end ContinuousSystem

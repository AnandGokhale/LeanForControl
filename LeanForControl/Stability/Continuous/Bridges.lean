import LeanForControl.Stability.Continuous.LyapunovTheorems
import LeanForControl.Stability.DefsAutonomous
import LeanForControl.Stability.DefsNonAutonomous
import Architect

/-!
# `Stability.Continuous.Bridges` — the existing stability predicates as views

The stability predicates of `Stability.DefsAutonomous` and `Stability.DefsNonAutonomous` are
stated on a raw vector field `f`.  This file relates them to the predicates of
`Stability.Continuous.Defs`, stated on the system `ContinuousSystem.autonomous f g`.  It is
temporary: it exists so that the older files can be migrated one at a time, and goes away when
they have been.

* `lyapunovStable_iff_stable` — for a time-invariant field, `LyapunovStable` (finite segments,
  any initial time) is exactly `Stable`.  The direction from `Stable` uses time invariance: a
  segment starting at `t₀` shifts to one starting at `0`.
* `Stable.stableNA` — `Stable` implies `StableNA`.  The converse fails: `StableNA` quantifies over
  solutions on `[t₀, ∞)` only, so a solution that escapes in finite time is not tested.  For
  `ẋ = x²` the origin is unstable — solutions from `x₀ > 0` blow up — yet `StableNA` holds,
  because no such solution exists on `[t₀, ∞)` and the remaining ones decay.

## The old Lyapunov theorems, derived from the new ones

The theorems of the retired `Stability.Autonomous` are proved in
`Stability.Continuous.LyapunovTheorems`.  Their old statements are kept here, proved by
translating the old certificate into a new one, applying the new theorem, and translating the
conclusion back.  Callers that still use the old predicates are unaffected, and each statement
records that the move lost nothing.

* `IsLocalLyapunovFunction.isUniformLyapunovFunction` — an old local Lyapunov function is a
  (time-invariant) uniform Lyapunov function of the system.
* `lyapunov_stable` — Lyapunov's stability theorem, in its old statement.
* `unstable_of_fixed_escape` — instability from a fixed escape radius, from
  `ContinuousSystem.unstable_of_escape`.
* `IsStrictLocalLyapunovFunction.isStrictUniformLyapunovFunction` — an old strict local Lyapunov
  function is a strict uniform Lyapunov function of the system.
* `tendsto_of_hasUniformConvergenceTime` — a uniform convergence time makes every solution on a
  ray starting in the ball converge, from any initial time.
* `lyapunov_local_asymptotic_stable` — Lyapunov's local asymptotic stability theorem.
* `LocallyExponentiallyStable.locallyExponentiallyStable` — the old local exponential stability
  of a field gives the new one of its system, with the same constants.
* `LocallyExponentiallyStable.lyapunovStable` — local exponential stability implies stability.
* `lyapunov_asymptotic_stable`, `lyapunov_global_asymptotic_stable` — Lyapunov's global
  asymptotic stability theorem, from
  `ContinuousSystem.globallyUniformlyAsymptoticallyStable_of_lyapunov`.

## The old calculus helpers

The helpers the retired `Stability.Autonomous` used to differentiate `V(x)` along a solution of
`ẋ = f(x)` are special cases of `Analysis.LieDerivative`, for a function of the state alone.
They are kept here in their old form for the callers that still use it; new code uses
`Analysis.LieDerivative` directly.
-/

open Set Filter Topology

namespace ContinuousSystem

section TimeInvariant

variable {n : ℕ} {Y : Type*}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- **`LyapunovStable` is `Stable`** for a time-invariant field.  `LyapunovStable` allows any
initial time with one `δ`; `Stable` allows `t₀ ≥ 0` with `δ` depending on `t₀`.  They agree
because time invariance shifts every segment to one starting at `0`. -/
@[blueprint "thm:continuousSystem-lyapunovStable-iff-stable"
  (title := "Lyapunov stability of a time-invariant field is stability")
  (statement := /-- For a time-invariant field $f$, \cref{def:lyapunovStable} holds if and only
    if the equilibrium of the system $\dot x = f(x)$ is stable
    (\cref{def:continuousSystem-stable}). -/)
  (proof := /-- The first allows every initial time with a single $\delta$, which in particular
    serves every $t_0 \ge 0$.  Conversely, stability at $t_0 = 0$ gives a $\delta$; a segment on
    $[t_0, t_1]$ shifts to one on $[0, t_1 - t_0]$ (\cref{lem:isIntegralCurveOn-shift-to-zero}),
    to which that $\delta$ applies. -/)]
theorem lyapunovStable_iff_stable (f : ℝⁿ → ℝⁿ) (g : ℝ → ℝⁿ → Y) (x_eq : ℝⁿ) :
    LyapunovStable f x_eq ↔ (autonomous (fun _ => f) g).Stable x_eq := by
  constructor
  · -- one `δ` for every initial time serves in particular every `t₀ ≥ 0`
    intro h ε hε t₀ _
    obtain ⟨δ, hδ, h_bound⟩ := h ε hε
    exact ⟨δ, hδ, fun t₁ x hx hx₀ => h_bound t₀ t₁ x hx hx₀⟩
  · -- the `δ` for `t₀ = 0` serves every initial time, after shifting the segment to `0`
    intro h ε hε
    obtain ⟨δ, hδ, h_bound⟩ := h ε hε 0 le_rfl
    refine ⟨δ, hδ, fun t₀ t₁ φ hφ hφ₀ t ht => ?_⟩
    have h_shift := hφ.shift_to_zero
    have h_near := h_bound (t₁ - t₀) (fun s => φ (s + t₀)) h_shift (by simpa using hφ₀)
      (t - t₀) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa using h_near

end TimeInvariant

section TimeVarying

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **`Stable` implies `StableNA`.**  Every solution on `[t₀, ∞)` restricts to every segment
`[t₀, t]`, where `Stable` bounds it.

The converse fails: `StableNA` does not test solutions that escape in finite time.  For
`ẋ = x²` the origin is not stable, but `StableNA` holds. -/
@[blueprint "thm:continuousSystem-stable-stableNA"
  (title := "Stability implies stability on forward-complete solutions")
  (statement := /-- If the equilibrium of $\dot x = f(t, x)$ is stable
    (\cref{def:continuousSystem-stable}), then \cref{def:stableNA} holds.

    The converse fails: \cref{def:stableNA} quantifies only over solutions on $[t_0, \infty)$, so
    a solution that escapes in finite time is not tested.  For $\dot x = x^2$ the origin is not
    stable, since solutions from $x_0 > 0$ blow up, yet \cref{def:stableNA} holds. -/)
  (proof := /-- A solution on $[t_0, \infty)$ restricts to every segment $[t_0, t]$, on which
    stability bounds it at the endpoint $t$. -/)]
theorem Stable.stableNA {f : ℝ → E → E} {g : ℝ → E → Y} {x_eq : E}
    (h : (autonomous f g).Stable x_eq) : StableNA f x_eq := by
  intro ε hε t₀ ht₀
  obtain ⟨δ, hδ, h_bound⟩ := h ε hε t₀ ht₀
  exact ⟨δ, hδ, fun φ hφ hφ₀ t ht =>
    h_bound t φ (IsIntegralCurveOn.mono hφ Icc_subset_Ici_self) hφ₀ t ⟨ht, le_rfl⟩⟩

end TimeVarying

end ContinuousSystem

/-! ## The old Lyapunov theorems -/

section Legacy

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The Lie derivative `x ↦ DV(x)[f(x)]` is continuous when `V` is C¹ and `f` is continuous:
`continuous_lieDerivative` for a function of the state alone. -/
theorem lie_deriv_continuous {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_c1 : ContDiff ℝ 1 V) (hf_cont : Continuous f) :
    Continuous (fun x : ℝⁿ => fderiv ℝ V x (f x)) :=
  ((continuous_lieDerivative (V := fun _ => V) (v := fun _ x => f x)
    (hV_c1.comp contDiff_snd) (hf_cont.comp continuous_snd)).comp
      (continuous_const.prodMk continuous_id : Continuous fun x : ℝⁿ => ((0 : ℝ), x))).congr
    fun x => lieDerivative_const (v := fun _ y => f y) (t := 0)
      ((hV_c1.differentiable one_ne_zero) x)

/-- The chain rule `(V ∘ φ)'(t) = DV(φ t)[f (φ t)]` along a solution segment, at an interior
time: `IsIntegralCurveOn.hasDerivWithinAt_lieDerivative` for a function of the state alone. -/
@[blueprint "lem:hasDerivAt-V-comp-traj"
  (title := "Chain rule along a trajectory")
  (latexEnv := "lemma")
  (statement := /-- Let $V$ be differentiable and let $\varphi$ be a solution segment on
    $[t_0, t_1]$.  Then at every interior time $t$,
    \[
      (V \circ \varphi)'(t) \;=\; DV(\varphi(t))\,[\,f(\varphi(t))\,] .
    \]
    This is \cref{lem:isIntegralCurveOn-hasDerivWithinAt-lieDerivative} for a function of the
    state alone (\cref{lem:lieDerivative-const}). -/)]
theorem hasDerivAt_V_comp_traj {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} (hV_diff : Differentiable ℝ V)
    {φ : ℝ → ℝⁿ} {t₀ t₁ : ℝ} (hφ : IsTrajectoryOn φ f t₀ t₁) {t : ℝ} (ht : t ∈ Ioo t₀ t₁) :
    HasDerivAt (V ∘ φ) (fderiv ℝ V (φ t) (f (φ t))) t := by
  have h := (IsIntegralCurveOn.hasDerivWithinAt_lieDerivative (V := fun _ => V) hφ
    (hV_diff.comp differentiable_snd) (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  rwa [lieDerivative_const (hV_diff _)] at h

/-- **Rate-bounded monotonicity.** If the Lie derivative is at most `-c` on the interior of the
solution's interval, then `t ↦ V (φ t) + c * t` is antitone on it.

The weight is what turns a *rate* bound into a bound on *elapsed time*: `V` is bounded below, so
`V (φ t) + c * t` being antitone caps how long `φ` can spend where the rate bound holds.  It is
plain monotonicity of the time-varying `W(t, x) = V(x) + c t`, whose Lie derivative along `f` is
`DV(x)[f(x)] + c`. -/
@[blueprint "lem:antitoneOn-V-add-linear"
  (title := "Rate-bounded monotonicity")
  (latexEnv := "lemma")
  (statement := /-- Let $\varphi$ be an integral curve of
    $f$ on a convex set $s$, with $DV(\varphi(t))[f(\varphi(t))] \le -c$ at every interior
    point.  Then $t \mapsto V(\varphi(t)) + ct$ is antitone on $s$.

    The weight is what turns a bound on the \emph{rate} into a bound on \emph{elapsed time}:
    since $V$ is bounded below, antitonicity of $V \circ \varphi + ct$ caps how long $\varphi$
    can remain where the rate bound holds.  Taking $c = 0$ gives plain monotonicity. -/)
  (proof := /-- $V(\varphi(t)) + ct = W(t, \varphi(t))$ for $W(t, x) = V(x) + ct$, whose Lie
    derivative along $f$ is $DV(x)[f(x)] + c \le 0$ (\cref{lem:lieDerivative-add-mul}); apply
    \cref{lem:isIntegralCurveOn-antitoneOn-of-lieDerivative-nonpos}. -/)]
theorem antitoneOn_V_add_linear {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ V) (_hV_cont : Continuous V)
    {φ : ℝ → ℝⁿ} {s : Set ℝ} (hs : Convex ℝ s)
    (hφ : IsIntegralCurveOn φ (fun _ x => f x) s)
    {c : ℝ} (hLie : ∀ t ∈ interior s, fderiv ℝ V (φ t) (f (φ t)) ≤ -c) :
    AntitoneOn (fun t => V (φ t) + c * t) s := by
  exact IsIntegralCurveOn.antitoneOn_of_lieDerivative_nonpos (V := fun t x => V x + c * t) hφ hs
    ((hV_diff.comp differentiable_snd).add (differentiable_fst.const_mul c)) fun t ht => by
      rw [lieDerivative_add_mul c (hV_diff _)]
      linarith [hLie t ht]

/-- The unweighted case of `antitoneOn_V_add_linear`: `V ∘ φ` is antitone wherever the Lie
derivative is nonpositive. -/
@[blueprint "lem:antitoneOn-V-comp-traj"
  (title := "$V$ is nonincreasing along a solution")
  (latexEnv := "lemma")
  (statement := /-- The unweighted case $c = 0$ of \cref{lem:antitoneOn-V-add-linear}:
    $V \circ \varphi$ is antitone wherever the Lie derivative is nonpositive.  This is the sense
    in which a Lyapunov function ``never increases along solutions''. -/)]
theorem antitoneOn_V_comp_traj {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ V) (hV_cont : Continuous V)
    {φ : ℝ → ℝⁿ} {s : Set ℝ} (hs : Convex ℝ s)
    (hφ : IsIntegralCurveOn φ (fun _ x => f x) s)
    (hLie : ∀ t ∈ interior s, fderiv ℝ V (φ t) (f (φ t)) ≤ 0) :
    AntitoneOn (V ∘ φ) s := by
  simpa [Function.comp_def] using
    antitoneOn_V_add_linear hV_diff hV_cont hs hφ (c := 0) (by simpa using hLie)

/-- `V` is nonincreasing on `[t₀, t₁]` when the solution segment stays in `D` on that
interval and the Lie derivative is nonpositive on `D`: the endpoint form of
`antitoneOn_V_comp_traj`. -/
@[blueprint "lem:V-nonincreasing-on"
  (title := "$V$ does not increase from the initial time")
  (latexEnv := "lemma")
  (statement := /-- \cref{lem:antitoneOn-V-comp-traj} in endpoint form: if $V$ is a local
    Lyapunov certificate on $D$ and the solution segment stays in $D$ throughout
    $[t_0, t_1]$, then $V(\varphi(t_1)) \le V(\varphi(t_0))$. -/)]
theorem V_nonincreasing_on {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq D) {φ : ℝ → ℝⁿ} {t₀ t₁ : ℝ}
    (hφ : IsTrajectoryOn φ f t₀ t₁) (hle : t₀ ≤ t₁) (hstay : ∀ t ∈ Icc t₀ t₁, φ t ∈ D) :
    V (φ t₁) ≤ V (φ t₀) := by
  have hanti : AntitoneOn (V ∘ φ) (Icc t₀ t₁) :=
    antitoneOn_V_comp_traj hV.hV_diff hV.hcont (convex_Icc t₀ t₁) hφ fun t ht => by
      rw [interior_Icc] at ht
      exact hV.hLie_nonpos (φ t) (hstay t (Ioo_subset_Icc_self ht))
  exact hanti (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle) hle

/-- An old local Lyapunov function `V(x)` is a uniform Lyapunov function `(t, x) ↦ V(x)` of the
system `ẋ = f(x)`: `V` is its own lower and upper bound. -/
theorem IsLocalLyapunovFunction.isUniformLyapunovFunction {Y : Type*} {f : ℝⁿ → ℝⁿ}
    {g : ℝ → ℝⁿ → Y} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq D) :
    (ContinuousSystem.autonomous (fun _ => f) g).IsUniformLyapunovFunction (fun _ => V) x_eq D :=
  ContinuousSystem.IsUniformLyapunovFunction.of_timeInvariant (hV.hD_open.mem_nhds hV.hD_mem)
    hV.hV_diff ⟨hV.hcont.continuousOn, hV.hzero, hV.hpos⟩ fun _ _ x hx => hV.hLie_nonpos x hx

/-- **Lyapunov's stability theorem.** If `V` is a local Lyapunov function on `D`, then
`x_eq` is stable with respect to every finite forward solution segment.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.1, first conclusion. -/
@[blueprint "thm:lyapunov-stable"
  (title := "Lyapunov's stability theorem")
  (statement := /-- If $V$ is a local Lyapunov function (\cref{def:isLocalLyapunovFunction}) for
    $\dot{x} = f(x)$ on a domain $D \ni x_{\mathrm{eq}}$, then $x_{\mathrm{eq}}$
    is stable on every finite forward solution segment
    (\cref{def:lyapunovStable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.1, first conclusion ($x = 0$ is
    stable under (4.2) and (4.3)).
  -/)
  (proof := /-- $V$ is a uniform Lyapunov function of the system $\dot x = f(x)$
    (\cref{lem:continuousSystem-isUniformLyapunovFunction-of-timeInvariant}), so the equilibrium
    is uniformly stable (\cref{thm:continuousSystem-isUniformLyapunovFunction-uniformlyStable}),
    hence stable, and stability of a time-invariant field is
    \cref{def:lyapunovStable} (\cref{thm:continuousSystem-lyapunovStable-iff-stable}). -/)]
theorem lyapunov_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsLocalLyapunovFunction f V x_eq D) :
    LyapunovStable f x_eq :=
  haveI : NeZero n := ⟨hn.ne'⟩
  (ContinuousSystem.lyapunovStable_iff_stable f (fun _ _ => ()) x_eq).mpr
    (hV.isUniformLyapunovFunction.uniformlyStable.stable)

/-- A fixed escape radius witnessed from arbitrarily small initial perturbations on finite
forward segments implies instability.

Reference: Khalil, *Nonlinear Systems*. -/
@[blueprint "thm:unstable-of-fixed-escape"
  (title := "Instability from a fixed escape radius")
  (statement := /-- Fix $\varepsilon > 0$.  If for every $\delta > 0$ some solution segment
    starts within $\delta$ of $x_{\mathrm{eq}}$ and reaches distance at least $\varepsilon$
    from it, then $x_{\mathrm{eq}}$ is unstable.  This is the contrapositive of stability, in
    the form the instability theorems produce their witnesses.

    Reference: Khalil, \emph{Nonlinear Systems}.
  -/)
  (proof := /-- \cref{lem:continuousSystem-unstable-of-escape} for the system
    $\dot x = f(x)$, translated by \cref{thm:continuousSystem-lyapunovStable-iff-stable}. -/)]
theorem unstable_of_fixed_escape
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {ε : ℝ} (hε : 0 < ε)
    (hescape : ∀ δ > 0, ∃ (T : ℝ) (φ : ℝ → ℝⁿ) (t : ℝ),
      IsTrajectoryOn φ f 0 T ∧ ‖φ 0 - x_eq‖ < δ ∧
        t ∈ Set.Icc (0 : ℝ) T ∧ ε ≤ ‖φ t - x_eq‖) :
    Unstable f x_eq := fun h =>
  ContinuousSystem.unstable_of_escape hε hescape
    ((ContinuousSystem.lyapunovStable_iff_stable f (fun _ _ => ()) x_eq).mp h)


/-- An old strict local Lyapunov function `V(x)` is a strict uniform Lyapunov function
`(t, x) ↦ V(x)` of the system `ẋ = f(x)`, for continuous `f`: the rate is `W₃ = -∇V · f`. -/
theorem IsStrictLocalLyapunovFunction.isStrictUniformLyapunovFunction {Y : Type*}
    {f : ℝⁿ → ℝⁿ} {g : ℝ → ℝⁿ → Y} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ}
    (hV : IsStrictLocalLyapunovFunction f V x_eq D) (hf_cont : Continuous f) :
    (ContinuousSystem.autonomous (fun _ => f) g).IsStrictUniformLyapunovFunction (fun _ => V)
      x_eq D :=
  ContinuousSystem.IsStrictUniformLyapunovFunction.of_timeInvariant_of_neg (fun _ _ => rfl)
    hf_cont (hV.hD_open.mem_nhds hV.hD_mem) hV.hV_c1 ⟨hV.hcont.continuousOn, hV.hzero, hV.hpos⟩
    hV.hequil hV.hLie_neg

/-- A uniform convergence time from the `c`-ball makes every solution of `ẋ = f(x)` on a ray
`[t₀, ∞)` that starts in the ball converge to `x_eq`, from any initial time: shift the solution to
start at `0`, and apply the convergence time to its segments `[0, t - t₀]`. -/
theorem tendsto_of_hasUniformConvergenceTime {Y : Type*} {f : ℝⁿ → ℝⁿ} {g : ℝ → ℝⁿ → Y}
    {x_eq : ℝⁿ} {c : ℝ}
    (h : (ContinuousSystem.autonomous (fun _ => f) g).HasUniformConvergenceTime x_eq c)
    {t₀ : ℝ} {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ y => f y) (Ici t₀))
    (h_init : ‖φ t₀ - x_eq‖ < c) :
    Tendsto φ atTop (𝓝 x_eq) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, -, h_conv⟩ := h ε hε
  refine ⟨t₀ + T, fun t ht => ?_⟩
  have h_seg := (IsIntegralCurveOn.mono hφ (Icc_subset_Ici_self : Icc t₀ t ⊆ Ici t₀)).shift_to_zero
  have h_near := h_conv 0 le_rfl (t - t₀) (fun s => φ (s + t₀)) h_seg (by simpa using h_init)
    (t - t₀) ⟨by linarith, le_rfl⟩
  rw [dist_eq_norm]
  simpa using h_near

/-- **Lyapunov's local asymptotic stability theorem.** `IsStrictLocalLyapunovFunction` implies
`LocalAsymptoticStable`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.1, second conclusion. -/
@[blueprint "thm:lyapunov-local-asymptotic-stable"
  (title := "Lyapunov's local asymptotic stability theorem")
  (statement := /-- If $V$ is a strict local Lyapunov function
    (\cref{def:isStrictLocalLyapunovFunction}) and $f$ is continuous, then
    $x_{\mathrm{eq}}$ is locally asymptotically stable
    (\cref{def:localAsymptoticStable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.1, second conclusion
    (strengthening (4.3) to (4.4) gives asymptotic stability).
  -/)
  (proof := /-- $V$ is a strict uniform Lyapunov function of the system $\dot x = f(x)$
    (\cref{lem:continuousSystem-isStrictUniformLyapunovFunction-of-timeInvariant-of-neg}), so
    the equilibrium is uniformly asymptotically stable
    (\cref{thm:continuousSystem-isStrictUniformLyapunovFunction-uniformlyAsymptoticallyStable}).
    Stability translates by \cref{thm:continuousSystem-lyapunovStable-iff-stable}; the uniform
    convergence time makes every solution on a ray from the basin converge, after shifting it
    to start at time $0$. -/)]
theorem lyapunov_local_asymptotic_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsStrictLocalLyapunovFunction f V x_eq D)
    (hf_cont : Continuous f) :
    LocalAsymptoticStable f x_eq := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨hUS, c, hc, h_conv⟩ := (hV.isStrictUniformLyapunovFunction (g := fun _ _ => ())
    hf_cont).uniformlyAsymptoticallyStable
  exact ⟨(ContinuousSystem.lyapunovStable_iff_stable f (fun _ _ => ()) x_eq).mpr hUS.stable,
    c, hc, fun _ _ hφ h_init => tendsto_of_hasUniformConvergenceTime h_conv hφ h_init⟩


/-- The old local exponential stability of `ẋ = f(x)` is the new one of its system, with the
same constants: the old estimate holds from every initial time, the new one asks only `t₀ ≥ 0`. -/
theorem LocallyExponentiallyStable.locallyExponentiallyStable {Y : Type*} {f : ℝⁿ → ℝⁿ}
    {g : ℝ → ℝⁿ → Y} {x_eq : ℝⁿ} (h : LocallyExponentiallyStable f x_eq) :
    (ContinuousSystem.autonomous (fun _ => f) g).LocallyExponentiallyStable x_eq := by
  obtain ⟨r, C, a, hr, hC, ha, h_decay⟩ := h
  exact ⟨r, hr, C, one_pos.trans_le hC, a, ha, fun t₀ _ t₁ x hx h_init t ht =>
    (h_decay t₀ t₁ x hx h_init t ht).trans_eq (by ring)⟩

/-- Local exponential stability on finite forward segments implies Lyapunov stability.

Reference: Khalil, *Nonlinear Systems*. -/
@[blueprint "thm:locallyExponentiallyStable-lyapunovStable"
  (title := "Exponential stability implies Lyapunov stability")
  (statement := /-- Local exponential stability implies Lyapunov stability.

    Reference: Khalil, \emph{Nonlinear Systems}.
  -/)
  (proof := /-- The estimate is local exponential stability of the system $\dot x = f(x)$
    (\cref{def:continuousSystem-locallyExponentiallyStable}), which implies uniform stability,
    hence stability; translate by \cref{thm:continuousSystem-lyapunovStable-iff-stable}. -/)]
theorem LocallyExponentiallyStable.lyapunovStable {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (h : LocallyExponentiallyStable f x_eq) : LyapunovStable f x_eq :=
  (ContinuousSystem.lyapunovStable_iff_stable f (fun _ _ => ()) x_eq).mpr
    h.locallyExponentiallyStable.uniformlyStable.stable


/-- `IsAsymptoticLyapunovFunction` implies `IsStrictLyapunovFunction`.
    Uses `isCompact_sublevel_set` to convert radial unboundedness into compact sublevel sets. -/
@[blueprint "lem:asymptotic-implies-strict"
  (title := "An asymptotic Lyapunov function is strict")
  (latexEnv := "lemma")
  (statement := /-- An asymptotic Lyapunov function is a strict one: radial unboundedness
    supplies the bounded-sublevel-set condition the strict notion requires. -/)
  (proof := /-- A continuous radially unbounded function has compact sublevel sets. -/)]
theorem asymptotic_implies_strict
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsAsymptoticLyapunovFunction f V x_eq) :
    IsStrictLyapunovFunction f V x_eq where
  hcont             := hV.hcont
  hV_c1             := hV.hV_c1
  hzero             := hV.hzero
  hpos              := hV.hpos
  hequil            := hV.hequil
  hLie_neg          := hV.hLie_neg
  hbounded_sublevel := isCompact_sublevel_set V hV.hcont hV.hradial

/-- **Lyapunov's global asymptotic stability theorem.** `IsStrictLyapunovFunction` implies
`GlobalAsymptoticStable`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.2, with (4.6) in its
compact-sublevel-set form. -/
@[blueprint "thm:lyapunov-asymptotic-stable"
  (title := "Lyapunov's global asymptotic stability theorem")
  (statement := /-- If $V$ is a global strict Lyapunov function
    (\cref{def:isStrictLyapunovFunction})
    and $f$ is continuous, then $x_{\mathrm{eq}}$ is globally asymptotically stable
    (\cref{def:globalAsymptoticStable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.2, with radial unboundedness
    (4.6) in its compact-sublevel-set form.
  -/)
  (proof := /-- The equilibrium of $\dot x = f(x)$ is globally uniformly asymptotically stable
    (\cref{thm:continuousSystem-globallyUniformlyAsymptoticallyStable-of-lyapunov}).  Stability
    translates by \cref{thm:continuousSystem-lyapunovStable-iff-stable}; a solution on a ray
    starts in some ball, from which the uniform convergence time makes it converge. -/)]
theorem lyapunov_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsStrictLyapunovFunction f V x_eq)
    (hf_cont : Continuous f) :
    GlobalAsymptoticStable f x_eq := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨hGUS, h_conv⟩ := ContinuousSystem.globallyUniformlyAsymptoticallyStable_of_lyapunov
    (s := ContinuousSystem.autonomous (fun _ => f) (fun _ _ => ())) (fun _ _ => rfl) hf_cont
    hV.hV_c1 ⟨hV.hcont.continuousOn, hV.hzero, fun x _ hx => hV.hpos x hx⟩
    hV.hbounded_sublevel hV.hLie_neg
  refine ⟨(ContinuousSystem.lyapunovStable_iff_stable f (fun _ _ => ()) x_eq).mpr
    hGUS.uniformlyStable.stable, fun t₀ φ hφ => ?_⟩
  exact tendsto_of_hasUniformConvergenceTime
    (h_conv _ ((norm_nonneg _).trans_lt (lt_add_one ‖φ t₀ - x_eq‖))) hφ (lt_add_one _)

/-- **Corollary.** `IsAsymptoticLyapunovFunction` implies `GlobalAsymptoticStable`
    (the classical radially-unbounded form of the theorem).

    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.2 (Barbashin–Krasovskii). -/
@[blueprint "thm:lyapunov-global-asymptotic-stable"
  (title := "Global asymptotic stability from a radially unbounded $V$")
  (statement := /-- If $V$ is a radially unbounded strict Lyapunov function
    (\cref{def:isAsymptoticLyapunovFunction}) and $f$ is continuous, then
    $x_{\mathrm{eq}}$ is globally asymptotically stable on finite forward
    solution segments.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.2 (Barbashin--Krasovskii).
  -/)
  (proof := /-- Radial unboundedness gives compact sublevel sets
    (\cref{lem:isCompact-sublevel-set}), so $V$ satisfies
    \cref{def:isStrictLyapunovFunction}; apply
    \cref{thm:lyapunov-asymptotic-stable}. -/)]
theorem lyapunov_global_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsAsymptoticLyapunovFunction f V x_eq)
    (hf_cont : Continuous f) :
    GlobalAsymptoticStable f x_eq :=
  lyapunov_asymptotic_stable hn (asymptotic_implies_strict hV) hf_cont

end Legacy

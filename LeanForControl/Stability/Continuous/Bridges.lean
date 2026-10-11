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

As theorems of `Stability.Autonomous` move to `Stability.Continuous.LyapunovTheorems`, their old
statements are kept here, proved by translating the old certificate into a new one, applying the
new theorem, and translating the conclusion back.  Callers that still use the old predicates are
unaffected, and each statement records that the move lost nothing.

* `IsLocalLyapunovFunction.isUniformLyapunovFunction` — an old local Lyapunov function is a
  (time-invariant) uniform Lyapunov function of the system.
* `lyapunov_stable` — Lyapunov's stability theorem, in its old statement.
* `unstable_of_fixed_escape` — instability from a fixed escape radius, from
  `ContinuousSystem.unstable_of_escape`.
-/

open Set

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

end Legacy

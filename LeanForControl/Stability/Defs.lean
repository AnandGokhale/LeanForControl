import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Group.Bounded


import Mathlib.Topology.Order.MonotoneContinuity

variable {n : ℕ}

/-!
# `Stability.Defs`

Core definitions for the stability theory of autonomous ODEs `ẋ = f(x)` on `ℝⁿ`.

## Notation

`ℝⁿ` denotes `EuclideanSpace ℝ (Fin n)` throughout this file and all files that import it.

## Contents

* **Trajectories and equilibria** (`IsTrajectory`, `IsEquilibrium`).
* **Stability predicates** (`LyapunovStable`, `LocalAsymptoticStable`,
  `GlobalAsymptoticStable`).
* **Sublevel sets** (`SublevelSet`).
* **Lyapunov function structures**, forming the hierarchy:
  - `IsLocalLyapunovFunction` → `LyapunovStable`
  - `IsStrictLocalLyapunovFunction` → `LocalAsymptoticStable`
  - `IsStrictLyapunovFunction` → `GlobalAsymptoticStable`
  - `IsAsymptoticLyapunovFunction` → `GlobalAsymptoticStable` (classical radially-unbounded form)
* **Positive invariance** (`IsPositivelyInvariant`).
* **Compact sublevel sets** (`isCompact_sublevel_set`).
-/

open Set Filter Topology

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## System primitives -/

/-- A global solution `φ : ℝ → ℝⁿ` of the autonomous ODE `ẋ = f(x)`,
    defined for all `t ∈ ℝ`. -/
def IsTrajectory (φ : ℝ → ℝⁿ) (f : ℝⁿ → ℝⁿ) : Prop :=
  ∀ t : ℝ, HasDerivAt φ (f (φ t)) t

/-- An equilibrium point `x_eq` of `ẋ = f(x)`: `f(x_eq) = 0`. -/
def IsEquilibrium (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  f x_eq = 0

/-! ## Stability predicates -/

/-- Standard Lyapunov (ε-δ) stability: trajectories starting near `x_eq` remain near `x_eq`
    for all future time. -/
def LyapunovStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ φ : ℝ → ℝⁿ,
    IsTrajectory φ f → ‖φ 0 - x_eq‖ < δ → ∀ t ≥ 0, ‖φ t - x_eq‖ < ε

/-- Local asymptotic stability: Lyapunov stable, and trajectories starting sufficiently near
    `x_eq` also converge to `x_eq` as `t → ∞`. -/
def LocalAsymptoticStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  LyapunovStable f x_eq ∧
  ∃ c > 0, ∀ φ : ℝ → ℝⁿ,
    IsTrajectory φ f → ‖φ 0 - x_eq‖ < c → Filter.Tendsto φ Filter.atTop (nhds x_eq)

/-- Global asymptotic stability: Lyapunov stable, and every trajectory converges to `x_eq`. -/
def GlobalAsymptoticStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  LyapunovStable f x_eq ∧
  ∀ φ : ℝ → ℝⁿ, IsTrajectory φ f → Filter.Tendsto φ Filter.atTop (nhds x_eq)

/-! ## Sublevel sets -/

/-- The sublevel set `{x | V(x) ≤ c}` of `V` at level `c`. -/
def SublevelSet (V : ℝⁿ → ℝ) (c : ℝ) : Set ℝⁿ := {x | V x ≤ c}

/-! ## Lyapunov function structures

Four structures forming a hierarchy:

  IsLocalLyapunovFunction (on domain D) → LyapunovStable
  IsStrictLocalLyapunovFunction (on domain D, compact sublevel set) → LocalAsymptoticStable
  IsStrictLyapunovFunction (global, compact sublevel sets) → GlobalAsymptoticStable
  IsAsymptoticLyapunovFunction (global, radially unbounded) → GlobalAsymptoticStable

For the local structures, V : ℝⁿ → ℝ is globally continuous and differentiable
(needed for chain rule and IVT arguments), but positivity and Lie-derivative
conditions hold only on the domain D. The bridge lemma `contDiffOn_extension`
justifies this: any C¹ function on open D extends to a globally C¹ function
agreeing with the original on a neighborhood of x_eq.

The Lie derivative DV(x)[f(x)] = fderiv ℝ V x (f x). -/

/-- Local Lyapunov certificate: `V` is positive definite on `D` and has nonpositive Lie
    derivative on `D`. Implies `LyapunovStable`.

    `D` is an open neighborhood of `x_eq`; `V` is globally smooth so that the chain rule
    and IVT arguments can be applied uniformly. -/
structure IsLocalLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) (D : Set ℝⁿ) : Prop where
  hD_open     : IsOpen D
  hD_mem      : x_eq ∈ D
  hcont       : Continuous V
  hV_diff     : Differentiable ℝ V
  hzero       : V x_eq = 0
  hpos        : ∀ x ∈ D, x ≠ x_eq → 0 < V x
  hLie_nonpos : ∀ x ∈ D, fderiv ℝ V x (f x) ≤ 0

/-- Strict local Lyapunov certificate: `V` has strictly negative Lie derivative on `D`
    and a compact sublevel set `{V ≤ c} ⊆ D`. Implies `LocalAsymptoticStable`.

    `hcompact`: ∃ c > 0 with `{V ≤ c} ⊆ D` and `{V ≤ c}` compact. This replaces radial
    unboundedness and holds whenever `D` is bounded or `V` grows toward `∂D`. -/
structure IsStrictLocalLyapunovFunction
    (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) (D : Set ℝⁿ) : Prop where
  hD_open   : IsOpen D
  hD_mem    : x_eq ∈ D
  hcont     : Continuous V
  hV_c1     : ContDiff ℝ 1 V
  hzero     : V x_eq = 0
  hpos      : ∀ x ∈ D, x ≠ x_eq → 0 < V x
  hequil    : f x_eq = 0
  hLie_neg  : ∀ x ∈ D, x ≠ x_eq → fderiv ℝ V x (f x) < 0
  hcompact  : ∃ c > 0, SublevelSet V c ⊆ D ∧ IsCompact (SublevelSet V c)

/-- Global strict Lyapunov certificate: `V` is C¹, positive definite, with strictly negative Lie
    derivative on all of `ℝⁿ`, and all sublevel sets are compact (coercivity). Implies GAS.

    `hbounded_sublevel` encodes coercivity; in `ℝⁿ` this is equivalent to radial unboundedness. -/
structure IsStrictLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont             : Continuous V
  hV_c1             : ContDiff ℝ 1 V
  hzero             : V x_eq = 0
  hpos              : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x
  hequil            : f x_eq = 0
  hLie_neg          : ∀ x : ℝⁿ, x ≠ x_eq → fderiv ℝ V x (f x) < 0
  hbounded_sublevel : ∀ c : ℝ, IsCompact {x : ℝⁿ | V x ≤ c}

/-- Classical GAS Lyapunov certificate: C¹, positive definite, strictly negative Lie derivative,
    and radially unbounded (`V(x) → ∞` as `‖x‖ → ∞`). Implies `IsStrictLyapunovFunction`
    via `isCompact_sublevel_set` in `Autonomous.lean`. -/
structure IsAsymptoticLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont    : Continuous V
  hV_c1    : ContDiff ℝ 1 V
  hzero    : V x_eq = 0
  hpos     : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x
  hequil   : f x_eq = 0
  hLie_neg : ∀ x : ℝⁿ, x ≠ x_eq → fderiv ℝ V x (f x) < 0
  hradial  : Filter.Tendsto V (Filter.comap norm Filter.atTop) Filter.atTop

/-! ## Positive invariance -/

/-- A set `S` is positively invariant for `ẋ = f(x)`: every trajectory starting in `S`
    remains in `S` for all `t ≥ 0`. -/
def IsPositivelyInvariant (S : Set ℝⁿ) (f : ℝⁿ → ℝⁿ) : Prop :=
  ∀ φ : ℝ → ℝⁿ, IsTrajectory φ f → φ 0 ∈ S → ∀ t ≥ 0, φ t ∈ S

/-- Sublevel sets of a radially unbounded continuous function are compact.

Proof:
1. Closed: `SublevelSet V c = V ⁻¹' (Iic c)`, closed by continuity.
2. Bounded: coercivity gives `R` with `SublevelSet V c ⊆ closedBall 0 R`.
3. Heine–Borel in `ℝⁿ`: closed + bounded = compact. -/
lemma isCompact_sublevel_set
    (V : ℝⁿ → ℝ) (hcont : Continuous V)
    (hradial : Filter.Tendsto V (Filter.comap norm Filter.atTop) Filter.atTop)
    (c : ℝ) : IsCompact (SublevelSet V c) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_Iic.preimage hcont
  · rw [comap_norm_atTop, Metric.cobounded_eq_cocompact] at hradial
    have hev : {x : ℝⁿ | c < V x} ∈ Filter.cocompact ℝⁿ :=
      hradial (Filter.eventually_gt_atTop c)
    rw [Filter.mem_cocompact] at hev
    obtain ⟨K, hK_compact, hK⟩ := hev
    rw [Metric.isBounded_iff_subset_closedBall 0]
    obtain ⟨R, hR⟩ := hK_compact.isBounded.subset_closedBall 0
    refine ⟨R, fun x hx => hR ?_⟩
    by_contra hxK
    have hVx : c < V x := hK (Set.mem_compl hxK)
    exact absurd hVx (not_lt.mpr hx)

/-! ## Extension lemma

If V₀ is C¹ on an open set D containing x₀, it can be extended to a globally
C¹ function agreeing with V₀ on some neighborhood of x₀.

Proof sketch: V = ψ · V₀ where ψ : ℝⁿ → ℝ is a ContDiffBump function with
ψ = 1 near x₀ and supp ψ compactly contained in D. Since supp ψ ⊆ D and ψ
vanishes near ∂D, the product ψ · V₀ is globally C¹. -/

-- lemma contDiffOn_extension
--     {D : Set ℝⁿ} (hD : IsOpen D) {x₀ : ℝⁿ} (hx₀ : x₀ ∈ D)
--     {V₀ : ℝⁿ → ℝ} (hV : ContDiffOn ℝ 1 V₀ D) :
--     ∃ (V : ℝⁿ → ℝ) (D' : Set ℝⁿ), IsOpen D' ∧ x₀ ∈ D' ∧ D' ⊆ D ∧
--       ContDiff ℝ 1 V ∧ Set.EqOn V V₀ D' := by
--   sorry

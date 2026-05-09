import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Group.Bounded
variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Class K and K∞ functions -/

-- α : [0, ∞) → ℝ, continuous, zero at zero, strictly increasing.
def IsClassK (α : ℝ → ℝ) : Prop :=
  ContinuousOn α (Set.Ici 0) ∧ α 0 = 0 ∧ StrictMonoOn α (Set.Ici 0)

-- Class K and radially unbounded: α(r) → ∞ as r → ∞.
def IsClassKInfty (α : ℝ → ℝ) : Prop :=
  IsClassK α ∧ Filter.Tendsto α Filter.atTop Filter.atTop

/-! ## System primitives -/

-- φ is a global solution of ẋ = f(x), defined for all t ∈ ℝ.
def IsTrajectory (φ : ℝ → ℝⁿ) (f : ℝⁿ → ℝⁿ) : Prop :=
  ∀ t : ℝ, HasDerivAt φ (f (φ t)) t

-- x_eq is an equilibrium point: f(x_eq) = 0.
def IsEquilibrium (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  f x_eq = 0

/-! ## Stability predicates -/

-- Standard ε-δ Lyapunov stability.
def LyapunovStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ φ : ℝ → ℝⁿ,
    IsTrajectory φ f → ‖φ 0 - x_eq‖ < δ → ∀ t ≥ 0, ‖φ t - x_eq‖ < ε

-- Lyapunov stable and trajectories starting near x_eq converge to x_eq.
def LocalAsymptoticStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  LyapunovStable f x_eq ∧
  ∃ c > 0, ∀ φ : ℝ → ℝⁿ,
    IsTrajectory φ f → ‖φ 0 - x_eq‖ < c → Filter.Tendsto φ Filter.atTop (nhds x_eq)

-- Lyapunov stable and every trajectory converges to x_eq.
def GlobalAsymptoticStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  LyapunovStable f x_eq ∧
  ∀ φ : ℝ → ℝⁿ, IsTrajectory φ f → Filter.Tendsto φ Filter.atTop (nhds x_eq)

/-! ## Lyapunov function structures

Three structures, forming a hierarchy:
  IsLocalLyapunovFunction → stability (Theorem 4.1, Part 1)
  IsStrictLyapunovFunction → GAS     (Theorem 4.1, Parts 2 & 3)
  IsAsymptoticLyapunovFunction       (classical K∞ formulation → GAS via the above)

The Lie derivative DV(x)[f(x)] is the directional derivative of V at x in the
direction f(x); it equals d/dt V(φ(t))|_{t=0} along the trajectory through x.
It is written `fderiv ℝ V x (f x)` in Lean. -/

-- Theorem 4.1, Part 1: V positive definite, Lie derivative ≤ 0 everywhere.
structure IsLocalLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont       : Continuous V
  hV_diff     : Differentiable ℝ V
  hzero       : V x_eq = 0
  hpos        : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x
  hLie_nonpos : ∀ x : ℝⁿ, fderiv ℝ V x (f x) ≤ 0

-- Theorem 4.1, Parts 2 & 3: strict Lie derivative + compact sublevel sets.
-- hbounded_sublevel encodes coercivity: sublevel sets {V ≤ c} are compact.
-- In ℝⁿ this is equivalent to radial unboundedness of V.
-- Under these global conditions the conclusion is GAS, not merely LAS.
structure IsStrictLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont             : Continuous V
  hV_c1             : ContDiff ℝ 1 V
  hzero             : V x_eq = 0
  hpos              : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x
  hequil            : f x_eq = 0
  hLie_neg          : ∀ x : ℝⁿ, x ≠ x_eq → fderiv ℝ V x (f x) < 0
  hbounded_sublevel : ∀ c : ℝ, IsCompact {x : ℝⁿ | V x ≤ c}

-- Global Lyapunov function with quantitative K∞ sandwich bounds.
-- Gives stability with explicit bounds on trajectory excursions.
-- V̇ ≤ 0 only; add strict condition for GAS.
structure IsGlobalLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont       : Continuous V
  hV_diff     : Differentiable ℝ V
  halphas     : ∃ α₁ α₂ : ℝ → ℝ, IsClassKInfty α₁ ∧ IsClassKInfty α₂ ∧
                  ∀ x : ℝⁿ, α₁ ‖x - x_eq‖ ≤ V x ∧ V x ≤ α₂ ‖x - x_eq‖
  hLie_nonpos : ∀ x : ℝⁿ, fderiv ℝ V x (f x) ≤ 0

-- Classical formulation for Theorem 4.1, Part 3:
-- C¹, positive definite, strict Lie derivative, radially unbounded.
-- This implies IsStrictLyapunovFunction (proven in Autonomous.lean using
-- isCompact_sublevel_set).
structure IsAsymptoticLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont    : Continuous V
  hV_c1    : ContDiff ℝ 1 V
  hzero    : V x_eq = 0
  hpos     : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x
  hequil   : f x_eq = 0
  hLie_neg : ∀ x : ℝⁿ, x ≠ x_eq → fderiv ℝ V x (f x) < 0
  hradial  : Filter.Tendsto V (Filter.comap norm Filter.atTop) Filter.atTop

/-! ## Sublevel sets -/

def SublevelSet (V : ℝⁿ → ℝ) (c : ℝ) : Set ℝⁿ := {x | V x ≤ c}

-- Sublevel sets of a radially unbounded continuous function are compact.
-- Proof strategy:
--   (1) Closed: SublevelSet V c = V ⁻¹' (Set.Iic c), closed by continuity of V.
--   (2) Bounded: if (xₙ) ⊆ SublevelSet V c with ‖xₙ‖ → ∞, then V(xₙ) → ∞
--       by hradial, contradicting V(xₙ) ≤ c.
--   (3) In ℝⁿ (finite-dimensional), closed + bounded = compact (Heine-Borel).
-- Lean path: Metric.isCompact_iff_isClosed_bounded (or ProperSpace argument).
lemma isCompact_sublevel_set
    (V : ℝⁿ → ℝ) (hcont : Continuous V)
    (hradial : Filter.Tendsto V (Filter.comap norm Filter.atTop) Filter.atTop)
    (c : ℝ) : IsCompact (SublevelSet V c) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · -- Closed: SublevelSet V c = V ⁻¹' Set.Iic c
    exact isClosed_Iic.preimage hcont
  · -- Bounded: coercivity gives an R with SublevelSet V c ⊆ closedBall 0 R
    -- Step 1: rewrite comap norm atTop as cobounded, then cobounded = cocompact
    rw [comap_norm_atTop, Metric.cobounded_eq_cocompact] at hradial
    -- Step 2: {x | c < V x} is in the cocompact filter
    have hev : {x : ℝⁿ | c < V x} ∈ Filter.cocompact ℝⁿ :=
      hradial (Filter.eventually_gt_atTop c)
    -- Step 3: unpack: ∃ compact K with Kᶜ ⊆ {x | c < V x}
    rw [Filter.mem_cocompact] at hev
    obtain ⟨K, hK_compact, hK⟩ := hev
    -- Step 4: SublevelSet V c ⊆ K, and K is bounded
    rw [Metric.isBounded_iff_subset_closedBall 0]
    obtain ⟨R, hR⟩ := hK_compact.isBounded.subset_closedBall 0
    refine ⟨R, fun x hx => hR ?_⟩
    by_contra hxK
    have hxKc : x ∈ Kᶜ := Set.mem_compl hxK
    have hVx : c < V x := hK hxKc
    exact absurd hVx (not_lt.mpr hx)

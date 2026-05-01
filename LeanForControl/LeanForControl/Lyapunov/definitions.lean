import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.Basic
variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)


---------------------------------------------------------
-- Class K and Class K_infty Definitions
---------------------------------------------------------

-- A class K function is continuous, zero at zero, and strictly increasing.
def IsClassK (α : ℝ → ℝ) : Prop :=
  ContinuousOn α (Set.Ici 0) ∧
  α 0 = 0 ∧
  StrictMonoOn α (Set.Ici 0)

-- A class K_infty function is a class K function that is radially unbounded.
def IsClassKInfty (α : ℝ → ℝ) : Prop :=
  IsClassK α ∧ Filter.Tendsto α Filter.atTop Filter.atTop


----------------------------------------------------------
-- We define a trajectory
def IsTrajectory (φ : ℝ → ℝⁿ) (f : ℝⁿ → ℝⁿ) : Prop :=
  ∀ t : ℝ, HasDerivAt φ (f (φ t)) t

-- An equilibrium point
def IsEquilibrium (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  f x_eq = 0

-- And Lyapunov stability
def LyapunovStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ φ : ℝ → ℝⁿ,
    IsTrajectory φ f → -- Removed explicit 'n'
    ‖φ 0 - x_eq‖ < δ →
    ∀ t ≥ 0, ‖φ t - x_eq‖ < ε

def AsymptoticallyStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  LyapunovStable f x_eq ∧
  ∃ c > 0, ∀ φ : ℝ → ℝⁿ,
    IsTrajectory φ f →
    ‖φ 0 - x_eq‖ < c →
    Filter.Tendsto φ Filter.atTop (nhds x_eq)



---------------------------------------------------------
-- Global Lyapunov Function Definition
---------------------------------------------------------

-- For Global Stability, V is sandwiched between two Class K_infty functions.
-- This intrinsically gives us V(x_eq) = 0, positivity, and radial unboundedness.
structure IsGlobalLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont : Continuous V
  halphas : ∃ α₁ α₂ : ℝ → ℝ, IsClassKInfty α₁ ∧ IsClassKInfty α₂ ∧
    ∀ x : ℝⁿ, α₁ ‖x - x_eq‖ ≤ V x ∧ V x ≤ α₂ ‖x - x_eq‖
  hderiv : ∀ φ : ℝ → ℝⁿ, IsTrajectory φ f →
            ∀ t : ℝ, HasDerivAt (V ∘ φ) (fderiv ℝ V (φ t) (f (φ t))) t
  hnonincr : ∀ φ : ℝ → ℝⁿ, IsTrajectory φ f →
              ∀ t : ℝ, fderiv ℝ V (φ t) (f (φ t)) ≤ 0


-- Finally, the definition of a Lyapunov function
structure IsLocalLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont    : Continuous V
  hzero    : V x_eq = 0
  hpos     : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x
  hderiv   : ∀ φ : ℝ → ℝⁿ, IsTrajectory φ f → -- Removed explicit 'n'
              ∀ t : ℝ, HasDerivAt (V ∘ φ) (fderiv ℝ V (φ t) (f (φ t))) t
  hnonincr : ∀ φ : ℝ → ℝⁿ, IsTrajectory φ f → -- Removed explicit 'n'
              ∀ t : ℝ, fderiv ℝ V (φ t) (f (φ t)) ≤ 0

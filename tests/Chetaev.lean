import LeanForControl.Stability.Continuous.Chetaev
import Mathlib.Analysis.Normed.Operator.Banach

/-!
Regression example for the geometric Chetaev criterion: constant rightward flow on
one-dimensional Euclidean space is unstable at zero, although zero is not an equilibrium.
The certificate is the coordinate function on the positive half-space. This checks the
boundary-based certificate construction, local radius hypotheses, and finite-segment theorem.
-/

open Set

namespace ChetaevRegression

noncomputable section

private abbrev State := EuclideanSpace ℝ (Fin 1)

/-- The real coordinate of a one-dimensional Euclidean state. -/
private def coordinate : State →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 1 ↦ ℝ) 0

/-- The positive coordinate half-space. -/
private def positiveRegion : Set State := coordinate ⁻¹' Ioi 0

/-- The unit vector giving constant rightward velocity. -/
private def velocity : State := PiLp.single 2 0 1

/-- The input-free time-invariant system with constant rightward velocity and unit output. -/
private def rightwardSystem : ContinuousSystem State Unit Unit :=
  ContinuousSystem.timeInvariant (fun _ _ ↦ velocity) (fun _ _ ↦ ())

/-- The coordinate projection is surjective. -/
private theorem coordinate_surjective : Function.Surjective coordinate := by
  intro r
  exact ⟨PiLp.single 2 0 r, by simp [coordinate]⟩

/-- Zero belongs to the boundary of the positive coordinate half-space. -/
private theorem zero_mem_boundary : (0 : State) ∈ frontier positiveRegion := by
  rw [positiveRegion,
    ← (coordinate.isOpenMap coordinate_surjective).preimage_frontier_eq_frontier_preimage
      coordinate.continuous (Ioi 0), frontier_Ioi]
  simp

/-- The coordinate is a Chetaev certificate for constant rightward flow in the unit ball. -/
private theorem rightward_certificate :
    rightwardSystem.IsChetaevFunction coordinate 0 positiveRegion 1 := by
  refine {
    hradius := by norm_num
    hD_open := isOpen_Ioi.preimage coordinate.continuous
    hmem_boundary := zero_mem_boundary
    hV_c1 := coordinate.contDiff
    hpos := ?_
    hboundary_zero := ?_
    hLie_pos := ?_
  }
  · intro x hx _
    exact hx
  · intro x hx _
    have hx_zero := coordinate.continuous.frontier_preimage_subset (Ioi 0) hx
    simpa [frontier_Ioi] using hx_zero
  · intro t _ x _ _
    rw [ContinuousSystem.lieDerivative, lieDerivative_const coordinate.differentiableAt,
      coordinate.fderiv]
    norm_num [rightwardSystem, ContinuousSystem.timeInvariant, coordinate, velocity]

/-- The geometric criterion proves instability at a base point that is not an equilibrium. -/
private theorem rightward_unstable_at_zero : rightwardSystem.Unstable 0 := by
  exact ContinuousSystem.unstable_of_geometric_chetaev (fun _ _ ↦ rfl)
    contDiff_const rightward_certificate

/-- The result negates `Stable`, so it also rules out the stronger `UniformlyStable` predicate. -/
private theorem rightward_not_uniformlyStable : ¬ rightwardSystem.UniformlyStable 0 := by
  intro h
  exact rightward_unstable_at_zero h.stable

/-- The velocity at zero is nonzero, so the preceding example cannot use an equilibrium premise. -/
private theorem rightward_not_equilibrium (t : ℝ) : rightwardSystem.F t 0 () ≠ 0 := by
  intro h
  have hcoordinate := congrArg coordinate h
  norm_num [rightwardSystem, ContinuousSystem.timeInvariant, coordinate, velocity] at hcoordinate

#print axioms rightward_unstable_at_zero
#print axioms rightward_not_uniformlyStable

end

end ChetaevRegression

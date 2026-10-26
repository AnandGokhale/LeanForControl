import LeanForControl.Analysis.ConvexAnalysis.Subdifferential
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# `Analysis.ConvexAnalysis.Prox` — the proximal operator

For `γ > 0` and `R` with effective domain `D`, the *proximal operator* of `γR` is

    prox_{γR}(v) = argmin_{z ∈ D} R(z) + ‖z - v‖² / (2γ).

For closed, convex, proper `R` the minimizer exists and is unique.  Following Mathlib's convention
for partial operations (`deriv`, `Real.sqrt`), `prox` is a total function: where no minimizer
exists it returns `v`, a value that the existence theorem shows is never used.

* `IsClosedConvexProper.exists_lower_bound` — `R` grows at most linearly downwards, so the
  quadratic term makes the prox objective coercive.
* `isMinOn_prox_objective_iff` — `z` minimizes the prox objective iff `(v - z)/γ ∈ ∂R(z)`.
* `prox_mem`, `isMinOn_prox` — existence: `prox` is a minimizer.
* `eq_prox_of_isMinOn` — uniqueness: every minimizer is `prox`.
* `eq_prox_iff` — the optimality condition `z = prox_{γR}(v) ↔ (v - z)/γ ∈ ∂R(z)`.
* `norm_prox_sub_prox_sq_le`, `lipschitzWith_prox` — firm nonexpansivity, hence nonexpansivity.
-/

open Set Filter Metric
open scoped RealInnerProductSpace Gradient

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

open scoped Classical in
/-- The *proximal operator* of `γR`: the minimizer over `D` of `y ↦ R y + ‖y - v‖² / (2γ)`.  It
exists and is unique when `R` is closed, convex and proper and `γ > 0`; otherwise it is `v`. -/
noncomputable def prox (γ : ℝ) (R : X → ℝ) (D : Set X) (v : X) : X :=
  if h : ∃ z ∈ D, IsMinOn (fun y => R y + ‖y - v‖ ^ 2 / (2 * γ)) D z then h.choose else v

namespace IsClosedConvexProper

variable {R : X → ℝ} {D : Set X}

/-- A closed convex proper function is lower semicontinuous on its domain. -/
theorem lowerSemicontinuousOn (hR : IsClosedConvexProper R D) : LowerSemicontinuousOn R D :=
  lowerSemicontinuousOn_iff_preimage_Iic.2 fun b =>
    ⟨{x ∈ D | R x ≤ b}, hR.isClosed_sublevel b, by ext x; simp⟩

/-- **Linear lower bound.**  A closed convex proper function grows at most linearly downwards:
for `x₀ ∈ D` there are `m` and `C ≥ 0` with `m - C ‖y - x₀‖ ≤ R y` on `D`.  It is bounded below
on the unit ball about `x₀` by compactness, and outside it by convexity along the segment from
`x₀`. -/
theorem exists_lower_bound [FiniteDimensional ℝ X] (hR : IsClosedConvexProper R D) {x₀ : X}
    (hx₀ : x₀ ∈ D) : ∃ m C : ℝ, 0 ≤ C ∧ ∀ y ∈ D, m - C * ‖y - x₀‖ ≤ R y := by
  -- `R` attains its minimum `R a` on the compact set `{y ∈ D | R y ≤ R x₀} ∩ B̄(x₀, 1)`.
  obtain ⟨a, ha, hmin⟩ := (hR.lowerSemicontinuousOn.mono
      (inter_subset_left.trans (sep_subset _ _))).exists_isMinOn
    (⟨x₀, ⟨hx₀, le_rfl⟩, mem_closedBall_self zero_le_one⟩ :
      ({y ∈ D | R y ≤ R x₀} ∩ closedBall x₀ 1).Nonempty)
    ((isCompact_closedBall x₀ 1).inter_left (hR.isClosed_sublevel (R x₀)))
  have h_ball : ∀ y ∈ D, ‖y - x₀‖ ≤ 1 → R a ≤ R y := fun y hy hr => by
    by_cases h : R y ≤ R x₀
    · exact hmin ⟨⟨hy, h⟩, mem_closedBall_iff_norm.2 hr⟩
    · exact ha.1.2.trans (le_of_not_ge h)
  refine ⟨R a, R x₀ - R a, sub_nonneg.2 ha.1.2, fun y hy => ?_⟩
  rcases le_or_gt ‖y - x₀‖ 1 with hr | hr
  · nlinarith [h_ball y hy hr, norm_nonneg (y - x₀), ha.1.2]
  -- Outside the ball, compare with the point `p` at distance `1` on the segment to `y`.
  set r := ‖y - x₀‖
  have hr₀ : 0 < r := by linarith
  have h_p : R a ≤ (1 - r⁻¹) * R x₀ + r⁻¹ * R y := calc
    R a ≤ R (x₀ + r⁻¹ • (y - x₀)) :=
      h_ball _ (hR.convexOn.1.add_smul_sub_mem hx₀ hy
        ⟨inv_nonneg.2 hr₀.le, inv_le_one_of_one_le₀ hr.le⟩)
        (by rw [add_sub_cancel_left, norm_smul, norm_inv, Real.norm_of_nonneg hr₀.le,
          inv_mul_cancel₀ hr₀.ne'])
    _ = R ((1 - r⁻¹) • x₀ + r⁻¹ • y) := by congr 1; module
    _ ≤ (1 - r⁻¹) * R x₀ + r⁻¹ * R y :=
      hR.convexOn.2 hx₀ hy (sub_nonneg.2 (inv_le_one_of_one_le₀ hr.le))
        (inv_nonneg.2 hr₀.le) (sub_add_cancel 1 _)
  have h_r : r * R a ≤ (r - 1) * R x₀ + R y := by
    have := mul_le_mul_of_nonneg_left h_p hr₀.le
    rwa [mul_add, ← mul_assoc, ← mul_assoc, mul_sub, mul_one, mul_inv_cancel₀ hr₀.ne',
      one_mul] at this
  nlinarith [ha.1.2]

end IsClosedConvexProper

variable {R : X → ℝ} {D : Set X} {γ : ℝ}

/-- For closed convex proper `R` and `γ > 0`, the prox objective `R y + ‖y - v‖² / (2γ)` has a
minimizer on `D`: it is lower semicontinuous, and coercive by the linear lower bound. -/
theorem exists_isMinOn_prox_objective [FiniteDimensional ℝ X] (hR : IsClosedConvexProper R D)
    (hγ : 0 < γ) (v : X) :
    ∃ z ∈ D, IsMinOn (fun y => R y + ‖y - v‖ ^ 2 / (2 * γ)) D z := by
  obtain ⟨x₀, hx₀⟩ := hR.nonempty
  obtain ⟨m, C, hC, hm⟩ := hR.exists_lower_bound hx₀
  set c := R x₀ + ‖x₀ - v‖ ^ 2 / (2 * γ)
  set d := ‖x₀ - v‖
  set ρ := d + 2 * γ * (C + |c - m| + C * d) + 1
  -- Minimize on the compact `K = {y ∈ D | R y ≤ c} ∩ B̄(x₀, ρ)`, which contains `x₀`.
  have hρ : 0 ≤ ρ := by positivity
  obtain ⟨z, hz, hzmin⟩ := ((hR.lowerSemicontinuousOn.mono
      (inter_subset_left.trans (sep_subset _ _))).add
      ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2 |>.div_const (2 * γ)
        |>.continuousOn.lowerSemicontinuousOn)).exists_isMinOn
    (⟨x₀, ⟨hx₀, le_add_of_nonneg_right (by positivity)⟩, mem_closedBall_self hρ⟩ :
      ({y ∈ D | R y ≤ c} ∩ closedBall x₀ ρ).Nonempty)
    ((isCompact_closedBall x₀ ρ).inter_left (hR.isClosed_sublevel c))
  refine ⟨z, hz.1.1, fun y hy => ?_⟩
  change R z + ‖z - v‖ ^ 2 / (2 * γ) ≤ R y + ‖y - v‖ ^ 2 / (2 * γ)
  have hzc : R z + ‖z - v‖ ^ 2 / (2 * γ) ≤ c :=
    hzmin ⟨⟨hx₀, le_add_of_nonneg_right (by positivity)⟩, mem_closedBall_self hρ⟩
  by_cases hK : y ∈ {y ∈ D | R y ≤ c} ∩ closedBall x₀ ρ
  · exact hzmin hK
  -- Off `K`, the objective exceeds `c`.
  refine hzc.trans ?_
  simp only [mem_inter_iff, mem_setOf_eq, hy, true_and, mem_closedBall_iff_norm, not_and_or,
    not_le] at hK
  rcases hK with hRy | hr
  · linarith [div_nonneg (sq_nonneg ‖y - v‖) (by positivity : (0 : ℝ) ≤ 2 * γ)]
  · have h_tri : ‖y - x₀‖ - d ≤ ‖y - v‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub y v x₀
      rw [norm_sub_rev v x₀] at this
      linarith
    have hs : 1 ≤ ‖y - x₀‖ - d := by
      have : 0 ≤ 2 * γ * (C + |c - m| + C * d) := by positivity
      linarith
    have h_sq : (‖y - x₀‖ - d) ^ 2 ≤ ‖y - v‖ ^ 2 := pow_le_pow_left₀ (by linarith) h_tri 2
    have h_key : 2 * γ * (c - m + C * ‖y - x₀‖) ≤ (‖y - x₀‖ - d) ^ 2 := by
      have h₁ : c - m ≤ |c - m| := le_abs_self _
      have h₂ : 2 * γ * (C + |c - m| + C * d) ≤ ‖y - x₀‖ - d := by linarith
      have h₃ : 0 ≤ 2 * γ * (|c - m| + C * d) :=
        mul_nonneg (by positivity) (add_nonneg (abs_nonneg _) (mul_nonneg hC (norm_nonneg _)))
      calc 2 * γ * (c - m + C * ‖y - x₀‖)
          ≤ 2 * γ * (|c - m| + C * d) + 2 * γ * C * (‖y - x₀‖ - d) := by
            linarith [mul_le_mul_of_nonneg_left h₁ (by positivity : (0 : ℝ) ≤ 2 * γ)]
        _ ≤ 2 * γ * (|c - m| + C * d) * (‖y - x₀‖ - d) + 2 * γ * C * (‖y - x₀‖ - d) := by
            linarith [le_mul_of_one_le_right h₃ hs]
        _ = 2 * γ * (C + |c - m| + C * d) * (‖y - x₀‖ - d) := by ring
        _ ≤ (‖y - x₀‖ - d) * (‖y - x₀‖ - d) := mul_le_mul_of_nonneg_right h₂ (by linarith)
        _ = (‖y - x₀‖ - d) ^ 2 := by ring
    have h_quad : c - m + C * ‖y - x₀‖ ≤ ‖y - v‖ ^ 2 / (2 * γ) :=
      (le_div_iff₀ (by positivity)).2 (by nlinarith)
    linarith [hm y hy]

/-- The gradient of the prox quadratic `y ↦ ‖y - v‖² / (2γ)` at `z` is `γ⁻¹ (z - v)`. -/
theorem hasGradientAt_norm_sub_sq_div [CompleteSpace X] (v z : X) (γ : ℝ) :
    HasGradientAt (fun y => ‖y - v‖ ^ 2 / (2 * γ)) (γ⁻¹ • (z - v)) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const v).norm_sq.mul_const (2 * γ)⁻¹
  simp only [id, ← div_eq_mul_inv] at h
  refine h.congr_fderiv ?_
  ext w
  simp
  ring

/-- **Prox optimality.**  For `R` convex on `D` and `γ > 0`, `z ∈ D` minimizes the prox objective
`R y + ‖y - v‖² / (2γ)` over `D` if and only if `(v - z)/γ ∈ ∂R(z)`. -/
theorem isMinOn_prox_objective_iff [CompleteSpace X] (hR : ConvexOn ℝ D R) (hγ : 0 < γ)
    {v z : X} :
    (z ∈ D ∧ IsMinOn (fun y => R y + ‖y - v‖ ^ 2 / (2 * γ)) D z) ↔
      γ⁻¹ • (v - z) ∈ subdifferential R D z := by
  constructor
  · rintro ⟨hz, hmin⟩
    have h := neg_gradient_mem_subdifferential_of_isMinOn hR
      (hasGradientAt_norm_sub_sq_div v z γ).differentiableAt hz
      (by simpa only [add_comm] using hmin)
    rwa [(hasGradientAt_norm_sub_sq_div v z γ).gradient, ← smul_neg, neg_sub] at h
  · intro h
    refine ⟨h.1, fun y hy => ?_⟩
    -- `‖y - v‖² = ‖y - z‖² - 2⟪y - z, v - z⟫ + ‖v - z‖²`, and the subgradient inequality
    -- absorbs the cross term.
    have h_sub := h.2 y hy
    rw [real_inner_smul_left, real_inner_comm] at h_sub
    change R z + ‖z - v‖ ^ 2 / (2 * γ) ≤ R y + ‖y - v‖ ^ 2 / (2 * γ)
    rw [show ‖y - v‖ ^ 2 = ‖y - z‖ ^ 2 - 2 * ⟪y - z, v - z⟫ + ‖v - z‖ ^ 2 by
      rw [show y - v = (y - z) - (v - z) by abel, norm_sub_sq_real], norm_sub_rev z v]
    have h_split : (‖y - z‖ ^ 2 - 2 * ⟪y - z, v - z⟫ + ‖v - z‖ ^ 2) / (2 * γ)
        = ‖y - z‖ ^ 2 / (2 * γ) - γ⁻¹ * ⟪y - z, v - z⟫ + ‖v - z‖ ^ 2 / (2 * γ) := by
      field_simp
    rw [h_split]
    linarith [div_nonneg (sq_nonneg ‖y - z‖) (by positivity : (0 : ℝ) ≤ 2 * γ)]

/-- **Firm nonexpansivity, pointwise.**  If `(v - p)/γ ∈ ∂R(p)` and `(w - q)/γ ∈ ∂R(q)`, then
`‖p - q‖² ≤ ⟪p - q, v - w⟫`: monotonicity of `∂R`. -/
theorem norm_sub_sq_le_inner_of_mem_subdifferential (hγ : 0 < γ) {v w p q : X}
    (hp : γ⁻¹ • (v - p) ∈ subdifferential R D p) (hq : γ⁻¹ • (w - q) ∈ subdifferential R D q) :
    ‖p - q‖ ^ 2 ≤ ⟪p - q, v - w⟫ := by
  have h := inner_sub_sub_nonneg_of_mem_subdifferential hp hq
  rw [← smul_sub, real_inner_smul_left] at h
  have h' : 0 ≤ ⟪(v - w) - (p - q), p - q⟫ := by
    rw [show (v - w) - (p - q) = (v - p) - (w - q) by abel]
    exact (mul_nonneg_iff_of_pos_left (inv_pos.2 hγ)).1 h
  rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm] at h'
  linarith

section Properties

/-- **Existence.**  For closed, convex, proper `R` and `γ > 0`, the proximal point lies in the
domain. -/
theorem prox_mem [FiniteDimensional ℝ X] (hR : IsClosedConvexProper R D) (hγ : 0 < γ) (v : X) :
    prox γ R D v ∈ D := by
  rw [prox, dif_pos (exists_isMinOn_prox_objective hR hγ v)]
  exact (exists_isMinOn_prox_objective hR hγ v).choose_spec.1

/-- **Existence.**  For closed, convex, proper `R` and `γ > 0`, the proximal point minimizes
`R y + ‖y - v‖² / (2γ)` over the domain. -/
theorem isMinOn_prox [FiniteDimensional ℝ X] (hR : IsClosedConvexProper R D) (hγ : 0 < γ)
    (v : X) : IsMinOn (fun y => R y + ‖y - v‖ ^ 2 / (2 * γ)) D (prox γ R D v) := by
  rw [prox, dif_pos (exists_isMinOn_prox_objective hR hγ v)]
  exact (exists_isMinOn_prox_objective hR hγ v).choose_spec.2

/-- **Uniqueness.**  Every minimizer of `R y + ‖y - v‖² / (2γ)` over the domain is the proximal
point. -/
theorem eq_prox_of_isMinOn [FiniteDimensional ℝ X] (hR : IsClosedConvexProper R D) (hγ : 0 < γ)
    {v z : X} (hz : z ∈ D) (hmin : IsMinOn (fun y => R y + ‖y - v‖ ^ 2 / (2 * γ)) D z) :
    z = prox γ R D v := by
  -- Both are minimizers, so both satisfy the optimality condition; monotonicity of `∂R` then
  -- gives `‖z - prox v‖² ≤ 0`.
  have h := norm_sub_sq_le_inner_of_mem_subdifferential hγ
    ((isMinOn_prox_objective_iff hR.convexOn hγ).1 ⟨hz, hmin⟩)
    ((isMinOn_prox_objective_iff hR.convexOn hγ).1 ⟨prox_mem hR hγ v, isMinOn_prox hR hγ v⟩)
  rw [sub_self, inner_zero_right] at h
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1
    (le_antisymm h (sq_nonneg _))))

/-- **Proximal optimality condition.**  `z = prox_{γR}(v)` if and only if `(v - z)/γ ∈ ∂R(z)`. -/
theorem eq_prox_iff [FiniteDimensional ℝ X] (hR : IsClosedConvexProper R D) (hγ : 0 < γ)
    {v z : X} : z = prox γ R D v ↔ γ⁻¹ • (v - z) ∈ subdifferential R D z := by
  constructor
  · rintro rfl
    exact (isMinOn_prox_objective_iff hR.convexOn hγ).1 ⟨prox_mem hR hγ v, isMinOn_prox hR hγ v⟩
  · intro h
    obtain ⟨hz, hmin⟩ := (isMinOn_prox_objective_iff hR.convexOn hγ).2 h
    exact eq_prox_of_isMinOn hR hγ hz hmin

/-- **Firm nonexpansivity.**
`‖prox_{γR}(v) - prox_{γR}(w)‖² ≤ ⟪prox_{γR}(v) - prox_{γR}(w), v - w⟫`. -/
theorem norm_prox_sub_prox_sq_le [FiniteDimensional ℝ X] (hR : IsClosedConvexProper R D)
    (hγ : 0 < γ) (v w : X) :
    ‖prox γ R D v - prox γ R D w‖ ^ 2 ≤ ⟪prox γ R D v - prox γ R D w, v - w⟫ := by
  exact norm_sub_sq_le_inner_of_mem_subdifferential hγ ((eq_prox_iff hR hγ).1 rfl)
    ((eq_prox_iff hR hγ).1 rfl)

/-- **Nonexpansivity.**  The proximal operator is `1`-Lipschitz. -/
theorem lipschitzWith_prox [FiniteDimensional ℝ X] (hR : IsClosedConvexProper R D) (hγ : 0 < γ) :
    LipschitzWith 1 (prox γ R D) := by
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have h := (norm_prox_sub_prox_sq_le hR hγ v w).trans (real_inner_le_norm _ _)
  nlinarith [norm_nonneg (prox γ R D v - prox γ R D w), norm_nonneg (v - w)]

end Properties

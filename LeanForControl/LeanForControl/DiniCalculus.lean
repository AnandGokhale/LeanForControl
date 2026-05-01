import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.MetricSpace.Basic

-- The StackExchange proof relies heavily on the Intermediate Value Theorem
import Mathlib.Topology.Connected.Basic

lemma antitone_of_hasDerivWithinAt_Ici_nonpos {g : ℝ → ℝ}
    (hcont : Continuous g)
    (hderiv : ∀ x, ∃ d_g ≤ 0, HasDerivWithinAt g d_g (Set.Ici x) x) :
    Antitone g := by
  intro s t hst

  -- Handle the trivial case so we can assume strict inequality s < t
  obtain h_eq | h_lt := eq_or_lt_of_le hst
  · rw [h_eq]

  -- MSE Step 1: The Epsilon-Shift
  -- We shift to a strictly decreasing function to generate a contradiction.
  apply le_of_forall_pos_le_add
  intro ε hε_pos

  -- Setup the contradiction: suppose g(t) > g(s) + ε * (t - s)
  by_contra h_contra
  push Not at h_contra

  -- We define h(x) = g(x) - ε * x
  let h : ℝ → ℝ := fun x => g x - ε * x
  have h_cont : Continuous h := hcont.sub (continuous_id.const_smul ε)

  -- By our contradiction assumption, h(s) < h(t)
  have h_s_lt_t : h s < h t := by
    -- Use linarith to unpack h_contra into h(s) < h(t)
    linarith [h_contra, h_cont.continuousAt s, h_cont.continuousAt t]

  -- MSE Step 2: The Intermediate Value Theorem
  -- Since h(s) < h(t), pick a midpoint y.
  let y := (h s + h t) / 2
  have hy_gt : h s < y := by linarith
  have hy_lt : y < h t := by linarith

  -- MSE Step 3: The Supremum Set S
  -- S = { x ∈ [s, t] | h(x) < y }
  let S := { x ∈ Set.Icc s t | h x < y }

  have hs_in_S : s ∈ S := by
    simp only [Set.mem_setOf_eq, Set.mem_Icc, le_refl, true_and]
    exact ⟨hst, hy_gt⟩
  have hS_bdd : BddAbove S := ⟨t, fun x hx => hx.1.2⟩

  -- Let r be the supremum of S
  let r := sSup S

  -- MSE Step 4: Prove h(r) = y
  have hr_eq_y : h r = y := by
    -- Because h is continuous, S is bounded, and r is the supremum.
    -- (This uses continuous limits and the definition of sSup).
    sorry

  -- MSE Step 5: Bounding the Right-Derivative
  -- For any x ∈ (r, t], x is NOT in S (since r is the supremum).
  -- Therefore, h(x) ≥ y = h(r).
  have h_right_bound : ∀ x ∈ Set.Ioc r t, h r ≤ h x := by
    intro x hx
    -- Use the fact that x > r means x ∉ S.
    -- Since x ∈ [s, t], the only way it fails S is if h(x) ≥ y.
    sorry

  -- Because h(x) ≥ h(r) to the right of r, the right-derivative of h at r must be ≥ 0.
  -- Wait, we need to extract the derivative at r first:
  obtain ⟨d_g, hd_g_le_zero, h_deriv_r⟩ := hderiv r

  -- MSE Step 6: The Final Contradiction
  -- We know D+g(r) ≤ 0. Therefore, D+h(r) = D+g(r) - ε ≤ -ε < 0.
  have d_h_lt_zero : d_g - ε < 0 := by linarith

  -- But the limit of the difference quotient (h(x) - h(r))/(x - r) is ≥ 0
  -- because h(x) ≥ h(r) for x > r.
  -- We use Mathlib's limit theorems to show this contradicts d_g - ε < 0.
  sorry

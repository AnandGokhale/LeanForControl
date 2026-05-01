import LeanForControl.Dini.DiniDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.LiminfLimsup

/-!
# Monotonicity from the Sign of the Dini Derivative

## Main Results

* `diniDerivRight_nonpos_antitoneOn` : **Layer 1 (core lemma)**. If `f` is continuous on
  `[a, b]` and `D⁺ f t ≤ 0` for all `t ∈ [a, b)`, then `f` is antitone on `[a, b]`.

The proof follows the classical ε-trick:

1. Fix `ε > 0` and define `g(t) = f(t) + ε · t`.
2. Show `D⁺ g(t) > 0` for all `t ∈ [a, b)` (since `D⁺g = D⁺f + ε ≥ ε > 0`).
3. Prove that a continuous function with strictly positive Dini derivative on `[a, b)`
   must be nondecreasing: if not, there is a first time the function decreases, which
   contradicts the Dini condition at that point.
4. Let `ε → 0` to conclude `f` is antitone.

## References

* Amann, H., *Ordinary Differential Equations*, Ch. II §3.
* Khalil, H.K., *Nonlinear Systems*, Appendix A.
-/

open Filter Set Topology

/-! ### Step 1: Positive Dini implies nondecreasing -/

/-- **Auxiliary.** If `g` is continuous on `[a, b]` and `D⁺ g t > 0` for all
`t ∈ [a, b)`, then `g` is nondecreasing on `[a, b]`.

*Proof sketch:*
Suppose for contradiction that `g(x) > g(y)` for some `x < y` in `[a, b]`.
By continuity, the set `{t ∈ [x, y] | g(t) ≥ g(x)}` is closed and contains
`x`.
Let `c` be its supremum in `[x, y]`.
Then `c < y` and `g(c) = g(x) ≥ g(t)` for
all `t ∈ (c, y]`.
But `D⁺ g c > 0` means `g(c + h) > g(c)` for small enough `h > 0`,
contradicting the definition of `c`. -/
theorem monotoneOn_of_diniDerivRight_pos {g : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn g (Icc a b))
    (hdini : ∀ t ∈ Ico a b, 0 < D⁺ g t) :
    MonotoneOn g (Icc a b) := by
  intro x hx y hy hxy
  by_contra h
  push Not at h
  set S := {t ∈ Icc x y | g x ≤ g t} with hS_def
  have hxS : x ∈ S := by simp [hS_def, hxy]
  have hS_ne : S.Nonempty := ⟨x, hxS⟩
  have hS_bdd : BddAbove S := ⟨y, fun t ht => ht.1.2⟩

  set c := sSup S
  have hc_mem_Icc : c ∈ Icc x y := by
    refine ⟨le_csSup hS_bdd hxS, ?_⟩
    exact csSup_le hS_ne fun t ht => ht.1.2

  have hc_in_S : c ∈ S := by
    -- 1. Restrict the continuity of g from [a, b] to [x, y]
    have h_subset : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
    have h_cont_xy : ContinuousOn g (Icc x y) := hcont.mono h_subset

    -- 2. Prove S is closed
    have hS_closed : IsClosed S := by
      -- Express S as the intersection of the closed interval [x, y]
      -- and the preimage of the closed interval [g(x), ∞)
      have hS_eq : S = Icc x y ∩ g ⁻¹' (Ici (g x)) := by
        ext t
        simp only [hS_def, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
      rw [hS_eq]

      -- A continuous function on a closed set has a closed preimage for any closed set
      exact ContinuousOn.preimage_isClosed_of_isClosed h_cont_xy isClosed_Icc isClosed_Ici

    -- 3. Since S is closed, non-empty, and bounded above, it contains its supremum
    exact hS_closed.csSup_mem hS_ne hS_bdd
  -- t ∈ (c, y],
  have h_gt_notin_S : ∀ t ∈ Ioc c y, t ∉ S := by
    intro t ht htS
    have ht_le_c : t ≤ c := le_csSup hS_bdd htS
    linarith [ht.1, ht_le_c]

  -- g(t) < g(x)
  have hgt_lt_gx : ∀ t ∈ Ioc c y, g t < g x := by
    intro t ht
    have ht_notin := h_gt_notin_S t ht
    -- First, establish that t is within the overall interval [x, y]
    have h_t_Icc : t ∈ Icc x y := ⟨by linarith [hc_mem_Icc.1, ht.1], ht.2⟩
    -- Unfold S to see why t was rejected
    simp only [hS_def, Set.mem_setOf_eq, h_t_Icc, true_and, not_le] at ht_notin
    exact ht_notin

  -- g(x) ≤ g(c)
  have hgc: g x ≤ g c:= hc_in_S.2


  have hgt_lt_gc : ∀ t ∈ Ioc c y, g t < g c := by
    intro t ht
    have h1 : g t < g x := hgt_lt_gx t ht
    exact lt_of_lt_of_le h1 hgc

  have h_diff_quot_neg : ∀ t ∈ Ioc c y, (g t - g c) / (t - c) < 0 := by
    intro t ht
    have ht_lt_gc : g t < g c := hgt_lt_gc t ht
    have h_num : g t - g c < 0 := by linarith
    have h_den : 0 < t - c := by linarith [ht.1]
    exact div_neg_of_neg_of_pos h_num h_den

  have hc_lt_y : c < y := by
    -- We already know c ≤ y from hc_mem_Icc.2
    -- If c = y, then hgc gives g(x) ≤ g(y), which contradicts h: g(y) < g(x)
    have h_le : c ≤ y := hc_mem_Icc.2
    by_contra h_not_lt
    have hc_eq_y : c = y := le_antisymm h_le (not_lt.mp h_not_lt)
    rw [hc_eq_y] at hgc
    linarith

  have hc_Ico : c ∈ Ico a b := ⟨by linarith [hx.1, hc_mem_Icc.1], by linarith [hy.2, hc_lt_y]⟩
  have hdini_pos : 0 < D⁺ g c := hdini c hc_Ico

  have h_Ioc_mem : Ioc c y ∈ 𝓝[>] c := by
    have h_nhds : Iio y ∈ 𝓝 c := isOpen_Iio.mem_nhds hc_lt_y
    have h_nhds_within : Iio y ∈ 𝓝[>] c := mem_nhdsWithin_of_mem_nhds h_nhds
    have h_inter : Ioi c ∩ Iio y ∈ 𝓝[>] c := Filter.inter_mem self_mem_nhdsWithin h_nhds_within
    exact Filter.mem_of_superset h_inter fun t ht => ⟨ht.1, le_of_lt ht.2⟩

  have h_ev_not : ∀ᶠ h in 𝓝[>] (0 : ℝ), ¬(0 < (g (c + h) - g c) / h) := by
    rw [mem_nhdsWithin] at *
    have hmem : Ioo 0 (y - c) ∈ 𝓝[>] (0 : ℝ) := by
      rw [show Ioo (0 : ℝ) (y - c) = Ioi 0 ∩ Iio (y - c) from by
        ext; simp [Ioo, Ioi, Iio]]

      exact Filter.inter_mem
        self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds (sub_pos.mpr hc_lt_y)))
    filter_upwards [hmem] with h ⟨hh_pos, hh_lt⟩
    have ht : c + h ∈ Ioc c y := ⟨by linarith, by linarith⟩
    have h_neg := h_diff_quot_neg (c + h) ht
    simp only [add_sub_cancel_left] at h_neg
    linarith

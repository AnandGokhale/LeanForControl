import Mathlib.Topology.Order.OrderClosed
import Architect

/-!
# Order topology

Facts about neighbourhoods in a linearly ordered topological space that the library needs and
Mathlib does not state.

* `exists_Icc_mem_nhdsWithin` — a point of a set sits in a segment, with endpoints in the set,
  that is a neighbourhood of the point within the set.
-/

open Set Filter Topology

/-- **A point of a set sits in a segment that is a neighbourhood of it in the set.**  In a linear
order with an order-closed topology, for `t ∈ I` there are `a ≤ t ≤ b` in `I` with `[a, b]` a
neighbourhood of `t` within `I`: take `a < t` if `I` has a point left of `t` and `a = t` otherwise,
and likewise for `b`.  For an interval `I` of reals the segment lies in `I`, which is how
statements about solutions on segments reach intervals. -/
@[blueprint "lem:exists-Icc-mem-nhdsWithin"
  (title := "Segments that are neighbourhoods within a set")
  (latexEnv := "lemma")
  (statement := /-- Let $I$ be a subset of a linearly ordered space with an order-closed topology,
    for instance $\mathbb{R}$.  For $t \in I$ there are $a \le t \le b$ in $I$ such that
    $[a, b]$ is a neighbourhood of $t$ within $I$. -/)
  (proof := /-- If $I$ has a point $a < t$, every point of $I$ near $t$ is $\ge a$; otherwise
    every point of $I$ is $\ge t$, and take $a = t$.  Likewise on the right. -/)]
lemma exists_Icc_mem_nhdsWithin {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderClosedTopology α] {I : Set α} {t : α} (ht : t ∈ I) :
    ∃ a ∈ I, ∃ b ∈ I, t ∈ Icc a b ∧ Icc a b ∈ 𝓝[I] t := by
  obtain ⟨a, ha, hat, h_lower⟩ : ∃ a ∈ I, a ≤ t ∧ ∀ᶠ τ in 𝓝[I] t, a ≤ τ := by
    by_cases hL : ∃ a ∈ I, a < t
    · obtain ⟨a, ha, hlt⟩ := hL
      exact ⟨a, ha, hlt.le,
        ((eventually_gt_nhds hlt).filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le⟩
    · push Not at hL
      exact ⟨t, ht, le_rfl, eventually_nhdsWithin_of_forall hL⟩
  obtain ⟨b, hb, htb, h_upper⟩ : ∃ b ∈ I, t ≤ b ∧ ∀ᶠ τ in 𝓝[I] t, τ ≤ b := by
    by_cases hR : ∃ b ∈ I, t < b
    · obtain ⟨b, hb, hlt⟩ := hR
      exact ⟨b, hb, hlt.le,
        ((eventually_lt_nhds hlt).filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le⟩
    · push Not at hR
      exact ⟨t, ht, le_rfl, eventually_nhdsWithin_of_forall hR⟩
  exact ⟨a, ha, b, hb, ⟨hat, htb⟩, h_lower.and h_upper⟩

import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.Real.Lemmas

import Architect

/-!
# Limits superior

General facts about `Filter.limsup` of real-valued functions, with no differential-equation
content of their own. They are stated over an arbitrary filter rather than the
`𝓝[>] 0` of the Dini derivative, which is the only place they are currently used.

Real-valued `limsup` is an infimum of upper bounds, so it is only well-behaved where the
function is bounded; each result below carries the boundedness hypotheses it needs.
-/

open Filter

/-- Adding a null function does not change a `limsup`, provided the other summand is bounded
    both above and below. -/
@[blueprint "lem:limsup-add-tendsto-zero"
  (statement := /-- Let $l$ be a nontrivial filter, let $f$ be bounded above and below along
    $l$, and let $g \to 0$ along $l$.  Then
    $\limsup_{l}(f + g) = \limsup_{l} f$. -/)
  (proof := /-- One inequality is subadditivity of $\limsup$ together with
    $\limsup_{l} g = 0$.  For the other, write $f = (f + g) + (-g)$ and apply the same
    argument, $-g$ also tending to $0$; the boundedness of $f + g$ needed for this follows
    from that of $f$ and $g$ separately. -/)]
lemma limsup_add_tendsto_zero {ι : Type*} {f g : ι → ℝ} {l : Filter ι} [l.NeBot]
    (hbdd_below : IsBoundedUnder (· ≥ ·) l f)
    (hbdd_above : IsBoundedUnder (· ≤ ·) l f)
    (hg : Tendsto g l (nhds 0)) :
    limsup (f + g) l = limsup f l := by
  apply le_antisymm
  · have h1 : limsup (f + g) l ≤ limsup f l + limsup g l :=
      limsup_add_le hbdd_below hbdd_above hg.isCoboundedUnder_le hg.isBoundedUnder_le
    rwa [hg.limsup_eq, add_zero] at h1
  · have hneg : Tendsto (fun i => -g i) l (nhds 0) := by simpa using hg.neg
    have hrw : f = fun i => (f i + g i) + (-g i) := by ext i; ring
    have hfg_bdd_below : IsBoundedUnder (· ≥ ·) l (f + g) := by
      obtain ⟨bf, hbf⟩ := hbdd_below
      obtain ⟨bg, hbg⟩ := hg.isBoundedUnder_ge
      refine ⟨bf + bg, ?_⟩
      simp only [Filter.eventually_map] at *
      filter_upwards [hbf, hbg] with i h1 h2
      simp [ge_iff_le] at *
      linarith
    have hfg_bdd_above : IsBoundedUnder (· ≤ ·) l (f + g) := by
      obtain ⟨bf, hbf⟩ := hbdd_above
      obtain ⟨bg, hbg⟩ := hg.isBoundedUnder_le
      refine ⟨bf + bg, ?_⟩
      simp only [Filter.eventually_map] at *
      filter_upwards [hbf, hbg] with i h1 h2
      simp only [Pi.add_apply]
      linarith
    have h2 : limsup (fun i => (f i + g i) + (-g i)) l ≤
              limsup (f + g) l + limsup (fun i => -g i) l :=
      limsup_add_le
        hfg_bdd_below
        hfg_bdd_above
        hneg.isCoboundedUnder_le
        hneg.isBoundedUnder_le
    rw [hneg.limsup_eq, add_zero] at h2
    rwa [← hrw] at h2

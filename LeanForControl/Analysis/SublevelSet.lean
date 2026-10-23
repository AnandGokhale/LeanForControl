import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Order.Filter.AtTopBot.Basic
import Architect

/-!
# Sublevel sets of radially unbounded functions

A continuous function on a proper normed space that tends to `∞` as `‖x‖ → ∞` has compact
sublevel sets `{x | V x ≤ c}`.  Theorems that need compact sublevel sets take them as a
hypothesis; this lemma supplies it from radial unboundedness.
-/

open Set Filter

/-- **Sublevel sets of a radially unbounded function are compact.** -/
@[blueprint "lem:isCompact-sublevel-set"
  (title := "Sublevel sets of a radially unbounded function are compact")
  (latexEnv := "lemma")
  (statement := /-- Let $E$ be a proper normed space.  If $V : E \to \mathbb{R}$ is continuous
    and radially unbounded ($V(x) \to \infty$ as $\|x\| \to \infty$), then every sublevel set
    $\{x \mid V(x) \le c\}$ is compact. -/)
  (proof := /-- Closed: it is $V^{-1}((-\infty, c])$, with $V$ continuous.  Bounded: radial
    unboundedness gives a compact $K$ off which $V > c$, so the sublevel set lies in $K$.
    Compact: closed and bounded in a proper space. -/)]
lemma isCompact_sublevel_set {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {V : E → ℝ}
    (hcont : Continuous V) (hradial : Tendsto V (comap norm atTop) atTop) (c : ℝ) :
    IsCompact {x | V x ≤ c} := by
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_Iic.preimage hcont)
  rw [comap_norm_atTop, Metric.cobounded_eq_cocompact] at hradial
  obtain ⟨K, hK_compact, hK⟩ := mem_cocompact.mp (hradial (eventually_gt_atTop c))
  exact hK_compact.isBounded.subset fun x (hx : V x ≤ c) =>
    by_contra fun hxK => (hK hxK).not_ge hx

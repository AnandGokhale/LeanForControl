import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue
import Architect

open MeasureTheory intervalIntegral Real Set Filter

/-- If a continuous function starts ≤ 0 and ends > 0, it has a last root `a` in `[t₀, t₁)`,
    after which it is strictly positive on `(a, t₁]`. -/
@[blueprint "lem:exists-greatest-zero-of-nonpos-of-pos"
  (title := "Greatest zero of a sign-changing continuous function")
  (latexEnv := "lemma")
  (statement := /-- Let $g$ be continuous on $[t_0, t_1]$ with $g(t_0) \le 0 < g(t_1)$. Then $g$
    has a \emph{last} root: there is $a \in [t_0, t_1)$ with $g(a) = 0$ and $g(t) > 0$ for every
    $t \in (a, t_1]$.-/)]
lemma ContinuousOn.exists_greatest_zero_of_nonpos_of_pos {g : ℝ → ℝ} {t₀ t₁ : ℝ}
    (hg_cont : ContinuousOn g (Icc t₀ t₁))
    (ht : t₀ < t₁) (hg_start : g t₀ ≤ 0) (hg_end : 0 < g t₁) :
    ∃ a ∈ Ico t₀ t₁, g a = 0 ∧ ∀ t ∈ Ioc a t₁, 0 < g t := by
  haveI : CompactSpace ↥(Icc t₀ t₁) := isCompact_iff_compactSpace.mp isCompact_Icc
  let f : Icc t₀ t₁ → ℝ := fun x => g x.val
  have h_pre_closed : IsClosed (f ⁻¹' {0}) := isClosed_singleton.preimage hg_cont.restrict
  -- 2. Prove the preimage is nonempty via IVT
  obtain ⟨c, hc_mem, hc_eq⟩ := intermediate_value_Icc ht.le hg_cont ⟨hg_start, hg_end.le⟩
  have h_pre_nonempty : (f ⁻¹' {0}).Nonempty := ⟨⟨c, hc_mem⟩, hc_eq⟩
  -- 3. A closed subset of a compact space is compact, so it attains its maximum!
  -- This completely replaces `sSup`, `BddAbove`, and the `Subtype.val ''` mapping.
  obtain ⟨m, hm_mem, hm_max⟩ :=
    h_pre_closed.isCompact.exists_isMaxOn h_pre_nonempty continuous_subtype_val.continuousOn
  let a := m.val
  use a
  have ha_mem_Icc : a ∈ Icc t₀ t₁ := m.property
  have ha_eq_zero : g a = 0 := hm_mem
  -- 4. Prove `a < t₁`
  have ha_lt_t1 : a < t₁ := by
    by_contra h_not
    have ha_eq_t1 : a = t₁ := le_antisymm ha_mem_Icc.2 (not_lt.mp h_not)
    rw [ha_eq_t1] at ha_eq_zero
    linarith
  refine ⟨⟨ha_mem_Icc.1, ha_lt_t1⟩, ha_eq_zero, ?_⟩
  -- 5. Strict positivity on (a, t₁] via IVT contradiction
  intro t ht_mem
  by_contra h_not
  push Not at h_not
  have h_cont_sub : ContinuousOn g (Icc t t₁) :=
    hg_cont.mono (Icc_subset_Icc (ha_mem_Icc.1.trans ht_mem.1.le) le_rfl)
  obtain ⟨r, hr_mem, hr_eq⟩ := intermediate_value_Icc ht_mem.2 h_cont_sub ⟨h_not, hg_end.le⟩
  -- Package `r` back into our subtype to contradict the maximum `m`
  let r_sub : Icc t₀ t₁ := ⟨r, ⟨ha_mem_Icc.1.trans (ht_mem.1.le.trans hr_mem.1), hr_mem.2⟩⟩
  have hr_in_pre : r_sub ∈ f ⁻¹' {0} := hr_eq
  -- By the definition of `exists_isMaxOn`, `m` is an upper bound for the set.
  have h_contra : a < a := ht_mem.1.trans_le (hr_mem.1.trans (hm_max hr_in_pre))
  linarith

/-- A continuous curve on `[t₀, t₁]`, `t₀ ≤ t₁`, which starts in an open set `D`
and ends outside `D` meets its topological boundary at some time in that interval.
Here `frontier D` is Mathlib's name for `∂D = closure D \ interior D`.
This lemma asserts a boundary hit, without selecting the first one. -/
@[blueprint "lem:exists-boundary-hit-on-continuous-segment"
  (title := "Boundary crossing by a continuous curve") (latexEnv := "lemma")
  (statement := /-- A continuous curve on $[t_0,t_1]$, with $t_0\le t_1$, starting
    in an open set $D$ and ending outside $D$ meets $\partial D$ on that interval. -/)
  (proof := /-- The image of the interval is connected. If it avoided the boundary,
    meeting $D$ would force the whole image to lie in $D$. -/)]
theorem exists_boundary_hit_on_continuous_segment
    {E : Type*} [TopologicalSpace E]
    {D : Set E} (hD : IsOpen D) {φ : ℝ → E} {t₀ t₁ : ℝ}
    (hφ : ContinuousOn φ (Icc t₀ t₁))
    (hstart : φ t₀ ∈ D) (hend : φ t₁ ∉ D) (ht : t₀ ≤ t₁) :
    ∃ t ∈ Icc t₀ t₁, φ t ∈ frontier D := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  let curveImage : Set E := φ '' Icc t₀ t₁
  have hconnected : IsPreconnected curveImage := isPreconnected_Icc.image φ hφ
  have hmeets_region : (curveImage ∩ D).Nonempty :=
    ⟨φ t₀, ⟨t₀, left_mem_Icc.mpr ht, rfl⟩, hstart⟩
  -- Without a boundary hit, every image point in the closure is already in D.
  have hclosure_inter_image : closure D ∩ curveImage ⊆ D := by
    intro x hx
    have hxnot : x ∉ frontier D := by
      rintro hxf
      obtain ⟨t, htI, rfl⟩ := hx.2
      exact hno t htI hxf
    rw [frontier, mem_diff] at hxnot
    simp only [not_and, not_not] at hxnot
    exact interior_subset (hxnot hx.1)
  have himage_in_region : curveImage ⊆ D :=
    hconnected.subset_of_closure_inter_subset hD hmeets_region hclosure_inter_image
  exact hend (himage_in_region ⟨t₁, right_mem_Icc.mpr ht, rfl⟩)

/-- If a continuous curve on `[t₀, T]` starts in an open set `D` and is outside it
at `t₁ ∈ [t₀, T]`, there is a first exit time `τ ∈ [t₀, t₁]`: the curve lies
in `D` on `[t₀, τ)` and on its topological boundary `∂D` at `τ`.
-/
@[blueprint "lem:exists-first-boundary-hit-of-exit"
  (title := "First exit from an open set") (latexEnv := "lemma")
  (statement := /-- If a continuous curve on $[t_0,T]$ starts in an open set $D$
    and is outside $D$ at $t_1\in[t_0,T]$, some $\tau\in[t_0,t_1]$ satisfies
    $\varphi(\tau)\in\partial D$ and $\varphi(t)\in D$ for $t\in[t_0,\tau)$. -/)
  (proof := /-- The nonempty compact set of exit times has a minimum. A boundary
    crossing by that time must occur at the minimum itself. -/)]
theorem exists_first_boundary_hit_of_exit
    {E : Type*} [TopologicalSpace E]
    {D : Set E} (hD : IsOpen D) {φ : ℝ → E} {t₀ T t₁ : ℝ}
    (hφ : ContinuousOn φ (Icc t₀ T))
    (hstart : φ t₀ ∈ D) (ht₁ : t₁ ∈ Icc t₀ T) (hend : φ t₁ ∉ D) :
    ∃ τ ∈ Icc t₀ t₁, φ τ ∈ frontier D ∧
      ∀ s ∈ Ico t₀ τ, φ s ∈ D := by
  -- The exit times form a nonempty compact set, so there is an earliest exit.
  let exitTimes : Set ℝ := Icc t₀ t₁ ∩ φ ⁻¹' Dᶜ
  have hφ_restrict : ContinuousOn φ (Icc t₀ t₁) :=
    hφ.mono (Icc_subset_Icc_right ht₁.2)
  have hexit_closed : IsClosed exitTimes :=
    hφ_restrict.preimage_isClosed_of_isClosed isClosed_Icc hD.isClosed_compl
  have hexit_compact : IsCompact exitTimes :=
    isCompact_Icc.of_isClosed_subset hexit_closed inter_subset_left
  have hexit_nonempty : exitTimes.Nonempty := ⟨t₁, ⟨⟨ht₁.1, le_rfl⟩, hend⟩⟩
  obtain ⟨τ, hτ_exit, hτ_first⟩ := hexit_compact.exists_isMinOn hexit_nonempty continuousOn_id
  have hτI : τ ∈ Icc t₀ t₁ := hτ_exit.1
  have hτout : φ τ ∉ D := hτ_exit.2
  have hstay : ∀ s ∈ Ico t₀ τ, φ s ∈ D := by
    intro s hs
    by_contra hsout
    have hs_exit : s ∈ exitTimes := ⟨⟨hs.1, hs.2.le.trans hτI.2⟩, hsout⟩
    exact (not_le_of_gt hs.2) (hτ_first hs_exit)
  -- A boundary hit occurs by τ; minimality forces it to be exactly τ.
  obtain ⟨q, hqI, hqfront⟩ :=
    exists_boundary_hit_on_continuous_segment hD
      (hφ_restrict.mono (Icc_subset_Icc_right hτI.2)) hstart hτout hτI.1
  have hqout : φ q ∉ D := by
    intro hqD
    have hdj : Disjoint D (frontier D) :=
      Set.disjoint_iff_inter_eq_empty.mpr hD.inter_frontier_eq
    exact Set.disjoint_left.1 hdj hqD hqfront
  have hq_exit : q ∈ exitTimes := ⟨⟨hqI.1, hqI.2.trans hτI.2⟩, hqout⟩
  have heq : q = τ := le_antisymm hqI.2 (hτ_first hq_exit)
  exact ⟨τ, hτI, heq ▸ hqfront, hstay⟩

/-- A continuous curve that starts inside the ball of radius `ρ` and later leaves it first meets
the sphere at some `τ`, staying in the closed ball until then. -/
@[blueprint "thm:exists-first-sphere-hit"
  (title := "First crossing of a sphere")
  (statement := /-- Let $\varphi$ be continuous on $[t_0, T]$ with
    $\|\varphi(t_0) - x_{\mathrm{eq}}\| < \rho$, and suppose some $t_1 \in [t_0, T]$ satisfies
    $\rho \le \|\varphi(t_1) - x_{\mathrm{eq}}\|$. Then there is a \emph{first} hitting time
    $\tau \in [t_0, T]$ of the sphere of radius $\rho$:
    \[
      \|\varphi(\tau) - x_{\mathrm{eq}}\| = \rho, \qquad
      \|\varphi(s) - x_{\mathrm{eq}}\| \le \rho \quad \forall\, s \in [t_0, \tau].
    \] -/)
  (proof := /-- Apply \cref{lem:exists-first-boundary-hit-of-exit} to the open ball.
    Its boundary lies in the sphere; before the first exit the curve remains in the ball. -/)]
theorem exists_first_sphere_hit
    {E : Type*} [NormedAddCommGroup E]
    {x_eq : E} {φ : ℝ → E} {ρ t₀ T t₁ : ℝ}
    (hφ : ContinuousOn φ (Icc t₀ T))
    (h₀ : ‖φ t₀ - x_eq‖ < ρ) (ht₁ : t₁ ∈ Icc t₀ T)
    (hfar : ρ ≤ ‖φ t₁ - x_eq‖) :
    ∃ τ ∈ Icc t₀ T, ‖φ τ - x_eq‖ = ρ ∧
      ∀ s ∈ Icc t₀ τ, ‖φ s - x_eq‖ ≤ ρ := by
  have hstart : φ t₀ ∈ Metric.ball x_eq ρ := by
    simpa [Metric.mem_ball, dist_eq_norm] using h₀
  have hend : φ t₁ ∉ Metric.ball x_eq ρ := by
    simpa [Metric.mem_ball, dist_eq_norm, not_lt] using hfar
  obtain ⟨τ, hτ, hboundary, hstay⟩ :=
    exists_first_boundary_hit_of_exit Metric.isOpen_ball hφ hstart ht₁ hend
  have hτeq : ‖φ τ - x_eq‖ = ρ := by
    simpa [Metric.mem_sphere, dist_eq_norm] using
      Metric.frontier_ball_subset_sphere hboundary
  refine ⟨τ, ⟨hτ.1, hτ.2.trans ht₁.2⟩, hτeq, ?_⟩
  intro t ht
  by_cases hhit : t = τ
  · simpa [hhit] using hτeq.le
  · have hbefore : t ∈ Ico t₀ τ := ⟨ht.1, ht.2.lt_of_ne hhit⟩
    exact (show ‖φ t - x_eq‖ < ρ by
      simpa [Metric.mem_ball, dist_eq_norm] using hstay t hbefore).le

/-- **Cutting off a field that is Lipschitz on a set.**  If `g` is `L`-Lipschitz and bounded by `B`
on `S`, and `χ` is `M`-Lipschitz with `|χ| ≤ 1` and vanishes off `S`, then `χ • g` is
`(L + M B)`-Lipschitz everywhere. -/
@[blueprint "lem:lipschitzWith-smul-of-lipschitzOnWith"
  (title := "Cutting off a field that is Lipschitz on a set")
  (latexEnv := "lemma")
  (statement := /-- Let $g$ be $L$-Lipschitz and bounded by $B$ on $S$, and let $\chi$ be
    $M$-Lipschitz with $|\chi| \le 1$, vanishing off $S$.  Then $\chi g$ is
    $(L + MB)$-Lipschitz on the whole space. -/)]
theorem lipschitzWith_smul_of_lipschitzOnWith {α F : Type*} [PseudoMetricSpace α]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {χ : α → ℝ} {g : α → F} {S : Set α} {M L B : NNReal}
    (hχ : LipschitzWith M χ) (hχ_le : ∀ y, |χ y| ≤ 1) (hχ_zero : ∀ y ∉ S, χ y = 0)
    (hg : LipschitzOnWith L g S) (hg_le : ∀ y ∈ S, ‖g y‖ ≤ B) :
    LipschitzWith (L + M * B) fun y => χ y • g y := by
  -- Away from `S`, `χ • g` is `0`, and next to a point of `S` it moves only through `χ`.
  have h_one : ∀ y z, y ∈ S → z ∉ S → ‖χ y • g y‖ ≤ (L + M * B) * dist y z := fun y z hy hz =>
    calc ‖χ y • g y‖
        = |χ y - χ z| * ‖g y‖ := by rw [hχ_zero z hz, sub_zero, norm_smul, Real.norm_eq_abs]
      _ ≤ (M * dist y z) * B := by
          gcongr
          · exact (Real.dist_eq _ _).symm.le.trans (hχ.dist_le_mul y z)
          · exact hg_le y hy
      _ ≤ (L + M * B) * dist y z := by nlinarith [dist_nonneg (x := y) (y := z), L.coe_nonneg]
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [dist_eq_norm]
  by_cases hy : y ∈ S <;> by_cases hz : z ∈ S
  · calc ‖χ y • g y - χ z • g z‖
        = ‖χ y • (g y - g z) + (χ y - χ z) • g z‖ := by rw [smul_sub, sub_smul]; abel_nf
      _ ≤ |χ y| * ‖g y - g z‖ + |χ y - χ z| * ‖g z‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 * (L * dist y z) + (M * dist y z) * B := by
          gcongr
          · exact hχ_le y
          · rw [← dist_eq_norm]; exact hg.dist_le_mul y hy z hz
          · exact (Real.dist_eq _ _).symm.le.trans (hχ.dist_le_mul y z)
          · exact hg_le z hz
      _ = (L + M * B) * dist y z := by ring
  · rw [hχ_zero z hz, zero_smul, sub_zero]
    exact h_one y z hy hz
  · rw [hχ_zero y hy, zero_smul, zero_sub, norm_neg, dist_comm]
    exact h_one z y hz hy
  · simp only [hχ_zero y hy, hχ_zero z hz, zero_smul, sub_zero, norm_zero]
    positivity

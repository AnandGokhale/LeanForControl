import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue
import Architect

open MeasureTheory intervalIntegral Real Set Filter

/-- If a continuous function starts ≤ 0 and ends > 0, it has a last root `a` in `[t₀, t₁)`,
    after which it is strictly positive on `(a, t₁]`. -/
@[blueprint "lem:exists-greatest-zero-of-nonpos-of-pos"
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

/-- A continuous curve that starts inside the ball of radius `ρ` and later leaves it first meets
the sphere at some `τ`, staying in the closed ball until then. -/
@[blueprint "thm:exists-first-sphere-hit"
  (statement := /-- Let $\varphi$ be continuous on $[t_0, T]$ with
    $\|\varphi(t_0) - x_{\mathrm{eq}}\| < \rho$, and suppose some $t_1 \in [t_0, T]$ satisfies
    $\rho \le \|\varphi(t_1) - x_{\mathrm{eq}}\|$. Then there is a \emph{first} hitting time
    $\tau \in [t_0, T]$ of the sphere of radius $\rho$:
    \[
      \|\varphi(\tau) - x_{\mathrm{eq}}\| = \rho, \qquad
      \|\varphi(s) - x_{\mathrm{eq}}\| \le \rho \quad \forall\, s \in [t_0, \tau].
    \] -/)]
theorem exists_first_sphere_hit
    {E : Type*} [NormedAddCommGroup E]
    {x_eq : E} {φ : ℝ → E} {ρ t₀ T t₁ : ℝ}
    (hφ : ContinuousOn φ (Icc t₀ T))
    (h₀ : ‖φ t₀ - x_eq‖ < ρ) (ht₁ : t₁ ∈ Icc t₀ T)
    (hfar : ρ ≤ ‖φ t₁ - x_eq‖) :
    ∃ τ ∈ Icc t₀ T, ‖φ τ - x_eq‖ = ρ ∧
      ∀ s ∈ Icc t₀ τ, ‖φ s - x_eq‖ ≤ ρ := by
  /-- Take the minimum of the closed set $[t_0, T] \cap \|\varphi(\cdot) - x_{\mathrm{eq}}\|^{-1}
  \{\rho\}$, which is nonempty by the intermediate value theorem. Minimality rules out an earlier
  excursion outside the ball: one would force a second crossing before $\tau$, again by the
  intermediate value theorem. -/
  let d : ℝ → ℝ := fun t ↦ ‖φ t - x_eq‖
  have hd : ContinuousOn d (Icc t₀ T) :=
    continuous_norm.comp_continuousOn (hφ.sub continuousOn_const)
  have hd₁ : ContinuousOn d (Icc t₀ t₁) := hd.mono (Icc_subset_Icc_right ht₁.2)
  have hhit : ∃ s ∈ Icc t₀ T, d s = ρ := by
    have hρmem : ρ ∈ Icc (d t₀) (d t₁) := ⟨h₀.le, hfar⟩
    obtain ⟨s, hs, hsρ⟩ := (intermediate_value_Icc ht₁.1 hd₁) hρmem
    exact ⟨s, ⟨hs.1, hs.2.trans ht₁.2⟩, hsρ⟩
  let S : Set ℝ := Icc t₀ T ∩ d ⁻¹' {ρ}
  have hS_closed : IsClosed S :=
    hd.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hS_compact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hS_closed inter_subset_left
  have hS_nonempty : S.Nonempty := by
    obtain ⟨s, hs, hsρ⟩ := hhit
    exact ⟨s, hs, hsρ⟩
  obtain ⟨τ, hτS, hτmin⟩ := hS_compact.exists_isMinOn hS_nonempty continuousOn_id
  have hτIcc : τ ∈ Icc t₀ T := hτS.1
  have hτeq : d τ = ρ := hτS.2
  refine ⟨τ, hτIcc, hτeq, ?_⟩
  intro s hs
  by_contra hnot
  have hρs : ρ < d s := lt_of_not_ge hnot
  have hslt : s < τ :=
    hs.2.lt_of_ne (fun h ↦ by subst s; exact (ne_of_lt hρs) hτeq.symm)
  have hds : ContinuousOn d (Icc t₀ s) := by
    apply hd.mono
    intro q hq
    exact ⟨hq.1, hq.2.trans (hs.2.trans hτIcc.2)⟩
  have hρmem : ρ ∈ Icc (d t₀) (d s) := ⟨h₀.le, hρs.le⟩
  obtain ⟨q, hq, hqρ⟩ := (intermediate_value_Icc hs.1 hds) hρmem
  have hqS : q ∈ S := ⟨⟨hq.1, hq.2.trans (hs.2.trans hτIcc.2)⟩, hqρ⟩
  have hτq : τ ≤ q := hτmin hqS
  exact (not_lt_of_ge (hτq.trans hq.2)) hslt


import LeanForControl.Stability.classK
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Basic


/-! ## Lemma 4.4 — KL bound for ẏ = -α(y)

Reference: Khalil, Nonlinear Systems, Lemma 4.4 / Appendix C.6.
-/

open Set Filter Topology MeasureTheory intervalIntegral Classical

/-! ### The η function -/




/-!
## Osgood Construction (Class K to Class KL)

Given a Class K function α, we can construct an associated Class KL function σ
via the flow of ẏ = -α(y). This requires evaluating the integral η(y) = -∫ 1/α(x) dx
and inverting it: σ(r, s) = η⁻¹(η(r) + s).
-/

section OsgoodConstruction

variable {a b : ℝ}

/-- η_base(y) = −∫_{base}^y 1/α(x) dx. The time-to-go function. -/
noncomputable def ClassK.eta (α : ClassK a b) (base y : ℝ) : ℝ :=
  -∫ x in base..y, (1 / α.toFun x)



/-- The Osgood condition: η(y) → +∞ as y → 0⁺.
    This guarantees the system reaches the origin only in infinite time. -/
def ClassK.EtaDiverges (α : ClassK a b) (base : ℝ) : Prop :=
  Filter.Tendsto (α.eta base) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop

/-- The mathematical inverse of η.
    Because η is only well-behaved on (0, a), this function will return
    junk values outside the range of η. -/
-- noncomputable def ClassK.etaInv (α : ClassK a b) (base : ℝ) : ℝ → ℝ :=
--   Function.invFun (α.eta base)
noncomputable def ClassK.etaInv (α : ClassK a b) (base : ℝ) : ℝ → ℝ :=
  fun t => if h : ∃ r ∈ Set.Ioo 0 a, α.eta base r = t
           then Classical.choose h
           else 0

/-- The piece-wise definition of the Class KL candidate.
    We isolate r = 0 to avoid evaluating η(0), which hits a singularity. -/
noncomputable def ClassK.sigma (α : ClassK a b) (base r s : ℝ) : ℝ :=
  if r = 0 then 0 else α.etaInv base (α.eta base r + s)



-- η'(y) = -1/α(y), via FTC
-- FTC (right endpoint form) requires: the integrand is interval-integrable on [base,y],
-- and strongly measurable in a neighbourhood of y. Both follow from continuity on Ioo 0 a.
lemma eta_hasDerivAt (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Ioo 0 a) (hcont_inv : ContinuousOn (fun x => 1 / α.toFun x) (Ioo 0 a))
    {y : ℝ} (hy : y ∈ Ioo 0 a) :
    HasDerivAt (α.eta base) (-1 / α.toFun y) y := by
    have hf_cont : ContinuousAt (fun x => 1 / α.toFun x) y :=
      hcont_inv.continuousAt (Ioo_mem_nhds hy.1 hy.2)
    have hf_intble : IntervalIntegrable (fun x => 1 / α.toFun x) volume base y := by
      apply (hcont_inv.mono _).intervalIntegrable
      intro x hx
      -- hx : x ∈ uIcc base y = Icc (min base y) (max base y)
      -- so hx.1 : min base y ≤ x,  hx.2 : x ≤ max base y
      exact ⟨lt_of_lt_of_le (lt_min hbase.1 hy.1) hx.1,
            lt_of_le_of_lt hx.2 (max_lt hbase.2 hy.2)⟩
    have hmeas : StronglyMeasurableAtFilter (fun x => 1 / α.toFun x) (𝓝 y) volume :=
      ⟨Ioo 0 a, Ioo_mem_nhds hy.1 hy.2, hcont_inv.aestronglyMeasurable measurableSet_Ioo⟩
    -- FTC: d/dy ∫_base^y f = f(y)
    have hderiv : HasDerivAt (fun u => ∫ x in base..u, 1 / α.toFun x) (1 / α.toFun y) y :=
      integral_hasDerivAt_right hf_intble hmeas hf_cont
    change HasDerivAt (fun u => -(∫ x in base..u, 1 / α.toFun x)) (-1 / α.toFun y) y
    have := hderiv.neg
    simp only at this
    convert this using 1
    ring


-- η is strictly decreasing: α > 0 makes η' = -1/α < 0 everywhere on (0, a).
lemma eta_strictAntiOn (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Ioo 0 a)
    (hpos : ∀ x ∈ Ioo 0 a, 0 < α.toFun x)
    (hcont_inv : ContinuousOn (fun x => 1 / α.toFun x) (Ioo 0 a)) :
    StrictAntiOn (α.eta base) (Ioo 0 a) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo 0 a)
    · -- ContinuousOn: each point has a HasDerivAt, hence is continuous
      exact fun y hy =>
        (eta_hasDerivAt α base hbase hcont_inv hy).continuousAt.continuousWithinAt
    · -- deriv < 0 on the interior (= Ioo 0 a itself)
      intro x hx
      rw [interior_Ioo] at hx
      rw [(eta_hasDerivAt α base hbase hcont_inv hx).deriv]
      exact div_neg_of_neg_of_pos (by norm_num) (hpos x hx)


lemma eta_continuousOn (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Ioo 0 a)
    (hcont_inv : ContinuousOn (fun x => 1 / α.toFun x) (Ioo 0 a)) :
    ContinuousOn (α.eta base) (Ioo 0 a) := fun _ hy =>
    (eta_hasDerivAt α base hbase hcont_inv hy).continuousAt.continuousWithinAt



-- Existence of the shifted preimage: η(r) + s lies in the range of η on (0, a).
-- Strategy: EtaDiverges gives a small ε near 0 where η(ε) ≥ η(r)+s (upper bound).
-- η(r) ≤ η(r)+s (lower bound since s ≥ 0). IVT on [ε, r] produces the witness r'.
lemma eta_add_mem_range (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Ioo 0 a)
    (hdiv : α.EtaDiverges base)
    (hcont_inv : ContinuousOn (fun x => 1 / α.toFun x) (Ioo 0 a))
    {r : ℝ} (hr : r ∈ Ioo 0 a) {s : ℝ} (hs : 0 ≤ s) :
    ∃ r' ∈ Ioo 0 a, α.eta base r' = α.eta base r + s:= by
    have hev : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), α.eta base r + s ≤ α.eta base x :=
    hdiv.eventually (Filter.eventually_ge_atTop _)
    have hIoo_nhd : Set.Ioo 0 r ∈ nhdsWithin 0 (Set.Ioi 0) := by
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio r, isOpen_Iio, hr.1, fun x ⟨hlt, hgt⟩ => ⟨hgt, hlt⟩⟩
    obtain ⟨ε, hε_large, hε_ioo⟩ :=
    (hev.and (Filter.eventually_of_mem hIoo_nhd (fun x hx => hx))).exists
    have hcont_Icc : ContinuousOn (α.eta base) (Set.Icc ε r) :=
    (eta_continuousOn α base hbase hcont_inv).mono
      (fun x hx => ⟨lt_of_lt_of_le hε_ioo.1 hx.1, lt_of_le_of_lt hx.2 hr.2⟩)
    obtain ⟨r', hr'_icc, hr'_eq⟩ :=
    intermediate_value_Icc' (le_of_lt hε_ioo.2) hcont_Icc
      ⟨le_add_of_nonneg_right hs, hε_large⟩
    exact ⟨r', ⟨lt_of_lt_of_le hε_ioo.1 hr'_icc.1, lt_of_le_of_lt hr'_icc.2 hr.2⟩, hr'_eq⟩



lemma etaInv_mem_Ioo (α : ClassK a b) (base : ℝ)
    {t : ℝ} (ht : ∃ r ∈ Ioo 0 a, α.eta base r = t) :
    α.etaInv base t ∈ Ioo 0 a := by
  simp only [ClassK.etaInv, dif_pos ht]
  exact (Classical.choose_spec ht).1

lemma eta_etaInv (α : ClassK a b) (base : ℝ)
    {t : ℝ} (ht : ∃ r ∈ Set.Ioo 0 a, α.eta base r = t) :
    α.eta base (α.etaInv base t) = t := by
  simp only [ClassK.etaInv, dif_pos ht]
  exact (Classical.choose_spec ht).2

-- η⁻¹ inherits strict anti-monotonicity from η by contrapositive:
-- if η⁻¹(t₂) ≥ η⁻¹(t₁) then η(η⁻¹(t₂)) ≤ η(η⁻¹(t₁)), i.e. t₂ ≤ t₁, contradiction.
lemma etaInv_strictAntiOn (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a)
    (hpos : ∀ x ∈ Set.Ioo 0 a, 0 < α.toFun x)
    (hcont_inv : ContinuousOn (fun x => 1 / α.toFun x) (Set.Ioo 0 a))
    {t₁ t₂ : ℝ}
    (ht₁ : ∃ r ∈ Set.Ioo 0 a, α.eta base r = t₁)
    (ht₂ : ∃ r ∈ Set.Ioo 0 a, α.eta base r = t₂)
    (hlt : t₁ < t₂) :
    α.etaInv base t₂ < α.etaInv base t₁ := by
  have h₁ := etaInv_mem_Ioo α base ht₁
  have h₂ := etaInv_mem_Ioo α base ht₂
  have heq₁ := eta_etaInv α base ht₁
  have heq₂ := eta_etaInv α base ht₂
  rcases lt_or_ge (α.etaInv base t₂) (α.etaInv base t₁) with h | h
  · exact h
  · exfalso
    rcases eq_or_lt_of_le h with h_eq | hlt'
    · -- etaInv t₁ = etaInv t₂  →  t₁ = t₂
      have := congr_arg (α.eta base) h_eq
      rw [heq₁, heq₂] at this
      linarith
    · -- etaInv t₁ < etaInv t₂  →  t₂ < t₁
      have := eta_strictAntiOn α base hbase hpos hcont_inv h₁ h₂ hlt'
      rw [heq₁, heq₂] at this
      linarith


-- η⁻¹(t) → 0 as t → +∞: large t forces the preimage into (0, δ) for any δ > 0,
-- because η is strictly decreasing and η(δ) is a finite threshold above which
-- η⁻¹(t) ≤ δ by anti-monotonicity.
lemma etaInv_tendsto_zero (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a)
    (hpos : ∀ x ∈ Set.Ioo 0 a, 0 < α.toFun x)
    (hcont_inv : ContinuousOn (fun x => 1 / α.toFun x) (Set.Ioo 0 a)) :
    Filter.Tendsto (α.etaInv base) Filter.atTop (nhds 0) := by
  apply tendsto_order.mpr
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- b < 0: etaInv t ≥ 0 always, so b < etaInv t
    rw [Filter.eventually_atTop]
    refine ⟨0, fun t _ => ?_⟩
    rcases Classical.em (∃ r ∈ Set.Ioo 0 a, α.eta base r = t) with hrange | hrange
    · linarith [(etaInv_mem_Ioo α base hrange).1]
    · simp only [ClassK.etaInv, dif_neg hrange]; linarith
  · -- b > 0: use threshold M = η(δ) where δ = min(b/2, a/2)
    set δ := min (b / 2) (a / 2)
    have hδ_pos  : 0 < δ := lt_min (by linarith) (by linarith [α.ha])
    have hδ_lt_a : δ < a := lt_of_le_of_lt (min_le_right _ _) (by linarith [α.ha])
    have hδ_lt_b : δ < b := lt_of_le_of_lt (min_le_left  _ _) (by linarith)
    have hδ_ioo  : δ ∈ Set.Ioo 0 a := ⟨hδ_pos, hδ_lt_a⟩
    filter_upwards [Filter.eventually_ge_atTop (α.eta base δ)] with t ht
    rcases Classical.em (∃ r ∈ Set.Ioo 0 a, α.eta base r = t) with hrange | hrange
    · have hmem := etaInv_mem_Ioo α base hrange
      have heq  := eta_etaInv α base hrange
      have hle  : α.etaInv base t ≤ δ := by
        by_contra h; push Not at h
        -- η strictly anti-mono: δ < etaInv(t) → η(etaInv(t)) < η(δ)
        -- but η(etaInv(t)) = t ≥ η(δ). Contradiction.
        linarith [eta_strictAntiOn α base hbase hpos hcont_inv hδ_ioo hmem h, heq]
      linarith
    · simp only [ClassK.etaInv, dif_neg hrange]; linarith

-- η⁻¹ is continuous at any t in the range of η.
-- Proof via order topology: for each one-sided bound on the output, use IVT on a compact
-- subinterval of (0, a) to find a t-neighbourhood mapping into the desired r-neighbourhood.
lemma etaInv_continuousAt (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a)
    (hpos : ∀ x ∈ Set.Ioo 0 a, 0 < α.toFun x)
    (hcont_inv : ContinuousOn (fun x => 1 / α.toFun x) (Set.Ioo 0 a))
    {t : ℝ} (ht : ∃ r ∈ Set.Ioo 0 a, α.eta base r = t) :
    ContinuousAt (α.etaInv base) t
    := by
  have h_r_mem := etaInv_mem_Ioo α base ht
  have h_r_eq := eta_etaInv α base ht
  set r := α.etaInv base t
  have heta_inj : ∀ x ∈ Set.Ioo 0 a, ∀ y ∈ Set.Ioo 0 a, α.eta base x = α.eta base y → x = y := by
    intro x hx y hy heq
    rcases lt_trichotomy x y with h | h | h
    · linarith [eta_strictAntiOn α base hbase hpos hcont_inv hx hy h]
    · exact h
    · linarith [eta_strictAntiOn α base hbase hpos hcont_inv hy hx h]
  have h_IVT : ∀ x₁ x₂, x₁ ∈ Set.Ioo 0 a → x₂ ∈ Set.Ioo 0 a → x₁ < r → r < x₂ →
      ∀ᶠ t' in 𝓝 (α.eta base r), x₁ ≤ α.etaInv base t' ∧ α.etaInv base t' ≤ x₂ := by
    intro x₁ x₂ hx₁ hx₂ hlt₁ hlt₂
    have h_t₁ := eta_strictAntiOn α base hbase hpos hcont_inv hx₁ h_r_mem hlt₁
    have h_t₂ := eta_strictAntiOn α base hbase hpos hcont_inv h_r_mem hx₂ hlt₂
    filter_upwards [Ioo_mem_nhds h_t₂ h_t₁] with t' ht'
    have hcont : ContinuousOn (α.eta base) (Set.Icc x₁ x₂) :=
      (eta_continuousOn α base hbase hcont_inv).mono
        (fun x hx => ⟨lt_of_lt_of_le hx₁.1 hx.1, lt_of_le_of_lt hx.2 hx₂.2⟩)
    obtain ⟨r', hr'_icc, hr'_eq⟩ := intermediate_value_Icc' (le_of_lt (lt_trans hlt₁ hlt₂))
      hcont ⟨le_of_lt ht'.1, le_of_lt ht'.2⟩
    have hr'_ioo : r' ∈ Set.Ioo 0 a :=
      ⟨lt_of_lt_of_le hx₁.1 hr'_icc.1, lt_of_le_of_lt hr'_icc.2 hx₂.2⟩
    have hetaInv_eq : α.etaInv base t' = r' :=
      heta_inj _ (etaInv_mem_Ioo α base ⟨r', hr'_ioo, hr'_eq⟩) _ hr'_ioo
        (by rw [eta_etaInv α base ⟨r', hr'_ioo, hr'_eq⟩, hr'_eq])
    rwa [hetaInv_eq]
  rw [ContinuousAt]
  change Filter.Tendsto (α.etaInv base) (𝓝 t) (𝓝 r)
  rw [← h_r_eq]
  apply tendsto_order.mpr
  constructor
  · -- Lower bound: z₁ < r
    intro z₁ hz₁
    set x₁ := (max 0 z₁ + r) / 2
    set x₂ := (r + a) / 2
    have h_max_lt : max 0 z₁ < r := max_lt h_r_mem.1 hz₁
    have h_max_ge : 0 ≤ max 0 z₁ := le_max_left 0 z₁
    -- Prove bounds on the explicit formulas so linarith can see the math
    have hx₁_pos : 0 < (max 0 z₁ + r) / 2 := by linarith
    have hx₁_lt_r : (max 0 z₁ + r) / 2 < r := by linarith
    have hx₂_gt_r : r < (r + a) / 2 := by linarith [h_r_mem.2]
    have hx₂_lt_a : (r + a) / 2 < a := by linarith [h_r_mem.2]
    have hx₁_mem : x₁ ∈ Set.Ioo 0 a := ⟨hx₁_pos, lt_trans hx₁_lt_r h_r_mem.2⟩
    have hx₂_mem : x₂ ∈ Set.Ioo 0 a := ⟨lt_trans h_r_mem.1 hx₂_gt_r, hx₂_lt_a⟩
    filter_upwards [h_IVT x₁ x₂ hx₁_mem hx₂_mem hx₁_lt_r hx₂_gt_r] with t' ht'
    linarith [ht'.1, show z₁ < x₁ by grind]
  · -- Upper bound: z₂ > r
    intro z₂ hz₂
    set x₁ := r / 2
    set x₂ := (r + min a z₂) / 2
    have h_min_gt : r < min a z₂ := lt_min h_r_mem.2 hz₂
    have h_min_le_a : min a z₂ ≤ a := min_le_left a z₂
    -- Prove bounds on the explicit formulas
    have hx₁_pos : 0 < r / 2 := by linarith [h_r_mem.1]
    have hx₁_lt_r : r / 2 < r := by linarith [h_r_mem.1]
    have hx₂_gt_r : r < (r + min a z₂) / 2 := by linarith
    have hx₂_lt_a : (r + min a z₂) / 2 < a := by linarith
    have hx₁_mem : x₁ ∈ Set.Ioo 0 a := ⟨hx₁_pos, lt_trans hx₁_lt_r h_r_mem.2⟩
    have hx₂_mem : x₂ ∈ Set.Ioo 0 a := ⟨lt_trans h_r_mem.1 hx₂_gt_r, hx₂_lt_a⟩
    filter_upwards [h_IVT x₁ x₂ hx₁_mem hx₂_mem hx₁_lt_r hx₂_gt_r] with t' ht'
    linarith [ht'.2, show x₂ < z₂ by grind [min_le_right a z₂]]



end OsgoodConstruction




theorem ClassK.sigma_isClassKL (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a)
    (hcont_inv : ContinuousOn (fun x => 1 / α.toFun x) (Set.Ioo 0 a))
    (hpos : ∀ x ∈ Set.Ioo 0 a, 0 < α.toFun x)
    (hdiv : α.EtaDiverges base) :
    ∃ σ : ClassKL a,
      (∀ r ∈ Set.Ioo 0 a, ∀ s ≥ 0, σ.toFun r s = α.sigma base r s) ∧
      (∀ s ≥ 0, σ.toFun 0 s = 0) := by
    refine ⟨{
      ha           := α.ha
      toFun        := α.sigma base
      -- σ(0, s) = 0 by definition
      map_zero     := fun s _ => by simp [ClassK.sigma]
      -- Continuity at r=0 needs etaInv_tendsto_zero; interior is composition of continuous fns
      continuous_r := fun s hs => by
        intro r hr
        rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
        · -- r = 0: σ(0,s) = 0; need σ(r,s) → 0 as r → 0⁺
          -- Rewrite Ico = {0} ∪ Ioo, handle each piece
          rw [show Set.Ico 0 a = {0} ∪ Set.Ioo 0 a from by
            ext x; simp only [Set.mem_Ico, le_iff_lt_or_eq]
            constructor
            · rintro ⟨h1 | h1, h2⟩
              · exact Or.inr ⟨h1, h2⟩
              · exact Or.inl h1.symm
            · rintro (rfl | ⟨h1, h2⟩)
              · exact ⟨Or.inr rfl, α.ha⟩
              · exact ⟨Or.inl h1, h2⟩]
          rw [ContinuousWithinAt, nhdsWithin_union, Filter.tendsto_sup]
          constructor
          · -- Case 1: The singleton {0} (Your existing logic)
            rw [nhdsWithin_singleton]
            simp only [Filter.Tendsto, Filter.map_pure, ClassK.sigma]
            exact pure_le_nhds 0
          · -- Case 2: The open interval Ioo 0 a

            -- 1. Resolve t= limit target: prove α.sigma base 0 s = 0 and rewrite it
            have h_sigma_zero : α.sigma base 0 s = 0 := by
              simp only [ClassK.sigma]
              tauto
            rw [h_sigma_zero]
            -- 2. Resolve the function body: prove they are locally equal
            have h_eq : (fun r => α.sigma base r s) =ᶠ[nhdsWithin 0 (Set.Ioo 0 a)]
                        (fun r => α.etaInv base (α.eta base r + s)) := by
              filter_upwards [self_mem_nhdsWithin] with r hr
              simp only [ClassK.sigma, if_neg hr.1.ne']
            -- 3. Re-establish your limits
            have h_eta_atTop : Filter.Tendsto (α.eta base) (nhdsWithin 0 (Set.Ioo 0 a))
                Filter.atTop :=
              hdiv.mono_left (nhdsWithin_mono 0 Set.Ioo_subset_Ioi_self)
            have h_add_atTop : Filter.Tendsto (fun r => α.eta base r + s)
                (nhdsWithin 0 (Set.Ioo 0 a)) Filter.atTop := by
              -- Since s ≥ 0, η(r) + s ≥ η(r). We use monotonicity at +∞.
              apply Filter.tendsto_atTop_mono (fun r => le_add_of_nonneg_right hs) h_eta_atTop
            have h_inv_zero : Filter.Tendsto (α.etaInv base) Filter.atTop (nhds 0)
              := etaInv_tendsto_zero α base hbase hpos hcont_inv
            -- 4. The goal now perfectly matches your composition's type
            exact (h_inv_zero.comp h_add_atTop).congr' h_eq.symm
        · -- r > 0: sigma = etaInv(eta(·) + s), continuous composition
          apply ContinuousAt.continuousWithinAt
          simp only [ClassK.sigma]
          have hcont_sum : ContinuousAt (fun x => α.eta base x + s) r :=
            (eta_hasDerivAt α base hbase hcont_inv ⟨hr_pos, hr.2⟩).continuousAt.add
              continuousAt_const
          have hcont_inv : ContinuousAt (α.etaInv base) (α.eta base r + s) :=
            etaInv_continuousAt α base hbase hpos hcont_inv
              (eta_add_mem_range α base hbase hdiv hcont_inv ⟨hr_pos, hr.2⟩ hs)
          have h_comp : ContinuousAt (fun x => α.etaInv base (α.eta base x + s)) r :=
            ContinuousAt.comp (f := fun x => α.eta base x + s) hcont_inv hcont_sum
          have h_eq : (fun x => α.etaInv base (α.eta base x + s)) =ᶠ[𝓝 r]
                      (fun x => if x = 0 then 0 else α.etaInv base (α.eta base x + s)) := by
            -- Filter over the open interval (0, ∞) using the fact that r > 0
            filter_upwards [isOpen_Ioi.mem_nhds hr_pos] with x hx
            -- For any x in this neighborhood, x > 0, so x ≠ 0
            exact (if_neg hx.ne').symm
          exact h_comp.congr h_eq

      -- σ strictly increasing in r: two cases
      strict_mono_r := fun s hs => by
        intro r₁ hr₁ r₂ hr₂ hr_lt
        rcases eq_or_lt_of_le hr₁.1 with rfl | hr₁_pos
        · -- r₁ = 0: σ(0,s) = 0, and σ(r₂,s) = etaInv(...) > 0
          simp only [ClassK.sigma]
          have hr₂_pos : (0 : ℝ) < r₂ := hr_lt
          rw [if_neg hr₂_pos.ne']
          exact (etaInv_mem_Ioo α base
            (eta_add_mem_range α base hbase hdiv hcont_inv ⟨hr₂_pos, hr₂.2⟩ hs)).1
        · -- 0 < r₁ < r₂: eta anti-mono gives eta(r₁)+s > eta(r₂)+s,
          --               then etaInv anti-mono flips back
          have hr₂_pos : (0 : ℝ) < r₂ := lt_trans hr₁_pos hr_lt
          simp only [ClassK.sigma, if_neg hr₁_pos.ne', if_neg hr₂_pos.ne']
          apply etaInv_strictAntiOn α base hbase hpos hcont_inv
          · exact eta_add_mem_range α base hbase hdiv hcont_inv ⟨hr₂_pos, hr₂.2⟩ hs
          · exact eta_add_mem_range α base hbase hdiv hcont_inv ⟨hr₁_pos, hr₁.2⟩ hs
          · linarith [eta_strictAntiOn α base hbase hpos hcont_inv
              ⟨hr₁_pos, hr₁.2⟩ ⟨hr₂_pos, hr₂.2⟩ hr_lt]
      -- σ ≥ 0: either r=0 (trivial) or etaInv lands in Ioo 0 a
      nonneg := fun r hr s hs => by
        simp only [ClassK.sigma]
        rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
        · simp
        · rw [if_neg hr_pos.ne']
          exact le_of_lt (etaInv_mem_Ioo α base
            (eta_add_mem_range α base hbase hdiv hcont_inv ⟨hr_pos, hr.2⟩ hs)).1
      -- σ antitone in s: larger s → larger input to etaInv → smaller output
      anti_s := fun r hr => by
        intro s₁ hs₁ s₂ hs₂ hs_le
        simp only [ClassK.sigma]
        rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
        · simp
        · simp only [if_neg hr_pos.ne']
          rcases eq_or_lt_of_le hs_le with rfl | hs_lt
          · exact le_refl _
          · exact le_of_lt (etaInv_strictAntiOn α base hbase hpos hcont_inv
              (eta_add_mem_range α base hbase hdiv hcont_inv ⟨hr_pos, hr.2⟩ hs₁)
              (eta_add_mem_range α base hbase hdiv hcont_inv ⟨hr_pos, hr.2⟩ hs₂)
              (by linarith))
      -- σ(r,s) → 0 as s → ∞: compose etaInv_tendsto_zero with (eta(r) + ·) → ∞
      tendsto_zero := fun r hr => by
        simp only [ClassK.sigma]
        rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
        · simp only; exact tendsto_const_nhds
        · simp only  [if_neg hr_pos.ne']
          have key : Filter.Tendsto (fun s => α.eta base r + s) Filter.atTop Filter.atTop :=
            tendsto_atTop_atTop_of_monotone
              (fun _ _ h => by linarith)
              (fun b => ⟨b - α.eta base r, by linarith⟩)
          exact (etaInv_tendsto_zero α base hbase hpos hcont_inv).comp key
    }, ⟨fun r _ s _ => rfl, fun s _ => by simp [ClassK.sigma]⟩⟩

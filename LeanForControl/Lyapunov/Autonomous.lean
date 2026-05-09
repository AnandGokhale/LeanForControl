import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import LeanForControl.Lyapunov.Defs

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Infrastructure -/

-- Chain rule: if V is differentiable and φ is a trajectory, then
-- d/dt (V ∘ φ)(t) = DV(φ(t))[f(φ(t))].
-- Lean path: (hV_diff.hasDerivAt (φ t)).comp_hasDerivAt t (htraj t)
-- using HasFDerivAt.comp_hasDerivAt from Mathlib.Analysis.Calculus.FDeriv.Comp.
lemma hasDerivAt_V_comp_traj
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ V)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f) (t : ℝ) :
    HasDerivAt (V ∘ φ) (fderiv ℝ V (φ t) (f (φ t))) t :=
  (hV_diff (φ t)).hasFDerivAt.comp_hasDerivAt t (htraj t)

-- V is nonincreasing along trajectories when the Lie derivative is ≤ 0.
-- Proof: (V ∘ φ)'(t) = fderiv ℝ V (φ t) (f (φ t)) ≤ 0 (chain rule + hLie_nonpos),
-- then apply antitone_of_deriv_nonpos.
lemma V_nonincreasing
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f) :
    Antitone (V ∘ φ) := by
  apply antitone_of_deriv_nonpos
  · exact fun t => (hasDerivAt_V_comp_traj hV.hV_diff htraj t).differentiableAt
  · intro t
    rw [(hasDerivAt_V_comp_traj hV.hV_diff htraj t).deriv]
    exact hV.hLie_nonpos (φ t)

-- Corollary: V(φ t) ≤ V(φ 0) for all t ≥ 0.
lemma V_le_initial
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f)
    {t : ℝ} (ht : 0 ≤ t) : V (φ t) ≤ V (φ 0) :=
  V_nonincreasing hV htraj ht

-- A trajectory is continuous: differentiability at every point implies continuity.
-- Lean path: continuous_iff_continuousAt + (htraj t).differentiableAt.continuousAt
lemma trajectory_continuous
    {f : ℝⁿ → ℝⁿ} {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f) :
    Continuous φ := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (htraj t).differentiableAt.continuousAt

-- The sphere Metric.sphere x_eq ε is nonempty when 0 < n and 0 < ε.
-- Proof: x_eq + EuclideanSpace.single ⟨0, hn⟩ ε lies on the sphere.
lemma sphere_nonempty
    (x_eq : ℝⁿ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (Metric.sphere x_eq ε).Nonempty := by
  refine ⟨x_eq + EuclideanSpace.single (⟨0, hn⟩ : Fin n) ε, ?_⟩
  rw [Metric.mem_sphere, dist_eq_norm]
  simp [PiLp.norm_single, abs_of_pos hε]

/-! ## Lyapunov function hierarchy -/

-- IsStrictLyapunovFunction → IsLocalLyapunovFunction:
-- weaken hLie_neg (< 0 for x ≠ x_eq) to hLie_nonpos (≤ 0 everywhere),
-- using the fact that fderiv ℝ V x_eq (f x_eq) = 0 when f is continuous
-- and x_eq is a critical point of V. In the sorry we cover both cases.
-- Also: ContDiff ℝ 1 V → Differentiable ℝ V.
lemma strict_implies_semidefinite
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLyapunovFunction f V x_eq) :
    IsLocalLyapunovFunction f V x_eq where
  hcont       := hV.hcont
  hV_diff     := hV.hV_c1.differentiable (by norm_num)
  hzero       := hV.hzero
  hpos        := hV.hpos
  hLie_nonpos := fun x => by
    by_cases hx : x = x_eq
    · simp only [hx, hV.hequil, map_zero, le_refl]
    · exact le_of_lt (hV.hLie_neg x hx)

-- IsAsymptoticLyapunovFunction → IsStrictLyapunovFunction:
-- hbounded_sublevel follows from isCompact_sublevel_set applied to hV.hradial.
lemma asymptotic_implies_strict
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsAsymptoticLyapunovFunction f V x_eq) :
    IsStrictLyapunovFunction f V x_eq where
  hcont             := hV.hcont
  hV_c1             := hV.hV_c1
  hzero             := hV.hzero
  hpos              := hV.hpos
  hequil            := hV.hequil
  hLie_neg          := hV.hLie_neg
  hbounded_sublevel := fun c =>
    isCompact_sublevel_set V hV.hcont hV.hradial c

/-! ## Theorem 4.1, Part 1: Lyapunov stability -/

-- If V is a local Lyapunov function, the equilibrium is Lyapunov stable.
--
-- Proof strategy (Khalil Theorem 4.1, Part 1):
-- Fix ε > 0.
-- (1) Let m = min_{x ∈ sphere x_eq ε} V(x).
--     Exists by compactness (isCompact_sphere) + continuity. Positive by hpos,
--     since x_eq ∉ sphere x_eq ε.
-- (2) By continuity of V at x_eq (V(x_eq) = 0), find δ > 0 with V(y) < m
--     whenever ‖y - x_eq‖ < δ.
-- (3) Take δ' = min δ ε. Suppose ‖φ 0 - x_eq‖ < δ' but ‖φ t - x_eq‖ ≥ ε for some t ≥ 0.
-- (4) By IVT (isPreconnected_Icc.intermediate_value₂ on the continuous function
--     t ↦ ‖φ t - x_eq‖), find t' ∈ [0, t] with ‖φ t' - x_eq‖ = ε.
-- (5) Contradiction: m ≤ V(φ t') ≤ V(φ 0) < m.
theorem lyapunov_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsLocalLyapunovFunction f V x_eq) :
    LyapunovStable f x_eq := by
  intro ε hε
  obtain ⟨x_min, hx_min_mem, hx_min_le⟩ :=
    (isCompact_sphere x_eq ε).exists_isMinOn (sphere_nonempty x_eq hn hε) hV.hcont.continuousOn
  have hx_min_ne : x_min ≠ x_eq := by
    intro heq; simp [heq] at hx_min_mem; linarith
  have hm_pos : 0 < V x_min := hV.hpos x_min hx_min_ne
  obtain ⟨δ', hδ'_pos, hδ'⟩ := Metric.continuousAt_iff.mp hV.hcont.continuousAt (V x_min) hm_pos
  refine ⟨min δ' ε, by positivity, ?_⟩
  intro φ htraj hclose t ht
  by_contra hcontra
  push Not at hcontra
  obtain ⟨t', ht'_mem, ht'_eq⟩ := isPreconnected_Icc.intermediate_value₂
      (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht)
      ((trajectory_continuous htraj).dist continuous_const).continuousOn
      continuousOn_const
      (le_of_lt (by rw [dist_eq_norm]; exact lt_of_lt_of_le hclose (min_le_right δ' ε)))
      (by rw [dist_eq_norm]; exact hcontra)
  have hV_init : V (φ 0) < V x_min := by
    have h := hδ' (by rw [dist_eq_norm]; exact lt_of_lt_of_le hclose (min_le_left δ' ε))
    rw [hV.hzero, Real.dist_eq, sub_zero] at h
    exact (abs_lt.mp h).2
  exact lt_irrefl (V x_min) <| calc V x_min
    _ ≤ V (φ t') := hx_min_le (by rw [Metric.mem_sphere]; exact ht'_eq)
    _ ≤ V (φ 0)  := V_le_initial hV htraj ht'_mem.1
    _ < V x_min  := hV_init

/-! ## Theorem 4.1, Parts 2 & 3: Asymptotic stability
    The proof factors into four helper lemmas. -/

-- V(φ t) ≥ 0 for all t.
-- Proof: V(x_eq) = 0 by hzero; V(x) > 0 for x ≠ x_eq by hpos. So V ≥ 0 everywhere.
lemma V_nonneg
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLyapunovFunction f V x_eq) (x : ℝⁿ) :
    0 ≤ V x := by
  by_cases hx : x = x_eq
  · simp [hx, hV.hzero]
  · exact le_of_lt (hV.hpos x hx)

-- V(φ(t)) → L as t → ∞ for some L ≥ 0.
-- Proof:
-- (1) V ∘ φ is antitone: apply V_nonincreasing (after strict_implies_semidefinite).
-- (2) V ∘ φ is bounded below by 0: apply V_nonneg.
-- (3) Antitone + bddBelow → tendsto to the infimum.
-- Lean path: Real.tendsto_of_antitone_bounded (or Filter.Tendsto.mono_left
-- via sInf of the range). May need to construct the limit via
-- Real.tendsto_of_bddBelow_antitone or tendsto_atTop_iInf.
lemma V_tendsto_limit
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLyapunovFunction f V x_eq)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f) :
    ∃ L ≥ 0, Filter.Tendsto (V ∘ φ) Filter.atTop (nhds L) := by
  have hanti : Antitone (V ∘ φ) := V_nonincreasing (strict_implies_semidefinite hV) htraj
  have hbdd : BddBelow (Set.range (V ∘ φ)) :=
    ⟨0, fun _ ⟨t, ht⟩ => ht ▸ V_nonneg hV _⟩
  exact ⟨⨅ t, (V ∘ φ) t,
    le_ciInf (fun t => V_nonneg hV (φ t)),
    tendsto_atTop_ciInf hanti hbdd⟩

-- The limit L from V_tendsto_limit equals 0 (key lemma).
--
-- Proof by contradiction: assume L > 0.
-- (a) Since V(φ t) ≥ L > 0 for all t (antitone + limit L), φ t ≠ x_eq for all t ≥ 0.
-- (b) Define K = {x | L/2 ≤ V x} ∩ SublevelSet V (V (φ 0)).
--     - SublevelSet V (V (φ 0)) compact by hbounded_sublevel.
--     - {V ≥ L/2} closed (continuity). Closed ∩ compact = compact.
-- (c) φ t ∈ K for all t ≥ 0:
--     upper bound: V(φ t) ≤ V(φ 0) by V_le_initial;
--     lower bound: V(φ t) ≥ L > L/2 (V ∘ φ antitone with limit L).
-- (d) The function x ↦ fderiv ℝ V x (f x) is continuous on K
--     (uses hV_c1 : ContDiff ℝ 1 V and hf_cont : Continuous f).
-- (e) On K every x ≠ x_eq, so hLie_neg gives fderiv ℝ V x (f x) < 0.
--     By EVT (IsCompact.exists_isMinOn) on K (compact), ∃ γ > 0, ∀ x ∈ K,
--     fderiv ℝ V x (f x) ≤ -γ.
-- (f) Integrate: V(φ t) = V(φ 0) + ∫₀ᵗ fderiv ℝ V (φ s) (f (φ s)) ds ≤ V(φ 0) - γ t.
--     (Uses hasDerivAt_V_comp_traj + intervalIntegral FTC.)
-- (g) For t > (V(φ 0) - L/2) / γ, V(φ t) < L/2, contradicting (c).
lemma V_limit_zero
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLyapunovFunction f V x_eq)
    (hf_cont : Continuous f)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f)
    {L : ℝ} (hL_nonneg : 0 ≤ L)
    (hL_tendsto : Filter.Tendsto (V ∘ φ) Filter.atTop (nhds L)) :
    L = 0 := by
  have hanti : Antitone (V ∘ φ) := V_nonincreasing (strict_implies_semidefinite hV) htraj
  -- V(φ t) ≥ L for all t (antitone function with limit L at +∞ dominates L from above)
  have hVt_ge : ∀ t, L ≤ V (φ t) := fun t => hanti.le_of_tendsto hL_tendsto t
  -- Suppose for contradiction L > 0
  by_contra hL_ne
  have hL_pos : 0 < L := lt_of_le_of_ne hL_nonneg (Ne.symm hL_ne)
  -- Build compact set K = {x | L/2 ≤ V x} ∩ SublevelSet V (V(φ 0))
  set c₀ := V (φ 0) with hc₀_def
  set K := {x : ℝⁿ | L / 2 ≤ V x} ∩ SublevelSet V c₀ with hK_def
  have hK_compact : IsCompact K := by
    apply (hV.hbounded_sublevel c₀).of_isClosed_subset
    · apply IsClosed.inter
      · exact isClosed_Ici.preimage hV.hcont
      · exact isClosed_Iic.preimage hV.hcont
    · intro x ⟨_, hVx⟩; exact hVx
  -- φ t ∈ K for all t ≥ 0
  have hphi_mem : ∀ t ≥ 0, φ t ∈ K := fun t ht =>
    ⟨le_trans (by linarith) (hVt_ge t), hanti ht⟩
  -- K is nonempty (φ 0 ∈ K)
  have hK_nonempty : K.Nonempty := ⟨φ 0, hphi_mem 0 le_rfl⟩
  -- The Lie derivative x ↦ fderiv ℝ V x (f x) is continuous
  have hLie_cont : Continuous fun x : ℝⁿ => fderiv ℝ V x (f x) := by
    have hfderiv_cont : Continuous (fderiv ℝ V) := hV.hV_c1.continuous_fderiv (by norm_num)
    exact (hfderiv_cont.clm_apply hf_cont)
  -- By EVT on K, the Lie derivative achieves a maximum; all values < 0 on K
  -- since ∀ x ∈ K, V x ≥ L/2 > 0 = V(x_eq), so x ≠ x_eq, so Lie < 0
  have hLie_neg_K : ∀ x ∈ K, fderiv ℝ V x (f x) < 0 := fun x hxK => by
    have hx1 : L / 2 ≤ V x := hxK.1
    apply hV.hLie_neg
    intro heq
    have : V x = 0 := by rw [heq]; exact hV.hzero
    linarith
  obtain ⟨x_max, hx_max_mem, hx_max_le⟩ :=
    hK_compact.exists_isMaxOn hK_nonempty hLie_cont.continuousOn
  -- γ = -(fderiv ℝ V x_max (f x_max)) > 0
  set γ := -(fderiv ℝ V x_max (f x_max)) with hγ_def
  have hγ_pos : 0 < γ := neg_pos.mpr (hLie_neg_K x_max hx_max_mem)
  -- ∀ x ∈ K, fderiv ℝ V x (f x) ≤ -γ
  have hLie_le : ∀ x ∈ K, fderiv ℝ V x (f x) ≤ -γ := fun x hx => by
    have h := isMaxOn_iff.mp hx_max_le x hx
    -- h : fderiv ℝ V x (f x) ≤ fderiv ℝ V x_max (f x_max) = -γ
    linarith [hγ_def]
  -- fun t => V(φ t) + γ * t is antitone on [0, ∞), giving V(φ t) ≤ V(φ 0) - γ*t
  have hbound : ∀ t ≥ 0, V (φ t) + γ * t ≤ V (φ 0) := by
    have hanti_sum : AntitoneOn (fun t => V (φ t) + γ * t) (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ))
      · exact (hV.hcont.comp_continuousOn
            (trajectory_continuous htraj).continuousOn).add
          (continuous_const.mul continuous_id).continuousOn
      · intro t ht
        have hd : HasDerivAt (fun s => V (φ s) + γ * s)
            (fderiv ℝ V (φ t) (f (φ t)) + γ * 1) t :=
          (hasDerivAt_V_comp_traj (hV.hV_c1.differentiable (by norm_num)) htraj t).add
            ((hasDerivAt_id t).const_mul γ)
        exact hd.differentiableAt.differentiableWithinAt
      · intro t ht
        have htge : (0 : ℝ) ≤ t := by
          rw [interior_Ici] at ht; exact le_of_lt ht
        have hd : HasDerivAt (fun s => V (φ s) + γ * s)
            (fderiv ℝ V (φ t) (f (φ t)) + γ * 1) t :=
          (hasDerivAt_V_comp_traj (hV.hV_c1.differentiable (by norm_num)) htraj t).add
            ((hasDerivAt_id t).const_mul γ)
        rw [hd.deriv]
        linarith [hLie_le (φ t) (hphi_mem t htge)]
    intro t ht
    have := hanti_sum (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    simpa using this
  -- For t large enough: V(φ t) ≤ V(φ 0) - γ*t < L/2, contradicting V(φ t) ≥ L/2
  set t₁ := (V (φ 0) - L / 2) / γ + 1
  have ht₁_nonneg : 0 ≤ t₁ := by
    -- t₁ = (V(φ 0) - L/2)/γ + 1 ≥ 1 > 0
    -- because V(φ 0) ≥ L/2 (since hVt_ge 0 gives L ≤ V(φ 0) and L > L/2)
    have hVphi0 : L / 2 ≤ V (φ 0) := by linarith [hVt_ge 0]
    have h_num : 0 ≤ V (φ 0) - L / 2 := by linarith
    have h_div : 0 ≤ (V (φ 0) - L / 2) / γ := div_nonneg h_num (le_of_lt hγ_pos)
    linarith
  have hVt₁_low : L / 2 ≤ V (φ t₁) := (hphi_mem t₁ ht₁_nonneg).1
  have hVt₁_high : V (φ t₁) ≤ V (φ 0) - γ * t₁ := by linarith [hbound t₁ ht₁_nonneg]
  have : V (φ 0) - γ * t₁ < L / 2 := by
    -- t₁ = (V(φ 0) - L/2)/γ + 1, so γ * t₁ = (V(φ 0) - L/2) + γ > V(φ 0) - L/2
    have heq : γ * t₁ = V (φ 0) - L / 2 + γ * 1 := by
      simp only [t₁]
      field_simp
    linarith
  linarith

-- If V(φ t) → 0 and V is positive definite, then φ t → x_eq.
-- Proof:
-- Fix ε > 0. The compact set K = SublevelSet V (V(φ 0)) ∩ {x | ‖x - x_eq‖ ≥ ε} is compact
-- (closed ∩ compact sublevel set). On K, x ≠ x_eq so V > 0; by EVT V achieves minimum γ > 0.
-- Since V(φ t) → 0 < γ, eventually V(φ t) < γ. For such t, V(φ t) ≤ V(φ 0) (antitone),
-- so φ t ∈ SublevelSet V (V(φ 0)). If ‖φ t - x_eq‖ ≥ ε, then φ t ∈ K, so V(φ t) ≥ γ.
-- Contradiction.
lemma tendsto_of_V_tendsto_zero
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLyapunovFunction f V x_eq)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f)
    (hV_tendsto : Filter.Tendsto (V ∘ φ) Filter.atTop (nhds 0)) :
    Filter.Tendsto φ Filter.atTop (nhds x_eq) := by
  have hanti : Antitone (V ∘ φ) := V_nonincreasing (strict_implies_semidefinite hV) htraj
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- K = {x | V x ≤ V(φ 0)} ∩ {x | ‖x - x_eq‖ ≥ ε} is compact
  set c₀ := V (φ 0)
  set K := {x : ℝⁿ | V x ≤ c₀ ∧ ε ≤ ‖x - x_eq‖} with hK_def
  have hK_compact : IsCompact K := by
    apply (hV.hbounded_sublevel c₀).of_isClosed_subset
    · apply IsClosed.inter
      · exact isClosed_Iic.preimage hV.hcont
      · exact isClosed_le continuous_const
          (continuous_norm.comp (continuous_id.sub continuous_const))
    · intro x ⟨hVx, _⟩; exact hVx
  -- On K, x ≠ x_eq (since ‖x - x_eq‖ ≥ ε > 0), so V x > 0
  -- If K is empty, we're done trivially (any T works)
  -- If K is nonempty, by EVT V achieves minimum γ > 0 on K
  by_cases hK_empty : K = ∅
  · -- K empty: every point with V x ≤ c₀ is within ε of x_eq
    use 0
    intro t ht
    rw [dist_eq_norm]
    have hVt : V (φ t) ≤ c₀ := hanti ht
    by_contra hcontra
    push Not at hcontra
    have : φ t ∈ K := ⟨hVt, hcontra⟩
    rw [hK_empty] at this; exact this
  · -- K nonempty: EVT gives minimum γ > 0
    have hK_nonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
    obtain ⟨x_min, hx_min_mem, hx_min_le⟩ :=
      hK_compact.exists_isMinOn hK_nonempty hV.hcont.continuousOn
    have hx_min_ne : x_min ≠ x_eq := by
      intro heq
      have : ε ≤ ‖x_eq - x_eq‖ := heq ▸ hx_min_mem.2
      simp at this; linarith
    have hγ_pos : 0 < V x_min := hV.hpos x_min hx_min_ne
    -- find T₀ with ∀ t ≥ T₀, V(φ t) < γ; use max T₀ 0 to ensure t ≥ 0
    rw [Metric.tendsto_atTop] at hV_tendsto
    obtain ⟨T₀, hT₀⟩ := hV_tendsto (V x_min) hγ_pos
    use max T₀ 0
    intro t ht
    rw [dist_eq_norm]
    have hVt_lt : V (φ t) < V x_min := by
      have h := hT₀ t (le_trans (le_max_left _ _) ht)
      simp only [Function.comp, Real.dist_eq, sub_zero] at h
      exact (abs_lt.mp h).2
    -- V(φ t) ≤ c₀: since t ≥ max T₀ 0 ≥ 0, antitone gives V(φ t) ≤ V(φ 0) = c₀
    have hVt_le_c0 : V (φ t) ≤ c₀ :=
      hanti (le_trans (le_max_right _ _) ht)
    by_contra hcontra
    push Not at hcontra
    exact absurd hVt_lt (not_lt.mpr (hx_min_le ⟨hVt_le_c0, hcontra⟩))

-- Theorem 4.1, Parts 2 & 3: IsStrictLyapunovFunction → GlobalAsymptoticStable.
-- Note: because hLie_neg and hbounded_sublevel are global conditions on all of ℝⁿ,
-- this proves GAS. A purely local result (LAS without GAS) would require restricting
-- V and f to a neighborhood of x_eq.
theorem lyapunov_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsStrictLyapunovFunction f V x_eq)
    (hf_cont : Continuous f) :
    GlobalAsymptoticStable f x_eq := by
  constructor
  · exact lyapunov_stable hn (strict_implies_semidefinite hV)
  · intro φ htraj
    obtain ⟨L, hL_nonneg, hL_tendsto⟩ := V_tendsto_limit hV htraj
    have hL_zero : L = 0 := V_limit_zero hV hf_cont htraj hL_nonneg hL_tendsto
    rw [hL_zero] at hL_tendsto
    exact tendsto_of_V_tendsto_zero hV htraj hL_tendsto

-- Corollary: IsAsymptoticLyapunovFunction (Khalil's classical form) → GAS.
-- Proof: asymptotic_implies_strict reduces to lyapunov_asymptotic_stable.
theorem lyapunov_global_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsAsymptoticLyapunovFunction f V x_eq)
    (hf_cont : Continuous f) :
    GlobalAsymptoticStable f x_eq :=
  lyapunov_asymptotic_stable hn (asymptotic_implies_strict hV) hf_cont

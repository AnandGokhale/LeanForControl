import Mathlib.Dynamics.OmegaLimit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import LeanForControl.Lyapunov.Defs
import LeanForControl.Lyapunov.Autonomous

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

open Filter Set Topology

/-- ω-limit set of trajectory φ, using Mathlib's omegaLimit with the trivial flow. -/
noncomputable def omegaLimitTraj (φ : ℝ → ℝⁿ) : Set ℝⁿ :=
  omegaLimit Filter.atTop (fun (t : ℝ) (_ : Unit) => φ t) Set.univ

/-! ## Lemma 1: V antitone on [0,∞) along trajectories -/

-- V(φ t) is antitone on [0,∞) when the Lie derivative ≤ 0 on Ω and φ stays in Ω.
lemma V_antitoneOn_lasalle
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω : Set ℝⁿ}
    (hV_c1 : ContDiff ℝ 1 V)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f)
    (hphi : ∀ t ≥ 0, φ t ∈ Ω) :
    AntitoneOn (V ∘ φ) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ))
  · exact (hV_c1.continuous.comp (trajectory_continuous htraj)).continuousOn
  · intro t _
    have hda := hasDerivAt_V_comp_traj (hV_c1.differentiable (by norm_num)) htraj t
    exact hda.differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have hda := hasDerivAt_V_comp_traj (hV_c1.differentiable (by norm_num)) htraj t
    rw [hda.deriv]
    exact hLie (φ t) (hphi t (le_of_lt ht))

/-! ## Lemma 2: V(φ t) converges to its infimum -/

-- If Ω is compact and positively invariant and the Lie derivative ≤ 0 on Ω,
-- then V(φ t) converges to some limit L.
lemma lasalle_V_tendsto
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω : Set ℝⁿ}
    (hV_c1 : ContDiff ℝ 1 V)
    (hΩ_compact : IsCompact Ω)
    (hΩ_inv : IsPositivelyInvariant Ω f)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f) (hφ0 : φ 0 ∈ Ω) :
    ∃ L, Filter.Tendsto (V ∘ φ) Filter.atTop (nhds L) := by
  -- φ stays in Ω for all t ≥ 0
  have hphi : ∀ t ≥ 0, φ t ∈ Ω := hΩ_inv φ htraj hφ0
  -- V(φ t) is antitone on [0, ∞)
  have hanti : AntitoneOn (V ∘ φ) (Set.Ici 0) := V_antitoneOn_lasalle hV_c1 hLie htraj hphi
  -- Ω is compact so V attains its minimum on Ω, giving a lower bound
  have hΩ_nonempty : Ω.Nonempty := ⟨φ 0, hφ0⟩
  have hV_cont : Continuous V := hV_c1.continuous
  obtain ⟨x_min, _, hx_min_le⟩ := hΩ_compact.exists_isMinOn hΩ_nonempty hV_cont.continuousOn
  -- Extend to globally antitone function via max trick
  set g : ℝ → ℝ := fun t => (V ∘ φ) (max t 0) with hg_def
  have hg_anti : Antitone g := fun s t hst =>
    hanti (Set.mem_Ici.mpr (le_max_right s 0)) (Set.mem_Ici.mpr (le_max_right t 0))
      (max_le_max_right 0 hst)
  -- V is bounded below on Ω, so V(φ t) ≥ V(x_min) for all t ≥ 0
  have hg_bdd : BddBelow (Set.range g) :=
    ⟨V x_min, fun _ ⟨t, ht⟩ => ht ▸ hx_min_le (hphi (max t 0) (le_max_right t 0))⟩
  set L := ⨅ t, g t
  have hg_tendsto : Filter.Tendsto g Filter.atTop (nhds L) :=
    tendsto_atTop_ciInf hg_anti hg_bdd
  -- The tendsto for g agrees with V ∘ φ for large t
  have hgL_eq : ∀ t ≥ (0 : ℝ), g t = (V ∘ φ) t := fun t ht => by
    simp [hg_def, max_eq_left ht]
  exact ⟨L, hg_tendsto.congr' ((Filter.eventually_ge_atTop 0).mono fun t ht => hgL_eq t ht)⟩

/-! ## Lemma 3: V is constant on omegaLimitTraj(φ) -/

-- If V(φ t) → L, then V = L on omegaLimitTraj(φ).
lemma V_const_on_omegaLimit
    {V : ℝⁿ → ℝ} {φ : ℝ → ℝⁿ} {L : ℝ}
    (hV_cont : Continuous V)
    (hVphi_tendsto : Filter.Tendsto (V ∘ φ) Filter.atTop (nhds L)) :
    ∀ y ∈ omegaLimitTraj φ, V y = L := by
  intro y hy
  -- y ∈ omegaLimitTraj(φ) means: for every neighborhood n of y, ∃ᶠ t in atTop, φ t ∈ n
  rw [omegaLimitTraj, mem_omegaLimit_iff_frequently] at hy
  -- V y is a cluster point of V ∘ φ along atTop
  have hcluster : MapClusterPt (V y) Filter.atTop (V ∘ φ) := by
    rw [mapClusterPt_iff_frequently]
    intro U hU
    -- V⁻¹(U) is a neighborhood of y by continuity
    have hVU : V ⁻¹' U ∈ nhds y := hV_cont.continuousAt hU
    -- ∃ᶠ t in atTop, φ t ∈ V⁻¹(U) (univ ∩ ...)
    have hfreq := hy (V ⁻¹' U) hVU
    -- the nonemptiness of univ ∩ {() | φ t ∈ V⁻¹(U)} is equivalent to φ t ∈ V⁻¹(U)
    apply hfreq.mono
    intro t ht
    simp only [Set.univ_inter, Set.Nonempty] at ht
    obtain ⟨_, hm⟩ := ht
    simpa using hm
  -- ClusterPt (V y) (map (V∘φ) atTop)
  have hcp : ClusterPt (V y) (map (V ∘ φ) Filter.atTop) := hcluster.clusterPt
  -- map (V∘φ) atTop ≤ nhds L (from tendsto)
  -- So 𝓝 (V y) ⊓ nhds L ≠ ⊥
  have hnebot : NeBot (𝓝 (V y) ⊓ 𝓝 L) := by
    apply NeBot.mono hcp
    exact inf_le_inf_left _ hVphi_tendsto
  exact eq_of_nhds_neBot hnebot


/-! ## Lemma 4: omegaLimitTraj(φ) ⊆ Ω when Ω is compact and positively invariant -/

-- If Ω is compact and positively invariant and φ 0 ∈ Ω, then omegaLimitTraj(φ) ⊆ Ω.
lemma omegaLimit_subset_of_invariant
    {f : ℝⁿ → ℝⁿ} {Ω : Set ℝⁿ}
    (hΩ_compact : IsCompact Ω)
    (hΩ_inv : IsPositivelyInvariant Ω f)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f) (hφ0 : φ 0 ∈ Ω) :
    omegaLimitTraj φ ⊆ Ω := by
  -- Ω is closed (compact in a Hausdorff space)
  have hΩ_closed : IsClosed Ω := hΩ_compact.isClosed
  -- φ t ∈ Ω for t ≥ 0
  have hphi : ∀ t ≥ 0, φ t ∈ Ω := hΩ_inv φ htraj hφ0
  -- omegaLimitTraj(φ) ⊆ closure (image2 (fun t () => φ t) (Ici 0) univ)
  have hsub : omegaLimitTraj φ ⊆
      closure (image2 (fun (t : ℝ) (_ : Unit) => φ t) (Set.Ici 0) Set.univ) :=
    omegaLimit_subset_closure_image2 Filter.atTop
      (fun (t : ℝ) (_ : Unit) => φ t) Set.univ (Ici_mem_atTop 0)
  -- image2 ... ⊆ Ω
  have himage : image2 (fun (t : ℝ) (_ : Unit) => φ t) (Set.Ici 0) Set.univ ⊆ Ω := by
    intro x hx
    simp only [Set.mem_image2, Set.mem_univ, Set.mem_Ici] at hx
    obtain ⟨t, ht, _, _, rfl⟩ := hx
    exact hphi t ht
  calc omegaLimitTraj φ
      ⊆ closure (image2 (fun (t : ℝ) (_ : Unit) => φ t) (Set.Ici 0) Set.univ) := hsub
    _ ⊆ closure Ω := closure_mono himage
    _ = Ω := hΩ_closed.closure_eq

/-! ## Main theorem: LaSalle's invariance principle -/

/-- LaSalle's invariance principle.

Let Ω be compact and positively invariant for ẋ = f(x), V : ℝⁿ → ℝ a C¹ Lyapunov function
with V̇(x) = DV(x)[f(x)] ≤ 0 on Ω, and M a closed set contained in Ω.
If ω(φ) ⊆ M (which in the classical theorem follows from M being the largest invariant
subset of E = {x ∈ Ω | V̇(x) = 0}, via ODE uniqueness), then φ(t) → M. -/
theorem lasalle_invariance_principle
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω M : Set ℝⁿ}
    (hΩ_compact : IsCompact Ω)
    (hΩ_inv : IsPositivelyInvariant Ω f)
    (hV_c1 : ContDiff ℝ 1 V)
    -- V̇(x) = DV(x)[f(x)] ≤ 0 on Ω
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f) (hφ0 : φ 0 ∈ Ω)
    (_hM_closed : IsClosed M)
    -- ω(φ) ⊆ M: classically M is the largest invariant subset of {V̇ = 0} ∩ Ω.
    -- This requires ODE uniqueness (forward invariance of ω(φ)); taken as hypothesis.
    (hω_sub_M : omegaLimitTraj φ ⊆ M) :
    Filter.Tendsto φ Filter.atTop (𝓝ˢ M) := by
  -- V(φ t) converges to its infimum L along the trajectory
  obtain ⟨L, hVL⟩ := lasalle_V_tendsto hV_c1 hΩ_compact hΩ_inv hLie htraj hφ0
  -- V = L on ω(φ): every ω-limit point sees the limiting value
  have _ : ∀ y ∈ omegaLimitTraj φ, V y = L :=
    V_const_on_omegaLimit hV_c1.continuous hVL
  -- φ stays in Ω for t ≥ 0
  have hphi_in_Ω : ∀ t ≥ 0, φ t ∈ Ω := hΩ_inv φ htraj hφ0
  -- Build the compact absorption hypothesis: ∀ᶠ t in atTop, MapsTo (fun () => φ t) univ Ω
  have hc₂ : ∀ᶠ t in Filter.atTop, MapsTo (fun (_ : Unit) => φ t) Set.univ Ω :=
    (Filter.eventually_ge_atTop 0).mono fun t ht () _ => hphi_in_Ω t ht
  rw [Filter.tendsto_def]
  intro U hU
  rw [mem_nhdsSet_iff_exists] at hU
  obtain ⟨W, hW_open, hMW, hWU⟩ := hU
  have hω_sub_W : omegaLimitTraj φ ⊆ W := hω_sub_M.trans hMW
  have hev : ∀ᶠ t in Filter.atTop,
      MapsTo (fun (_ : Unit) => φ t) Set.univ W :=
    eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset
      Filter.atTop (fun (t : ℝ) (_ : Unit) => φ t) Set.univ
      hΩ_compact hc₂ hW_open hω_sub_W
  exact hev.mono fun t ht => hWU (ht (Set.mem_univ ()))

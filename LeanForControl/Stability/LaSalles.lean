import Mathlib.Dynamics.OmegaLimit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import LeanForControl.Stability.Defs
import LeanForControl.Stability.Autonomous
import Architect

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-!
# `Stability.LaSalles`

LaSalle's invariance principle and its corollaries (Barbashin–Krasovskii theorems).

## Main results

* `lasalle_invariance_principle` — if `Ω` is compact and positively invariant, `V` is C¹ with
  `V̇ ≤ 0` on `Ω`, and `ω(φ) ⊆ M` for a closed set `M`, then `φ(t) → M`.
* `lasalle_local_asymptotic_stable` (Corollary 4.1 / Barbashin) — local asymptotic stability
  via a compact sublevel set and LaSalle.
* `lasalle_global_asymptotic_stable` (Corollary 4.2 / Krasovskii) — global asymptotic stability
  when `V` is radially unbounded and `V̇ ≤ 0` everywhere.

## Proof strategy

1. `V_antitoneOn_lasalle`: `V ∘ φ` is antitone on `[0, ∞)` (Lie derivative ≤ 0 on Ω).
2. `lasalle_V_tendsto`: `V(φ t) → L` via monotone convergence on the compact orbit.
3. `V_const_on_omegaLimit`: `V = L` on `ω(φ)` (cluster-point argument).
4. `omegaLimit_subset_of_invariant`: `ω(φ) ⊆ Ω` since `Ω` is closed and φ stays in `Ω`.
5. The main theorem combines these to show `φ t → M` via the open-neighborhood criterion.
-/

open Filter Set Topology

/-- ω-limit set of trajectory φ, using Mathlib's omegaLimit with the trivial flow. -/
noncomputable def omegaLimitTraj (φ : ℝ → ℝⁿ) : Set ℝⁿ :=
  omegaLimit Filter.atTop (fun (t : ℝ) (_ : Unit) => φ t) Set.univ

/-! ## Lemma 1: V antitone on [0,∞) along trajectories -/

/-- `V(φ t)` is antitone on `[0, ∞)` when the Lie derivative `V̇ ≤ 0` on `Ω` and `φ` stays
    in `Ω`. -/
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

/-- If `Ω` is compact and positively invariant and the Lie derivative `V̇ ≤ 0` on `Ω`,
    then `V(φ t)` converges to some limit `L` as `t → ∞`. -/
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

/-- If `V(φ t) → L`, then `V(y) = L` for every `y ∈ ω(φ)`. -/
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

/-- If `Ω` is compact, positively invariant, and `φ 0 ∈ Ω`, then `ω(φ) ⊆ Ω`. -/
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
@[blueprint "thm:lasalle-invariance-principle"
  (statement := /-- \textbf{LaSalle's invariance principle.}
    Let $\Omega$ be compact and positively invariant for $\dot{x} = f(x)$,
    $V \in C^{1}$ with $\dot{V}(x) \le 0$ on $\Omega$, and $M \subseteq \Omega$ closed.
    If the $\omega$-limit set of any trajectory $\varphi$ starting in $\Omega$ satisfies
    $\omega(\varphi) \subseteq M$, then $\varphi(t) \to M$ as $t \to \infty$. -/)]
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

/-! ## Corollaries 4.1 and 4.2: Barbashin–Krasovskii theorems -/

/-- Corollary 4.1 (Barbashin): local asymptotic stability via LaSalle.
    V C¹ and positive definite on D, V̇ ≤ 0 on D, compact sublevel set Ωc ⊆ D,
    every trajectory starting in Ωc has ω-limit set ⊆ {x_eq}. -/
@[blueprint "thm:lasalle-local-asymptotic-stable"
  (statement := /-- \textbf{Corollary 4.1 (Barbashin).}
    If $V \in C^1$ is positive definite on $D$, $\dot{V} \le 0$ on $D$, there exists a
    compact sublevel set $\Omega_c \subseteq D$, and every trajectory starting in $\Omega_c$
    has $\omega$-limit set $\subseteq \{x_{\mathrm{eq}}\}$, then $x_{\mathrm{eq}}$ is
    locally asymptotically stable (\cref{def:localAsymptoticStable}). -/)]
theorem lasalle_local_asymptotic_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV_c1 : ContDiff ℝ 1 V)
    (hV_local : IsLocalLyapunovFunction f V x_eq D)
    {c : ℝ} (hc_pos : 0 < c)
    (hΩ_sub_D : SublevelSet V c ⊆ D)
    (hΩ_compact : IsCompact (SublevelSet V c))
    (hΩ_inv : IsPositivelyInvariant (SublevelSet V c) f)
    (hLasalle : ∀ φ : ℝ → ℝⁿ, IsTrajectory φ f →
                  φ 0 ∈ SublevelSet V c → omegaLimitTraj φ ⊆ {x_eq}) :
    LocalAsymptoticStable f x_eq := by
  refine ⟨lyapunov_stable hn hV_local, ?_⟩
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hV_local.hcont.continuousAt c hc_pos
  refine ⟨δ, hδ_pos, fun φ htraj hφ0 => ?_⟩
  have hV0 : V (φ 0) < c := by
    have h := hδ (by rwa [dist_eq_norm])
    rw [Real.dist_eq, hV_local.hzero, sub_zero] at h
    exact (abs_lt.mp h).2
  have hφ0_in : φ 0 ∈ SublevelSet V c := le_of_lt hV0
  have hconv := lasalle_invariance_principle hΩ_compact hΩ_inv hV_c1
    (fun x hx => hV_local.hLie_nonpos x (hΩ_sub_D hx))
    htraj hφ0_in isClosed_singleton (hLasalle φ htraj hφ0_in)
  rwa [nhdsSet_singleton] at hconv

/-- Corollary 4.2 (Krasovskii): global asymptotic stability via LaSalle.
    V C¹, positive definite, radially unbounded, V̇ ≤ 0 on ℝⁿ,
    every trajectory has ω-limit set ⊆ {x_eq}. -/
@[blueprint "thm:lasalle-global-asymptotic-stable"
  (statement := /-- \textbf{Corollary 4.2 (Krasovskii).}
    If $V \in C^1$ is positive definite, $\dot{V} \le 0$ on $\mathbb{R}^n$, radially
    unbounded, and every trajectory has $\omega$-limit set $\subseteq \{x_{\mathrm{eq}}\}$,
    then $x_{\mathrm{eq}}$ is globally asymptotically stable
    (\cref{def:globalAsymptoticStable}). -/)]
theorem lasalle_global_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV_c1 : ContDiff ℝ 1 V)
    (hzero : V x_eq = 0)
    (hpos : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x)
    (hLie : ∀ x : ℝⁿ, fderiv ℝ V x (f x) ≤ 0)
    (hradial : Filter.Tendsto V (Filter.comap norm Filter.atTop) Filter.atTop)
    (hLasalle : ∀ φ : ℝ → ℝⁿ, IsTrajectory φ f → omegaLimitTraj φ ⊆ {x_eq}) :
    GlobalAsymptoticStable f x_eq := by
  have hV_local : IsLocalLyapunovFunction f V x_eq Set.univ :=
    { hD_open := isOpen_univ
      hD_mem := Set.mem_univ _
      hcont := hV_c1.continuous
      hV_diff := hV_c1.differentiable (by norm_num)
      hzero := hzero
      hpos := fun x _ hx => hpos x hx
      hLie_nonpos := fun x _ => hLie x }
  refine ⟨lyapunov_stable hn hV_local, fun φ htraj => ?_⟩
  set c := V (φ 0) with hc_def
  have hΩ_compact : IsCompact (SublevelSet V c) :=
    isCompact_sublevel_set V hV_c1.continuous hradial c
  have hΩ_inv : IsPositivelyInvariant (SublevelSet V c) f := by
    intro ξ hξ hξ0 t ht
    have hanti := V_antitoneOn_lasalle hV_c1 (fun x _ => hLie x) hξ
      (fun s _ => Set.mem_univ _)
    exact (hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht).trans hξ0
  have hφ0_in : φ 0 ∈ SublevelSet V c := by simp [SublevelSet, hc_def]
  have hconv := lasalle_invariance_principle hΩ_compact hΩ_inv hV_c1
    (fun x _ => hLie x) htraj hφ0_in isClosed_singleton (hLasalle φ htraj)
  rwa [nhdsSet_singleton] at hconv

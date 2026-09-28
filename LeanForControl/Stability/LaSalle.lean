import Mathlib.Dynamics.OmegaLimit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import LeanForControl.Stability.DefsAutonomous
import LeanForControl.Stability.Autonomous
import LeanForControl.ODEs.PicardLindelof
import Architect

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-!
# `Stability.LaSalle`

LaSalle's invariance principle and its corollaries (Barbashin–Krasovskii theorems).

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.1 and Theorem 4.4.

## Main results

* `omegaLimitTraj` and `mem_omegaLimitTraj_iff` — the ω-limit set of a trajectory.
* `isPositivelyInvariant_omegaLimitTraj` — it is positively invariant (Khalil, Lemma 4.1).
* `lieDeriv_eq_zero_on_omegaLimitTraj` — `V̇` vanishes on it, i.e. `ω(φ) ⊆ E`.
* `lasalle_invariance_principle` — `φ(t) → M` for any `M` absorbing the positively invariant
  subsets of `E = LieDerivZeroSet f V Ω`.
* `lasalle_local_asymptotic_stable` (Barbashin's theorem) — local asymptotic stability
  via a compact sublevel set and LaSalle.
* `lasalle_global_asymptotic_stable` (Krasovskii's theorem) — global asymptotic stability
  when `V` is radially unbounded and `V̇ ≤ 0` everywhere.

## Proof strategy

1. `V ∘ φ` is antitone on `[0, ∞)`, since the Lie derivative is `≤ 0` on `Ω`.
2. `V(φ t) → L` by monotone convergence, `V` being bounded below on the compact `Ω`.
3. `V = L` on `ω(φ)`, by continuity and a cluster-point argument.
4. `ω(φ) ⊆ Ω`, since `Ω` is closed and `φ` stays in `Ω`.
5. `ω(φ)` is positively invariant — the one step that needs uniqueness of solutions, supplied
   here by a Grönwall comparison rather than by a globally defined flow. Steps 3 and 5 together
   force `V̇ = 0` on `ω(φ)`, so `ω(φ) ⊆ E`.
6. `φ t → ω(φ) ⊆ M` via the open-neighbourhood criterion for compact absorbing sets.

## Hypotheses that go beyond Khalil

`f` is assumed globally `LipschitzWith` (for uniqueness, via `dist_le_of_trajectories_ODE`) and
`ContDiff ℝ 1` (for existence of a solution through each ω-limit point). Khalil assumes only
that `f` is locally Lipschitz; trajectories here stay in the compact `Ω`, so a local hypothesis
should suffice, but the Grönwall tool in use takes a global one.

Invariance of `ω(φ)` is proved in the *forward* direction only. Khalil's `M` is the largest
invariant subset of `E`; `M` here must absorb every *positively* invariant subset, a larger
family, so the hypothesis on `M` is correspondingly stronger.
-/

open Filter Set Topology
open scoped Pointwise

/-- The ω-limit set of a trajectory `φ`: the points `φ` returns arbitrarily close to,
    arbitrarily late.

Mathlib's `omegaLimit` is stated for a family of maps indexed by a set; a single trajectory is
the degenerate case where the index set is `Unit`, which is what the `fun (t : ℝ) (_ : Unit)`
and `Set.univ` below encode. -/
@[blueprint "def:omegaLimitTraj"
  (statement := /-- The \emph{$\omega$-limit set} of a trajectory $\varphi$ is
    \[
      \omega(\varphi) = \bigcap_{T \ge 0} \overline{\{\varphi(t) : t \ge T\}},
    \]
    the set of points $y$ such that $\varphi(t)$ is frequently in every neighbourhood of $y$ as
    $t \to \infty$. -/)]
noncomputable def omegaLimitTraj (φ : ℝ → ℝⁿ) : Set ℝⁿ :=
  omegaLimit Filter.atTop (fun (t : ℝ) (_ : Unit) => φ t) Set.univ

/-- Membership unfolded: `y` is an ω-limit point of `φ` exactly when `φ` is frequently in every
    neighbourhood of `y`.

Mathlib's `mem_omegaLimit_iff_frequently` is stated for a family of maps, so its right-hand side
asks for a nonempty intersection with `Set.univ`; over `Unit` that collapses to membership. -/
@[blueprint "lem:mem-omegaLimitTraj-iff"
  (statement := /-- $y \in \omega(\varphi)$ (\cref{def:omegaLimitTraj}) if and only if for
    every neighbourhood $U$ of $y$ there are arbitrarily large $t$ with
    $\varphi(t) \in U$. -/)]
lemma mem_omegaLimitTraj_iff {φ : ℝ → ℝⁿ} {y : ℝⁿ} :
    y ∈ omegaLimitTraj φ ↔ ∀ U ∈ 𝓝 y, ∃ᶠ t in Filter.atTop, φ t ∈ U := by
  rw [omegaLimitTraj, mem_omegaLimit_iff_frequently]
  refine forall₂_congr fun U _ => ⟨fun h => h.mono fun t ht => ?_, fun h => h.mono fun t ht => ?_⟩
  · simp only [Set.univ_inter, Set.nonempty_def, Set.mem_preimage] at ht
    exact ht.choose_spec
  · exact ⟨(), by simpa using ht⟩

/-! ## Invariance of the ω-limit set -/

/-- **The ω-limit set of a trajectory is positively invariant** (Khalil, Lemma 4.1).

This is the step that makes LaSalle's principle a theorem about Lyapunov functions rather than
a fact about compact sets: it is what turns `V ≡ a` on `ω(φ)` into `V̇ = 0` on `ω(φ)`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.1. -/
@[blueprint "lem:isPositivelyInvariant-omegaLimitTraj"
  (statement := /-- Let $f$ be Lipschitz and let $\varphi$ be a solution of $\dot{x} = f(x)$ on
    $[0,\infty)$.  Then the $\omega$-limit set $\omega(\varphi)$ (\cref{def:omegaLimitTraj}) is
    positively invariant (\cref{def:isPositivelyInvariant}): every solution segment starting in
    $\omega(\varphi)$ remains in $\omega(\varphi)$.

    Neither boundedness of $\varphi$ nor compactness of an enclosing set is needed; those
    hypotheses of Khalil's Lemma 4.1 are what make $\omega(\varphi)$ nonempty and compact, not
    what make it invariant. -/)
  (proof := /-- Let $\psi$ solve the equation on $[t_0, t_1]$ with $p = \psi(t_0) \in
    \omega(\varphi)$, and fix $t \in [t_0, t_1]$.  Given $\varepsilon > 0$, put
    $C = e^{K(t_1 - t_0)}$ and pick, by the definition of the $\omega$-limit set, arbitrarily
    large $r$ with $\|\varphi(r) - p\| < \varepsilon / C$.  The time-shifted curve
    $u(\cdot) = \varphi(\cdot + r - t_0)$ solves the same autonomous equation on $[t_0, t_1]$ and
    satisfies $u(t_0) = \varphi(r)$, so Grönwall gives
    \[
      \|\varphi(r + t - t_0) - \psi(t)\| = \|u(t) - \psi(t)\|
        \le \|\varphi(r) - p\|\, e^{K(t - t_0)} < \varepsilon .
    \]
    Since $r$ may be taken arbitrarily large, so may $r + t - t_0$; hence $\varphi$ is frequently
    within $\varepsilon$ of $\psi(t)$, i.e. $\psi(t) \in \omega(\varphi)$.

    Khalil argues instead with the flow map and the semigroup identity
    $\phi(t + t_i; x_0) = \phi(t; \phi(t_i; x_0))$, which presumes a globally defined flow.
    Comparing the two solutions directly needs only uniqueness, in its quantitative Grönwall
    form. -/)]
theorem isPositivelyInvariant_omegaLimitTraj
    {f : ℝⁿ → ℝⁿ} {K : NNReal} (hf : LipschitzWith K f)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici 0)) :
    IsPositivelyInvariant (omegaLimitTraj φ) f := by
  intro t₀ t₁ ψ hψ hψ0 t ht
  rw [mem_omegaLimitTraj_iff] at hψ0 ⊢
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  -- Shrink `ε` by the worst-case Grönwall amplification over the whole segment.
  set C : ℝ := Real.exp (K * (t₁ - t₀)) with hC_def
  have hC_pos : 0 < C := Real.exp_pos _
  have hfreq := hψ0 (Metric.ball (ψ t₀) (ε / C)) (Metric.ball_mem_nhds _ (div_pos hε hC_pos))
  rw [Filter.frequently_atTop] at hfreq ⊢
  intro a
  obtain ⟨r, hr_ge, hr⟩ := hfreq (max a 0)
  have hr0 : (0 : ℝ) ≤ r := (le_max_right a 0).trans hr_ge
  -- The trajectory restarted at time `r`, re-anchored to `t₀`.
  have hu : IsIntegralCurveOn (fun s => φ (s + (r - t₀))) (fun _ x => f x) (Set.Icc t₀ t₁) := by
    refine (hφ.comp_add_autonomous (r - t₀)).mono fun s hs => ?_
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg, Set.mem_Ici]
    linarith [hs.1]
  have hcmp := dist_le_of_isIntegralCurveOn_Icc (fun _ => hf) hu hψ t ht
  simp only [show t₀ + (r - t₀) = r by ring] at hcmp
  refine ⟨r + (t - t₀), by linarith [(le_max_left a 0).trans hr_ge, ht.1], hball ?_⟩
  have hexp : Real.exp (K * (t - t₀)) ≤ C := by
    rw [hC_def]
    exact Real.exp_le_exp.mpr (by nlinarith [K.coe_nonneg, ht.1, ht.2])
  have : dist (φ (r + (t - t₀))) (ψ t) < ε := by
    calc dist (φ (r + (t - t₀))) (ψ t)
        = dist (φ (t + (r - t₀))) (ψ t) := by rw [show r + (t - t₀) = t + (r - t₀) by ring]
      _ ≤ dist (φ r) (ψ t₀) * Real.exp (K * (t - t₀)) := hcmp
      _ ≤ dist (φ r) (ψ t₀) * C := mul_le_mul_of_nonneg_left hexp dist_nonneg
      _ < (ε / C) * C := mul_lt_mul_of_pos_right (Metric.mem_ball.mp hr) hC_pos
      _ = ε := div_mul_cancel₀ ε hC_pos.ne'
  exact Metric.mem_ball.mpr this

/-! ## Lemma 1: V antitone on [0,∞) along trajectories -/

/-- `V(φ t)` is antitone on `[0, ∞)` when the Lie derivative `V̇ ≤ 0` on `Ω` and `φ` stays
    in `Ω`. -/
private lemma V_antitoneOn_lasalle
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω : Set ℝⁿ}
    (hV_c1 : ContDiff ℝ 1 V)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici 0))
    (hphi : ∀ t ≥ 0, φ t ∈ Ω) :
    AntitoneOn (V ∘ φ) (Set.Ici 0) :=
  antitoneOn_V_comp_traj (hV_c1.differentiable (by norm_num)) hV_c1.continuous
    (convex_Ici (0 : ℝ)) hφ fun t ht => by
      rw [interior_Ici] at ht
      exact hLie (φ t) (hphi t (le_of_lt ht))

/-! ## Lemma 2: V(φ t) converges to its infimum -/

/-- If `Ω` is compact and positively invariant and the Lie derivative `V̇ ≤ 0` on `Ω`,
    then `V(φ t)` converges to some limit `L` as `t → ∞`. -/
private lemma lasalle_V_tendsto
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω : Set ℝⁿ}
    (hV_c1 : ContDiff ℝ 1 V)
    (hΩ_compact : IsCompact Ω)
    (hΩ_inv : IsPositivelyInvariant Ω f)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici 0)) (hφ0 : φ 0 ∈ Ω) :
    ∃ L, Filter.Tendsto (V ∘ φ) Filter.atTop (nhds L) := by
  -- φ stays in Ω for all t ≥ 0
  have hphi : ∀ t ≥ 0, φ t ∈ Ω := fun t ht =>
    hΩ_inv 0 t φ (hφ.mono (fun r hr => hr.1)) hφ0 t ⟨ht, le_rfl⟩
  -- V(φ t) is antitone on [0, ∞)
  have hanti : AntitoneOn (V ∘ φ) (Set.Ici 0) := V_antitoneOn_lasalle hV_c1 hLie hφ hphi
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
private lemma V_const_on_omegaLimit
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
private lemma omegaLimit_subset_of_invariant
    {f : ℝⁿ → ℝⁿ} {Ω : Set ℝⁿ}
    (hΩ_compact : IsCompact Ω)
    (hΩ_inv : IsPositivelyInvariant Ω f)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici 0)) (hφ0 : φ 0 ∈ Ω) :
    omegaLimitTraj φ ⊆ Ω := by
  -- Ω is closed (compact in a Hausdorff space)
  have hΩ_closed : IsClosed Ω := hΩ_compact.isClosed
  -- φ t ∈ Ω for t ≥ 0
  have hphi : ∀ t ≥ 0, φ t ∈ Ω := fun t ht =>
    hΩ_inv 0 t φ (hφ.mono (fun r hr => hr.1)) hφ0 t ⟨ht, le_rfl⟩
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

/-! ## Lemma 5: the Lie derivative vanishes on the ω-limit set -/

/-- **`V̇ = 0` on `ω(φ)`.** This is where the four preceding lemmas combine: `V(φ t)` converges
    to some `L`, so `V ≡ L` on `ω(φ)`; `ω(φ)` is positively invariant, so the solution through
    an ω-limit point stays in `ω(φ)`, where `V` is constant; hence its derivative — which is
    exactly the Lie derivative `DV(y)[f(y)]` — vanishes.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), proof of Theorem 4.4. -/
@[blueprint "lem:lieDeriv-eq-zero-on-omegaLimitTraj"
  (statement := /-- Let $\Omega$ be compact and positively invariant for $\dot{x} = f(x)$ with
    $f$ of class $C^{1}$ and Lipschitz, let $V \in C^{1}$ satisfy $\dot{V} \le 0$ on $\Omega$,
    and let $\varphi$ be a solution on $[0,\infty)$ with $\varphi(0) \in \Omega$.  Then
    \[
      \dot{V}(y) = DV(y)\,[\,f(y)\,] = 0
      \qquad \text{for every } y \in \omega(\varphi).
    \]
    Equivalently $\omega(\varphi) \subseteq E = \{x : \dot{V}(x) = 0\}$. -/)
  (proof := /-- Along the trajectory $V$ is nonincreasing and bounded below on the compact set
    $\Omega$, so $V(\varphi(t)) \to L$ for some $L$; by continuity of $V$ every
    $\omega$-limit point sees that same value, so $V \equiv L$ on $\omega(\varphi)$.  Fix
    $y \in \omega(\varphi)$ and let $\psi$ solve $\dot{x} = f(x)$ on $[0,T]$, $T > 0$, with
    $\psi(0) = y$; such a $\psi$ exists because $f$ is $C^{1}$.  By
    \cref{lem:isPositivelyInvariant-omegaLimitTraj} the whole segment $\psi([0,T])$ lies in
    $\omega(\varphi)$, so $V \circ \psi \equiv L$ there.  A constant function has vanishing
    derivative, and the chain rule identifies that derivative at $0$ with
    $DV(\psi(0))[\dot\psi(0)] = DV(y)[f(y)]$.  Uniqueness of the derivative within $[0,T]$ at
    its left endpoint (valid because $T > 0$) gives $DV(y)[f(y)] = 0$. -/)]
theorem lieDeriv_eq_zero_on_omegaLimitTraj
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω : Set ℝⁿ} {K : NNReal}
    (hf_lip : LipschitzWith K f) (hf_c1 : ContDiff ℝ 1 f)
    (hV_c1 : ContDiff ℝ 1 V)
    (hΩ_compact : IsCompact Ω)
    (hΩ_inv : IsPositivelyInvariant Ω f)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici 0)) (hφ0 : φ 0 ∈ Ω) :
    ∀ y ∈ omegaLimitTraj φ, fderiv ℝ V y (f y) = 0 := by
  obtain ⟨L, hVL⟩ := lasalle_V_tendsto hV_c1 hΩ_compact hΩ_inv hLie hφ hφ0
  have hVconst := V_const_on_omegaLimit hV_c1.continuous hVL
  have hinv := isPositivelyInvariant_omegaLimitTraj hf_lip hφ
  intro y hy
  -- A solution through `y`, which stays in `ω(φ)` by invariance.
  obtain ⟨T, ψ, hT, hψ0, hψ⟩ := (hf_c1.contDiffAt (x := y)).exists_isIntegralCurveOn_Icc
  have hψ_mem : ∀ s ∈ Set.Icc 0 T, ψ s ∈ omegaLimitTraj φ :=
    hinv 0 T ψ hψ (hψ0 ▸ hy)
  -- `V ∘ ψ` is therefore constantly `L` on `[0, T]`, so its derivative at `0` is `0`.
  have hconst : ∀ s ∈ Set.Icc 0 T, (V ∘ ψ) s = L := fun s hs => hVconst _ (hψ_mem s hs)
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have hchain : HasDerivWithinAt (V ∘ ψ) (fderiv ℝ V (ψ 0) (f (ψ 0))) (Set.Icc 0 T) 0 :=
    (hV_c1.differentiable (by norm_num) (ψ 0)).hasFDerivAt.comp_hasDerivWithinAt 0 (hψ 0 hmem0)
  rw [hψ0] at hchain
  have hzero : HasDerivWithinAt (V ∘ ψ) 0 (Set.Icc 0 T) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) _ L).congr hconst (hconst 0 hmem0)
  exact (uniqueDiffOn_Icc hT 0 hmem0).eq_deriv _ hchain hzero

/-! ## Main theorem: LaSalle's invariance principle -/

/-- `E = {x ∈ Ω | V̇(x) = 0}`, the set where the Lie derivative of `V` along `f` vanishes.

LaSalle's principle localizes a trajectory's limiting behaviour inside this set: `V̇ ≤ 0` on `Ω`
says `V` never increases, and `E` is where it momentarily stops decreasing. -/
@[blueprint "def:lieDerivZeroSet"
  (statement := /-- For $\dot{x} = f(x)$, a function $V$ and a set $\Omega$, put
    \[
      E = \{x \in \Omega : \dot{V}(x) = DV(x)\,[\,f(x)\,] = 0\},
    \]
    the subset of $\Omega$ on which the Lie derivative of $V$ along $f$ vanishes. -/)]
def LieDerivZeroSet (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (Ω : Set ℝⁿ) : Set ℝⁿ :=
  {x ∈ Ω | fderiv ℝ V x (f x) = 0}

/-- LaSalle's invariance principle.

Let Ω be compact and positively invariant for ẋ = f(x), V : ℝⁿ → ℝ a C¹ Lyapunov function
with V̇(x) = DV(x)[f(x)] ≤ 0 on Ω, and M any set large enough to contain every positively
invariant subset of `LieDerivZeroSet f V Ω`. Then φ(t) → M. -/
@[blueprint "thm:lasalle-invariance-principle"
  (statement := /-- \textbf{LaSalle's invariance principle.}
    Let $\Omega$ be compact and positively invariant for $\dot{x} = f(x)$ with $f$ of class
    $C^{1}$ and Lipschitz, let $V \in C^{1}$ satisfy $\dot{V}(x) \le 0$ on $\Omega$, and put
    \[
      E = \{x \in \Omega : \dot{V}(x) = 0\}
    \]
    (\cref{def:lieDerivZeroSet}).  Let $M$ contain every positively invariant subset of $E$.
    Then every trajectory $\varphi$ on $[0,\infty)$ starting in $\Omega$ satisfies
    $\varphi(t) \to M$ as $t \to \infty$.

    Khalil takes $M$ to be the largest \emph{invariant} subset of $E$.  Here $M$ must absorb
    every \emph{positively} invariant subset, which is a larger family, so the hypothesis on
    $M$ is correspondingly stronger; what is proved about $\omega(\varphi)$ is forward
    invariance (\cref{lem:isPositivelyInvariant-omegaLimitTraj}), and backward invariance would
    require solutions through every $\omega$-limit point to extend backwards in time. -/)
  (proof := /-- The $\omega$-limit set lies in $\Omega$, because $\Omega$ is closed and
    $\varphi$ stays in it, and $\dot{V}$ vanishes on it
    (\cref{lem:lieDeriv-eq-zero-on-omegaLimitTraj}); hence
    $\omega(\varphi) \subseteq E$.  It is positively invariant by
    \cref{lem:isPositivelyInvariant-omegaLimitTraj}, so the hypothesis on $M$ gives
    $\omega(\varphi) \subseteq M$.  Finally, a trajectory confined to a compact set converges
    to its own $\omega$-limit set: for any open $W \supseteq M \supseteq \omega(\varphi)$,
    $\varphi$ is eventually in $W$. -/)]
theorem lasalle_invariance_principle
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω M : Set ℝⁿ} {K : NNReal}
    (hΩ_compact : IsCompact Ω)
    (hΩ_inv : IsPositivelyInvariant Ω f)
    (hf_lip : LipschitzWith K f)
    (hf_c1 : ContDiff ℝ 1 f)
    (hV_c1 : ContDiff ℝ 1 V)
    -- V̇(x) = DV(x)[f(x)] ≤ 0 on Ω
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici 0)) (hφ0 : φ 0 ∈ Ω)
    -- `M` is any set absorbing the positively invariant subsets of `E = {x ∈ Ω | V̇ x = 0}`.
    (hM : ∀ N ⊆ LieDerivZeroSet f V Ω, IsPositivelyInvariant N f → N ⊆ M) :
    Filter.Tendsto φ Filter.atTop (𝓝ˢ M) := by
  -- ω(φ) ⊆ E: it lies in Ω, and V̇ vanishes on it.
  have hω_sub_E : omegaLimitTraj φ ⊆ LieDerivZeroSet f V Ω := fun y hy =>
    ⟨omegaLimit_subset_of_invariant hΩ_compact hΩ_inv hφ hφ0 hy,
      lieDeriv_eq_zero_on_omegaLimitTraj hf_lip hf_c1 hV_c1 hΩ_compact hΩ_inv hLie hφ hφ0 y hy⟩
  -- ω(φ) is positively invariant, so `M` absorbs it.
  have hω_sub_M : omegaLimitTraj φ ⊆ M :=
    hM _ hω_sub_E (isPositivelyInvariant_omegaLimitTraj hf_lip hφ)
  -- φ stays in Ω for t ≥ 0
  have hphi_in_Ω : ∀ t ≥ 0, φ t ∈ Ω := fun t ht =>
    hΩ_inv 0 t φ (hφ.mono (fun r hr => hr.1)) hφ0 t ⟨ht, le_rfl⟩
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

/-! ## Barbashin–Krasovskii theorems -/

/-- Barbashin's theorem: local asymptotic stability via LaSalle.
    `V` C¹ and positive definite on `D`, `V̇ ≤ 0` on `D`, a compact positively invariant
    sublevel set `Ωc ⊆ D`, and `{x_eq}` the only positively invariant subset of
    `LieDerivZeroSet f V Ωc`.

    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Corollary 4.1. -/
@[blueprint "thm:lasalle-local-asymptotic-stable"
  (statement := /-- \textbf{Barbashin's theorem.}
    Let $V \in C^{1}$ be a local Lyapunov function for $\dot{x} = f(x)$ on a domain $D$
    (\cref{def:isLocalLyapunovFunction}).  Suppose for some $c > 0$ the sublevel set
    $\Omega_{c} = \{V \le c\}$ is contained in $D$, compact, and positively invariant, that
    $f$ is $C^{1}$ and Lipschitz, and that $\{x_{\mathrm{eq}}\}$ is the only positively
    invariant subset of $E = \{x \in \Omega_{c} : \dot{V}(x) = 0\}$
    (\cref{def:lieDerivZeroSet}).  Then $x_{\mathrm{eq}}$ is locally asymptotically stable
    (\cref{def:localAsymptoticStable}).

    The hypothesis on $E$ is the one a user of LaSalle actually discharges: solve
    $\dot{V} = 0$ and check that no solution can stay there but the equilibrium.  Positive
    invariance of $\Omega_{c}$ is a hypothesis rather than a consequence of $\dot{V} \le 0$:
    deducing it would need a solution through each point of $\Omega_{c}$. -/)]
theorem lasalle_local_asymptotic_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV_c1 : ContDiff ℝ 1 V)
    (hV_local : IsLocalLyapunovFunction f V x_eq D)
    {c : ℝ} (hc_pos : 0 < c)
    (hΩ_sub_D : SublevelSet V c ⊆ D)
    (hΩ_compact : IsCompact (SublevelSet V c))
    (hΩ_inv : IsPositivelyInvariant (SublevelSet V c) f)
    {K : NNReal} (hf_lip : LipschitzWith K f) (hf_c1 : ContDiff ℝ 1 f)
    -- `{x_eq}` is the only positively invariant set on which `V̇` vanishes.
    (hLasalle : ∀ N ⊆ LieDerivZeroSet f V (SublevelSet V c),
                  IsPositivelyInvariant N f → N ⊆ {x_eq}) :
    LocalAsymptoticStable f x_eq := by
  refine ⟨lyapunov_stable hn hV_local, ?_⟩
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hV_local.hcont.continuousAt c hc_pos
  refine ⟨δ, hδ_pos, fun t₀ φ hφ hφ0 => ?_⟩
  -- re-anchor the solution at `0`, where the LaSalle machinery lives
  have hψ : IsIntegralCurveOn (fun s => φ (s + t₀)) (fun _ x => f x) (Set.Ici 0) := by
    have hset : -t₀ +ᵥ Set.Ici t₀ = Set.Ici (0 : ℝ) := by
      ext x
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg, Set.mem_Ici]
      constructor <;> intro h <;> linarith
    have h := hφ.comp_add_autonomous t₀
    rwa [hset] at h
  have hV0 : V (φ (0 + t₀)) < c := by
    have h := hδ (show dist (φ t₀) x_eq < δ by rw [dist_eq_norm]; exact hφ0)
    rw [Real.dist_eq, hV_local.hzero, sub_zero] at h
    simpa using (abs_lt.mp h).2
  have hψ0_in : (fun s => φ (s + t₀)) 0 ∈ SublevelSet V c := le_of_lt hV0
  have hconv := lasalle_invariance_principle hΩ_compact hΩ_inv hf_lip hf_c1 hV_c1
    (fun x hx => hV_local.hLie_nonpos x (hΩ_sub_D hx)) hψ hψ0_in hLasalle
  rw [nhdsSet_singleton] at hconv
  exact Filter.Tendsto.congr (fun x => by simp)
    (hconv.comp (Filter.tendsto_atTop_add_const_right Filter.atTop (-t₀) Filter.tendsto_id))

/-- Krasovskii's theorem: global asymptotic stability via LaSalle.
    `V` C¹, positive definite, radially unbounded, `V̇ ≤ 0` on `ℝⁿ`, and `{x_eq}` the only
    positively invariant subset of `LieDerivZeroSet f V Ωc` for every sublevel set `Ωc`.

    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Corollary 4.2. -/
@[blueprint "thm:lasalle-global-asymptotic-stable"
  (statement := /-- \textbf{Krasovskii's theorem.}
    If $V \in C^{1}$ is positive definite, $\dot{V} \le 0$ on $\mathbb{R}^{n}$ and radially
    unbounded, $f$ is $C^{1}$ and Lipschitz, and for every $c$ the only positively invariant
    subset of $E_{c} = \{x \in \Omega_{c} : \dot{V}(x) = 0\}$ (\cref{def:lieDerivZeroSet})
    is $\{x_{\mathrm{eq}}\}$, then $x_{\mathrm{eq}}$ is globally asymptotically stable
    (\cref{def:globalAsymptoticStable}).

    Unlike Barbashin's theorem (\cref{thm:lasalle-local-asymptotic-stable}) no positively
    invariant set is assumed: radial unboundedness makes every sublevel set compact, and
    $\dot{V} \le 0$ then keeps the trajectory inside the one through its initial state. -/)]
theorem lasalle_global_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV_c1 : ContDiff ℝ 1 V)
    (hzero : V x_eq = 0)
    (hpos : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x)
    (hLie : ∀ x : ℝⁿ, fderiv ℝ V x (f x) ≤ 0)
    (hradial : Filter.Tendsto V (Filter.comap norm Filter.atTop) Filter.atTop)
    {K : NNReal} (hf_lip : LipschitzWith K f) (hf_c1 : ContDiff ℝ 1 f)
    -- `{x_eq}` is the only positively invariant set on which `V̇` vanishes.
    (hLasalle : ∀ c : ℝ, ∀ N ⊆ LieDerivZeroSet f V (SublevelSet V c),
                  IsPositivelyInvariant N f → N ⊆ {x_eq}) :
    GlobalAsymptoticStable f x_eq := by
  have hV_local : IsLocalLyapunovFunction f V x_eq Set.univ :=
    { hD_open := isOpen_univ
      hD_mem := Set.mem_univ _
      hcont := hV_c1.continuous
      hV_diff := hV_c1.differentiable (by norm_num)
      hzero := hzero
      hpos := fun x _ hx => hpos x hx
      hLie_nonpos := fun x _ => hLie x }
  refine ⟨lyapunov_stable hn hV_local, fun t₀ φ hφ => ?_⟩
  have hψ : IsIntegralCurveOn (fun s => φ (s + t₀)) (fun _ x => f x) (Set.Ici 0) := by
    have hset : -t₀ +ᵥ Set.Ici t₀ = Set.Ici (0 : ℝ) := by
      ext x
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg, Set.mem_Ici]
      constructor <;> intro h <;> linarith
    have h := hφ.comp_add_autonomous t₀
    rwa [hset] at h
  set c := V ((fun s => φ (s + t₀)) 0) with hc_def
  have hΩ_compact : IsCompact (SublevelSet V c) :=
    isCompact_sublevel_set V hV_c1.continuous hradial c
  have hΩ_inv : IsPositivelyInvariant (SublevelSet V c) f := by
    intro s₀ s₁ ξ hξ hξ0 t ht
    exact le_trans (V_nonincreasing_on hV_local
      (hξ.mono (Set.Icc_subset_Icc_right ht.2)) ht.1 (fun _ _ => Set.mem_univ _)) hξ0
  have hψ0_in : (fun s => φ (s + t₀)) 0 ∈ SublevelSet V c := by
    simp [SublevelSet, hc_def]
  have hconv := lasalle_invariance_principle hΩ_compact hΩ_inv hf_lip hf_c1 hV_c1
    (fun x _ => hLie x) hψ hψ0_in (hLasalle c)
  rw [nhdsSet_singleton] at hconv
  exact Filter.Tendsto.congr (fun x => by simp)
    (hconv.comp (Filter.tendsto_atTop_add_const_right Filter.atTop (-t₀) Filter.tendsto_id))

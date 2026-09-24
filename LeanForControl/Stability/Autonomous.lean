import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import LeanForControl.ODEs.ODE_properties
import LeanForControl.Stability.DefsAutonomous
import LeanForControl.Stability.LyapunovIndirect.DefsForward
import Architect

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-!
# `Stability.Autonomous`

Lyapunov stability theorems for autonomous ODEs `ẋ = f(x)` on `ℝⁿ`.

## Main results

* **Lyapunov's stability theorem** (`lyapunov_stable`): `IsLocalLyapunovFunction` implies
  `LyapunovStable`.
* **Lyapunov's global asymptotic stability theorem** (`lyapunov_asymptotic_stable`):
  `IsStrictLyapunovFunction` implies `GlobalAsymptoticStable`.
* **Corollary** (`lyapunov_global_asymptotic_stable`): `IsAsymptoticLyapunovFunction` implies
  `GlobalAsymptoticStable` (the classical radially-unbounded form of the theorem).
* **Lyapunov's local asymptotic stability theorem** (`lyapunov_local_asymptotic_stable`):
  `IsStrictLocalLyapunovFunction` implies `LocalAsymptoticStable`.

## Proof strategy

The proofs follow the classical Lyapunov stability arguments (Khalil, *Nonlinear Systems*,
3rd ed.):
1. **Lyapunov stability**: first-exit-time argument using monotonicity of `V ∘ φ` on `[0, T*]`
   and a minimum-on-sphere lower bound.
2. **GAS**: monotone convergence `V(φ t) → L`, then `L = 0` via a compact-sublevel-set
   linear-bound contradiction, then `φ t → x_eq` via the EVT minimum on `{V ≥ γ}`.
3. **LAS**: same as GAS but restricted to a compact sublevel set `{V ≤ c₀} ⊆ D`.
-/

/-! ## Infrastructure -/

/-- Chain rule for `V ∘ φ`: if `φ` is a trajectory of `f` and `V` is differentiable, then
    `(V ∘ φ)'(t) = DV(φ(t))[f(φ(t))]`. -/
lemma hasDerivAt_V_comp_traj
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ V)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f) (t : ℝ) :
    HasDerivAt (V ∘ φ) (fderiv ℝ V (φ t) (f (φ t))) t :=
  (hV_diff (φ t)).hasFDerivAt.comp_hasDerivAt t (htraj t)

/-- A trajectory `φ` of `ẋ = f(x)` is continuous (differentiability implies continuity). -/
lemma trajectory_continuous
    {f : ℝⁿ → ℝⁿ} {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f) :
    Continuous φ :=
  continuous_iff_continuousAt.mpr fun t => (htraj t).differentiableAt.continuousAt

/-- The sphere `Metric.sphere x_eq ε` is nonempty when `0 < n` and `0 < ε`. -/
lemma sphere_nonempty
    (x_eq : ℝⁿ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (Metric.sphere x_eq ε).Nonempty := by
  refine ⟨x_eq + EuclideanSpace.single (⟨0, hn⟩ : Fin n) ε, ?_⟩
  rw [Metric.mem_sphere, dist_eq_norm]
  simp [PiLp.norm_single, abs_of_pos hε]

/-- The Lie derivative `x ↦ DV(x)[f(x)]` is continuous when `V` is C¹ and `f` is continuous. -/
lemma lie_deriv_continuous
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_c1 : ContDiff ℝ 1 V) (hf_cont : Continuous f) :
    Continuous (fun x : ℝⁿ => fderiv ℝ V x (f x)) :=
  (hV_c1.continuous_fderiv (by norm_num)).clm_apply hf_cont

/-- If `φ` stays in a compact set `K ⊆ D` on which the Lie derivative satisfies
    `DV(x)[f(x)] ≤ −γ < 0`, then `V(φ t) + γ · t ≤ V(φ 0)` for all `t ≥ 0`.
    Used to derive the linear-decay contradiction in the GAS proofs. -/
lemma V_plus_linear_bound
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ V) (hV_cont : Continuous V)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f)
    {K : Set ℝⁿ} (hphi_in_K : ∀ t ≥ 0, φ t ∈ K)
    {γ : ℝ} (_hγ_pos : 0 < γ)
    (hLie_le : ∀ x ∈ K, fderiv ℝ V x (f x) ≤ -γ) :
    ∀ t ≥ 0, V (φ t) + γ * t ≤ V (φ 0) := by
  have hanti_sum : AntitoneOn (fun t => V (φ t) + γ * t) (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ))
    · exact (hV_cont.comp_continuousOn (trajectory_continuous htraj).continuousOn).add
        (continuous_const.mul continuous_id).continuousOn
    · exact fun t _ => ((hasDerivAt_V_comp_traj hV_diff htraj t).add
        ((hasDerivAt_id t).const_mul γ)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have hd : HasDerivAt (fun s => V (φ s) + γ * s)
          (fderiv ℝ V (φ t) (f (φ t)) + γ * 1) t :=
        (hasDerivAt_V_comp_traj hV_diff htraj t).add ((hasDerivAt_id t).const_mul γ)
      rw [hd.deriv]
      linarith [hLie_le (φ t) (hphi_in_K t (le_of_lt ht))]
  intro t ht
  simpa using hanti_sum (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht

/-! ## Monotonicity of V along trajectories -/

/-- `V` is nonincreasing on `[t₀, t₁]` when the solution segment stays in `D` on that
    interval and the Lie derivative is nonpositive on `D`.

    Proof: `(V ∘ φ)'(t) = DV(φ(t))[f(φ(t))] ≤ 0` by `hLie_nonpos`,
    then `antitoneOn_of_deriv_nonpos` applies. -/
lemma V_nonincreasing_on
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq D)
    {φ : ℝ → ℝⁿ} {t₀ t₁ : ℝ}
    (hφ : IsTrajectoryOn φ f t₀ t₁)
    (hle : t₀ ≤ t₁)
    (hstay : ∀ t ∈ Set.Icc t₀ t₁, φ t ∈ D) :
    V (φ t₁) ≤ V (φ t₀) := by
  have hderiv : ∀ t ∈ Set.Ioo t₀ t₁, HasDerivAt φ (f (φ t)) t := fun t ht =>
    (hφ t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hanti : AntitoneOn (V ∘ φ) (Set.Icc t₀ t₁) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t₀ t₁)
    · exact hV.hcont.comp_continuousOn hφ.continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hV.hV_diff (φ t)).hasFDerivAt.comp_hasDerivAt t (hderiv t ht)).differentiableAt
        |>.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [((hV.hV_diff (φ t)).hasFDerivAt.comp_hasDerivAt t (hderiv t ht)).deriv]
      exact hV.hLie_nonpos (φ t) (hstay t (Set.Ioo_subset_Icc_self ht))
  exact hanti (Set.left_mem_Icc.mpr hle) (Set.right_mem_Icc.mpr hle) hle

/-- Convenience wrapper for `V_nonincreasing_on` when `D = Set.univ` (used by GAS proofs). -/
lemma V_nonincreasing
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq Set.univ)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f) :
    Antitone (V ∘ φ) :=
  fun _ _ hab =>
    V_nonincreasing_on hV (fun t _ => (htraj t).hasDerivWithinAt) hab
      (fun _ _ => Set.mem_univ _)

/-- `V(φ t) ≤ V(φ 0)` for all `t ≥ 0` when the Lyapunov conditions hold globally
    (`D = Set.univ`). -/
lemma V_le_initial
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq Set.univ)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f)
    {t : ℝ} (ht : 0 ≤ t) : V (φ t) ≤ V (φ 0) :=
  V_nonincreasing hV htraj ht

/-! ## Lyapunov function hierarchy -/

/-- `IsStrictLyapunovFunction` implies `IsLocalLyapunovFunction` on `Set.univ`.

    The equilibrium case uses `fderiv ℝ V x_eq (f x_eq) = fderiv ℝ V x_eq 0 = 0`
    (zero map of a continuous linear map). -/
lemma strict_implies_semidefinite
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLyapunovFunction f V x_eq) :
    IsLocalLyapunovFunction f V x_eq Set.univ where
  hD_open     := isOpen_univ
  hD_mem      := Set.mem_univ _
  hcont       := hV.hcont
  hV_diff     := hV.hV_c1.differentiable (by norm_num)
  hzero       := hV.hzero
  hpos        := fun x _ hx => hV.hpos x hx
  hLie_nonpos := fun x _ => by
    by_cases hx : x = x_eq
    · simp only [hx, hV.hequil, map_zero, le_refl]
    · exact le_of_lt (hV.hLie_neg x hx)

/-- `IsAsymptoticLyapunovFunction` implies `IsStrictLyapunovFunction`.
    Uses `isCompact_sublevel_set` to convert radial unboundedness into compact sublevel sets. -/
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
  hbounded_sublevel := isCompact_sublevel_set V hV.hcont hV.hradial

/-- `IsStrictLocalLyapunovFunction` implies `IsLocalLyapunovFunction` (on the same `D`).
    The equilibrium satisfies `Lie ≤ 0` trivially since `f(x_eq) = 0`. -/
lemma strict_local_implies_semidefinite
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLocalLyapunovFunction f V x_eq D) :
    IsLocalLyapunovFunction f V x_eq D where
  hD_open     := hV.hD_open
  hD_mem      := hV.hD_mem
  hcont       := hV.hcont
  hV_diff     := hV.hV_c1.differentiable (by norm_num)
  hzero       := hV.hzero
  hpos        := hV.hpos
  hLie_nonpos := fun x hxD => by
    by_cases hx : x = x_eq
    · simp only [hx, hV.hequil, map_zero, le_refl]
    · exact le_of_lt (hV.hLie_neg x hxD hx)

/-! ## Forward invariance of sublevel sets -/

/-- If `{V ≤ c} ⊆ D` and `V(φ 0) < c`, then `V(φ t) < c` for all `t ≥ 0`.

Proof by contradiction via a first-exit-time argument:
1. Let `S = {t ≥ 0 | c ≤ V(φ t)}`. If nonempty, let `T* = sInf S`.
2. `T* > 0`: `V(φ 0) < c` so `0 ∉ S`; `S` closed, so `T* ∉ {0}`.
3. `T* ∈ S` (`S` is closed).
4. For `t ∈ [0, T*)`: `V(φ t) < c` by minimality, so `φ t ∈ {V < c} ⊆ D`.
5. `V_nonincreasing_on` on `[0, T*]` gives `V(φ T*) ≤ V(φ 0) < c`.
6. But `T* ∈ S` means `c ≤ V(φ T*)`. Contradiction. -/
lemma sublevel_set_invariant
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq D)
    {φ : ℝ → ℝⁿ} {t₀ t₁ : ℝ} (hφ : IsTrajectoryOn φ f t₀ t₁)
    {c : ℝ} (hΩ_sub_D : SublevelSet V c ⊆ D)
    (h0 : V (φ t₀) < c) :
    ∀ t ∈ Set.Icc t₀ t₁, V (φ t) < c := by
  have hcont : ContinuousOn (V ∘ φ) (Set.Icc t₀ t₁) :=
    hV.hcont.comp_continuousOn hφ.continuousOn
  intro t ht
  by_contra hge
  push Not at hge
  set S := Set.Icc t₀ t₁ ∩ (V ∘ φ) ⁻¹' (Set.Ici c) with hS_def
  have hS_nonempty : S.Nonempty := ⟨t, ht, hge⟩
  have hS_bddBelow : BddBelow S := ⟨t₀, fun s hs => hs.1.1⟩
  have hS_closed : IsClosed S :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  set T := sInf S with hT_def
  have hT_mem : T ∈ S := hS_closed.csInf_mem hS_nonempty hS_bddBelow
  have hT_ge_c : c ≤ V (φ T) := hT_mem.2
  have hT_gt : t₀ < T := by
    rcases lt_or_eq_of_le hT_mem.1.1 with h | h
    · exact h
    · exact absurd hT_ge_c (by rw [← h] at hT_ge_c ⊢; linarith)
  have hlt_of_lt : ∀ s : ℝ, t₀ ≤ s → s < T → V (φ s) < c := by
    intro s hs_nonneg hs_lt
    by_contra h
    push Not at h
    exact absurd (csInf_le hS_bddBelow
      ⟨⟨hs_nonneg, le_of_lt (lt_of_lt_of_le hs_lt hT_mem.1.2)⟩, h⟩) (not_le.mpr hs_lt)
  have hVs_le : ∀ s : ℝ, t₀ ≤ s → s < T → V (φ s) ≤ V (φ t₀) := by
    intro s hs_nonneg hs_lt
    have hsub : Set.Icc t₀ s ⊆ Set.Icc t₀ t₁ :=
      Set.Icc_subset_Icc_right (le_of_lt (lt_of_lt_of_le hs_lt hT_mem.1.2))
    exact V_nonincreasing_on hV (hφ.mono hsub) hs_nonneg fun r hr =>
      hΩ_sub_D (le_of_lt (hlt_of_lt r hr.1 (lt_of_le_of_lt hr.2 hs_lt)))
  haveI hNeBot : (nhdsWithin T (Set.Ico t₀ T)).NeBot := by
    rw [nhdsWithin_Ico_eq_nhdsLT hT_gt]
    exact nhdsLT_neBot_of_exists_lt ⟨t₀, hT_gt⟩
  have hVs_bound : ∀ᶠ s in nhdsWithin T (Set.Ico t₀ T), (V ∘ φ) s ≤ V (φ t₀) :=
    eventually_nhdsWithin_of_forall (fun s hs => hVs_le s hs.1 hs.2)
  have hTwithin : ContinuousWithinAt (V ∘ φ) (Set.Ico t₀ T) T :=
    (hcont T hT_mem.1).mono (fun r hr => ⟨hr.1, le_of_lt (lt_of_lt_of_le hr.2 hT_mem.1.2)⟩)
  have hVT_le : V (φ T) ≤ V (φ t₀) := le_of_tendsto hTwithin hVs_bound
  linarith

/-! ## Lyapunov stability -/

/-- Time invariance lifts the anchored-at-zero form of forward Lyapunov stability to the
anchor-free predicate, so a first-exit argument may be run at the origin and transported. -/
lemma forwardLyapunovStable_of_anchored_zero {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (h : ∀ ε > 0, ∃ δ > 0, ∀ (t₁ : ℝ) (φ : ℝ → ℝⁿ),
      IsTrajectoryOn φ f 0 t₁ → ‖φ 0 - x_eq‖ < δ →
        ∀ t ∈ Set.Icc 0 t₁, ‖φ t - x_eq‖ < ε) :
    ForwardLyapunovStable f x_eq := by
  intro ε hε
  obtain ⟨δ, hδ, hbase⟩ := h ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t₀ t₁ φ hφ hφ0 t ht
  have hψ0 : ‖(fun s => φ (s + t₀)) 0 - x_eq‖ < δ := by simpa using hφ0
  have hmem : t - t₀ ∈ Set.Icc 0 (t₁ - t₀) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simpa using hbase (t₁ - t₀) (fun s => φ (s + t₀)) hφ.shift_to_zero hψ0 (t - t₀) hmem

open Set in
/-- **Lyapunov's stability theorem.** If `V` is a local Lyapunov function on `D`, then
    `x_eq` is stable with respect to every finite forward solution segment.

Proof sketch:
1. `D` open + `x_eq ∈ D` → `closedBall x_eq ε₀ ⊆ D` for some `ε₀ > 0`.
2. `m = min V` on `sphere x_eq ε' > 0` (compact sphere, `V > 0` away from `x_eq`).
3. Find `δ` with `V(y) < m` for `‖y − x_eq‖ < δ` (continuity at `x_eq`, `V(x_eq) = 0`).
4. If `‖φ 0 − x_eq‖ < δ` and `‖φ t* − x_eq‖ ≥ ε` for some `t*`, let `T* = sInf Q`
   where `Q = {t ≥ 0 | ε' ≤ ‖φ t − x_eq‖}`.
5. `V_nonincreasing_on` on `[0, T*]` gives `V(φ T*) ≤ V(φ 0) < m ≤ V(φ T*)`. Contradiction.

The first-exit argument runs on segments anchored at `0`; time invariance, via
`forwardLyapunovStable_of_anchored_zero`, carries it to segments anchored anywhere. -/
@[blueprint "thm:lyapunov-stable"
  (statement := /-- \textbf{Lyapunov's stability theorem.}
    If $V$ is a local Lyapunov function (\cref{def:isLocalLyapunovFunction}) for
    $\dot{x} = f(x)$ on a domain $D \ni x_{\mathrm{eq}}$, then $x_{\mathrm{eq}}$
    is stable on every finite forward solution segment
    (\cref{def:forwardLyapunovStable}). -/)
  (proof := /-- Pick $\varepsilon_{0}$ so $\overline{B}(x_{\mathrm{eq}},\varepsilon_{0})
    \subseteq D$. Let $m = \min_{S_{\varepsilon'}} V > 0$. Choose $\delta$ with
    $V < m$ on $B(x_{\mathrm{eq}},\delta)$. If $\|\varphi(t^{*})-x_{\mathrm{eq}}\|
    \ge \varepsilon$, monotonicity of $V$ gives $V(\varphi(t^{*})) \le V(\varphi(0))
    < m \le V(\varphi(t^{*}))$, a contradiction. -/)]
theorem lyapunov_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsLocalLyapunovFunction f V x_eq D) :
    ForwardLyapunovStable f x_eq := by
  apply forwardLyapunovStable_of_anchored_zero
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp hV.hD_open x_eq hV.hD_mem
  set ε₀ := r / 2
  have hε₀_pos : 0 < ε₀ := by dsimp [ε₀]; linarith
  have hcBall_sub_D : Metric.closedBall x_eq ε₀ ⊆ D := by
    intro x hx
    apply hr_ball
    rw [Metric.mem_ball, Metric.mem_closedBall] at *
    dsimp [ε₀] at *
    linarith
  intro ε hε
  set ε' := min ε ε₀
  have hε'_pos : 0 < ε' := lt_min hε hε₀_pos
  have hε'_le_ε : ε' ≤ ε := min_le_left _ _
  have hcBall'_sub_D : Metric.closedBall x_eq ε' ⊆ D :=
    (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans hcBall_sub_D
  have hsphere'_sub_D : Metric.sphere x_eq ε' ⊆ D :=
    Metric.sphere_subset_closedBall.trans hcBall'_sub_D
  obtain ⟨x_min, hx_min_mem, hx_min_le⟩ :=
    (isCompact_sphere x_eq ε').exists_isMinOn
      (sphere_nonempty x_eq hn hε'_pos) hV.hcont.continuousOn
  set m := V x_min
  have hm_pos : 0 < m := by
    apply hV.hpos x_min (hsphere'_sub_D hx_min_mem)
    intro heq
    have hx := hx_min_mem
    rw [heq, Metric.mem_sphere, dist_self] at hx
    exact (ne_of_gt hε'_pos) hx.symm
  have hV_cont_at : ContinuousAt V x_eq := hV.hcont.continuousAt
  rw [Metric.continuousAt_iff] at hV_cont_at
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hV_cont_at m hm_pos
  set δ := min δ₀ ε'
  refine ⟨δ, lt_min hδ₀_pos hε'_pos, ?_⟩
  intro t₁ φ hφ hφ0 t ht
  have hφ0ε' : ‖φ 0 - x_eq‖ < ε' := hφ0.trans_le (min_le_right _ _)
  have hV0_lt_m : V (φ 0) < m := by
    have hnear : dist (V (φ 0)) (V x_eq) < m := hδ₀ (by
      rw [dist_eq_norm]
      exact hφ0.trans_le (min_le_left _ _))
    simp only [Real.dist_eq, hV.hzero, sub_zero] at hnear
    exact (abs_lt.mp hnear).2
  by_contra hnot
  push Not at hnot
  have hge_ε' : ε' ≤ ‖φ t - x_eq‖ := hε'_le_ε.trans hnot
  set Q := {s : ℝ | s ∈ Icc (0 : ℝ) t ∧ ε' ≤ ‖φ s - x_eq‖}
  have hQ_nonempty : Q.Nonempty := ⟨t, ⟨ht.1, le_rfl⟩, hge_ε'⟩
  have hQ_bddBelow : BddBelow Q := ⟨0, fun s hs => hs.1.1⟩
  have hφ_cont : ContinuousOn (fun s => ‖φ s - x_eq‖) (Icc (0 : ℝ) t) :=
    (continuous_norm.comp_continuousOn
      ((hφ.continuousOn.mono (Icc_subset_Icc le_rfl ht.2)).sub continuousOn_const))
  have hQ_closed : IsClosed Q := by
    exact isClosed_Icc.isClosed_le continuousOn_const hφ_cont
  set Tstar := sInf Q
  have hTstar_mem : Tstar ∈ Q := hQ_closed.csInf_mem hQ_nonempty hQ_bddBelow
  have hTstar_pos : 0 < Tstar := by
    rcases lt_or_eq_of_le hTstar_mem.1.1 with hpos | hzero
    · exact hpos
    · exact False.elim ((not_le_of_gt hφ0ε') (by simpa [hzero] using hTstar_mem.2))
  have hlt_ε' : ∀ s : ℝ, 0 ≤ s → s < Tstar → ‖φ s - x_eq‖ < ε' := by
    intro s hs0 hsT
    by_contra hs
    push Not at hs
    have hs_le_t : s ≤ t := (le_of_lt hsT).trans hTstar_mem.1.2
    exact (not_le_of_gt hsT) (csInf_le hQ_bddBelow ⟨⟨hs0, hs_le_t⟩, hs⟩)
  have hTstar_eq : ‖φ Tstar - x_eq‖ = ε' := by
    apply le_antisymm _ hTstar_mem.2
    by_contra hlt
    push Not at hlt
    have hcont_sub : ContinuousOn (fun s => ‖φ s - x_eq‖) (Icc (0 : ℝ) Tstar) :=
      hφ_cont.mono (Icc_subset_Icc le_rfl hTstar_mem.1.2)
    obtain ⟨s₀, hs₀_mem, hs₀_val⟩ :=
      intermediate_value_Icc (le_of_lt hTstar_pos) hcont_sub
        ⟨le_of_lt hφ0ε', le_of_lt hlt⟩
    have hs₀_ge : Tstar ≤ s₀ := csInf_le hQ_bddBelow
      ⟨⟨hs₀_mem.1, hs₀_mem.2.trans hTstar_mem.1.2⟩, ge_of_eq hs₀_val⟩
    have hs₀_eq : s₀ = Tstar := le_antisymm hs₀_mem.2 hs₀_ge
    exact (not_lt_of_ge (le_of_eq (hs₀_eq ▸ hs₀_val))) hlt
  have hstay : ∀ s ∈ Icc (0 : ℝ) Tstar, φ s ∈ D := by
    intro s hs
    apply hcBall'_sub_D
    rw [Metric.mem_closedBall, dist_eq_norm]
    rcases eq_or_lt_of_le hs.2 with heq | hlt
    · subst s
      exact le_of_eq hTstar_eq
    · exact le_of_lt (hlt_ε' s hs.1 hlt)
  have hVT_le : V (φ Tstar) ≤ V (φ 0) :=
    V_nonincreasing_on hV (hφ.mono (Icc_subset_Icc_right (hTstar_mem.1.2.trans ht.2)))
      (le_of_lt hTstar_pos) hstay
  have hVT_ge : m ≤ V (φ Tstar) :=
    hx_min_le (by rw [Metric.mem_sphere, dist_eq_norm]; exact hTstar_eq)
  linarith

/-! ## Shared limit lemmas -/

/-- If `φ t` stays in a compact set `K ⊆ D` where the Lie derivative is strictly negative and
    `L ≤ V(φ t)` for all `t ≥ 0`, then `L = 0`.

    Proof: if `L > 0`, pick `K = {L/2 ≤ V} ∩ SublevelSet V c₀` (compact). The Lie derivative
    attains its maximum `−γ < 0` on `K` (EVT), giving `V(φ t) + γ · t ≤ V(φ 0)`.
    For large `t`, this forces `V(φ t) < L/2`, contradicting `L ≤ V(φ t)`. -/
lemma V_limit_zero_of_compact
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ}
    (hcont : Continuous V) (hV_c1 : ContDiff ℝ 1 V)
    (hzero : V x_eq = 0)
    (hLie_neg : ∀ x ∈ D, x ≠ x_eq → fderiv ℝ V x (f x) < 0)
    (hf_cont : Continuous f)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f)
    {c₀ : ℝ} (hSub_sub_D : SublevelSet V c₀ ⊆ D) (hSub_compact : IsCompact (SublevelSet V c₀))
    (hphi0_le : V (φ 0) ≤ c₀)
    (hanti : AntitoneOn (V ∘ φ) (Set.Ici 0))
    {L : ℝ} (hL_nonneg : 0 ≤ L) (hVt_ge_L : ∀ t ≥ 0, L ≤ V (φ t)) :
    L = 0 := by
  by_contra hL_ne
  have hL_pos : 0 < L := lt_of_le_of_ne hL_nonneg (Ne.symm hL_ne)
  set K := {x : ℝⁿ | L / 2 ≤ V x} ∩ SublevelSet V c₀
  have hK_compact : IsCompact K :=
    hSub_compact.of_isClosed_subset
      ((isClosed_Ici.preimage hcont).inter (isClosed_Iic.preimage hcont))
      (fun x ⟨_, hVx⟩ => hVx)
  have hK_sub_D : K ⊆ D := fun x hxK => hSub_sub_D hxK.2
  have hphi_mem_K : ∀ t ≥ 0, φ t ∈ K := fun t ht =>
    ⟨le_trans (by linarith) (hVt_ge_L t ht),
     (hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht).trans hphi0_le⟩
  have hK_nonempty : K.Nonempty := ⟨φ 0, hphi_mem_K 0 le_rfl⟩
  have hLie_neg_K : ∀ x ∈ K, fderiv ℝ V x (f x) < 0 := fun x hxK =>
    hLie_neg x (hK_sub_D hxK) (fun heq => by
      have hVx0 : V x = 0 := heq ▸ hzero
      have hLhalf : L / 2 ≤ V x := hxK.1
      linarith)
  obtain ⟨x_max, hx_max_mem, hx_max_le⟩ :=
    hK_compact.exists_isMaxOn hK_nonempty (lie_deriv_continuous hV_c1 hf_cont).continuousOn
  set γ := -(fderiv ℝ V x_max (f x_max))
  have hγ_pos : 0 < γ := neg_pos.mpr (hLie_neg_K x_max hx_max_mem)
  have hLie_le : ∀ x ∈ K, fderiv ℝ V x (f x) ≤ -γ := fun x hx => by
    have h := isMaxOn_iff.mp hx_max_le x hx; linarith
  have hbound := V_plus_linear_bound (hV_c1.differentiable (by norm_num)) hcont
    htraj hphi_mem_K hγ_pos hLie_le
  set t₁ := (V (φ 0) - L / 2) / γ + 1
  have ht₁_nonneg : 0 ≤ t₁ := by
    have hnum : 0 ≤ V (φ 0) - L / 2 := by linarith [hVt_ge_L 0 le_rfl]
    have hdiv : 0 ≤ (V (φ 0) - L / 2) / γ := div_nonneg hnum (le_of_lt hγ_pos)
    linarith
  have hγt₁ : γ * t₁ = V (φ 0) - L / 2 + γ := by
    simp only [t₁]
    field_simp
  linarith [hVt_ge_L t₁ ht₁_nonneg, hbound t₁ ht₁_nonneg]

/-- If `V(φ t) → 0` and `φ t` stays in a compact sublevel set `{V ≤ c₀} ⊆ D`, then
    `φ t → x_eq`.

    Proof: for any `ε > 0`, the set `K_ε = {V ≤ c₀} ∩ {‖· − x_eq‖ ≥ ε}` is compact.
    If `K_ε` is empty, the conclusion is immediate. Otherwise, `V` attains its minimum
    on `K_ε` at some `x_min` with `V(x_min) > 0`; for large `t`, `V(φ t) < V(x_min)`,
    so `φ t ∉ K_ε`, i.e., `‖φ t − x_eq‖ < ε`. -/
lemma tendsto_of_V_tendsto_zero_compact
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ}
    (hcont : Continuous V)
    (hpos : ∀ x ∈ D, x ≠ x_eq → 0 < V x)
    {φ : ℝ → ℝⁿ} (_htraj : IsTrajectory φ f)
    {c₀ : ℝ} (hSub_compact : IsCompact (SublevelSet V c₀))
    (hSub_sub_D : SublevelSet V c₀ ⊆ D)
    (hanti : AntitoneOn (V ∘ φ) (Set.Ici 0))
    (hphi0_le : V (φ 0) ≤ c₀)
    (hV_tendsto : Filter.Tendsto (V ∘ φ) Filter.atTop (nhds 0)) :
    Filter.Tendsto φ Filter.atTop (nhds x_eq) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K_ε := SublevelSet V c₀ ∩ {x : ℝⁿ | ε ≤ ‖x - x_eq‖}
  have hKε_compact : IsCompact K_ε :=
    hSub_compact.of_isClosed_subset
      ((isClosed_Iic.preimage hcont).inter
        (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))))
      (fun x ⟨hVx, _⟩ => hVx)
  by_cases hKε_empty : K_ε = ∅
  · exact ⟨0, fun t ht => by
      rw [dist_eq_norm]
      have hVt_le : V (φ t) ≤ c₀ :=
        (hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht).trans hphi0_le
      by_contra hcontra
      push Not at hcontra
      have hmem : φ t ∈ K_ε := ⟨hVt_le, hcontra⟩
      simp only [hKε_empty, Set.mem_empty_iff_false] at hmem⟩
  · have hKε_nonempty : K_ε.Nonempty := Set.nonempty_iff_ne_empty.mpr hKε_empty
    obtain ⟨x_min, hx_min_mem, hx_min_le⟩ :=
      hKε_compact.exists_isMinOn hKε_nonempty hcont.continuousOn
    have hx_min_ne : x_min ≠ x_eq := fun heq => by
      have : ε ≤ ‖x_eq - x_eq‖ := heq ▸ hx_min_mem.2
      simp at this; linarith
    have hγε_pos : 0 < V x_min := hpos x_min (hSub_sub_D hx_min_mem.1) hx_min_ne
    rw [Metric.tendsto_atTop] at hV_tendsto
    obtain ⟨T₀, hT₀⟩ := hV_tendsto (V x_min) hγε_pos
    exact ⟨max T₀ 0, fun t ht => by
      rw [dist_eq_norm]
      have hVt_lt_min : V (φ t) < V x_min := by
        have h := hT₀ t (le_trans (le_max_left _ _) ht)
        simp only [Function.comp, Real.dist_eq, sub_zero] at h
        exact (abs_lt.mp h).2
      have hVt_le : V (φ t) ≤ c₀ :=
        (hanti (Set.mem_Ici.mpr le_rfl)
          (Set.mem_Ici.mpr (le_trans (le_max_right _ _) ht))
          (le_trans (le_max_right _ _) ht)).trans hphi0_le
      by_contra hcontra
      push Not at hcontra
      exact absurd hVt_lt_min (not_lt.mpr (hx_min_le ⟨hVt_le, hcontra⟩))⟩

/-! ## Global asymptotic stability -/

/-- `V(φ t) ≥ 0` for all `t`, when `V` is a strict Lyapunov function. -/
lemma V_nonneg
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLyapunovFunction f V x_eq) (x : ℝⁿ) :
    0 ≤ V x := by
  by_cases hx : x = x_eq
  · simp [hx, hV.hzero]
  · exact le_of_lt (hV.hpos x hx)

/-- `V(φ t)` converges to some `L ≥ 0` as `t → ∞` when `V` is a strict Lyapunov function.
    Follows from monotone convergence: `V ∘ φ` is antitone and bounded below by 0. -/
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

/-- The limit `L` in `V_tendsto_limit` is actually `0`. -/
lemma V_limit_zero
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLyapunovFunction f V x_eq)
    (hf_cont : Continuous f)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f)
    {L : ℝ} (hL_nonneg : 0 ≤ L)
    (hL_tendsto : Filter.Tendsto (V ∘ φ) Filter.atTop (nhds L)) :
    L = 0 := by
  have hanti := V_nonincreasing (strict_implies_semidefinite hV) htraj
  exact V_limit_zero_of_compact hV.hcont hV.hV_c1 hV.hzero
    (fun x _ hx => hV.hLie_neg x hx)
    hf_cont htraj
    (fun _ _ => Set.mem_univ _)
    (hV.hbounded_sublevel (V (φ 0)))
    le_rfl
    (hanti.antitoneOn (Set.Ici 0))
    hL_nonneg
    (fun t _ => hanti.le_of_tendsto hL_tendsto t)

/-- If `V(φ t) → 0` under a strict Lyapunov function, then `φ t → x_eq`. -/
lemma tendsto_of_V_tendsto_zero
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLyapunovFunction f V x_eq)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f)
    (hV_tendsto : Filter.Tendsto (V ∘ φ) Filter.atTop (nhds 0)) :
    Filter.Tendsto φ Filter.atTop (nhds x_eq) :=
  tendsto_of_V_tendsto_zero_compact hV.hcont
    (fun x _ hx => hV.hpos x hx)
    htraj
    (hV.hbounded_sublevel (V (φ 0)))
    (fun _ _ => Set.mem_univ _)
    ((V_nonincreasing (strict_implies_semidefinite hV) htraj).antitoneOn (Set.Ici 0))
    le_rfl
    hV_tendsto

open Set in
/-- **Uniform entry time.** A segment that starts in the sublevel set `{V ≤ M}`, stays in the
certificate domain `D`, and remains outside the ball of radius `δ` about `x_eq`, can do so only
for a time depending on `M` and `δ` — not on the segment.

This uniformity is what separates asymptotic stability from mere per-solution convergence: the
Lie derivative is bounded away from `0` on the compact set `{V ≤ M} ∩ {δ ≤ ‖x - x_eq‖}`, so `V`
is drained at a rate shared by every solution.

Stated for a local certificate; the global case is this with `D = univ`. That the segment stays
in `D` is a hypothesis rather than a conclusion, since deriving it is exactly sublevel-set
invariance, which the caller is better placed to supply. -/
lemma time_outside_ball_le
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq D) (hV_c1 : ContDiff ℝ 1 V)
    (hLie_neg : ∀ x ∈ D, x ≠ x_eq → fderiv ℝ V x (f x) < 0) (hf_cont : Continuous f)
    {M : ℝ} (hM_sub : SublevelSet V M ⊆ D) (hM_compact : IsCompact (SublevelSet V M))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ τ ≥ 0, ∀ (t₀ t₁ : ℝ) (φ : ℝ → ℝⁿ), IsTrajectoryOn φ f t₀ t₁ → t₀ ≤ t₁ →
      V (φ t₀) ≤ M → (∀ t ∈ Icc t₀ t₁, φ t ∈ D) →
      (∀ t ∈ Icc t₀ t₁, δ ≤ ‖φ t - x_eq‖) → t₁ - t₀ ≤ τ := by
  have hout_closed : IsClosed {x : ℝⁿ | δ ≤ ‖x - x_eq‖} :=
    isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
  set K : Set ℝⁿ := SublevelSet V M ∩ {x : ℝⁿ | δ ≤ ‖x - x_eq‖} with hK_def
  have hK_compact : IsCompact K := hM_compact.inter_right hout_closed
  have hmem_K : ∀ x : ℝⁿ, V x ≤ M → δ ≤ ‖x - x_eq‖ → x ∈ K := fun x h₁ h₂ => ⟨h₁, h₂⟩
  have hK_sub_D : ∀ x ∈ K, x ∈ D := fun x hx => hM_sub hx.1
  have hK_ne_eq : ∀ x ∈ K, x ≠ x_eq := by
    intro x hx hxeq
    have h2 : δ ≤ ‖x - x_eq‖ := hx.2
    rw [hxeq, sub_self, norm_zero] at h2
    linarith
  rcases K.eq_empty_or_nonempty with hKempty | hKne
  · refine ⟨0, le_rfl, fun t₀ t₁ φ _ hle hM _ hout => ?_⟩
    have hmem : φ t₀ ∈ K := hmem_K (φ t₀) hM (hout t₀ ⟨le_rfl, hle⟩)
    rw [hKempty] at hmem
    simp at hmem
  · have hM_pos : 0 < M := by
      obtain ⟨x, hx⟩ := hKne
      exact lt_of_lt_of_le (hV.hpos x (hK_sub_D x hx) (hK_ne_eq x hx)) hx.1
    obtain ⟨x_max, hx_max_mem, hx_max⟩ :=
      hK_compact.exists_isMaxOn hKne (lie_deriv_continuous hV_c1 hf_cont).continuousOn
    set γ := -(fderiv ℝ V x_max (f x_max)) with hγ_def
    have hγ_pos : 0 < γ := by
      have h := hLie_neg x_max (hK_sub_D x_max hx_max_mem) (hK_ne_eq x_max hx_max_mem)
      rw [hγ_def]; linarith
    refine ⟨M / γ, le_of_lt (div_pos hM_pos hγ_pos), ?_⟩
    intro t₀ t₁ φ hφ hle hMle hstayD hout
    have hVle : ∀ t ∈ Icc t₀ t₁, V (φ t) ≤ M := by
      intro t ht
      refine le_trans ?_ hMle
      exact V_nonincreasing_on hV (hφ.mono (Icc_subset_Icc_right ht.2)) ht.1
        (fun r hr => hstayD r ⟨hr.1, hr.2.trans ht.2⟩)
    have hW_anti : AntitoneOn (fun t => V (φ t) + γ * t) (Icc t₀ t₁) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc t₀ t₁)
      · exact (hV.hcont.comp_continuousOn hφ.continuousOn).add
          (continuous_const.mul continuous_id).continuousOn
      · intro t ht
        rw [interior_Icc] at ht
        have hd : HasDerivAt φ (f (φ t)) t :=
          (hφ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
        exact ((((hV_c1.differentiable (by norm_num)) (φ t)).hasFDerivAt.comp_hasDerivAt t
          hd).add ((hasDerivAt_id t).const_mul γ)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht' : t ∈ Icc t₀ t₁ := Ioo_subset_Icc_self ht
        have hd : HasDerivAt φ (f (φ t)) t :=
          (hφ t ht').hasDerivAt (Icc_mem_nhds ht.1 ht.2)
        have hWd : HasDerivAt (fun s => V (φ s) + γ * s)
            (fderiv ℝ V (φ t) (f (φ t)) + γ) t := by
          simpa using
            ((((hV_c1.differentiable (by norm_num)) (φ t)).hasFDerivAt.comp_hasDerivAt t
              hd).add ((hasDerivAt_id t).const_mul γ))
        rw [hWd.deriv]
        have hle_max : fderiv ℝ V (φ t) (f (φ t)) ≤ fderiv ℝ V x_max (f x_max) :=
          hx_max (hmem_K (φ t) (hVle t ht') (hout t ht'))
        rw [hγ_def]
        linarith
    have hstep : V (φ t₁) + γ * t₁ ≤ V (φ t₀) + γ * t₀ :=
      hW_anti (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle) hle
    have hV1_nonneg : 0 ≤ V (φ t₁) := by
      rcases eq_or_ne (φ t₁) x_eq with h | h
      · rw [h, hV.hzero]
      · exact (hV.hpos _ (hstayD t₁ (right_mem_Icc.mpr hle)) h).le
    have hbound : γ * (t₁ - t₀) ≤ M := by
      have hexp : γ * (t₁ - t₀) = γ * t₁ - γ * t₀ := by ring
      rw [hexp]
      linarith [hVle t₀ ⟨le_rfl, hle⟩]
    rw [le_div_iff₀ hγ_pos]
    linarith [hbound, mul_comm γ (t₁ - t₀)]

open Set in
/-- **Lyapunov's global asymptotic stability theorem.** `IsStrictLyapunovFunction` implies
    `ForwardGlobalAsymptoticStable`.

Proof sketch: stability supplies a radius `δ` from which a solution can no longer leave the
`ε`-ball. `time_outside_ball_le` bounds how long a solution can stay outside that `δ`-ball, so it
has entered by `t₀ + τ₀ + 1`; re-applying stability *at that entry time* — which needs the
anchor-free form of the predicate — pins it inside the `ε`-ball from then on. The bound is in
fact uniform over solutions; only the per-solution consequence is recorded here. -/
@[blueprint "thm:lyapunov-asymptotic-stable"
  (statement := /-- \textbf{Lyapunov's global asymptotic stability theorem.}
    If $V$ is a global strict Lyapunov function (\cref{def:isStrictLyapunovFunction})
    and $f$ is continuous, then $x_{\mathrm{eq}}$ is globally asymptotically stable
    (\cref{def:forwardGlobalAsymptoticStable}). -/)
  (proof := /-- Stability from \cref{thm:lyapunov-stable} fixes $\delta$ for the given
    $\varepsilon$. On the compact set $\{V \le M\} \cap \{\delta \le \|x-x_{\rm eq}\|\}$ the Lie
    derivative is at most $-\gamma < 0$, so $V$ is drained at a definite rate and the
    $\delta$-ball is reached in finite time; stability applied at the entry time keeps the
    solution within $\varepsilon$ thereafter. -/)]
theorem lyapunov_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsStrictLyapunovFunction f V x_eq)
    (hf_cont : Continuous f) :
    ForwardGlobalAsymptoticStable f x_eq := by
  have hstable : ForwardLyapunovStable f x_eq :=
    lyapunov_stable hn (strict_implies_semidefinite hV)
  refine ⟨hstable, ?_⟩
  intro t₀ φ hφ
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := hstable ε hε
  obtain ⟨τ₀, hτ₀_nonneg, hτ₀⟩ :=
    time_outside_ball_le (strict_implies_semidefinite hV) hV.hV_c1
      (fun x _ hx => hV.hLie_neg x hx) hf_cont (Set.subset_univ _)
      (hV.hbounded_sublevel (V (φ t₀))) hδ_pos
  refine ⟨t₀ + (τ₀ + 1), fun t ht => ?_⟩
  rw [dist_eq_norm]
  by_cases hex : ∃ s ∈ Icc t₀ (t₀ + (τ₀ + 1)), ‖φ s - x_eq‖ < δ
  · obtain ⟨s, hs_mem, hs⟩ := hex
    have hsub : Icc s t ⊆ Ici t₀ := fun r hr => le_trans hs_mem.1 hr.1
    exact hδ s t φ (hφ.mono hsub) hs t ⟨le_trans hs_mem.2 ht, le_rfl⟩
  · push Not at hex
    have hsub : Icc t₀ (t₀ + (τ₀ + 1)) ⊆ Ici t₀ := fun r hr => hr.1
    have hdwell := hτ₀ t₀ (t₀ + (τ₀ + 1)) φ (hφ.mono hsub) (by linarith) le_rfl
      (fun _ _ => Set.mem_univ _) hex
    linarith

/-- **Corollary.** `IsAsymptoticLyapunovFunction` implies `ForwardGlobalAsymptoticStable`
    (the classical radially-unbounded form of the theorem). -/
@[blueprint "thm:lyapunov-global-asymptotic-stable"
  (statement := /-- \textbf{Corollary.}
    If $V$ is a radially unbounded strict Lyapunov function
    (\cref{def:isAsymptoticLyapunovFunction}) and $f$ is continuous, then
    $x_{\mathrm{eq}}$ is globally asymptotically stable on finite forward
    solution segments. -/)
  (proof := /-- Radial unboundedness gives compact sublevel sets
    (\cref{lem:isCompact-sublevel-set}), so $V$ satisfies
    \cref{def:isStrictLyapunovFunction}; apply
    \cref{thm:lyapunov-asymptotic-stable}. -/)]
theorem lyapunov_global_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsAsymptoticLyapunovFunction f V x_eq)
    (hf_cont : Continuous f) :
    ForwardGlobalAsymptoticStable f x_eq :=
  lyapunov_asymptotic_stable hn (asymptotic_implies_strict hV) hf_cont

/-! ## Local asymptotic stability (IsStrictLocalLyapunovFunction) -/

open Set in
/-- **Lyapunov's local asymptotic stability theorem.** `IsStrictLocalLyapunovFunction` implies
    `ForwardLocalAsymptoticStable`.

Proof sketch:
1. `hcompact` gives `c₀ > 0` with `{V ≤ c₀} ⊆ D` compact.
2. `lyapunov_stable` on the semidefinite part gives forward Lyapunov stability, hence for each
   `ε` a radius `δ` from which a solution can no longer leave the `ε`-ball.
3. Continuity of `V` at `x_eq` gives the basin `δ₀`: starting within it forces `V (φ t₀) < c₀`,
   and `sublevel_set_invariant` then keeps the solution inside `D`.
4. `time_outside_ball_le` caps the time spent outside the `δ`-ball, so the solution has entered
   it by `t₀ + τ₀ + 1`; stability re-applied at that entry time finishes. -/
@[blueprint "thm:lyapunov-local-asymptotic-stable"
  (statement := /-- \textbf{Lyapunov's local asymptotic stability theorem.}
    If $V$ is a strict local Lyapunov function
    (\cref{def:isStrictLocalLyapunovFunction}) and $f$ is continuous, then
    $x_{\mathrm{eq}}$ is locally asymptotically stable
    (\cref{def:forwardLocalAsymptoticStable}). -/)
  (proof := /-- The compact sublevel set $\Omega_{c_{0}} \subseteq D$ is positively
    invariant, so the Lie derivative is at most $-\gamma < 0$ off any ball around
    $x_{\mathrm{eq}}$, draining $V$ at a definite rate; the $\delta$-ball supplied by
    stability is therefore reached in finite time, and stability applied at the entry
    time confines the solution thereafter. -/)]
theorem lyapunov_local_asymptotic_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsStrictLocalLyapunovFunction f V x_eq D)
    (hf_cont : Continuous f) :
    ForwardLocalAsymptoticStable f x_eq := by
  obtain ⟨c₀, hc₀_pos, hΩ_sub_D, hΩ_compact⟩ := hV.hcompact
  have hV_local := strict_local_implies_semidefinite hV
  have hstable : ForwardLyapunovStable f x_eq := lyapunov_stable hn hV_local
  refine ⟨hstable, ?_⟩
  have hVcont_at : ContinuousAt V x_eq := hV.hcont.continuousAt
  rw [Metric.continuousAt_iff] at hVcont_at
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hVcont_at c₀ hc₀_pos
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro t₀ φ hφ hφ0
  have hV0_lt : V (φ t₀) < c₀ := by
    have h := hδ₀ (by rw [dist_eq_norm]; exact hφ0)
    rw [Real.dist_eq, hV.hzero, sub_zero] at h
    exact (abs_lt.mp h).2
  have hstayD : ∀ (t₁ : ℝ), ∀ s ∈ Icc t₀ t₁, φ s ∈ D := fun t₁ s hs =>
    hΩ_sub_D (le_of_lt (sublevel_set_invariant hV_local
      (hφ.mono (fun r hr => hr.1)) hΩ_sub_D hV0_lt s hs))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := hstable ε hε
  obtain ⟨τ₀, hτ₀_nonneg, hτ₀⟩ :=
    time_outside_ball_le hV_local hV.hV_c1 hV.hLie_neg hf_cont hΩ_sub_D hΩ_compact hδ_pos
  refine ⟨t₀ + (τ₀ + 1), fun t ht => ?_⟩
  rw [dist_eq_norm]
  by_cases hex : ∃ s ∈ Icc t₀ (t₀ + (τ₀ + 1)), ‖φ s - x_eq‖ < δ
  · obtain ⟨s, hs_mem, hs⟩ := hex
    have hsub : Icc s t ⊆ Ici t₀ := fun r hr => le_trans hs_mem.1 hr.1
    exact hδ s t φ (hφ.mono hsub) hs t ⟨le_trans hs_mem.2 ht, le_rfl⟩
  · push Not at hex
    have hsub : Icc t₀ (t₀ + (τ₀ + 1)) ⊆ Ici t₀ := fun r hr => hr.1
    have hdwell := hτ₀ t₀ (t₀ + (τ₀ + 1)) φ (hφ.mono hsub) (by linarith)
      (le_of_lt hV0_lt) (fun s hs => hstayD _ s hs) hex
    linarith

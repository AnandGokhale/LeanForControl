import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import LeanForControl.Stability.Defs
import Architect

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-!
# `Stability.Autonomous`

Lyapunov stability theorems for autonomous ODEs `ẋ = f(x)` on `ℝⁿ`.

## Main results

* **Theorem 4.1, Part 1** (`lyapunov_stable`): `IsLocalLyapunovFunction` implies
  `LyapunovStable`.
* **Theorem 4.1, Parts 2 & 3** (`lyapunov_asymptotic_stable`): `IsStrictLyapunovFunction`
  implies `GlobalAsymptoticStable`.
* **Corollary** (`lyapunov_global_asymptotic_stable`): `IsAsymptoticLyapunovFunction` implies
  `GlobalAsymptoticStable` (the classical radially-unbounded form of the theorem).
* **Theorem 4.1 (local)** (`lyapunov_local_asymptotic_stable`):
  `IsStrictLocalLyapunovFunction` implies `LocalAsymptoticStable`.

## Proof strategy

The proofs follow the textbook structure (Khalil, Chapter 4):
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

/-- `V` is nonincreasing on `[a, b]` when the trajectory stays in `D` on that interval
    and the Lie derivative is nonpositive on `D`.

    Proof: `(V ∘ φ)'(t) = DV(φ(t))[f(φ(t))] ≤ 0` by `hLie_nonpos`,
    then `antitoneOn_of_deriv_nonpos` applies. -/
lemma V_nonincreasing_on
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq D)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f)
    {a b : ℝ} (hab : a ≤ b)
    (hstay : ∀ t ∈ Set.Icc a b, φ t ∈ D) :
    V (φ b) ≤ V (φ a) := by
  have hanti : AntitoneOn (V ∘ φ) (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    · exact (hV.hcont.comp (trajectory_continuous htraj)).continuousOn
    · exact fun t _ => (hasDerivAt_V_comp_traj hV.hV_diff htraj t).differentiableAt
        |>.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hasDerivAt_V_comp_traj hV.hV_diff htraj t).deriv]
      exact hV.hLie_nonpos (φ t) (hstay t (Set.Ioo_subset_Icc_self ht))
  exact hanti (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab

/-- Convenience wrapper for `V_nonincreasing_on` when `D = Set.univ` (used by GAS proofs). -/
lemma V_nonincreasing
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq Set.univ)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f) :
    Antitone (V ∘ φ) :=
  fun _ _ hab => V_nonincreasing_on hV htraj hab (fun _ _ => Set.mem_univ _)

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
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f)
    {c : ℝ} (hΩ_sub_D : SublevelSet V c ⊆ D)
    (h0 : V (φ 0) < c) :
    ∀ t ≥ 0, V (φ t) < c := by
  have hcont : Continuous (V ∘ φ) :=
    hV.hcont.comp (trajectory_continuous htraj)
  intro t ht
  by_contra hge
  push Not at hge
  set S := {s : ℝ | 0 ≤ s ∧ c ≤ V (φ s)} with hS_def
  have hS_nonempty : S.Nonempty := ⟨t, ht, hge⟩
  have hS_bddBelow : BddBelow S := ⟨0, fun s hs => hs.1⟩
  have hS_closed : IsClosed S := by
    have : S = (V ∘ φ) ⁻¹' (Set.Ici c) ∩ Set.Ici 0 := by
      ext s; simp [hS_def, and_comm]
    rw [this]
    exact (isClosed_Ici.preimage hcont).inter isClosed_Ici
  set T := sInf S with hT_def
  have hT_mem : T ∈ S := hS_closed.csInf_mem hS_nonempty hS_bddBelow
  have hT_ge_c : c ≤ V (φ T) := hT_mem.2
  have hT_pos : 0 < T := by
    rcases lt_or_eq_of_le hT_mem.1 with h | h
    · exact h
    · exact absurd (h ▸ hT_mem) (by simp [hS_def]; linarith)
  have hlt_of_lt : ∀ s : ℝ, 0 ≤ s → s < T → V (φ s) < c := by
    intro s hs_nonneg hs_lt
    by_contra h
    push Not at h
    exact absurd (csInf_le hS_bddBelow ⟨hs_nonneg, h⟩) (not_le.mpr hs_lt)
  have hVs_le : ∀ s : ℝ, 0 ≤ s → s < T → V (φ s) ≤ V (φ 0) := by
    intro s hs_nonneg hs_lt
    exact V_nonincreasing_on hV htraj hs_nonneg fun r hr =>
      hΩ_sub_D (le_of_lt (hlt_of_lt r hr.1 (lt_of_le_of_lt hr.2 hs_lt)))
  haveI hNeBot : (nhdsWithin T (Set.Ico 0 T)).NeBot := by
    rw [nhdsWithin_Ico_eq_nhdsLT hT_pos]
    exact nhdsLT_neBot_of_exists_lt ⟨0, hT_pos⟩
  have hVs_bound : ∀ᶠ s in nhdsWithin T (Set.Ico 0 T), (V ∘ φ) s ≤ V (φ 0) :=
    eventually_nhdsWithin_of_forall (fun s hs => hVs_le s hs.1 hs.2)
  have hVT_le : V (φ T) ≤ V (φ 0) := le_of_tendsto hcont.continuousWithinAt hVs_bound
  linarith

/-! ## Theorem 4.1, Part 1: Lyapunov stability -/

/-- **Theorem 4.1, Part 1.** If `V` is a local Lyapunov function on `D`, then `x_eq` is
    Lyapunov stable.

Proof sketch:
1. `D` open + `x_eq ∈ D` → `closedBall x_eq ε₀ ⊆ D` for some `ε₀ > 0`.
2. `m = min V` on `sphere x_eq ε' > 0` (compact sphere, `V > 0` away from `x_eq`).
3. Find `δ` with `V(y) < m` for `‖y − x_eq‖ < δ` (continuity at `x_eq`, `V(x_eq) = 0`).
4. If `‖φ 0 − x_eq‖ < δ` and `‖φ t* − x_eq‖ ≥ ε` for some `t*`, let `T* = sInf Q`
   where `Q = {t ≥ 0 | ε' ≤ ‖φ t − x_eq‖}`.
5. `V_nonincreasing_on` on `[0, T*]` gives `V(φ T*) ≤ V(φ 0) < m ≤ V(φ T*)`. Contradiction. -/
@[blueprint "thm:lyapunov-stable"
  (statement := /-- \textbf{Theorem 4.1, Part 1.}
    If $V$ is a local Lyapunov function (\cref{def:isLocalLyapunovFunction}) for
    $\dot{x} = f(x)$ on a domain $D \ni x_{\mathrm{eq}}$, then $x_{\mathrm{eq}}$
    is Lyapunov stable (\cref{def:lyapunovStable}). -/)
  (proof := /-- Pick $\varepsilon_{0}$ so $\overline{B}(x_{\mathrm{eq}},\varepsilon_{0})
    \subseteq D$. Let $m = \min_{S_{\varepsilon'}} V > 0$. Choose $\delta$ with
    $V < m$ on $B(x_{\mathrm{eq}},\delta)$. If $\|\varphi(t^{*})-x_{\mathrm{eq}}\|
    \ge \varepsilon$, monotonicity of $V$ gives $V(\varphi(t^{*})) \le V(\varphi(0))
    < m \le V(\varphi(t^{*}))$, a contradiction. -/)]
theorem lyapunov_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsLocalLyapunovFunction f V x_eq D) :
    LyapunovStable f x_eq := by
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp hV.hD_open x_eq hV.hD_mem
  set ε₀ := r / 2 with hε₀_def
  have hε₀_pos : 0 < ε₀ := by linarith
  have hcBall_sub_D : Metric.closedBall x_eq ε₀ ⊆ D := by
    intro x hx
    apply hr_ball
    rw [Metric.mem_ball, Metric.mem_closedBall] at *
    linarith
  have hsphere_sub_D : Metric.sphere x_eq ε₀ ⊆ D :=
    Metric.sphere_subset_closedBall.trans hcBall_sub_D
  intro ε hε
  set ε' := min ε ε₀
  have hε'_le_ε : ε' ≤ ε := by grind
  have hcBall'_sub_D : Metric.closedBall x_eq ε' ⊆ D :=
    (Metric.closedBall_subset_closedBall (by grind)).trans hcBall_sub_D
  have hsphere'_sub_D : Metric.sphere x_eq ε' ⊆ D :=
    Metric.sphere_subset_closedBall.trans
      ((Metric.closedBall_subset_closedBall (by grind)).trans hcBall_sub_D)
  obtain ⟨x_min, hx_min_mem, hx_min_le⟩ :=
    (isCompact_sphere x_eq ε').exists_isMinOn
    (sphere_nonempty x_eq hn (by grind))
    hV.hcont.continuousOn
  set m := V x_min
  have hm_pos : 0 < m := by
    apply hV.hpos x_min (hsphere'_sub_D hx_min_mem)
    intro heq
    have : (x_min : ℝⁿ) ∈ Metric.sphere x_eq ε' := hx_min_mem
    rw [heq, Metric.mem_sphere, dist_self] at this
    exact absurd this (ne_of_lt (by grind))
  have hV_cont_at : ContinuousAt V x_eq := hV.hcont.continuousAt
  rw [Metric.continuousAt_iff] at hV_cont_at
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hV_cont_at m hm_pos
  set δ := min δ₀ ε'
  refine ⟨δ, (by grind), ?_⟩
  intro φ htraj hφ0 t ht
  have hV0_lt_m : V (φ 0) < m := by
    have := hδ₀ ((dist_eq_norm (φ 0) x_eq).symm ▸ hφ0.trans_le (by grind))
    simp only [Real.dist_eq, hV.hzero, sub_zero] at this
    exact (abs_lt.mp this).2
  by_contra hge
  push Not at hge
  have hge_ε' : ε' ≤ ‖φ t - x_eq‖ := hε'_le_ε.trans hge
  set Q := {s : ℝ | 0 ≤ s ∧ ε' ≤ ‖φ s - x_eq‖}
  have hQ_bddBelow : BddBelow Q := ⟨0, fun s hs => hs.1⟩
  have hphi_cont : Continuous (fun s => ‖φ s - x_eq‖) :=
    continuous_norm.comp ((trajectory_continuous htraj).sub continuous_const)
  have hQ_closed : IsClosed Q := by
    have : Q = (fun s => ‖φ s - x_eq‖) ⁻¹' (Set.Ici ε') ∩ Set.Ici 0 := by
      ext s; simp [Q, and_comm]
    rw [this]
    exact (isClosed_Ici.preimage hphi_cont).inter isClosed_Ici
  set T := sInf Q
  have hT_mem : T ∈ Q := hQ_closed.csInf_mem ⟨t, ht, hge_ε'⟩ hQ_bddBelow
  have hphi0_lt_ε' : ‖φ 0 - x_eq‖ < ε' := hφ0.trans_le (by grind)
  have hT_pos : 0 < T := by
    rcases lt_or_eq_of_le hT_mem.1 with h | h
    · exact h
    · exact absurd (h ▸ hT_mem)
        (by simp only [Q, Set.mem_setOf_eq, le_refl, true_and, not_le]; exact hphi0_lt_ε')
  have hlt_ε' : ∀ s : ℝ, 0 ≤ s → s < T → ‖φ s - x_eq‖ < ε' := by
    intro s hs_nonneg hs_lt
    by_contra h; push Not at h
    exact absurd (csInf_le hQ_bddBelow ⟨hs_nonneg, h⟩) (not_le.mpr hs_lt)
  have hT_eq_ε' : ‖φ T - x_eq‖ = ε' := by
    apply le_antisymm _ hT_mem.2
    by_contra hlt
    push Not at hlt
    obtain ⟨s₀, hs₀_mem, hs₀_val⟩ :=
      intermediate_value_Icc (le_of_lt hT_pos) hphi_cont.continuousOn
        ⟨le_of_lt hphi0_lt_ε', le_of_lt hlt⟩
    have hs₀_ge_T : T ≤ s₀ := csInf_le hQ_bddBelow ⟨hs₀_mem.1, ge_of_eq hs₀_val⟩
    linarith [le_antisymm hs₀_mem.2 hs₀_ge_T ▸ hs₀_val]
  have hstay : ∀ s ∈ Set.Icc (0 : ℝ) T, φ s ∈ D := by
    intro s hs
    apply hcBall'_sub_D
    rw [Metric.mem_closedBall, dist_eq_norm]
    rcases eq_or_lt_of_le hs.2 with heq | hlt
    · rw [heq]; exact le_of_eq hT_eq_ε'
    · exact le_of_lt (hlt_ε' s hs.1 hlt)
  have hVT_le : V (φ T) ≤ V (φ 0) := V_nonincreasing_on hV htraj (le_of_lt hT_pos) hstay
  have hVT_ge_m : m ≤ V (φ T) :=
    hx_min_le (by rw [Metric.mem_sphere, dist_eq_norm]; exact hT_eq_ε')
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

/-! ## Theorem 4.1, Parts 2 & 3: Global asymptotic stability -/

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

/-- **Theorem 4.1, Parts 2 & 3.** `IsStrictLyapunovFunction` implies `GlobalAsymptoticStable`. -/
@[blueprint "thm:lyapunov-asymptotic-stable"
  (statement := /-- \textbf{Theorem 4.1, Parts 2 \& 3.}
    If $V$ is a global strict Lyapunov function (\cref{def:isStrictLyapunovFunction})
    and $f$ is continuous, then $x_{\mathrm{eq}}$ is globally asymptotically stable
    (\cref{def:globalAsymptoticStable}). -/)
  (proof := /-- Stability from \cref{thm:lyapunov-stable}. For convergence:
    $V(\varphi(t)) \to L \ge 0$ by monotone convergence; $L = 0$ by a
    LaSalle-type argument; $\varphi(t) \to x_{\mathrm{eq}}$ by coercivity. -/)]
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

/-- **Corollary.** `IsAsymptoticLyapunovFunction` implies `GlobalAsymptoticStable`
    (the classical radially-unbounded form of Khalil's theorem). -/
@[blueprint "thm:lyapunov-global-asymptotic-stable"
  (statement := /-- \textbf{Corollary.}
    If $V$ is a radially unbounded strict Lyapunov function
    (\cref{def:isAsymptoticLyapunovFunction}) and $f$ is continuous, then
    $x_{\mathrm{eq}}$ is globally asymptotically stable. -/)
  (proof := /-- Radial unboundedness gives compact sublevel sets
    (\cref{lem:isCompact-sublevel-set}), so $V$ satisfies
    \cref{def:isStrictLyapunovFunction}; apply
    \cref{thm:lyapunov-asymptotic-stable}. -/)]
theorem lyapunov_global_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsAsymptoticLyapunovFunction f V x_eq)
    (hf_cont : Continuous f) :
    GlobalAsymptoticStable f x_eq :=
  lyapunov_asymptotic_stable hn (asymptotic_implies_strict hV) hf_cont

/-! ## Local asymptotic stability (IsStrictLocalLyapunovFunction) -/

/-- **Theorem 4.1 (local).** `IsStrictLocalLyapunovFunction` implies `LocalAsymptoticStable`.

Proof sketch:
1. `hcompact` gives `c₀ > 0` with `{V ≤ c₀} ⊆ D` compact.
2. `lyapunov_stable` on the semidefinite part gives `LyapunovStable`.
3. For convergence: trajectories starting in `int({V ≤ c₀})` stay in `{V ≤ c₀} ⊆ D`
   (`sublevel_set_invariant`). `V(φ t) → L ≥ 0` via monotone convergence.
   `V_limit_zero_of_compact` gives `L = 0`.
   `tendsto_of_V_tendsto_zero_compact` gives `φ t → x_eq`. -/
@[blueprint "thm:lyapunov-local-asymptotic-stable"
  (statement := /-- \textbf{Theorem 4.1 (local).}
    If $V$ is a strict local Lyapunov function
    (\cref{def:isStrictLocalLyapunovFunction}) and $f$ is continuous, then
    $x_{\mathrm{eq}}$ is locally asymptotically stable
    (\cref{def:localAsymptoticStable}). -/)
  (proof := /-- The compact sublevel set $\Omega_{c_{0}} \subseteq D$ is
    positively invariant. $V(\varphi(t)) \to L \ge 0$ by monotone convergence;
    $L = 0$ by compactness; $\varphi(t) \to x_{\mathrm{eq}}$. -/)]
theorem lyapunov_local_asymptotic_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsStrictLocalLyapunovFunction f V x_eq D)
    (hf_cont : Continuous f) :
    LocalAsymptoticStable f x_eq := by
  obtain ⟨c₀, hc₀_pos, hΩ_sub_D, hΩ_compact⟩ := hV.hcompact
  have hV_local := strict_local_implies_semidefinite hV
  refine ⟨lyapunov_stable hn hV_local, ?_⟩
  have hVcont_at : ContinuousAt V x_eq := hV.hcont.continuousAt
  rw [Metric.continuousAt_iff] at hVcont_at
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hVcont_at c₀ hc₀_pos
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro φ htraj hφ0
  have hV0_lt : V (φ 0) < c₀ := by
    have h := hδ₀ (by rw [dist_eq_norm]; exact hφ0)
    rw [Real.dist_eq, hV.hzero, sub_zero] at h
    exact (abs_lt.mp h).2
  have hSub_compact : IsCompact (SublevelSet V (V (φ 0))) :=
    hΩ_compact.of_isClosed_subset (isClosed_Iic.preimage hV.hcont)
      (fun x hVx => le_trans hVx (le_of_lt hV0_lt))
  have hSub_sub_D : SublevelSet V (V (φ 0)) ⊆ D :=
    fun x hVx => hΩ_sub_D (le_trans hVx (le_of_lt hV0_lt))
  have hVt_lt : ∀ t ≥ 0, V (φ t) < c₀ :=
    sublevel_set_invariant hV_local htraj hΩ_sub_D hV0_lt
  have hphit_in_D : ∀ t ≥ 0, φ t ∈ D := fun t ht => hΩ_sub_D (le_of_lt (hVt_lt t ht))
  have hanti : AntitoneOn (V ∘ φ) (Set.Ici 0) := fun s hs t ht hst =>
    V_nonincreasing_on hV_local htraj hst (fun r hr => hphit_in_D r (hs.trans hr.1))
  have hVt_nonneg : ∀ t ≥ 0, 0 ≤ V (φ t) := fun t ht => by
    by_cases hx : φ t = x_eq
    · simp [hx, hV.hzero]
    · exact le_of_lt (hV.hpos (φ t) (hphit_in_D t ht) hx)
  set g : ℝ → ℝ := fun t => (V ∘ φ) (max t 0) with hg_def
  have hg_anti : Antitone g := fun s t hst =>
    hanti (Set.mem_Ici.mpr (le_max_right s 0)) (Set.mem_Ici.mpr (le_max_right t 0))
      (max_le_max_right 0 hst)
  have hg_bdd : BddBelow (Set.range g) :=
    ⟨0, fun _ ⟨t, ht⟩ => ht ▸ hVt_nonneg (max t 0) (le_max_right t 0)⟩
  set L := ⨅ t, g t
  have hL_nonneg : 0 ≤ L := le_ciInf fun t => hVt_nonneg (max t 0) (le_max_right t 0)
  have hg_tendsto : Filter.Tendsto g Filter.atTop (nhds L) :=
    tendsto_atTop_ciInf hg_anti hg_bdd
  have hgL_eq : ∀ t ≥ (0 : ℝ), g t = (V ∘ φ) t := fun t ht => by
    simp [hg_def, max_eq_left ht]
  have hVphi_tendsto : Filter.Tendsto (V ∘ φ) Filter.atTop (nhds L) :=
    hg_tendsto.congr' ((Filter.eventually_ge_atTop 0).mono fun t ht => hgL_eq t ht)
  have hVt_ge_L : ∀ t ≥ 0, L ≤ V (φ t) := fun t ht => by
    have := hg_anti.le_of_tendsto hg_tendsto t; rwa [hgL_eq t ht] at this
  have hL_zero : L = 0 :=
    V_limit_zero_of_compact hV.hcont hV.hV_c1 hV.hzero
      (fun x hxD hx => hV.hLie_neg x hxD hx)
      hf_cont htraj hSub_sub_D hSub_compact le_rfl hanti hL_nonneg hVt_ge_L
  rw [hL_zero] at hVphi_tendsto
  exact tendsto_of_V_tendsto_zero_compact hV.hcont
    (fun x hxD hx => hV.hpos x hxD hx)
    htraj hSub_compact hSub_sub_D hanti le_rfl hVphi_tendsto

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import LeanForControl.Lyapunov.Defs

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Infrastructure -/

-- Chain rule: d/dt (V ∘ φ)(t) = DV(φ(t))[f(φ(t))].
-- Uses global Differentiable ℝ V (from IsLocalLyapunovFunction).
lemma hasDerivAt_V_comp_traj
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ V)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f) (t : ℝ) :
    HasDerivAt (V ∘ φ) (fderiv ℝ V (φ t) (f (φ t))) t :=
  (hV_diff (φ t)).hasFDerivAt.comp_hasDerivAt t (htraj t)

-- A trajectory is continuous.
lemma trajectory_continuous
    {f : ℝⁿ → ℝⁿ} {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f) :
    Continuous φ := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (htraj t).differentiableAt.continuousAt

-- The sphere Metric.sphere x_eq ε is nonempty when 0 < n and 0 < ε.
lemma sphere_nonempty
    (x_eq : ℝⁿ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (Metric.sphere x_eq ε).Nonempty := by
  refine ⟨x_eq + EuclideanSpace.single (⟨0, hn⟩ : Fin n) ε, ?_⟩
  rw [Metric.mem_sphere, dist_eq_norm]
  simp [PiLp.norm_single, abs_of_pos hε]

lemma lie_deriv_continuous
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_c1 : ContDiff ℝ 1 V) (hf_cont : Continuous f) :
    Continuous (fun x : ℝⁿ => fderiv ℝ V x (f x)) :=
  (hV_c1.continuous_fderiv (by norm_num)).clm_apply hf_cont

-- V(φ t) + γ * t ≤ V(φ 0) when φ stays in K where Lie ≤ -γ < 0.
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
    · intro t _
      exact ((hasDerivAt_V_comp_traj hV_diff htraj t).add
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

-- V is nonincreasing on [a, b] when the trajectory stays in D on that interval.
-- Proof: (V ∘ φ)'(t) = fderiv ℝ V (φ t) (f (φ t)) ≤ 0 by hLie_nonpos (using hstay),
-- then apply antitoneOn_of_deriv_nonpos.
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
    · -- DifferentiableWithinAt ℝ (V ∘ φ) (interior (Icc a b)) t
      intro t _
      exact (hasDerivAt_V_comp_traj hV.hV_diff htraj t).differentiableAt
        |>.differentiableWithinAt
    · -- deriv (V ∘ φ) t ≤ 0 for t ∈ interior (Icc a b)
      intro t ht
      rw [interior_Icc] at ht
      rw [(hasDerivAt_V_comp_traj hV.hV_diff htraj t).deriv]
      exact hV.hLie_nonpos (φ t) (hstay t (Set.Ioo_subset_Icc_self ht))
  exact hanti (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab

-- Convenience wrapper for D = Set.univ (used by GAS proofs).
lemma V_nonincreasing
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq Set.univ)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f) :
    Antitone (V ∘ φ) :=
  fun _ _ hab => V_nonincreasing_on hV htraj hab (fun _ _ => Set.mem_univ _)

-- V(φ t) ≤ V(φ 0) for t ≥ 0 when conditions are global (D = Set.univ).
lemma V_le_initial
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq Set.univ)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f)
    {t : ℝ} (ht : 0 ≤ t) : V (φ t) ≤ V (φ 0) :=
  V_nonincreasing hV htraj ht

/-! ## Lyapunov function hierarchy -/

-- IsStrictLyapunovFunction → IsLocalLyapunovFunction on Set.univ.
-- The x_eq case: fderiv ℝ V x_eq (f x_eq) = fderiv ℝ V x_eq 0 = 0 (map_zero of CLM).
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

-- IsAsymptoticLyapunovFunction → IsStrictLyapunovFunction.
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

-- IsStrictLocalLyapunovFunction → IsLocalLyapunovFunction (on the same D).
lemma strict_local_implies_semidefinite
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLocalLyapunovFunction f V x_eq D) :
    IsLocalLyapunovFunction f V x_eq D where
  hD_open     := hV.hD_open
  hD_mem      := hV.hD_mem
  hcont       := hV.hcont
  hV_diff     := hV.hV_c1.differentiable (by norm_num)
  hzero       := hV.hzero
  hpos        := fun x hxD hx => hV.hpos x hxD hx
  hLie_nonpos := fun x hxD => by
    by_cases hx : x = x_eq
    · simp only [hx, hV.hequil, map_zero, le_refl]
    · exact le_of_lt (hV.hLie_neg x hxD hx)

/-! ## Forward invariance of sublevel sets -/

-- If {V ≤ c} ⊆ D and V(φ 0) < c, then V(φ t) < c for all t ≥ 0.
--
-- Proof (first-exit-time / sInf argument):
-- Let S = {t ≥ 0 | c ≤ V(φ t)} (closed, bounded below by 0).
-- Suppose S nonempty; let T* = sInf S. Then:
-- (1) T* > 0: V(φ 0) < c so 0 ∉ S; S is closed, so T* ∉ {0}.
-- (2) T* ∈ S (S closed, inf is in S).
-- (3) For t ∈ [0, T*): V(φ t) < c (by minimality), so φ t ∈ {V < c} ⊆ D.
-- (4) V_nonincreasing_on on [0, T*] (hstay from (3) + φ(T*) ∈ {V ≤ c} ⊆ D):
--     V(φ(T*)) ≤ V(φ 0) < c.
-- (5) But T* ∈ S means c ≤ V(φ(T*)). Contradiction.
lemma sublevel_set_invariant
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq D)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f)
    {c : ℝ} (hΩ_sub_D : SublevelSet V c ⊆ D)
    (h0 : V (φ 0) < c) :
    ∀ t ≥ 0, V (φ t) < c := by
  -- We note that V ∘ φ is continuous
  have hcont : Continuous (V ∘ φ) :=
    hV.hcont.comp (trajectory_continuous htraj)
  -- Proof by contradiction, if possible, let c ≤ V(φ t) for some t ≥ 0
  intro t ht
  by_contra hge
  push Not at hge
  -- S = {t ≥ 0 | c ≤ V(φ t)} is nonempty, bounded below
  set S := {s : ℝ | 0 ≤ s ∧ c ≤ V (φ s)} with hS_def
  have hS_nonempty : S.Nonempty := ⟨t, ht, hge⟩
  have hS_bddBelow : BddBelow S := ⟨0, fun s hs => hs.1⟩
  -- S is closed: preimage of [c, ∞) under continuous V ∘ φ, intersected with [0, ∞)
  have hS_closed : IsClosed S := by
    have : S = (V ∘ φ) ⁻¹' (Set.Ici c) ∩ Set.Ici 0 := by
      ext s; simp [hS_def, and_comm]
    rw [this]
    exact (isClosed_Ici.preimage hcont).inter isClosed_Ici
  -- T* = sInf S is in S
  set T := sInf S with hT_def
  have hT_mem : T ∈ S := hS_closed.csInf_mem hS_nonempty hS_bddBelow
  have hT_ge_c : c ≤ V (φ T) := hT_mem.2
  -- T > 0: since V(φ 0) < c, 0 ∉ S, and T = sInf S ≥ 0.
  have hT_pos : 0 < T := by
    rcases lt_or_eq_of_le hT_mem.1 with h | h
    · exact h
    · exact absurd (h ▸ hT_mem) (by simp [hS_def]; linarith)
  -- For s ∈ [0, T), V(φ s) < c, so φ s ∈ D (via SublevelSet)
  have hlt_of_lt : ∀ s : ℝ, 0 ≤ s → s < T → V (φ s) < c := by
    intro s hs_nonneg hs_lt
    by_contra h
    push Not at h
    exact absurd (csInf_le hS_bddBelow ⟨hs_nonneg, h⟩) (not_le.mpr hs_lt)
  -- For t ∈ [0, T), φ t ∈ {V < c} ⊆ SublevelSet V c ⊆ D
  -- For t = T, use limit: V(φ T) ≤ V(φ 0) < c
  -- Use le_of_tendsto: V(φ T) ≤ V(φ 0) because V ∘ φ tends to V(φ T) as s → T⁻
  -- and V(φ s) ≤ V(φ 0) for all s ∈ [0, T)
  -- Key: for s ∈ [0, T), φ stays in D on [0, s], so V_nonincreasing_on applies
  have hVs_le : ∀ s : ℝ, 0 ≤ s → s < T → V (φ s) ≤ V (φ 0) := by
    intro s hs_nonneg hs_lt
    apply V_nonincreasing_on hV htraj hs_nonneg
    intro r hr
    exact hΩ_sub_D (le_of_lt (hlt_of_lt r hr.1 (lt_of_le_of_lt hr.2 hs_lt)))
  -- Now use continuity to get V(φ T) ≤ V(φ 0) < c, contradicting T ∈ S
  -- nhdsWithin T (Ico 0 T) is NeBot (equals nhdsWithin T (Iio T) which is NeBot since 0 < T)
  haveI hNeBot : (nhdsWithin T (Set.Ico 0 T)).NeBot := by
    rw [nhdsWithin_Ico_eq_nhdsLT hT_pos]
    exact nhdsLT_neBot_of_exists_lt ⟨0, hT_pos⟩
  have hVs_bound : ∀ᶠ s in nhdsWithin T (Set.Ico 0 T), (V ∘ φ) s ≤ V (φ 0) :=
    eventually_nhdsWithin_of_forall (fun s hs => hVs_le s hs.1 hs.2)
  have hVT_le : V (φ T) ≤ V (φ 0) := le_of_tendsto hcont.continuousWithinAt hVs_bound
  linarith

/-! ## Theorem 4.1, Part 1: Lyapunov stability -/

-- If V is a local Lyapunov function on D, the equilibrium is Lyapunov stable.
--
-- Proof (first-exit-time argument):
-- Fix ε > 0.
-- (1) D open + x_eq ∈ D → get ε₀ with closedBall x_eq ε₀ ⊆ D.
-- (2) Let ε' = min ε ε₀. Sphere x_eq ε' ⊆ closedBall x_eq ε₀ ⊆ D.
-- (3) m = min V on sphere x_eq ε' > 0 (compactness + hpos in D).
-- (4) Find δ ≤ ε' with V(y) < m for ‖y - x_eq‖ < δ (continuity at x_eq, V(x_eq) = 0).
-- (5) Suppose ‖φ 0 - x_eq‖ < δ, for contradiction ‖φ t* - x_eq‖ ≥ ε for some t* ≥ 0.
-- (6) T* = sInf{t ≥ 0 | ε' ≤ ‖φ t - x_eq‖} > 0 (φ 0 in ball δ < ε').
-- (7) T* ∈ closed set, ‖φ(T*) - x_eq‖ = ε' (by IVT + minimality).
-- (8) For t ∈ [0, T*], ‖φ t - x_eq‖ ≤ ε' ≤ ε₀ → φ t ∈ closedBall ε₀ ⊆ D.
-- (9) V_nonincreasing_on on [0, T*] → V(φ(T*)) ≤ V(φ 0) < m.
-- (10) φ(T*) ∈ sphere ε' → V(φ(T*)) ≥ m. Contradiction.
theorem lyapunov_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsLocalLyapunovFunction f V x_eq D) :
    LyapunovStable f x_eq := by
  -- Step 1: D is open, x_eq ∈ D → get r > 0 with ball x_eq r ⊆ D
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp hV.hD_open x_eq hV.hD_mem
  -- ε₀ = r/2; closedBall x_eq ε₀ ⊆ ball x_eq r ⊆ D
  set ε₀ := r / 2 with hε₀_def
  have hε₀_pos : 0 < ε₀ := by linarith
  have hcBall_sub_D : Metric.closedBall x_eq ε₀ ⊆ D := by
    intro x hx
    apply hr_ball
    rw [Metric.mem_ball, Metric.mem_closedBall] at *
    linarith
  -- sphere x_eq ε₀ ⊆ D and ≠ x_eq on sphere
  have hsphere_sub_D : Metric.sphere x_eq ε₀ ⊆ D :=
    Metric.sphere_subset_closedBall.trans hcBall_sub_D
  -- Fix ε > 0
  intro ε hε
  -- Step 2: ε' = min ε ε₀
  set ε' := min ε ε₀
  have hε'_le_ε : ε' ≤ ε := by grind
  -- closedBall x_eq ε' ⊆ D
  have hcBall'_sub_D : Metric.closedBall x_eq ε' ⊆ D :=
    (Metric.closedBall_subset_closedBall (by grind)).trans hcBall_sub_D
  -- sphere x_eq ε' ⊆ D
  have hsphere'_sub_D : Metric.sphere x_eq ε' ⊆ D :=
    Metric.sphere_subset_closedBall.trans
      ((Metric.closedBall_subset_closedBall (by grind)).trans hcBall_sub_D)
  -- Step 3: sphere x_eq ε' is compact and nonempty
  -- Step 4: m = min V on sphere x_eq ε' > 0
  have hV_cont_on : ContinuousOn V (Metric.sphere x_eq ε') :=
    hV.hcont.continuousOn
  obtain ⟨x_min, hx_min_mem, hx_min_le⟩ :=
    (isCompact_sphere x_eq ε').exists_isMinOn
    (sphere_nonempty x_eq hn (by grind))
    hV_cont_on
  set m := V x_min
  have hm_pos : 0 < m := by
    apply hV.hpos x_min (hsphere'_sub_D hx_min_mem)
    intro heq
    have : (x_min : ℝⁿ) ∈ Metric.sphere x_eq ε' := hx_min_mem
    rw [heq, Metric.mem_sphere, dist_self] at this
    exact absurd this (ne_of_lt (by grind))
  -- Step 5: continuity of V at x_eq (V(x_eq) = 0) gives δ > 0 with V y < m for ‖y - x_eq‖ < δ
  -- Use Metric.continuousAt_iff for V at x_eq
  have hV_cont_at : ContinuousAt V x_eq := hV.hcont.continuousAt
  rw [Metric.continuousAt_iff] at hV_cont_at
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hV_cont_at m hm_pos
  -- δ = min δ₀ ε', so δ ≤ ε'
  set δ := min δ₀ ε'
  refine ⟨δ, (by grind), ?_⟩
  -- Step 6: Fix trajectory with ‖φ 0 - x_eq‖ < δ, show ‖φ t - x_eq‖ < ε for all t ≥ 0
  intro φ htraj hφ0 t ht
  -- V(φ 0) < m (from δ₀ and continuity)
  have hV0_lt_m : V (φ 0) < m := by
    have := hδ₀ ((dist_eq_norm (φ 0) x_eq).symm ▸ hφ0.trans_le (by grind))
    simp only [Real.dist_eq, hV.hzero, sub_zero] at this
    exact (abs_lt.mp this).2
  -- Prove ‖φ t - x_eq‖ < ε by contradiction
  by_contra hge
  push Not at hge
  -- ‖φ t - x_eq‖ ≥ ε ≥ ε' (so t witnesses nonemptiness of Q)
  have hge_ε' : ε' ≤ ‖φ t - x_eq‖ := hε'_le_ε.trans hge
  -- Let Q = {s : ℝ | 0 ≤ s ∧ ε' ≤ ‖φ s - x_eq‖}
  set Q := {s : ℝ | 0 ≤ s ∧ ε' ≤ ‖φ s - x_eq‖}
  --have hQ_nonempty : Q.Nonempty := ⟨t, ht, hge_ε'⟩
  have hQ_bddBelow : BddBelow Q := ⟨0, fun s hs => hs.1⟩
  -- Q is closed
  have hphi_cont : Continuous (fun s => ‖φ s - x_eq‖) :=
    continuous_norm.comp ((trajectory_continuous htraj).sub continuous_const)
  have hQ_closed : IsClosed Q := by
    have : Q = (fun s => ‖φ s - x_eq‖) ⁻¹' (Set.Ici ε') ∩ Set.Ici 0 := by
      ext s; simp [Q, and_comm]
    rw [this]
    exact (isClosed_Ici.preimage hphi_cont).inter isClosed_Ici
  -- T* = sInf Q ∈ Q
  set T := sInf Q
  have hT_mem : T ∈ Q := hQ_closed.csInf_mem ⟨t, ht, hge_ε'⟩ hQ_bddBelow
  have hT_ge_ε' : ε' ≤ ‖φ T - x_eq‖ := hT_mem.2
  -- T > 0: ‖φ 0 - x_eq‖ < δ ≤ ε', so 0 ∉ Q
  have hphi0_lt_ε' : ‖φ 0 - x_eq‖ < ε' := hφ0.trans_le (by grind)
  have hT_pos : 0 < T := by
    rcases lt_or_eq_of_le hT_mem.1 with h | h
    · exact h
    · exact absurd (h ▸ hT_mem)
        (by simp only [Q, Set.mem_setOf_eq, le_refl, true_and, not_le]; exact hphi0_lt_ε')
  -- For s ∈ [0, T): s ∉ Q → ‖φ s - x_eq‖ < ε'
  have hlt_ε' : ∀ s : ℝ, 0 ≤ s → s < T → ‖φ s - x_eq‖ < ε' := by
    intro s hs_nonneg hs_lt
    by_contra h
    push Not at h
    exact absurd (csInf_le hQ_bddBelow ⟨hs_nonneg, h⟩) (not_le.mpr hs_lt)
  -- IVT: ‖φ T - x_eq‖ = ε'
  -- At s=0: ‖φ 0 - x_eq‖ < ε', at s=T: ‖φ T - x_eq‖ ≥ ε'.
  -- IVT gives s₀ ∈ [0, T] with ‖φ s₀ - x_eq‖ = ε'. Minimality → s₀ ≥ T → s₀ = T.
  have hT_eq_ε' : ‖φ T - x_eq‖ = ε' := by
    apply le_antisymm _ hT_ge_ε'
    by_contra hlt
    push Not at hlt
    obtain ⟨s₀, hs₀_mem, hs₀_val⟩ :=
      intermediate_value_Icc (le_of_lt hT_pos) hphi_cont.continuousOn
        ⟨le_of_lt hphi0_lt_ε', le_of_lt hlt⟩
    have hs₀_ge_T : T ≤ s₀ := csInf_le hQ_bddBelow ⟨hs₀_mem.1, ge_of_eq hs₀_val⟩
    linarith [le_antisymm hs₀_mem.2 hs₀_ge_T ▸ hs₀_val]
  -- hstay: ∀ s ∈ [0, T], φ s ∈ D
  have hstay : ∀ s ∈ Set.Icc (0 : ℝ) T, φ s ∈ D := by
    intro s hs
    apply hcBall'_sub_D
    rw [Metric.mem_closedBall, dist_eq_norm]
    rcases eq_or_lt_of_le hs.2 with heq | hlt
    · -- s = T
      rw [heq]
      exact le_of_eq hT_eq_ε'
    · -- s < T
      exact le_of_lt (hlt_ε' s hs.1 hlt)
  -- V_nonincreasing_on on [0, T]: V(φ T) ≤ V(φ 0) < m
  have hVT_le : V (φ T) ≤ V (φ 0) := V_nonincreasing_on hV htraj (le_of_lt hT_pos) hstay
  have hVT_ge_m : m ≤ V (φ T) :=
    hx_min_le (by rw [Metric.mem_sphere, dist_eq_norm]; exact hT_eq_ε')
  linarith

/-! ## Shared limit lemmas -/

-- If φ t stays in K ⊆ D (compact, Lie < 0 on K), V∘φ is antitone on [0,∞),
-- and L ≤ V(φ t) for t ≥ 0, then L = 0.
-- Encodes the γ-linear-bound contradiction used by both global and local GAS proofs.
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
  -- K = {L/2 ≤ V} ∩ {V ≤ c₀}; φ stays in K for t ≥ 0
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

-- If V(φ t) → 0, φ t stays in compact SublevelSet V c₀ ⊆ D, then φ t → x_eq.
lemma tendsto_of_V_tendsto_zero_compact
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ}
    (hcont : Continuous V) (hzero : V x_eq = 0)
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

/-! ## Theorem 4.1, Parts 2 & 3: Global asymptotic stability
    (IsStrictLyapunovFunction, conditions on all of ℝⁿ)
    The proofs below are unchanged from before — they use D = Set.univ via
    strict_implies_semidefinite and the V_nonincreasing wrapper. -/

-- V(φ t) ≥ 0 for all t.
lemma V_nonneg
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLyapunovFunction f V x_eq) (x : ℝⁿ) :
    0 ≤ V x := by
  by_cases hx : x = x_eq
  · simp [hx, hV.hzero]
  · exact le_of_lt (hV.hpos x hx)

-- V(φ(t)) → L as t → ∞ for some L ≥ 0.
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

-- The limit L = 0 (key lemma for GAS).
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

-- If V(φ t) → 0, then φ t → x_eq.
lemma tendsto_of_V_tendsto_zero
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLyapunovFunction f V x_eq)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f)
    (hV_tendsto : Filter.Tendsto (V ∘ φ) Filter.atTop (nhds 0)) :
    Filter.Tendsto φ Filter.atTop (nhds x_eq) :=
  tendsto_of_V_tendsto_zero_compact hV.hcont hV.hzero
    (fun x _ hx => hV.hpos x hx)
    htraj
    (hV.hbounded_sublevel (V (φ 0)))
    (fun _ _ => Set.mem_univ _)
    ((V_nonincreasing (strict_implies_semidefinite hV) htraj).antitoneOn (Set.Ici 0))
    le_rfl
    hV_tendsto

-- Theorem 4.1, Parts 2 & 3: IsStrictLyapunovFunction → GlobalAsymptoticStable.
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

-- Corollary: IsAsymptoticLyapunovFunction → GAS (Khalil's classical form).
theorem lyapunov_global_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsAsymptoticLyapunovFunction f V x_eq)
    (hf_cont : Continuous f) :
    GlobalAsymptoticStable f x_eq :=
  lyapunov_asymptotic_stable hn (asymptotic_implies_strict hV) hf_cont

/-! ## Local asymptotic stability (IsStrictLocalLyapunovFunction) -/

-- Theorem 4.1, Part 2 (local): IsStrictLocalLyapunovFunction → LocalAsymptoticStable.
--
-- Proof sketch:
-- (1) hcompact gives c₀ > 0 with Ωc₀ ⊆ D compact.
-- (2) lyapunov_stable applied to the semidefinite part of hV gives LyapunovStable.
-- (3) For convergence: trajectory starting in int(Ωc₀) stays in Ωc₀ ⊆ D (sublevel_set_invariant).
--     V_tendsto_limit (with compactness replacing radial unboundedness) gives V(φ t) → L ≥ 0.
--     V_limit_zero on the compact Ωc₀ gives L = 0.
--     tendsto_of_V_tendsto_zero (local version) gives φ t → x_eq.
theorem lyapunov_local_asymptotic_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsStrictLocalLyapunovFunction f V x_eq D)
    (hf_cont : Continuous f) :
    LocalAsymptoticStable f x_eq := by
  obtain ⟨c₀, hc₀_pos, hΩ_sub_D, hΩ_compact⟩ := hV.hcompact
  have hV_local := strict_local_implies_semidefinite hV
  -- Part 1: Lyapunov stability
  refine ⟨lyapunov_stable hn hV_local, ?_⟩
  -- Basin of attraction via c₀
  have hVcont_at : ContinuousAt V x_eq := hV.hcont.continuousAt
  rw [Metric.continuousAt_iff] at hVcont_at
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hVcont_at c₀ hc₀_pos
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro φ htraj hφ0
  -- V(φ 0) < c₀
  have hV0_lt : V (φ 0) < c₀ := by
    have h := hδ₀ (by rw [dist_eq_norm]; exact hφ0)
    rw [Real.dist_eq, hV.hzero, sub_zero] at h
    exact (abs_lt.mp h).2
  -- compact sublevel set containing φ's orbit
  have hSub_compact : IsCompact (SublevelSet V (V (φ 0))) :=
    hΩ_compact.of_isClosed_subset (isClosed_Iic.preimage hV.hcont)
      (fun x hVx => le_trans hVx (le_of_lt hV0_lt))
  have hSub_sub_D : SublevelSet V (V (φ 0)) ⊆ D :=
    fun x hVx => hΩ_sub_D (le_trans hVx (le_of_lt hV0_lt))
  -- V(φ t) < c₀ for t ≥ 0
  have hVt_lt : ∀ t ≥ 0, V (φ t) < c₀ :=
    sublevel_set_invariant hV_local htraj hΩ_sub_D hV0_lt
  -- φ stays in D for t ≥ 0
  have hphit_in_D : ∀ t ≥ 0, φ t ∈ D := fun t ht => hΩ_sub_D (le_of_lt (hVt_lt t ht))
  -- V∘φ antitone on [0,∞)
  have hanti : AntitoneOn (V ∘ φ) (Set.Ici 0) := fun s hs t ht hst =>
    V_nonincreasing_on hV_local htraj hst (fun r hr => hphit_in_D r (hs.trans hr.1))
  -- V(φ t) ≥ 0 for t ≥ 0
  have hVt_nonneg : ∀ t ≥ 0, 0 ≤ V (φ t) := fun t ht => by
    by_cases hx : φ t = x_eq
    · simp [hx, hV.hzero]
    · exact le_of_lt (hV.hpos (φ t) (hphit_in_D t ht) hx)
  -- Extend to global antitone via max trick, get V(φ t) → L ≥ 0
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
  -- L = 0
  have hL_zero : L = 0 :=
    V_limit_zero_of_compact hV.hcont hV.hV_c1 hV.hzero
      (fun x hxD hx => hV.hLie_neg x hxD hx)
      hf_cont htraj hSub_sub_D hSub_compact le_rfl hanti hL_nonneg hVt_ge_L
  -- φ t → x_eq
  rw [hL_zero] at hVphi_tendsto
  exact tendsto_of_V_tendsto_zero_compact hV.hcont hV.hzero
    (fun x hxD hx => hV.hpos x hxD hx)
    htraj hSub_compact hSub_sub_D hanti le_rfl hVphi_tendsto

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.Basic
import LeanForControl.Lyapunov.definitions

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)


lemma global_is_local_lyapunov (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ)
    (hV : IsGlobalLyapunovFunction f V x_eq) :
    IsLocalLyapunovFunction f V x_eq := by
  obtain ⟨hcont, halphas, hderiv, hnonincr⟩ := hV
  -- Extract the Class K_infty bounding functions and their core properties
  -- We specifically pull out the zero and strict monotonicity properties of α₁ and α₂
  obtain ⟨α₁, α₂, ⟨⟨_, hα₁_zero, hα₁_strict_mono⟩, _⟩, ⟨⟨_, hα₂_zero, _⟩, _⟩, h_sandwich⟩ := halphas
  refine ⟨hcont, ?_, ?_, hderiv, hnonincr⟩
  · -- Proof of hzero: V(x_eq) = 0
    -- Since α₁(‖x_eq - x_eq‖) ≤ V(x_eq) ≤ α₂(‖x_eq - x_eq‖)
    have h_upper : V x_eq ≤ 0 := by
      have h2 := (h_sandwich x_eq).2
      simp only [sub_self, norm_zero] at h2
      rwa [hα₂_zero] at h2
    have h_lower : 0 ≤ V x_eq := by
      have h1 := (h_sandwich x_eq).1
      simp only [sub_self, norm_zero] at h1
      rwa [hα₁_zero] at h1
    linarith
  · -- Proof of hpos: ∀ x ≠ x_eq, 0 < V x
    intro x hx
    -- The norm is strictly positive because x ≠ x_eq
    have h_norm_pos : 0 < ‖x - x_eq‖ := norm_sub_pos_iff.mpr hx
    -- Apply the lower bound from the sandwich condition: α₁(‖x - x_eq‖) ≤ V(x)
    have h_lower := (h_sandwich x).1
    -- Use strict monotonicity of α₁ to show α₁(‖x - x_eq‖) > 0
    have h_alpha_pos : 0 < α₁ ‖x - x_eq‖ := by
      have h_mono : α₁ 0 < α₁ ‖x - x_eq‖ :=
        hα₁_strict_mono (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr (le_of_lt h_norm_pos)) h_norm_pos
      rwa [hα₁_zero] at h_mono
    linarith


-- Lemma 1: V is nonincreasing along trajectories
lemma V_nonincreasing (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ)
    (hV : IsLocalLyapunovFunction f V x_eq)
    (φ : ℝ → ℝⁿ) (htraj : IsTrajectory φ f) :
    Antitone (V ∘ φ) := by
  have h1 : ∀ t, HasDerivAt (V ∘ φ) (fderiv ℝ V (φ t) (f (φ t))) t := fun t => hV.hderiv φ htraj t
  have h2 : ∀ t, fderiv ℝ V (φ t) (f (φ t)) ≤ 0 := fun t => hV.hnonincr φ htraj t
  apply antitone_of_deriv_nonpos
  · -- Differentiable ℝ (V ∘ φ)
    intro t
    exact (h1 t).differentiableAt
  · -- ∀ t, deriv (V ∘ φ) t ≤ 0
    intro t
    rw [(h1 t).deriv]
    exact h2 t

-- A useful consequence: V(φ t) ≤ V(φ 0) for all t ≥ 0
lemma V_le_initial (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ)
    (hV : IsLocalLyapunovFunction f V x_eq)
    (φ : ℝ → ℝⁿ) (htraj : IsTrajectory φ f)
    (t : ℝ) (ht : 0 ≤ t) :
    V (φ t) ≤ V (φ 0) :=
  V_nonincreasing f V x_eq hV φ htraj ht


lemma V_le_initial_global (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ)
    (hV : IsGlobalLyapunovFunction f V x_eq)
    (φ : ℝ → ℝⁿ) (htraj : IsTrajectory φ f)
    (t : ℝ) (ht : 0 ≤ t) :
    V (φ t) ≤ V (φ 0) := by
  have hV_local : IsLocalLyapunovFunction f V x_eq := global_is_local_lyapunov f V x_eq hV
  exact V_le_initial f V x_eq hV_local φ htraj t ht



-- Lemma 2: trajectories are continuous)
lemma trajectory_continuous (φ : ℝ → ℝⁿ) (f : ℝⁿ → ℝⁿ) (htraj : IsTrajectory φ f) :
    Continuous φ := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (htraj t).differentiableAt.continuousAt

-- Lemma 3: the sphere around x_eq is nonempty, we prove this by finding one point in the sphere
lemma sphere_nonempty (x_eq : ℝⁿ) (ε : ℝ) (hn : 0 < n) (hε : 0 < ε) :
    (Metric.sphere x_eq ε).Nonempty := by
  refine ⟨x_eq + EuclideanSpace.single (⟨0, hn⟩ : Fin n) ε, ?_⟩
  rw [Metric.mem_sphere, dist_eq_norm]
  simp [PiLp.norm_single, abs_of_pos hε]


-- The main theorem: if there exists a Lyapunov function, then the equilibrium is stable
theorem local_lyapunov_stable
    (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ)
    (hn : 0 < n)
    (hV : IsLocalLyapunovFunction f V x_eq) :
    LyapunovStable f x_eq := by
  intro ε hε
  -- Step 1: The sphere of radius epsilon is compact and nonempty
  have hS_compact : IsCompact (Metric.sphere x_eq ε) := isCompact_sphere x_eq ε
  have hS_nonempty : (Metric.sphere x_eq ε).Nonempty := sphere_nonempty x_eq ε hn hε
  -- Step 2: V achieves a minimum m ON the sphere
  obtain ⟨x_min, hx_min_mem, hx_min_le⟩ :=
    hS_compact.exists_isMinOn hS_nonempty hV.hcont.continuousOn
  -- Let V(x_min) = m be the minimum value of V on the sphere
  set m := V x_min
  -- Step 3: x_min != x_eq, since x_eq is not on the sphere, so m > 0 by positivity of V
  have hx_min_ne : x_min ≠ x_eq := by
    intro heq
    simp [heq] at hx_min_mem
    linarith
  have hm_pos : 0 < m := hV.hpos x_min hx_min_ne
  -- Step 4: By continuity find delta with V x < m
  have hcont_at : ContinuousAt V x_eq := hV.hcont.continuousAt
  rw [Metric.continuousAt_iff] at hcont_at
  obtain ⟨δ', hδ'_pos, hδ'⟩ := hcont_at m hm_pos
  -- hδ' : ∀ y, dist y x_eq < δ' → dist (V y) (V x_eq) < m

  -- Take δ = min δ' ε (must be close enough for both V < m AND inside ball)
  refine ⟨min δ' ε, by positivity, ?_⟩
  intro φ htraj hclose t ht
  -- hclose : ‖φ 0 - x_eq‖ < min δ' ε

  -- Unpack the min bound into two separate facts
  have hclose_δ : dist (φ 0) x_eq < δ' := by
    rw [dist_eq_norm]; linarith [min_le_left δ' ε]
  have hclose_ε : dist (φ 0) x_eq < ε := by
    rw [dist_eq_norm]; linarith [min_le_right δ' ε]
-- ⑤ Suppose for contradiction ‖φ t - x_eq‖ ≥ ε
  by_contra hcontra
  push Not at hcontra
  -- hcontra : ε ≤ ‖φ t - x_eq‖

  -- ⑥ IVT: φ starts inside ball, ends outside → must cross the sphere
  have hφ_cont : Continuous φ := trajectory_continuous φ f htraj
  -- Define g s = dist (φ s) x_eq, which is continuous
  set g := fun s => dist (φ s) x_eq with hg_def
  have hg_cont : Continuous g := hφ_cont.dist continuous_const
  -- Restate the boundary conditions in terms of g
  have hg_0 : g 0 < ε := hclose_ε
  have hg_t : ε ≤ g t := by
    simp [hg_def, dist_eq_norm]
    linarith
  -- IVT: ∃ t' ∈ [0, t] with g t' = ε
  obtain ⟨t', ht'_mem, ht'_eq⟩ :=
    isPreconnected_Icc.intermediate_value₂
      (Set.mem_Icc.mpr ⟨le_refl 0, ht⟩)   -- 0 ∈ [0, t]
      (Set.mem_Icc.mpr ⟨ht, le_refl t⟩)   -- t ∈ [0, t]
      hg_cont.continuousOn
      continuousOn_const
      (le_of_lt hg_0)
      hg_t
  -- ⑦ φ t' is on the sphere
  have ht'_on_sphere : φ t' ∈ Metric.sphere x_eq ε := by
    rw [Metric.mem_sphere]
    exact ht'_eq  -- g t' = ε means dist (φ t') x_eq = ε
  -- V(φ t') ≥ m since x_min minimizes V on the sphere
  have hV_t'_ge : m ≤ V (φ t') :=
    hx_min_le ht'_on_sphere
  -- V(φ t') ≤ V(φ 0) since V∘φ is antitone and t' ≥ 0
  have hV_t'_le : V (φ t') ≤ V (φ 0) :=
    V_le_initial f V x_eq hV φ htraj t' ht'_mem.1
    -- V(φ t') ≥ m since x_min minimizes V on the sphere
  have hV_t'_ge : m ≤ V (φ t') :=
    hx_min_le ht'_on_sphere
  -- V(φ t') ≤ V(φ 0) since V∘φ is antitone and t' ≥ 0
  have hV_t'_le : V (φ t') ≤ V (φ 0) :=
    V_le_initial f V x_eq hV φ htraj t' ht'_mem.1
  -- V(φ 0) < m from continuity + closeness of φ 0 to x_eq
  have hV_init : V (φ 0) < m := by
    have h := hδ' hclose_δ
    rw [hV.hzero, Real.dist_eq] at h
    linarith [abs_lt.mp (by linarith : |V (φ 0) - 0| < m)]
  linarith



-- The core global bound: α₁(\|φ(t)\|) ≤ α₂(\|φ(0)\|)
-- This inequality proves that the trajectory is globally bounded by the initial state.
theorem global_lyapunov_bound
    (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ)
    (hV : IsGlobalLyapunovFunction f V x_eq)
    (φ : ℝ → ℝⁿ) (htraj : IsTrajectory φ f)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ α₁ α₂ : ℝ → ℝ, IsClassKInfty α₁ ∧ IsClassKInfty α₂ ∧
      α₁ ‖φ t - x_eq‖ ≤ α₂ ‖φ 0 - x_eq‖ := by
  -- Extract the Class K_infty functions from the Lyapunov property
  obtain ⟨α₁, α₂, hα₁_K, hα₂_K, h_sandwich⟩ := hV.halphas
  -- Provide them to fulfill the existential goal
  refine ⟨α₁, α₂, hα₁_K, hα₂_K, ?_⟩
  -- Step 1: α₁(‖φ t - x_eq‖) ≤ V(φ t) from the lower sandwich bound
  have h1 : α₁ ‖φ t - x_eq‖ ≤ V (φ t) := (h_sandwich (φ t)).1
  -- Step 2: V(φ t) ≤ V(φ 0) because V is non-increasing along the trajectory
  have h2 : V (φ t) ≤ V (φ 0) := V_le_initial_global f V x_eq hV φ htraj t ht
  -- Step 3: V(φ 0) ≤ α₂(‖φ 0 - x_eq‖) from the upper sandwich bound
  have h3 : V (φ 0) ≤ α₂ ‖φ 0 - x_eq‖ := (h_sandwich (φ 0)).2
  -- Step 4: Chain the inequalities together
  linarith

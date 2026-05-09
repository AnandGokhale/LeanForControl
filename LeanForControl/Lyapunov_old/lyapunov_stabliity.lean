import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.MonotoneConvergence

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
  -- Step 1: The ball of radius epsilon is compact and nonempty, V achieves a minimum ON the ball
  obtain ⟨x_min, hx_min_mem, hx_min_le⟩ :=
    (isCompact_sphere x_eq ε).exists_isMinOn (sphere_nonempty x_eq ε hn hε)
    hV.hcont.continuousOn
  -- Step 3: x_min != x_eq, since x_eq is not on the sphere, so m > 0 by positivity of V
  have hx_min_ne : x_min ≠ x_eq := by
    intro heq
    simp [heq] at hx_min_mem
    linarith
  have hm_pos : 0 < V x_min := hV.hpos x_min hx_min_ne
  -- Step 4: By continuity find delta with V x < m
  obtain ⟨δ', hδ'_pos, hδ'⟩ := Metric.continuousAt_iff.mp hV.hcont.continuousAt (V x_min) hm_pos
  -- Take δ = min δ' ε (must be close enough for both V < m AND inside ball)
  refine ⟨min δ' ε, by positivity, ?_⟩
  intro φ htraj hclose t ht
  by_contra hcontra
  push Not at hcontra
  -- Step 5: Continuity directly into the IVT
  obtain ⟨t', ht'_mem, ht'_eq⟩ := isPreconnected_Icc.intermediate_value₂
      (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht)
      ((trajectory_continuous φ f htraj).dist continuous_const).continuousOn
      continuousOn_const
      (le_of_lt (by rw [dist_eq_norm]; exact lt_of_lt_of_le hclose (min_le_right δ' ε)))
      (by rw [dist_eq_norm]; exact hcontra)
  -- Step 6: Isolate the V(φ 0) bound
  have hV_init : V (φ 0) < V x_min := by
    have h := hδ' (by rw [dist_eq_norm]; exact lt_of_lt_of_le hclose (min_le_left δ' ε))
    rw [hV.hzero, Real.dist_eq, sub_zero] at h
    exact (abs_lt.mp h).2
  -- Step 7: Collapse the final contradiction using a calc block
  exact lt_irrefl (V x_min) <| calc V x_min
    _ ≤ V (φ t') := hx_min_le (by rw [Metric.mem_sphere]; exact ht'_eq)
    _ ≤ V (φ 0)  := V_le_initial f V x_eq hV φ htraj t' ht'_mem.1
    _ < V x_min  := hV_init


theorem lyapunov_global_asymptotic_stable
    (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ)
    (hV : IsGlobalLyapunovFunction f V x_eq)
    (φ : ℝ → ℝⁿ) (htraj : IsIntegralSolution f φ) :
    Filter.Tendsto φ Filter.atTop (nhds x_eq) := by

  -- 1. Define the initial energy level c = V (φ 0)
  set c := V (φ 0)

  -- 2. Establish the sublevel set Ω_c
  set Ω_c := SublevelSet V c

  -- 3. Show Ω_c is compact
  have hΩ_compact : IsCompact Ω_c :=
    isCompact_sublevel_set V hV.hcont hV.hradial c

  -- 4. Prove positive invariance of Ω_c
  have h_invariant : ∀ t ≥ 0, φ t ∈ Ω_c := by
    -- V is strictly decreasing along trajectories (hV.hstrictneg + IsIntegralSolution)
    -- Since V(φ t) ≤ V(φ 0) = c, φ t ∈ Ω_c for all t ≥ 0.
    sorry

  -- 5. The limit L = inf { V(φ t) } exists and L ≥ 0
  -- (This is identical to your previous local proof setup)
  sorry

  -- 6. Contradiction if L > 0
  -- Let K = Ω_c ∩ { x | V x ≥ L }.
  -- K is closed (intersection of closed sets) and bounded (subset of Ω_c), thus compact.
  -- By EVT on K, Vdot attains a maximum -γ < 0.
  -- By the FTC, V(φ t) ≤ V(φ 0) - γt, which forces V(φ t) < 0 eventually, contradicting V ≥ 0.
  -- Therefore, L = 0.
  sorry

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

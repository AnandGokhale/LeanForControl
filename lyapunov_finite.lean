import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.Basic

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)


-- We define a trajectory
def IsTrajectory (φ : ℝ → ℝⁿ) (f : ℝⁿ → ℝⁿ) : Prop :=
  ∀ t : ℝ, HasDerivAt φ (f (φ t)) t

-- An equilibrium point
def IsEquilibrium (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  f x_eq = 0

-- And Lyapunov stability
def LyapunovStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ φ : ℝ → ℝⁿ,
    IsTrajectory φ f → -- Removed explicit 'n'
    ‖φ 0 - x_eq‖ < δ →
    ∀ t ≥ 0, ‖φ t - x_eq‖ < ε


-- Finally, the definition of a Lyapunov function
structure IsLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont    : Continuous V
  hzero    : V x_eq = 0
  hpos     : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x
  hderiv   : ∀ φ : ℝ → ℝⁿ, IsTrajectory φ f → -- Removed explicit 'n'
              ∀ t : ℝ, HasDerivAt (V ∘ φ) (fderiv ℝ V (φ t) (f (φ t))) t
  hnonincr : ∀ φ : ℝ → ℝⁿ, IsTrajectory φ f → -- Removed explicit 'n'
              ∀ t : ℝ, fderiv ℝ V (φ t) (f (φ t)) ≤ 0



-- Lemma 1: V is nonincreasing along trajectories
lemma V_nonincreasing (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ)
    (hV : IsLyapunovFunction f V x_eq)
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
    (hV : IsLyapunovFunction f V x_eq)
    (φ : ℝ → ℝⁿ) (htraj : IsTrajectory φ f)
    (t : ℝ) (ht : 0 ≤ t) :
    V (φ t) ≤ V (φ 0) :=
  V_nonincreasing f V x_eq hV φ htraj ht

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
theorem lyapunov_stable
    (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ)
    (hn : 0 < n)
    (hV : IsLyapunovFunction f V x_eq) :
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

import LeanForControl.Analysis.MonotoneFunctions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Basic
import Architect

import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKInfty
import LeanForControl.Comparison.ClassKL


open Set Filter Topology MeasureTheory Metric

/-!
# `Stability.LyapunovBounds`

Class K sandwich bounds for continuous positive-definite functions.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Appendix C.

## Main result

**Class K sandwich bounds** (`LyapunovClassKBounds`): Let `V : ℝⁿ → ℝ` be continuous on the
closed ball `closedBall 0 r`, with `V(0) = 0` and `V(x) > 0` for every nonzero `x` in that ball.
Then there exist class K functions `α₁, α₂` on `[0, r)` (i.e. `ClassK r b₁`, `ClassK r b₂`) such
that `α₁(‖x‖) ≤ V(x) ≤ α₂(‖x‖)` for all `x` with `‖x‖ < r`.

The intermediate comparisons `α₁ ≤ ψ` and `φ ≤ α₂` (steps 4–5 below) hold on the closed
interval `[0, r]`; the final bound is stated on the open ball because `α₁, α₂` are class K only
on `[0, r)`.

## Proof sketch

1. Define `ψ(s) = inf_{s ≤ ‖x‖ ≤ r} V(x)` (`psi_fn`) and `φ(s) = sup_{‖x‖ ≤ s} V(x)`
   (`phi_fn`).
2. Show `ψ(‖x‖) ≤ V(x) ≤ φ(‖x‖)` (`V_ge_psi`, `V_le_phi`).
3. Establish that `ψ` is zero at 0, positive away from 0, and monotone (`psi_fn_zero`,
   `psi_fn_pos`, `psi_fn_mono`); similarly for `φ` (`phi_fn_zero`, `phi_fn_mono`).
4. Apply the smoothing lemmas from `LeanForControl.Analysis.MonotoneFunctions` to obtain
   strictly monotone continuous functions `f ≤ ψ` and `φ ≤ g`.
5. Package via `ClassK.of_strictMono` to get the class K bounds `α₁ ≤ ψ ≤ V` and
   `V ≤ φ ≤ α₂`.
-/

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

-- ─── 1. Core Definitions ──────────────────────────────────────────────────────

/-- The annulus `{x | s ≤ ‖x‖ ≤ r}`, implemented as the set difference of two balls. -/
private def annulus (s r : ℝ) : Set ℝⁿ :=
  Metric.closedBall 0 r \ Metric.ball 0 s

/-- `ψ(s) = inf_{x ∈ annulus s r} V(x)`.
    Tracks the minimum of `V` on the shell `{s ≤ ‖x‖ ≤ r}`; serves as the
    lower comparison function before smoothing. -/
private noncomputable def psi_fn (r : ℝ) (V : ℝⁿ → ℝ) (s : ℝ) : ℝ :=
  sInf (V '' annulus s r)

/-- `φ(s) = sup_{‖x‖ ≤ s} V(x)`.
    Tracks the maximum of `V` on the closed ball of radius `s`; serves as the
    upper comparison function before smoothing. -/
private noncomputable def phi_fn (V : ℝⁿ → ℝ) (s : ℝ) : ℝ :=
  sSup (V '' Metric.closedBall 0 s)

-- ─── 2. Properties of the Lower Comparison Function ψ ─────────────────────────

/-- `ψ(0) = 0`: the annulus degenerates to `{0}`, so the infimum is `V(0) = 0`. -/
private lemma psi_fn_zero {r : ℝ} {V : ℝⁿ → ℝ} (hr : 0 < r) (hV_zero : V 0 = 0)
    (hV_nonneg : ∀ x ∈ closedBall (0 : ℝⁿ) r, 0 ≤ V x) : psi_fn r V 0 = 0 := by
  unfold psi_fn
  apply le_antisymm
  · -- sInf ≤ 0: exhibit V(0) = 0 as a member of the image
    apply csInf_le
    · use 0
      rintro _ ⟨x, hx, rfl⟩
      exact hV_nonneg x hx.1
    · exact ⟨0, ⟨Metric.mem_closedBall_self hr.le,
        fun h => not_lt_of_ge (norm_nonneg 0) (mem_ball_zero_iff.mp h)⟩, hV_zero⟩
  · -- 0 ≤ sInf: V is non-negative on the annulus, and the annulus is non-empty
    apply le_csInf
    · exact ⟨0, 0, ⟨Metric.mem_closedBall_self hr.le,
        fun h => not_lt_of_ge (norm_nonneg 0) (mem_ball_zero_iff.mp h)⟩, hV_zero⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hV_nonneg x hx.1

/-- `ψ(s) > 0` for `0 < s ≤ r`: the Extreme Value Theorem gives a minimizer `x` in
    the compact annulus; since `‖x‖ ≥ s > 0` we have `x ≠ 0`, hence `V(x) > 0`. -/
private lemma psi_fn_pos {r : ℝ} {V : ℝⁿ → ℝ} [NeZero n]
    (hV_cont : ContinuousOn V (closedBall (0 : ℝⁿ) r))
    (hV_pos : ∀ x : ℝⁿ, x ∈ closedBall (0 : ℝⁿ) r → x ≠ 0 → 0 < V x)
    {s : ℝ} (hs_pos : 0 < s) (hs_le : s ≤ r) : 0 < psi_fn r V s := by
  unfold psi_fn
  have h_comp : IsCompact (annulus s r) :=
    IsCompact.diff (isCompact_closedBall (0 : ℝⁿ) r) isOpen_ball
  have h_sub : annulus s r ⊆ closedBall (0 : ℝⁿ) r := Set.diff_subset
  have hV_contA : ContinuousOn V (annulus s r) := hV_cont.mono h_sub
  -- The annulus is non-empty: the unit-vector coordinate scaled to radius s lies in it
  have h_nonempty : (annulus s r : Set ℝⁿ).Nonempty := by
    let x : ℝⁿ := PiLp.single 2 (0 : Fin n) s
    use x
    have hx_norm : ‖x‖ = s := by
      rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos hs_pos]
    simp only [annulus, Set.mem_diff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right,
      hx_norm]
    exact ⟨hs_le, not_lt_of_ge le_rfl⟩
  -- EVT: attain the infimum at some x ∈ annulus
  obtain ⟨x, hx_mem, hx_min⟩ := h_comp.exists_isMinOn h_nonempty hV_contA
  -- The infimum equals V(x)
  have h_inf_eq : sInf (V '' annulus s r) = V x := by
    apply le_antisymm
    · apply csInf_le
      · use 0
        rintro _ ⟨y, hy, rfl⟩
        by_cases hy0 : y = 0
        · subst hy0
          have h_norm : s ≤ ‖(0 : ℝⁿ)‖ :=
            not_lt.mp fun h => hy.2 (mem_ball_zero_iff.mpr h)
          rw [norm_zero] at h_norm; linarith
        · exact (hV_pos y (h_sub hy) hy0).le
      · exact Set.mem_image_of_mem V hx_mem
    · apply le_csInf
      · exact h_nonempty.image V
      · rintro _ ⟨y, hy, rfl⟩
        exact hx_min hy
  rw [h_inf_eq]
  -- x ∈ annulus so ‖x‖ ≥ s > 0, hence x ≠ 0, hence V(x) > 0
  have hx_ne : x ≠ 0 := by
    rintro rfl
    have h_norm : s ≤ ‖(0 : ℝⁿ)‖ :=
      not_lt.mp fun h => hx_mem.2 (mem_ball_zero_iff.mpr h)
    rw [norm_zero] at h_norm; linarith
  exact hV_pos x (h_sub hx_mem) hx_ne

/-- `ψ` is monotone: enlarging the annulus (decreasing the inner radius) can only
    decrease the infimum, since we are taking inf over a larger set. -/
private lemma psi_fn_mono {r : ℝ} {V : ℝⁿ → ℝ} [NeZero n]
    (hV_cont : ContinuousOn V (closedBall (0 : ℝⁿ) r))
    {s₁ s₂ : ℝ} (h_le : s₁ ≤ s₂) (h_bound : s₂ ≤ r) (hs1_nonneg : 0 ≤ s₁) :
    psi_fn r V s₁ ≤ psi_fn r V s₂ := by
  unfold psi_fn
  apply csInf_le_csInf
  · -- The image over the full closed ball (a superset) is bounded below
    have h_comp : IsCompact (closedBall (0 : ℝⁿ) r) := isCompact_closedBall _ _
    have h_bdd := (h_comp.image_of_continuousOn hV_cont).bddBelow
    exact h_bdd.mono (Set.image_mono Set.diff_subset)
  · -- annulus s₁ r is non-empty: exhibit a point at radius s₂ ≥ s₁
    let x : ℝⁿ := PiLp.single 2 (0 : Fin n) s₂
    have hx_norm : ‖x‖ = s₂ := by
      rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg (hs1_nonneg.trans h_le)]
    refine ⟨V x, x, ?_, rfl⟩
    simp only [annulus, Set.mem_diff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right,
      hx_norm]
    exact ⟨h_bound, not_lt_of_ge le_rfl⟩
  · -- annulus s₂ r ⊆ annulus s₁ r (larger inner radius ⟹ smaller set ⟹ larger infimum)
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    simp only [annulus, Set.mem_diff, Metric.mem_closedBall, dist_zero_right,
      Metric.mem_ball, not_lt] at hx ⊢
    exact ⟨hx.1, h_le.trans hx.2⟩

-- ─── 3. Lower Sandwich: ψ(‖x‖) ≤ V(x) ───────────────────────────────────────

/-- `V(x) ≥ ψ(‖x‖)`: since `x` belongs to the annulus `{y | ‖x‖ ≤ ‖y‖ ≤ r}`,
    `V(x)` is an element of the set whose infimum defines `ψ(‖x‖)`. -/
private lemma V_ge_psi {r : ℝ} {V : ℝⁿ → ℝ}
    (hV_zero : V 0 = 0)
    (hV_pos : ∀ x : ℝⁿ, x ∈ closedBall 0 r → x ≠ 0 → 0 < V x)
    {x : ℝⁿ} (hx : ‖x‖ ≤ r) : psi_fn r V ‖x‖ ≤ V x := by
  unfold psi_fn
  apply csInf_le
  · -- 0 is a lower bound: V ≥ 0 on the annulus (positive-definiteness + V(0) = 0)
    use 0
    rintro _ ⟨y, hy_annulus, rfl⟩
    simp only [annulus, Set.mem_diff] at hy_annulus
    rcases eq_or_ne y 0 with rfl | hne
    · exact le_of_eq hV_zero.symm
    · exact (hV_pos y hy_annulus.1 hne).le
  · -- x lies in annulus ‖x‖ r, so V(x) is in the image
    exact ⟨x, ⟨mem_closedBall_zero_iff.mpr hx,
      fun h => absurd (mem_ball_zero_iff.mp h) (lt_irrefl ‖x‖)⟩, rfl⟩

-- ─── 4. Properties of the Upper Comparison Function φ ─────────────────────────

/-- `φ(0) = 0`: the closed ball of radius 0 contains only `0`, so the supremum is `V(0) = 0`. -/
private lemma phi_fn_zero {V : ℝⁿ → ℝ} (hV_zero : V 0 = 0) : phi_fn V 0 = 0 := by
  unfold phi_fn
  apply le_antisymm
  · apply csSup_le
    · exact ⟨0, 0, Metric.mem_closedBall_self le_rfl, hV_zero⟩
    · -- Every element of the image is V(0) = 0 (the only point in the ball is 0)
      rintro _ ⟨x, hx, rfl⟩
      simp only [Metric.mem_closedBall, dist_zero_right, norm_le_zero_iff] at hx
      rw [hx, hV_zero]
  · apply le_csSup
    · use 0
      rintro _ ⟨x, hx, rfl⟩
      simp only [Metric.mem_closedBall, dist_zero_right, norm_le_zero_iff] at hx
      rw [hx, hV_zero]
    · exact ⟨0, Metric.mem_closedBall_self le_rfl, hV_zero⟩

/-- `φ` is monotone: a larger ball contains more of `V`, so its supremum is no smaller. -/
private lemma phi_fn_mono {r : ℝ} {V : ℝⁿ → ℝ} (hV_cont : ContinuousOn V (closedBall (0 : ℝⁿ) r))
    {s₁ s₂ : ℝ} (h_le : s₁ ≤ s₂) (h_bound : s₂ ≤ r) (hs1_nonneg : 0 ≤ s₁) :
    phi_fn V s₁ ≤ phi_fn V s₂ := by
  unfold phi_fn
  apply csSup_le_csSup
  · -- The image over the larger ball is bounded above (compact + continuous)
    have h_comp : IsCompact (closedBall (0 : ℝⁿ) s₂) := isCompact_closedBall (0 : ℝⁿ) s₂
    have h_sub : closedBall (0 : ℝⁿ) s₂ ⊆ closedBall (0 : ℝⁿ) r :=
      Metric.closedBall_subset_closedBall h_bound
    exact (h_comp.image_of_continuousOn (hV_cont.mono h_sub)).bddAbove
  · -- The smaller ball's image is non-empty: V(0) ∈ V '' closedBall 0 s₁
    exact ⟨V 0, 0, Metric.mem_closedBall_self hs1_nonneg, rfl⟩
  · -- closedBall s₁ ⊆ closedBall s₂
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, Metric.closedBall_subset_closedBall h_le hx, rfl⟩

/-- `φ` is continuous at `0` from the right: on a small ball `V` is close to `V(0) = 0`, so
    its supremum there is too. -/
private lemma phi_fn_continuousWithinAt {r : ℝ} {V : ℝⁿ → ℝ} (hr : 0 < r)
    (hV_cont : ContinuousOn V (closedBall (0 : ℝⁿ) r)) (hV_zero : V 0 = 0) :
    ContinuousWithinAt (phi_fn V) (Set.Icc 0 r) 0 := by
  refine Metric.continuousWithinAt_iff.mpr fun ε hε => ?_
  obtain ⟨δ, hδ, hV⟩ := Metric.continuousWithinAt_iff.mp
    (hV_cont 0 (Metric.mem_closedBall_self hr.le)) (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun {s} hs hds => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1] at hds
  -- every value of `V` on `closedBall 0 s` is within `ε / 2` of `V 0 = 0`
  have h_le : phi_fn V s ≤ ε / 2 := by
    refine csSup_le ⟨V 0, 0, Metric.mem_closedBall_self hs.1, rfl⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    have h := hV (Metric.closedBall_subset_closedBall hs.2 hx)
      ((Metric.mem_closedBall.mp hx).trans_lt hds)
    rw [hV_zero, Real.dist_eq, sub_zero] at h
    exact (le_abs_self _).trans h.le
  have h_ge : 0 ≤ phi_fn V s := phi_fn_zero hV_zero ▸ phi_fn_mono hV_cont hs.1 hs.2 le_rfl
  rw [phi_fn_zero hV_zero, Real.dist_eq, sub_zero, abs_of_nonneg h_ge]
  linarith

-- ─── 5. Upper Sandwich: V(x) ≤ φ(‖x‖) ───────────────────────────────────────

/-- `V(x) ≤ φ(‖x‖)`: since `x ∈ closedBall 0 ‖x‖`, `V(x)` is an element of the
    set whose supremum defines `φ(‖x‖)`. -/
private lemma V_le_phi {r : ℝ} {V : ℝⁿ → ℝ}
    (hV_cont : ContinuousOn V (closedBall 0 r))
    {x : ℝⁿ} (hx : ‖x‖ ≤ r) : V x ≤ phi_fn V ‖x‖ := by
  unfold phi_fn
  apply le_csSup
  · -- The image over closedBall 0 ‖x‖ is bounded above (compact + continuous)
    have h_sub : closedBall (0 : ℝⁿ) ‖x‖ ⊆ closedBall (0 : ℝⁿ) r :=
      Metric.closedBall_subset_closedBall hx
    have h_comp : IsCompact (closedBall (0 : ℝⁿ) ‖x‖) := isCompact_closedBall (0 : ℝⁿ) ‖x‖
    have h_cont : ContinuousOn V (closedBall 0 ‖x‖) := hV_cont.mono h_sub
    exact (h_comp.image_of_continuousOn h_cont).bddAbove
  · -- x ∈ closedBall 0 ‖x‖
    exact ⟨x, mem_closedBall_zero_iff.mpr le_rfl, rfl⟩

-- ─── 6. Class K Packaging ─────────────────────────────────────────────────────

/-! ### Packaging ψ and φ into Class K Functions

We apply the smoothing results from `LeanForControl.Analysis.MonotoneFunctions` to turn the
(merely monotone) comparison functions `ψ` and `φ` into full `ClassK` structures.  The final
bounds follow by transitivity: `α₁ ≤ ψ ≤ V ≤ φ ≤ α₂`. -/

/-- There exists a class K function `α₁ : ClassK r b₁` (class K on `[0, r)`) with
    `α₁(s) ≤ ψ(s)` for every `s ∈ [0, r]`. The comparison includes the endpoint `s = r`, where
    `α₁.toFun` is still defined although it lies outside the class-K domain.
    Combined with `V_ge_psi`, this gives `α₁(‖x‖) ≤ V(x)` for `‖x‖ ≤ r`. -/
private lemma exists_classK_lower_bound [NeZero n] (hr : 0 < r)
    (hV_cont : ContinuousOn V (closedBall 0 r))
    (hV_zero : V 0 = 0) (hV_pos : ∀ x : ℝⁿ, x ∈ closedBall 0 r → x ≠ 0 → 0 < V x) :
    ∃ (b₁ : ℝ) (α₁ : ClassK r b₁), ∀ s, 0 ≤ s → s ≤ r → α₁.toFun s ≤ psi_fn r V s := by
  -- Derive non-negativity from V(0) = 0 and strict positivity away from 0
  have hV_nonneg : ∀ x ∈ closedBall (0 : ℝⁿ) r, 0 ≤ V x := fun x hx =>
    if h : x = 0 then by simp [h, hV_zero] else (hV_pos x hx h).le
  -- Verify the three hypotheses of the lower smoothing lemma for ψ
  have hψ_zero : psi_fn r V 0 = 0 := psi_fn_zero hr hV_zero hV_nonneg
  have hψ_pos : ∀ s, 0 < s → s ≤ r → 0 < psi_fn r V s := fun s hs hs_le =>
    psi_fn_pos hV_cont hV_pos hs hs_le
  have hψ_mono : ∀ s₁ s₂, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ r → psi_fn r V s₁ ≤ psi_fn r V s₂ :=
    fun s₁ s₂ hs1 hs_le hs2_le => psi_fn_mono hV_cont hs_le hs2_le hs1
  -- Apply the smoothing lemma to get a strictly monotone continuous f ≤ ψ
  rcases exists_strictMono_lower_bound r hr (psi_fn r V) hψ_zero hψ_pos hψ_mono
    with ⟨f, b₁, hb₁_pos, hf_zero, hf_r, hf_cont, hf_mono, hf_bound⟩
  exact ⟨b₁, ClassK.of_strictMono hr hb₁_pos f hf_zero hf_r hf_cont hf_mono, hf_bound⟩

/-- There exists a class K function `α₂ : ClassK r b₂` (class K on `[0, r)`) with
    `φ(s) ≤ α₂(s)` for every `s ∈ [0, r]`. The comparison includes the endpoint `s = r`, where
    `α₂.toFun` is still defined although it lies outside the class-K domain.
    Combined with `V_le_phi`, this gives `V(x) ≤ α₂(‖x‖)` for `‖x‖ ≤ r`. -/
private lemma exists_classK_upper_bound (hr : 0 < r) (hV_cont : ContinuousOn V (closedBall 0 r))
    (hV_zero : V 0 = 0) :
    ∃ (b₂ : ℝ) (α₂ : ClassK r b₂), ∀ s, 0 ≤ s → s ≤ r → phi_fn V s ≤ α₂.toFun s := by
  -- Verify the three hypotheses of the upper smoothing lemma for φ
  have hφ_zero : phi_fn V 0 = 0 := phi_fn_zero hV_zero
  have hφ_mono : MonotoneOn (phi_fn V) (Set.Icc 0 r) :=
    fun _ hs₁ _ hs₂ hle => phi_fn_mono hV_cont hle hs₂.2 hs₁.1
  have hφ_cont : ContinuousWithinAt (phi_fn V) (Set.Icc 0 r) 0 :=
    phi_fn_continuousWithinAt hr hV_cont hV_zero
  -- Apply the smoothing lemma to get a strictly monotone continuous φ ≤ f
  rcases exists_strictMono_upper_bound r hr (phi_fn V) hφ_zero hφ_mono hφ_cont
    with ⟨f, b₂, hb₂_pos, hf_zero, hf_r, hf_cont, hf_mono, hf_bound⟩
  exact ⟨b₂, ClassK.of_strictMono hr hb₂_pos f hf_zero hf_r hf_cont hf_mono, hf_bound⟩

-- ─── 7. Main Theorem ──────────────────────────────────────────────────────────

/-- **Class K sandwich bounds**: For any `V` continuous and positive definite on the closed
    ball `closedBall 0 r`, there exist class K functions `α₁`, `α₂` on `[0, r)` such that

      `α₁(‖x‖) ≤ V(x) ≤ α₂(‖x‖)` for all `x` with `‖x‖ < r`.

    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.3 (proved in his Appendix C.4).
    Differences:
    - The bound holds on the open ball `‖x‖ < r`, with `α₁, α₂` class `K` on `[0, r)`; Khalil
      states it on `[0, r]`.
    - The radially unbounded `K∞` case is not derived here. -/
@[blueprint "thm:lyapunov-class-K-bounds"
  (title := "Class $\\mathcal{K}$ sandwich bounds")
  (statement := /-- Let $V : \mathbb{R}^{n} \to \mathbb{R}$ be continuous on $\overline{B}(0,r)$
    with
    $V(0) = 0$ and $V(x) > 0$ for every nonzero $x$ in that ball.  Then there are class
    $\mathcal{K}$ functions $\alpha_1, \alpha_2$ on $[0, r)$ with
    \[
      \alpha_1(\|x\|) \;\le\; V(x) \;\le\; \alpha_2(\|x\|)
      \qquad \forall\, \|x\| < r.
    \]
    The conclusion holds on the \emph{open} ball: $\alpha_1$ and $\alpha_2$ are class
    $\mathcal{K}$ on $[0, r)$, so neither is defined at $\|x\| = r$.

    This is what lets a Lyapunov argument be run entirely in terms of comparison functions:
    positive definiteness is a pointwise condition, and this converts it into monotone bounds
    in the single variable $\|x\|$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.3 (proved in his Appendix C.4).
    Differences: \begin{itemize} \item The bound holds on the open ball $\|x\| < r$, with $\alpha_1,
    \alpha_2$ class $\mathcal{K}$ on $[0,r)$; Khalil states it on $[0,r]$. \item The radially
    unbounded $\mathcal{K}_{\infty}$ case is not derived here. \end{itemize}
  -/)
  (proof := /-- For the lower bound take $\psi(s) = \inf\{V(x) : s \le \|x\| \le r\}$,
    the infimum of $V$ over the annulus of inner radius $s$: it vanishes at $0$, is positive for
    $s > 0$ by compactness and positive definiteness, and is nondecreasing.  For the upper bound
    take $\phi(s) = \sup\{V(x) : \|x\| \le s\}$, similarly nondecreasing and vanishing at
    $0$.  Neither is continuous or strictly monotone, so smooth them:
    \cref{lem:exists-strictMono-lower-bound} gives a class $\mathcal{K}$ minorant of $\psi$
    and \cref{lem:exists-strictMono-upper-bound} a class $\mathcal{K}$ majorant of $\phi$.
    Since $\psi(\|x\|) \le V(x) \le \phi(\|x\|)$ pointwise, these sandwich $V$. -/)]
theorem LyapunovClassKBounds [NeZero n] (hr : 0 < r) (hV_cont : ContinuousOn V (closedBall 0 r))
    (hV_zero : V 0 = 0) (hV_pos : ∀ x : ℝⁿ, x ∈ closedBall 0 r → x ≠ 0 → 0 < V x) :
    ∃ (b₁ b₂ : ℝ) (α₁ : ClassK r b₁) (α₂ : ClassK r b₂),
      ∀ x : ℝⁿ, ‖x‖ < r → α₁.toFun ‖x‖ ≤ V x ∧ V x ≤ α₂.toFun ‖x‖ := by
  obtain ⟨b₁, α₁, hα₁_le_psi⟩ := exists_classK_lower_bound hr hV_cont hV_zero hV_pos
  obtain ⟨b₂, α₂, hphi_le_α₂⟩ := exists_classK_upper_bound hr hV_cont hV_zero
  refine ⟨b₁, b₂, α₁, α₂, ?_⟩
  intro x hx
  have h_norm_pos : 0 ≤ ‖x‖ := norm_nonneg x
  -- Chain both inequalities: α₁ ≤ ψ ≤ V and V ≤ φ ≤ α₂
  exact ⟨le_trans (hα₁_le_psi ‖x‖ h_norm_pos hx.le) (V_ge_psi hV_zero hV_pos hx.le),
         le_trans (V_le_phi hV_cont hx.le) (hphi_le_α₂ ‖x‖ h_norm_pos hx.le)⟩

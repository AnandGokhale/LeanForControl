import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.MonotoneContinuity


open Set Filter Topology MeasureTheory intervalIntegral


variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)




/-! ## Class K and K∞ functions -/

-- α : [0, ∞) → ℝ, continuous, zero at zero, strictly increasing.
-- def IsClassK (α : ℝ → ℝ) : Prop :=
--   ContinuousOn α (Set.Ici 0) ∧ α 0 = 0 ∧ StrictMonoOn α (Set.Ici 0)


structure ClassK (a b : ℝ) where
  ha : 0 < a
  hb : 0 < b

  -- Total functions for smooth algebraic manipulation
  toFun : ℝ → ℝ
  invFun : ℝ → ℝ

  -- Core Class K properties
  map_zero : toFun 0 = 0
  continuous : ContinuousOn toFun (Set.Ico 0 a)
  strict_mono : StrictMonoOn toFun (Set.Ico 0 a)

  -- Strict bijection guarantees explicitly where you need them
  maps_to : Set.MapsTo toFun (Set.Ico 0 a) (Set.Ico 0 b)
  inv_maps_to : Set.MapsTo invFun (Set.Ico 0 b) (Set.Ico 0 a)
  left_inv : Set.LeftInvOn invFun toFun (Set.Ico 0 a)
  right_inv : Set.RightInvOn invFun toFun (Set.Ico 0 b)

-- 1. Coercion: This allows you to write `α x` instead of `α.toFun x`
instance {a b : ℝ} : CoeFun (ClassK a b) (fun _ => ℝ → ℝ) where
  coe α := α.toFun

-- 2. The Inverse: Trivial to define, and it outputs a rigorous Class K function
def ClassK.symm {a b : ℝ} (α : ClassK a b) : ClassK b a where
  ha := α.hb
  hb := α.ha
  toFun := α.invFun
  invFun := α.toFun
  maps_to := α.inv_maps_to
  inv_maps_to := α.maps_to
  left_inv := α.right_inv
  right_inv := α.left_inv
  -- You will need to provide the topological proofs here once,
  -- and then never worry about them again.
  map_zero := by   -- Proof that α⁻¹(0) = 0
    have h0 : (0 : ℝ) ∈ Set.Ico 0 a := ⟨le_refl 0, α.ha⟩
    have h_left := α.left_inv h0
    rw [α.map_zero] at h_left
    exact h_left
  continuous := by
    -- Strict monotonicity of invFun on Ico 0 b (same argument as strict_mono below)
    have inv_mono : StrictMonoOn α.invFun (Set.Ico 0 b) := by
      intro y₁ hy₁ y₂ hy₂ hy_lt
      apply lt_of_not_ge
      intro h_ge
      rcases eq_or_lt_of_le h_ge with h_eq | h_gt
      · have h_apply : α.toFun (α.invFun y₁) = α.toFun (α.invFun y₂) := by rw [h_eq]
        rw [α.right_inv hy₁, α.right_inv hy₂] at h_apply; linarith
      · have h_apply := α.strict_mono (α.inv_maps_to hy₂) (α.inv_maps_to hy₁) h_gt
        rw [α.right_inv hy₂, α.right_inv hy₁] at h_apply; linarith
    -- invFun 0 = 0
    have inv_zero : α.invFun 0 = 0 := by
      have h0 : (0 : ℝ) ∈ Set.Ico 0 a := ⟨le_refl 0, α.ha⟩
      have h_left := α.left_inv h0; rw [α.map_zero] at h_left; exact h_left
    -- invFun surjects from Ico 0 b onto Ico 0 a (via left_inv + maps_to)
    have inv_surj : ∀ x ∈ Set.Ico 0 a, ∃ w ∈ Set.Ico 0 b, α.invFun w = x :=
      fun x hx => ⟨α.toFun x, α.maps_to hx, α.left_inv hx⟩
    -- Helper: for any y ∈ Ico 0 b, invFun y < a
    have inv_lt_a : ∀ y ∈ Set.Ico 0 b, α.invFun y < a :=
      fun y hy => (α.inv_maps_to hy).2
    -- Witness helper for hfs_r: given invFun y < z, find w ∈ Ico 0 b with invFun w ∈ Ioc (invFun y) z
    have find_right : ∀ (y : ℝ), y ∈ Set.Ico 0 b → ∀ z > α.invFun y,
        ∃ w ∈ Set.Ico 0 b, α.invFun w ∈ Set.Ioc (α.invFun y) z := by
      intro y hy z hz
      by_cases hza : z < a
      · -- z ∈ Ico 0 a; take w = toFun z, invFun w = z
        -- 0 ≤ invFun y < z, so 0 ≤ z
        have hz0 : 0 ≤ z := le_of_lt (lt_of_le_of_lt (α.inv_maps_to hy).1 hz)
        obtain ⟨w, hw, hinv⟩ := inv_surj z ⟨hz0, hza⟩
        exact ⟨w, hw, by rw [hinv]; exact ⟨hz, le_refl z⟩⟩
      · -- z ≥ a; pick any x ∈ Ioo (invFun y) a
        have hiy_lt_a : α.invFun y < a := inv_lt_a y hy
        obtain ⟨x, hxl, hxr⟩ := exists_between hiy_lt_a
        have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt (α.inv_maps_to hy).1 hxl)
        obtain ⟨w, hw, hinv⟩ := inv_surj x ⟨hx0, hxr⟩
        exact ⟨w, hw, by rw [hinv]; exact ⟨hxl, le_of_lt (lt_of_lt_of_le hxr (not_lt.mp hza))⟩⟩
    -- Prove ContinuousOn pointwise
    intro y hy
    obtain ⟨hy0, hyb⟩ := hy
    by_cases h0 : y = 0
    · -- Left endpoint y = 0: right continuity within Ici 0, then restrict to Ico 0 b
      subst h0
      apply ContinuousWithinAt.mono _ Set.Ico_subset_Ici_self
      apply StrictMonoOn.continuousWithinAt_right_of_exists_between inv_mono
      · -- Ico 0 b ∈ 𝓝[≥] 0
        rw [mem_nhdsGE_iff_exists_Ico_subset' α.hb]
        exact ⟨b, α.hb, Set.Ico_subset_Ico_right le_rfl⟩
      · -- ∀ z > invFun 0 = 0, find c ∈ Ico 0 b with invFun c ∈ Ioc 0 z
        rw [inv_zero]
        intro z hz
        by_cases hza : z < a
        · have hz0 : 0 ≤ z := le_of_lt hz
          obtain ⟨w, hw, hinv⟩ := inv_surj z ⟨hz0, hza⟩
          exact ⟨w, hw, by rw [hinv]; exact ⟨hz, le_refl z⟩⟩
        · obtain ⟨x, hx0, hxa⟩ := exists_between α.ha
          obtain ⟨w, hw, hinv⟩ := inv_surj x ⟨le_of_lt hx0, hxa⟩
          exact ⟨w, hw, by rw [hinv]; exact ⟨hx0, le_of_lt (lt_of_lt_of_le hxa (not_lt.mp hza))⟩⟩
    · -- Interior point 0 < y < b: ContinuousAt → ContinuousWithinAt
      have hy0' : 0 < y := lt_of_le_of_ne hy0 (Ne.symm h0)
      have hico_nhd : Set.Ico 0 b ∈ 𝓝 y := Ico_mem_nhds_iff.mpr ⟨hy0', hyb⟩
      apply ContinuousAt.continuousWithinAt
      apply StrictMonoOn.continuousAt_of_exists_between inv_mono hico_nhd
      · -- ∀ z < invFun y, find c ∈ Ico 0 b with invFun c ∈ Ico z (invFun y)
        intro z hz
        have hinvy_pos : 0 < α.invFun y := by
          have h0b : (0 : ℝ) ∈ Set.Ico 0 b := ⟨le_refl 0, α.hb⟩
          have := inv_mono h0b ⟨le_of_lt hy0', hyb⟩ hy0'
          rwa [inv_zero] at this
        have hinvy_lt_a : α.invFun y < a := inv_lt_a y ⟨le_of_lt hy0', hyb⟩
        -- pick x ∈ Ioo (max z 0) (invFun y) ⊆ Ico 0 a
        have hmax : max z 0 < α.invFun y := max_lt hz hinvy_pos
        obtain ⟨x, hxl, hxr⟩ := exists_between hmax
        have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt (le_max_right z 0) hxl)
        obtain ⟨w, hw, hinv⟩ := inv_surj x ⟨hx0, lt_trans hxr hinvy_lt_a⟩
        exact ⟨w, hw, hinv ▸ ⟨le_of_lt (lt_of_le_of_lt (le_max_left z 0) hxl), hxr⟩⟩
      · -- ∀ z > invFun y, find c ∈ Ico 0 b with invFun c ∈ Ioc (invFun y) z
        exact find_right y ⟨le_of_lt hy0', hyb⟩

  strict_mono := by -- Proof that the inverse of a strict mono is strict mono
    intro y₁ hy₁ y₂ hy₂ hy_lt
    have hx₁ := α.inv_maps_to hy₁
    have hx₂ := α.inv_maps_to hy₂
    apply lt_of_not_ge
    intro h_ge
    rcases eq_or_lt_of_le h_ge with h_eq | h_gt
    · -- Case 1: invFun y₁ = invFun y₂
      have h_apply : α.toFun (α.invFun y₁) = α.toFun (α.invFun y₂) := by rw [h_eq]
      -- Simplify to y₁ = y₂ using right_inv
      rw [α.right_inv hy₁, α.right_inv hy₂] at h_apply
      linarith -- Contradicts y₁ < y₂
    · -- Case 2: invFun y₁ > invFun y₂
      -- Apply strict monotonicity of the forward function
      have h_apply := α.strict_mono hx₂ hx₁ h_gt
      -- Simplify to y₂ < y₁ using right_inv
      rw [α.right_inv hy₂, α.right_inv hy₁] at h_apply
      linarith -- Contradicts y₁ < y₂

/-- Composition of two ClassK functions is ClassK. -/
def ClassK.comp {a b c : ℝ} (β : ClassK b c) (α : ClassK a b) : ClassK a c where
  ha        := α.ha
  hb        := β.hb
  toFun     := β.toFun ∘ α.toFun
  invFun    := α.invFun ∘ β.invFun
  map_zero  := by change β.toFun (α.toFun 0) = 0; rw [α.map_zero, β.map_zero]
  continuous := β.continuous.comp α.continuous α.maps_to
  strict_mono := by
    intro x hx y hy hxy
    exact β.strict_mono (α.maps_to hx) (α.maps_to hy) (α.strict_mono hx hy hxy)
  maps_to   := β.maps_to.comp α.maps_to
  inv_maps_to := α.inv_maps_to.comp β.inv_maps_to
  left_inv  := by
    intro x hx
    change α.invFun (β.invFun (β.toFun (α.toFun x))) = x
    rw [β.left_inv (α.maps_to hx)]
    exact α.left_inv hx
  right_inv := by
    intro y hy
    change β.toFun (α.toFun (α.invFun (β.invFun y))) = y
    rw [α.right_inv (β.inv_maps_to hy)]
    exact β.right_inv hy

-- Class K and radially unbounded: α(r) → ∞ as r → ∞.
structure ClassKInfty where
  toFun : ℝ → ℝ
  invFun : ℝ → ℝ

  -- Core Class K properties on [0, ∞)
  map_zero : toFun 0 = 0
  continuous : ContinuousOn toFun (Ici 0)
  strict_mono : StrictMonoOn toFun (Ici 0)

  -- The infinity condition
  tendsto_atTop : Tendsto toFun atTop atTop

  -- Global bijections on [0, ∞)
  maps_to : MapsTo toFun (Ici 0) (Ici 0)
  inv_maps_to : MapsTo invFun (Ici 0) (Ici 0)
  left_inv : LeftInvOn invFun toFun (Ici 0)
  right_inv : RightInvOn invFun toFun (Ici 0)

-- Coercion so you can evaluate it as `α r`
instance : CoeFun ClassKInfty (fun _ => ℝ → ℝ) where
  coe α := α.toFun

-- The inverse is trivially another Class K_infty function
-- Helper: invFun is strictly monotone on [0, ∞)
private lemma ClassKInfty.invFun_strictMono (α : ClassKInfty) :
    StrictMonoOn α.invFun (Set.Ici 0) := by
  intro y₁ hy₁ y₂ hy₂ hy_lt
  apply lt_of_not_ge
  intro h_ge
  rcases eq_or_lt_of_le h_ge with h_eq | h_gt
  · have h_apply : α.toFun (α.invFun y₁) = α.toFun (α.invFun y₂) := by rw [h_eq]
    rw [α.right_inv hy₁, α.right_inv hy₂] at h_apply; linarith
  · have h_apply := α.strict_mono (α.inv_maps_to hy₂) (α.inv_maps_to hy₁) h_gt
    rw [α.right_inv hy₂, α.right_inv hy₁] at h_apply; linarith

-- Helper: invFun 0 = 0
private lemma ClassKInfty.invFun_zero (α : ClassKInfty) : α.invFun 0 = 0 := by
  have h0 : (0 : ℝ) ∈ Set.Ici 0 := self_mem_Ici
  have h_left := α.left_inv h0
  rw [α.map_zero] at h_left
  exact h_left

def ClassKInfty.symm (α : ClassKInfty) : ClassKInfty where
  toFun := α.invFun
  invFun := α.toFun
  maps_to := α.inv_maps_to
  inv_maps_to := α.maps_to
  left_inv := α.right_inv
  right_inv := α.left_inv
  map_zero := α.invFun_zero
  strict_mono := α.invFun_strictMono
  continuous := by
    have inv_mono : StrictMonoOn α.invFun (Set.Ici 0) := α.invFun_strictMono
    have inv_zero : α.invFun 0 = 0 := α.invFun_zero
    -- invFun surjects: for x ≥ 0, ∃ w ≥ 0 with invFun w = x
    have inv_surj : ∀ x : ℝ, 0 ≤ x → ∃ w ∈ Set.Ici 0, α.invFun w = x :=
      fun x hx => ⟨α.toFun x, α.maps_to hx, α.left_inv hx⟩
    -- Prove ContinuousOn pointwise
    intro y hy
    by_cases h0 : y = 0
    · -- Left endpoint y = 0: right continuity within Ici 0
      subst h0
      apply StrictMonoOn.continuousWithinAt_right_of_exists_between inv_mono
      · -- Ici 0 ∈ 𝓝[≥] 0
        rw [mem_nhdsGE_iff_exists_Ico_subset' (by norm_num : (0:ℝ) < 1)]
        exact ⟨1, by norm_num, Set.Ico_subset_Ici_self⟩
      · -- ∀ z > invFun 0 = 0, find w ∈ Ici 0 with invFun w ∈ Ioc 0 z
        rw [inv_zero]
        intro z hz
        obtain ⟨w, hw, hinv⟩ := inv_surj z (le_of_lt hz)
        exact ⟨w, hw, by rw [hinv]; exact ⟨hz, le_refl z⟩⟩
    · -- Interior point y > 0
      have hy0' : 0 < y := lt_of_le_of_ne hy (Ne.symm h0)
      have hici_nhd : Set.Ici 0 ∈ 𝓝 y :=
        mem_of_superset (Ioi_mem_nhds hy0') Set.Ioi_subset_Ici_self
      apply ContinuousAt.continuousWithinAt
      apply StrictMonoOn.continuousAt_of_exists_between inv_mono hici_nhd
      · -- ∀ z < invFun y, find w ∈ Ici 0 with invFun w ∈ Ico z (invFun y)
        intro z hz
        have hinvy_pos : 0 < α.invFun y := by
          have h0ci : (0 : ℝ) ∈ Set.Ici 0 := self_mem_Ici
          have := inv_mono h0ci hy hy0'
          rwa [inv_zero] at this
        have hmax : max z 0 < α.invFun y := max_lt hz hinvy_pos
        obtain ⟨x, hxl, hxr⟩ := exists_between hmax
        have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt (le_max_right z 0) hxl)
        obtain ⟨w, hw, hinv⟩ := inv_surj x hx0
        exact ⟨w, hw, hinv ▸ ⟨le_of_lt (lt_of_le_of_lt (le_max_left z 0) hxl), hxr⟩⟩
      · -- ∀ z > invFun y, find w ∈ Ici 0 with invFun w ∈ Ioc (invFun y) z
        intro z hz
        have hz0 : 0 ≤ z :=
          le_of_lt (lt_of_le_of_lt (α.inv_maps_to hy) hz)
        obtain ⟨w, hw, hinv⟩ := inv_surj z hz0
        exact ⟨w, hw, by rw [hinv]; exact ⟨hz, le_refl z⟩⟩
  tendsto_atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    by_cases hb : b ≤ 0
    · -- take a = 0; for y ≥ 0, invFun y ≥ 0 ≥ b
      exact ⟨0, fun y hy => le_trans hb (α.inv_maps_to hy)⟩
    · -- take a = toFun b; for y ≥ a, invFun y ≥ b
      have hb_pos : 0 < b := not_le.mp hb
      have hb_ici : (b : ℝ) ∈ Set.Ici 0 := le_of_lt hb_pos
      refine ⟨α.toFun b, fun y hy => ?_⟩
      have hy_ici : y ∈ Set.Ici 0 := le_trans (α.maps_to hb_ici) hy
      have hmono : α.invFun (α.toFun b) ≤ α.invFun y :=
        α.invFun_strictMono.monotoneOn (α.maps_to hb_ici) hy_ici hy
      have hinv_b : α.invFun (α.toFun b) = b := α.left_inv hb_ici
      linarith

/-- Composition of two ClassKInfty functions is ClassKInfty. -/
def ClassKInfty.comp (β α : ClassKInfty) : ClassKInfty where
  toFun      := β.toFun ∘ α.toFun
  invFun     := α.invFun ∘ β.invFun
  map_zero   := by change β.toFun (α.toFun 0) = 0; rw [α.map_zero, β.map_zero]
  continuous  := β.continuous.comp α.continuous α.maps_to
  strict_mono := by
    intro x hx y hy hxy
    exact β.strict_mono (α.maps_to hx) (α.maps_to hy) (α.strict_mono hx hy hxy)
  tendsto_atTop := β.tendsto_atTop.comp α.tendsto_atTop
  maps_to    := β.maps_to.comp α.maps_to
  inv_maps_to := α.inv_maps_to.comp β.inv_maps_to
  left_inv   := by
    intro x hx
    change α.invFun (β.invFun (β.toFun (α.toFun x))) = x
    rw [β.left_inv (α.maps_to hx)]
    exact α.left_inv hx
  right_inv  := by
    intro y hy
    change β.toFun (α.toFun (α.invFun (β.invFun y))) = y
    rw [α.right_inv (β.inv_maps_to hy)]
    exact β.right_inv hy

/-! ## Class KL functions (Definition 4.3) -/

/-- β : [0, a) × [0, ∞) → [0, ∞) is class KL if its r-slices are class K
    and its s-slices are strictly decreasing and tend to zero. -/
structure ClassKL (a : ℝ) where
  ha : 0 < a
  toFun : ℝ → ℝ → ℝ

  -- (a) r-slices are class K
  map_zero      : ∀ s ≥ 0, toFun 0 s = 0
  continuous_r  : ∀ s ≥ 0, ContinuousOn (fun r => toFun r s) (Set.Ico 0 a)
  strict_mono_r : ∀ s ≥ 0, StrictMonoOn (fun r => toFun r s) (Set.Ico 0 a)
  nonneg        : ∀ r ∈ Set.Ico 0 a, ∀ s ≥ 0, 0 ≤ toFun r s

  -- (b) s-slices are decreasing (antitone) and tend to zero
  anti_s       : ∀ r ∈ Set.Ico 0 a, AntitoneOn (fun s => toFun r s) (Set.Ici 0)
  tendsto_zero  : ∀ r ∈ Set.Ico 0 a,
      Filter.Tendsto (fun s => toFun r s) Filter.atTop (nhds 0)

/-- Composing a ClassKL function on the left with a ClassKInfty function yields ClassKL. -/
def ClassKL.comp_left {a : ℝ} (β : ClassKL a) (α : ClassKInfty) : ClassKL a where
  ha            := β.ha
  toFun r s     := α.toFun (β.toFun r s)
  map_zero s hs := by simp only [β.map_zero s hs, α.map_zero]
  continuous_r s hs :=
    α.continuous.comp (β.continuous_r s hs) (fun r hr => β.nonneg r hr s hs)
  strict_mono_r s hs x hx y hy hxy :=
    α.strict_mono (β.nonneg x hx s hs) (β.nonneg y hy s hs)
      (β.strict_mono_r s hs hx hy hxy)
  nonneg r hr s hs := α.maps_to (β.nonneg r hr s hs)
  anti_s r hr s₁ hs₁ s₂ hs₂ hs :=
    α.strict_mono.monotoneOn (β.nonneg r hr s₂ hs₂) (β.nonneg r hr s₁ hs₁)
      (β.anti_s r hr hs₁ hs₂ hs)
  tendsto_zero r hr := by
    have hβ := β.tendsto_zero r hr
    have hβ_ici : ∀ᶠ s in Filter.atTop, β.toFun r s ∈ Set.Ici 0 := by
      filter_upwards [eventually_ge_atTop 0] with s hs
      exact β.nonneg r hr s hs
    have hβ_within := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun s => β.toFun r s) hβ hβ_ici
    have hα_cont := α.continuous.continuousWithinAt self_mem_Ici
    have h := hα_cont.tendsto.comp hβ_within
    rwa [α.map_zero] at h

/-- Composing a ClassKL function on the right with a ClassK function yields ClassKL. -/
def ClassKL.comp_right {a b : ℝ} (β : ClassKL b) (α : ClassK a b) : ClassKL a where
  ha            := α.ha
  toFun r s     := β.toFun (α.toFun r) s
  map_zero s hs := by simp only [α.map_zero, β.map_zero s hs]
  continuous_r s hs :=
    (β.continuous_r s hs).comp α.continuous α.maps_to
  strict_mono_r s hs x hx y hy hxy :=
    β.strict_mono_r s hs (α.maps_to hx) (α.maps_to hy) (α.strict_mono hx hy hxy)
  nonneg r hr s hs :=
    β.nonneg (α.toFun r) (α.maps_to hr) s hs
  anti_s r hr :=
    β.anti_s (α.toFun r) (α.maps_to hr)
  tendsto_zero r hr :=
    β.tendsto_zero (α.toFun r) (α.maps_to hr)

def IsClassKInfty (f : ℝ → ℝ) : Prop := ∃ α : ClassKInfty, α.toFun = f





-- Global Lyapunov function with quantitative K∞ sandwich bounds.
structure IsGlobalLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont       : Continuous V
  hV_diff     : Differentiable ℝ V
  halphas     : ∃ α₁ α₂ : ℝ → ℝ, IsClassKInfty α₁ ∧ IsClassKInfty α₂ ∧
                  ∀ x : ℝⁿ, α₁ ‖x - x_eq‖ ≤ V x ∧ V x ≤ α₂ ‖x - x_eq‖
  hLie_nonpos : ∀ x : ℝⁿ, fderiv ℝ V x (f x) ≤ 0

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue
import LeanForControl.axioms
import LeanForControl.Comparison.ClassK
import Architect

open Set Filter Topology MeasureTheory intervalIntegral


-- ─── Class K∞ ─────────────────────────────────────────────────────────────────

/-! ### Class K∞

A *class K∞* function is like class K but defined globally on `[0, ∞)` and satisfying
`f(r) → ∞` as `r → ∞`.  It is the natural comparison function for global stability
certificates and ISS bounds. -/

/-- A class K∞ function: continuous, strictly increasing, `f(0) = 0`, radially unbounded
    (`f(r) → ∞`), all on `[0, ∞)`. -/
@[blueprint "def:isClassKInfty"
  (statement := /-- A \emph{class $\mathcal{K}_{\infty}$} function is a continuous
    strictly increasing map $\alpha : [0,\infty) \to [0,\infty)$ with $\alpha(0) = 0$
    and $\alpha(r) \to \infty$ as $r \to \infty$. -/)]
structure ClassKInfty where
  /-- The forward function of a class K∞ function. -/
  toFun : ℝ → ℝ
  /-- The inverse function of a class K∞ function. -/
  invFun  : ℝ → ℝ
  map_zero      : toFun 0 = 0
  continuous    : ContinuousOn toFun (Ici 0)
  strict_mono   : StrictMonoOn toFun (Ici 0)
  tendsto_atTop : Tendsto toFun atTop atTop
  maps_to       : MapsTo toFun (Ici 0) (Ici 0)
  inv_maps_to   : MapsTo invFun (Ici 0) (Ici 0)
  left_inv      : LeftInvOn invFun toFun (Ici 0)
  right_inv     : RightInvOn invFun toFun (Ici 0)

/-- Allows writing `α r` instead of `α.toFun r`. -/
instance : CoeFun ClassKInfty (fun _ => ℝ → ℝ) where
  coe α := α.toFun



@[fun_prop]
theorem ClassKInfty.continuousOn (α : ClassKInfty) :
    ContinuousOn α.toFun (Set.Ici 0) := α.continuous



@[simp]
theorem ClassKInfty.zero_iff (α : ClassKInfty) {x : ℝ} (hx : 0 ≤ x) :
    α.toFun x = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact α.strict_mono.injOn hx self_mem_Ici (by rw [h, α.map_zero])
  · rintro rfl; exact α.map_zero

@[simp]
theorem ClassKInfty.pos_iff (α : ClassKInfty) {x : ℝ} (hx : 0 ≤ x) :
    0 < α.toFun x ↔ 0 < x := by
  constructor
  · intro h
    rcases eq_or_lt_of_le hx with rfl | hpos
    · rw [α.map_zero] at h; exact absurd h (lt_irrefl 0)
    · exact hpos
  · intro hpos
    have := α.strict_mono self_mem_Ici hx hpos
    rwa [α.map_zero] at this

@[simp]
theorem ClassKInfty.strict_mono_iff (α : ClassKInfty) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    α.toFun x < α.toFun y ↔ x < y :=
  α.strict_mono.lt_iff_lt hx hy

@[simp]
theorem ClassKInfty.mono_iff (α : ClassKInfty) {x y : ℝ}
    (hx : x ∈ Set.Ici 0) (hy : y ∈ Set.Ici 0) :
    α.toFun x ≤ α.toFun y ↔ x ≤ y :=
  α.strict_mono.le_iff_le hx hy

@[simp]
theorem ClassKInfty.left_inv_apply (α : ClassKInfty) {x : ℝ} (hx : 0 ≤ x) :
    α.invFun (α.toFun x) = x :=
  α.left_inv hx

@[simp]
theorem ClassKInfty.right_inv_apply (α : ClassKInfty) {y : ℝ} (hy : 0 ≤ y) :
    α.toFun (α.invFun y) = y :=
  α.right_inv hy

@[simp]
theorem ClassKInfty.inv_mono_iff (α : ClassKInfty) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    α.invFun x ≤ α.invFun y ↔ x ≤ y := by
  rw [← α.strict_mono.le_iff_le (α.inv_maps_to hx) (α.inv_maps_to hy),
      α.right_inv hx, α.right_inv hy]



-- ─── ClassKInfty Construction ─────────────────────────────────────────────────

/-- `f` maps `[0, ∞)` into `[0, ∞)` when `f(0) = 0` and `f` is strictly monotone on
    `[0, ∞)`: either `x = 0` (giving `f(0) = 0`) or `x > 0` (giving `f(x) > f(0) = 0`). -/
private lemma ClassKInfty.mapsTo_of_basic (f : ℝ → ℝ) (hf_zero : f 0 = 0)
    (hf_mono : StrictMonoOn f (Set.Ici 0)) : Set.MapsTo f (Set.Ici 0) (Set.Ici 0) := by
  intro x hx
  have hx_le : 0 ≤ x := hx
  rcases eq_or_lt_of_le hx_le with h_eq | hpos
  · rw [← h_eq, hf_zero]; exact Set.mem_Ici.mpr (le_refl 0)
  · have h0_mem : (0 : ℝ) ∈ Set.Ici 0 := Set.mem_Ici.mpr (le_refl 0)
    have hfx_pos : f 0 < f x := hf_mono h0_mem hx hpos
    rw [hf_zero] at hfx_pos; exact hfx_pos.le

/-- `f` maps `[0, ∞)` surjectively onto `[0, ∞)` when `f(0) = 0`, `f` is continuous on
    `[0, ∞)`, and `f(x) → ∞`. Given `y ≥ 0`, coercivity provides `b` with `f(b) ≥ y`;
    IVT on `[0, b]` then yields the preimage. -/
private lemma ClassKInfty.surjOn_of_basic (f : ℝ → ℝ) (hf_zero : f 0 = 0)
    (hf_cont : ContinuousOn f (Set.Ici 0))
    (hf_tendsto : Filter.Tendsto f Filter.atTop Filter.atTop) :
    Set.SurjOn f (Set.Ici 0) (Set.Ici 0) := by
  intro y hy
  -- Tendsto gives an upper bound a with f(b) ≥ y for b = max 0 a
  obtain ⟨a, ha⟩ := Filter.tendsto_atTop_atTop.mp hf_tendsto y
  let b := max 0 a
  have h0_le_b : (0 : ℝ) ≤ b := le_max_left 0 a
  have ha_le_b : a ≤ b := le_max_right 0 a
  have hy_le_fb : y ≤ f b := ha b ha_le_b
  have h0_le_y : f 0 ≤ y := by rw [hf_zero]; exact hy
  have hy_mem_Icc : y ∈ Set.Icc (f 0) (f b) := ⟨h0_le_y, hy_le_fb⟩
  have hcont_Icc : ContinuousOn f (Set.Icc 0 b) := hf_cont.mono Set.Icc_subset_Ici_self
  have hy_in_image : y ∈ f '' Set.Icc 0 b :=
    intermediate_value_Icc h0_le_b hcont_Icc hy_mem_Icc
  obtain ⟨x, hx_icc, hxy⟩ := hy_in_image
  exact ⟨x, hx_icc.1, hxy⟩

/-- Smart constructor for `ClassKInfty`: requires only `f(0) = 0`, continuity on `[0,∞)`,
    strict monotonicity on `[0,∞)`, and `f(r) → ∞`. -/
noncomputable def ClassKInfty.of_strictMono (f : ℝ → ℝ)
    (hf_zero : f 0 = 0) (hf_cont : ContinuousOn f (Set.Ici 0))
    (hf_mono : StrictMonoOn f (Set.Ici 0))
    (hf_tendsto : Filter.Tendsto f Filter.atTop Filter.atTop) : ClassKInfty where
  toFun         := f
  invFun        := Function.invFunOn f (Set.Ici 0)
  map_zero      := hf_zero
  continuous    := hf_cont
  strict_mono   := hf_mono
  tendsto_atTop := hf_tendsto
  maps_to       := ClassKInfty.mapsTo_of_basic f hf_zero hf_mono
  inv_maps_to   := Set.SurjOn.mapsTo_invFunOn
    (ClassKInfty.surjOn_of_basic f hf_zero hf_cont hf_tendsto)
  right_inv     := Set.SurjOn.rightInvOn_invFunOn
    (ClassKInfty.surjOn_of_basic f hf_zero hf_cont hf_tendsto)
  left_inv      := Set.InjOn.leftInvOn_invFunOn hf_mono.injOn

-- ─── ClassKInfty Operations ───────────────────────────────────────────────────

/-- The inverse of a class K∞ function is strictly monotone on `[0, ∞)`. -/
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

/-- `invFun 0 = 0` for any class K∞ function: follows from `left_inv` at `0` and `map_zero`. -/
private lemma ClassKInfty.invFun_zero (α : ClassKInfty) : α.invFun 0 = 0 := by
  have h0 : (0 : ℝ) ∈ Set.Ici 0 := self_mem_Ici
  have h_left := α.left_inv h0
  rw [α.map_zero] at h_left; exact h_left

/-- The inverse of a class K∞ function is again class K∞. -/
def ClassKInfty.symm (α : ClassKInfty) : ClassKInfty where
  toFun       := α.invFun
  invFun      := α.toFun
  maps_to     := α.inv_maps_to
  inv_maps_to := α.maps_to
  left_inv    := α.right_inv
  right_inv   := α.left_inv
  map_zero    := α.invFun_zero
  strict_mono := α.invFun_strictMono
  continuous  := by
    have inv_mono : StrictMonoOn α.invFun (Set.Ici 0) := α.invFun_strictMono
    have inv_zero : α.invFun 0 = 0 := α.invFun_zero
    have inv_surj : ∀ x : ℝ, 0 ≤ x → ∃ w ∈ Set.Ici 0, α.invFun w = x :=
      fun x hx => ⟨α.toFun x, α.maps_to hx, α.left_inv hx⟩
    intro y hy
    by_cases h0 : y = 0
    · -- Left endpoint: right-continuity suffices
      subst h0
      apply StrictMonoOn.continuousWithinAt_right_of_exists_between inv_mono
      · rw [mem_nhdsGE_iff_exists_Ico_subset' (by norm_num : (0:ℝ) < 1)]
        exact ⟨1, by norm_num, Set.Ico_subset_Ici_self⟩
      · rw [inv_zero]
        intro z hz
        obtain ⟨w, hw, hinv⟩ := inv_surj z (le_of_lt hz)
        exact ⟨w, hw, by rw [hinv]; exact ⟨hz, le_refl z⟩⟩
    · -- Interior point: ContinuousAt via between-points criterion
      have hy0' : 0 < y := lt_of_le_of_ne hy (Ne.symm h0)
      have hici_nhd : Set.Ici 0 ∈ 𝓝 y :=
        mem_of_superset (Ioi_mem_nhds hy0') Set.Ioi_subset_Ici_self
      apply ContinuousAt.continuousWithinAt
      apply StrictMonoOn.continuousAt_of_exists_between inv_mono hici_nhd
      · intro z hz
        have hinvy_pos : 0 < α.invFun y := by
          have h0ci : (0 : ℝ) ∈ Set.Ici 0 := self_mem_Ici
          have := inv_mono h0ci hy hy0'; rwa [inv_zero] at this
        have hmax : max z 0 < α.invFun y := max_lt hz hinvy_pos
        obtain ⟨x, hxl, hxr⟩ := exists_between hmax
        have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt (le_max_right z 0) hxl)
        obtain ⟨w, hw, hinv⟩ := inv_surj x hx0
        exact ⟨w, hw, hinv ▸ ⟨le_of_lt (lt_of_le_of_lt (le_max_left z 0) hxl), hxr⟩⟩
      · intro z hz
        have hz0 : 0 ≤ z := le_of_lt (lt_of_le_of_lt (α.inv_maps_to hy) hz)
        obtain ⟨w, hw, hinv⟩ := inv_surj z hz0
        exact ⟨w, hw, by rw [hinv]; exact ⟨hz, le_refl z⟩⟩
  tendsto_atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    by_cases hb : b ≤ 0
    · -- invFun y ≥ 0 ≥ b for any y ≥ 0
      exact ⟨0, fun y hy => le_trans hb (α.inv_maps_to hy)⟩
    · -- For y ≥ toFun b, monotonicity gives invFun y ≥ invFun (toFun b) = b
      have hb_pos : 0 < b := not_le.mp hb
      have hb_ici : (b : ℝ) ∈ Set.Ici 0 := le_of_lt hb_pos
      refine ⟨α.toFun b, fun y hy => ?_⟩
      have hy_ici : y ∈ Set.Ici 0 := le_trans (α.maps_to hb_ici) hy
      have hmono : α.invFun (α.toFun b) ≤ α.invFun y :=
        α.invFun_strictMono.monotoneOn (α.maps_to hb_ici) hy_ici hy
      have hinv_b : α.invFun (α.toFun b) = b := α.left_inv hb_ici
      linarith

/-- Composition of two class K∞ functions is class K∞. -/
def ClassKInfty.comp (β α : ClassKInfty) : ClassKInfty where
  toFun         := β.toFun ∘ α.toFun
  invFun        := α.invFun ∘ β.invFun
  map_zero      := by change β.toFun (α.toFun 0) = 0; rw [α.map_zero, β.map_zero]
  continuous    := β.continuous.comp α.continuous α.maps_to
  strict_mono   := by
    intro x hx y hy hxy
    exact β.strict_mono (α.maps_to hx) (α.maps_to hy) (α.strict_mono hx hy hxy)
  tendsto_atTop := β.tendsto_atTop.comp α.tendsto_atTop
  maps_to       := β.maps_to.comp α.maps_to
  inv_maps_to   := α.inv_maps_to.comp β.inv_maps_to
  left_inv := by
    intro x hx
    change α.invFun (β.invFun (β.toFun (α.toFun x))) = x
    rw [β.left_inv (α.maps_to hx)]; exact α.left_inv hx
  right_inv := by
    intro y hy
    change β.toFun (α.toFun (α.invFun (β.invFun y))) = y
    rw [α.right_inv (β.inv_maps_to hy)]; exact β.right_inv hy




-- ─── ClassKInfty Closure Properties ─────────────────────────────────────────

/-- The power function `r ↦ r ^ p` is class K∞ for any `p > 0`. -/
noncomputable def ClassKInfty.power (p : ℝ) (hp : 0 < p) : ClassKInfty :=
  ClassKInfty.of_strictMono (fun r => r ^ p)
    (Real.zero_rpow hp.ne')
    (continuousOn_id.rpow_const fun _ _ => Or.inr hp.le)
    (fun _ hx _ _ hxy => Real.rpow_lt_rpow hx hxy hp)
    (tendsto_rpow_atTop hp)

/-- Any class K∞ function restricts to a class K function on `[0, a)`. -/
noncomputable def ClassKInfty.toClassK (α : ClassKInfty) {a : ℝ} (ha : 0 < a) :
    ClassK a (α.toFun a) :=
  ClassK.of_strictMono ha
    ((α.pos_iff (Set.mem_Ici.mpr ha.le)).mpr ha)
    α.toFun
    α.map_zero
    rfl
    (α.continuous.mono Set.Icc_subset_Ici_self)
    (α.strict_mono.mono Set.Icc_subset_Ici_self)


/-- Sum of two class K functions on the same domain is class K.
    `(α + β)(a) = α(a) + β(a) = b + c`. -/
noncomputable def ClassKInfty.add (α : ClassKInfty) (β : ClassKInfty) :
    ClassKInfty :=
  ClassKInfty.of_strictMono (fun x => α x + β x)
    (by simp [α.map_zero, β.map_zero])
    (α.continuous.add β.continuous)
    (α.strict_mono.add β.strict_mono)
    (Filter.Tendsto.atTop_add_atTop α.tendsto_atTop β.tendsto_atTop)

/-- Positive scalar multiple of a class K function is class K.
    `(c • α)(a) = c * b`. -/
noncomputable def ClassKInfty.smul (α : ClassKInfty) (c : ℝ) (hc : 0 < c) :
    ClassKInfty :=
  ClassKInfty.of_strictMono (fun x => c * α x)
    (by simp [α.map_zero])
    (continuousOn_const.mul α.continuous)
    (fun x hx y hy hxy => mul_lt_mul_of_pos_left (α.strict_mono hx hy hxy) hc)
    (Filter.Tendsto.const_mul_atTop hc α.tendsto_atTop)

/-- Pointwise minimum of two class K functions on the same domain is class K.
    `min(α, β)(a) = min(b, c)`. -/
noncomputable def ClassKInfty.min_fn (α : ClassKInfty) (β : ClassKInfty) :
    ClassKInfty :=
  ClassKInfty.of_strictMono (fun x => min (α x) (β x))
    (by
    simp [α.map_zero, β.map_zero]
    )
    (continuous_min.comp_continuousOn (α.continuous.prodMk β.continuous))
    (fun x hx y hy hxy => lt_min
      ((min_le_left _ _).trans_lt (α.strict_mono hx hy hxy))
      ((min_le_right _ _).trans_lt (β.strict_mono hx hy hxy)))
    (Filter.tendsto_atTop_atTop.mpr fun b =>
          let ⟨N₁, h₁⟩ := Filter.tendsto_atTop_atTop.mp α.tendsto_atTop b
          let ⟨N₂, h₂⟩ := Filter.tendsto_atTop_atTop.mp β.tendsto_atTop b
          ⟨max N₁ N₂, fun x hx => le_min
            (h₁ x (le_of_max_le_left hx))
            (h₂ x (le_of_max_le_right hx))⟩)



lemma exists_classKInfty_upper_bound (ω : ℝ → ℝ)
    (hω_zero : ω 0 = 0)
    (hω_mono : MonotoneOn ω (Set.Ici 0)) :
    ∃ α : ClassKInfty, ∀ r ≥ 0, ω r ≤ α.toFun r := by
  obtain ⟨f, hf_zero, hf_cont, hf_mono, hf_top, hf_bound⟩ :=
    exists_strictMono_upper_bound_global ω hω_zero hω_mono
  exact ⟨ClassKInfty.of_strictMono f hf_zero hf_cont hf_mono hf_top,
         fun r hr => hf_bound r hr⟩

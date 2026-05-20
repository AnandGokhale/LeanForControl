import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue
import Architect

open Set Filter Topology MeasureTheory intervalIntegral

/-!
# `Stability.classK`

Class K, K∞, and KL comparison functions.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definitions 4.2–4.4.

Comparison functions are the standard vocabulary for quantitative stability estimates
(Lyapunov sandwich bounds, ISS gains, asymptotic decay rates, etc.).

* `ClassK a b`  — strictly increasing continuous bijection `[0, a) → [0, b)`, zero at zero.
* `ClassKInfty` — same but on all of `[0, ∞)`, with `f(r) → ∞` as `r → ∞`.
* `ClassKL a`   — class K in the first argument, strictly decreasing to zero in the second.

Each structure stores both `toFun` and its inverse `invFun` so that `symm` and `comp`
never require re-proving the inverse properties.
-/

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

-- ─── Class K ──────────────────────────────────────────────────────────────────

/-! ### Class K

A *class K* function is a strictly increasing continuous bijection `f : [0,a) → [0,b)`
satisfying `f(0) = 0`. -/

/-- A class K function on `[0,a)`: continuous, strictly increasing, zero at zero,
    together with a stored inverse that witnesses the bijection `[0,a) ↔ [0,b)`. -/
@[blueprint "def:isClassK"
  (statement := /-- A \emph{class $\mathcal{K}$} function on $[0,a)$ is a
    continuous strictly increasing map $\alpha : [0,a) \to [0,b)$ with
    $\alpha(0) = 0$. The structure records both $\alpha$ and its inverse
    $\alpha^{-1} : [0,b) \to [0,a)$. -/)]
structure ClassK (a b : ℝ) where
  ha : 0 < a
  hb : 0 < b
  /-- The forward function of a class K function. -/
  toFun  : ℝ → ℝ
  /-- The inverse function of a class K function. -/
  invFun : ℝ → ℝ
  map_zero    : toFun 0 = 0
  continuous  : ContinuousOn toFun (Set.Ico 0 a)
  strict_mono : StrictMonoOn toFun (Set.Ico 0 a)
  maps_to     : Set.MapsTo toFun (Set.Ico 0 a) (Set.Ico 0 b)
  inv_maps_to : Set.MapsTo invFun (Set.Ico 0 b) (Set.Ico 0 a)
  left_inv    : Set.LeftInvOn invFun toFun (Set.Ico 0 a)
  right_inv   : Set.RightInvOn invFun toFun (Set.Ico 0 b)

/-- Allows writing `α x` instead of `α.toFun x`. -/
instance {a b : ℝ} : CoeFun (ClassK a b) (fun _ => ℝ → ℝ) where
  coe α := α.toFun

-- ─── ClassK Construction ──────────────────────────────────────────────────────

/-- `f` maps `[0, a)` into `[0, b)` when `f(0) = 0`, `f(a) = b`, and `f` is strictly
    monotone on `[0, a]`. Monotonicity from `0` gives `f(x) ≥ 0`; strict monotonicity
    before `a` gives `f(x) < b`. -/
private lemma ClassK.mapsTo_of_boundary {a b : ℝ} (ha : 0 < a)
    (f : ℝ → ℝ) (hf_zero : f 0 = 0) (hf_a : f a = b)
    (hf_mono : StrictMonoOn f (Set.Icc 0 a)) :
    Set.MapsTo f (Set.Ico 0 a) (Set.Ico 0 b) := by
  intro x hx
  have h0_icc : (0 : ℝ) ∈ Set.Icc 0 a := ⟨le_refl 0, ha.le⟩
  have ha_icc : a ∈ Set.Icc 0 a := ⟨ha.le, le_refl a⟩
  have hx_icc : x ∈ Set.Icc 0 a := ⟨hx.1, hx.2.le⟩
  constructor
  · -- f x ≥ 0: monotonicity from 0
    have h_lo := hf_mono.monotoneOn h0_icc hx_icc hx.1
    rwa [hf_zero] at h_lo
  · -- f x < b: strict monotonicity before endpoint
    have h_hi := hf_mono hx_icc ha_icc hx.2
    rwa [hf_a] at h_hi

/-- `f` maps `[0, a)` surjectively onto `[0, b)` when `f(0) = 0`, `f(a) = b`, and `f` is
    continuous on `[0, a]`. Given `y ∈ [0, b)`, IVT on `[0, a]` finds a preimage `x`;
    strict monotonicity before `a` ensures `x < a`. -/
private lemma ClassK.surjOn_of_boundary {a b : ℝ} (ha : 0 < a)
    (f : ℝ → ℝ) (hf_zero : f 0 = 0) (hf_a : f a = b)
    (hf_cont : ContinuousOn f (Set.Icc 0 a)) :
    Set.SurjOn f (Set.Ico 0 a) (Set.Ico 0 b) := by
  intro y hy
  have h0_le_y : f 0 ≤ y := by rw [hf_zero]; exact hy.1
  have hy_le_a : y ≤ f a := by rw [hf_a]; exact hy.2.le
  have hy_mem_Icc : y ∈ Set.Icc (f 0) (f a) := ⟨h0_le_y, hy_le_a⟩
  have hy_in_image : y ∈ f '' Set.Icc 0 a :=
    intermediate_value_Icc ha.le hf_cont hy_mem_Icc
  obtain ⟨x, hx_icc, hxy⟩ := hy_in_image
  -- x < a because y < b = f a, so x cannot equal a
  have hx_lt_a : x < a := by
    apply lt_of_le_of_ne hx_icc.2
    intro h_eq; rw [h_eq, hf_a] at hxy; exact ne_of_lt hy.2 hxy.symm
  exact ⟨x, ⟨hx_icc.1, hx_lt_a⟩, hxy⟩

/-- Smart constructor: given `f : ℝ → ℝ` with `f(0) = 0`, `f(a) = b`, continuity and strict
    monotonicity on `[0, a]`, builds the full `ClassK a b` structure (inverse included). -/
noncomputable def ClassK.of_strictMono {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f : ℝ → ℝ) (hf_zero : f 0 = 0) (hf_a : f a = b)
    (hf_cont : ContinuousOn f (Set.Icc 0 a))
    (hf_mono : StrictMonoOn f (Set.Icc 0 a)) : ClassK a b where
  ha := ha
  hb := hb
  toFun    := f
  invFun   := Function.invFunOn f (Set.Ico 0 a)
  map_zero    := hf_zero
  continuous  := hf_cont.mono Set.Ico_subset_Icc_self
  strict_mono := hf_mono.mono Set.Ico_subset_Icc_self
  maps_to     := ClassK.mapsTo_of_boundary ha f hf_zero hf_a hf_mono
  inv_maps_to := Set.SurjOn.mapsTo_invFunOn
    (ClassK.surjOn_of_boundary ha f hf_zero hf_a hf_cont)
  right_inv   := Set.SurjOn.rightInvOn_invFunOn
    (ClassK.surjOn_of_boundary ha f hf_zero hf_a hf_cont)
  left_inv    := Set.InjOn.leftInvOn_invFunOn
    (hf_mono.mono Set.Ico_subset_Icc_self).injOn

-- ─── ClassK Operations ────────────────────────────────────────────────────────

/-- The inverse of a class K function `[0,a) → [0,b)` is class K on `[0,b) → [0,a)`. -/
def ClassK.symm {a b : ℝ} (α : ClassK a b) : ClassK b a where
  ha          := α.hb
  hb          := α.ha
  toFun       := α.invFun
  invFun      := α.toFun
  maps_to     := α.inv_maps_to
  inv_maps_to := α.maps_to
  left_inv    := α.right_inv
  right_inv   := α.left_inv
  map_zero := by
    have h0 : (0 : ℝ) ∈ Set.Ico 0 a := ⟨le_refl 0, α.ha⟩
    have h_left := α.left_inv h0
    rw [α.map_zero] at h_left; exact h_left
  continuous := by
    have inv_mono : StrictMonoOn α.invFun (Set.Ico 0 b) := by
      intro y₁ hy₁ y₂ hy₂ hy_lt
      apply lt_of_not_ge
      intro h_ge
      rcases eq_or_lt_of_le h_ge with h_eq | h_gt
      · have h_apply : α.toFun (α.invFun y₁) = α.toFun (α.invFun y₂) := by rw [h_eq]
        rw [α.right_inv hy₁, α.right_inv hy₂] at h_apply; linarith
      · have h_apply := α.strict_mono (α.inv_maps_to hy₂) (α.inv_maps_to hy₁) h_gt
        rw [α.right_inv hy₂, α.right_inv hy₁] at h_apply; linarith
    have inv_zero : α.invFun 0 = 0 := by
      have h0 : (0 : ℝ) ∈ Set.Ico 0 a := ⟨le_refl 0, α.ha⟩
      have h_left := α.left_inv h0; rw [α.map_zero] at h_left; exact h_left
    have inv_surj : ∀ x ∈ Set.Ico 0 a, ∃ w ∈ Set.Ico 0 b, α.invFun w = x :=
      fun x hx => ⟨α.toFun x, α.maps_to hx, α.left_inv hx⟩
    have inv_lt_a : ∀ y ∈ Set.Ico 0 b, α.invFun y < a :=
      fun y hy => (α.inv_maps_to hy).2
    -- Find a right-witness for the continuity criterion: given invFun y < z,
    -- produce w ∈ Ico 0 b with invFun w ∈ Ioc (invFun y) z.
    have find_right : ∀ (y : ℝ), y ∈ Set.Ico 0 b → ∀ z > α.invFun y,
        ∃ w ∈ Set.Ico 0 b, α.invFun w ∈ Set.Ioc (α.invFun y) z := by
      intro y hy z hz
      by_cases hza : z < a
      · have hz0 : 0 ≤ z := le_of_lt (lt_of_le_of_lt (α.inv_maps_to hy).1 hz)
        obtain ⟨w, hw, hinv⟩ := inv_surj z ⟨hz0, hza⟩
        exact ⟨w, hw, by rw [hinv]; exact ⟨hz, le_refl z⟩⟩
      · have hiy_lt_a : α.invFun y < a := inv_lt_a y hy
        obtain ⟨x, hxl, hxr⟩ := exists_between hiy_lt_a
        have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt (α.inv_maps_to hy).1 hxl)
        obtain ⟨w, hw, hinv⟩ := inv_surj x ⟨hx0, hxr⟩
        exact ⟨w, hw, by rw [hinv]; exact ⟨hxl, le_of_lt (lt_of_lt_of_le hxr (not_lt.mp hza))⟩⟩
    intro y hy
    obtain ⟨hy0, hyb⟩ := hy
    by_cases h0 : y = 0
    · -- Left endpoint: use right-continuity within Ici 0
      subst h0
      apply ContinuousWithinAt.mono _ Set.Ico_subset_Ici_self
      apply StrictMonoOn.continuousWithinAt_right_of_exists_between inv_mono
      · rw [mem_nhdsGE_iff_exists_Ico_subset' α.hb]
        exact ⟨b, α.hb, Set.Ico_subset_Ico_right le_rfl⟩
      · rw [inv_zero]
        intro z hz
        by_cases hza : z < a
        · have hz0 : 0 ≤ z := le_of_lt hz
          obtain ⟨w, hw, hinv⟩ := inv_surj z ⟨hz0, hza⟩
          exact ⟨w, hw, by rw [hinv]; exact ⟨hz, le_refl z⟩⟩
        · obtain ⟨x, hx0, hxa⟩ := exists_between α.ha
          obtain ⟨w, hw, hinv⟩ := inv_surj x ⟨le_of_lt hx0, hxa⟩
          exact ⟨w, hw, by rw [hinv]; exact ⟨hx0, le_of_lt (lt_of_lt_of_le hxa (not_lt.mp hza))⟩⟩
    · -- Interior point: ContinuousAt via the between-points criterion
      have hy0' : 0 < y := lt_of_le_of_ne hy0 (Ne.symm h0)
      have hico_nhd : Set.Ico 0 b ∈ 𝓝 y := Ico_mem_nhds_iff.mpr ⟨hy0', hyb⟩
      apply ContinuousAt.continuousWithinAt
      apply StrictMonoOn.continuousAt_of_exists_between inv_mono hico_nhd
      · intro z hz
        have hinvy_pos : 0 < α.invFun y := by
          have h0b : (0 : ℝ) ∈ Set.Ico 0 b := ⟨le_refl 0, α.hb⟩
          have := inv_mono h0b ⟨le_of_lt hy0', hyb⟩ hy0'
          rwa [inv_zero] at this
        have hinvy_lt_a : α.invFun y < a := inv_lt_a y ⟨le_of_lt hy0', hyb⟩
        have hmax : max z 0 < α.invFun y := max_lt hz hinvy_pos
        obtain ⟨x, hxl, hxr⟩ := exists_between hmax
        have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt (le_max_right z 0) hxl)
        obtain ⟨w, hw, hinv⟩ := inv_surj x ⟨hx0, lt_trans hxr hinvy_lt_a⟩
        exact ⟨w, hw, hinv ▸ ⟨le_of_lt (lt_of_le_of_lt (le_max_left z 0) hxl), hxr⟩⟩
      · exact find_right y ⟨le_of_lt hy0', hyb⟩
  strict_mono := by
    intro y₁ hy₁ y₂ hy₂ hy_lt
    have hx₁ := α.inv_maps_to hy₁
    have hx₂ := α.inv_maps_to hy₂
    apply lt_of_not_ge
    intro h_ge
    rcases eq_or_lt_of_le h_ge with h_eq | h_gt
    · -- invFun y₁ = invFun y₂ implies y₁ = y₂ via right_inv: contradiction
      have h_apply : α.toFun (α.invFun y₁) = α.toFun (α.invFun y₂) := by rw [h_eq]
      rw [α.right_inv hy₁, α.right_inv hy₂] at h_apply; linarith
    · -- invFun y₁ > invFun y₂ implies y₁ > y₂ via forward strict_mono: contradiction
      have h_apply := α.strict_mono hx₂ hx₁ h_gt
      rw [α.right_inv hy₂, α.right_inv hy₁] at h_apply; linarith

/-- Composition of two class K functions is class K
    (the composed inverse is the reverse composition of inverses). -/
def ClassK.comp {a b c : ℝ} (β : ClassK b c) (α : ClassK a b) : ClassK a c where
  ha          := α.ha
  hb          := β.hb
  toFun       := β.toFun ∘ α.toFun
  invFun      := α.invFun ∘ β.invFun
  map_zero    := by change β.toFun (α.toFun 0) = 0; rw [α.map_zero, β.map_zero]
  continuous  := β.continuous.comp α.continuous α.maps_to
  strict_mono := by
    intro x hx y hy hxy
    exact β.strict_mono (α.maps_to hx) (α.maps_to hy) (α.strict_mono hx hy hxy)
  maps_to     := β.maps_to.comp α.maps_to
  inv_maps_to := α.inv_maps_to.comp β.inv_maps_to
  left_inv := by
    intro x hx
    change α.invFun (β.invFun (β.toFun (α.toFun x))) = x
    rw [β.left_inv (α.maps_to hx)]; exact α.left_inv hx
  right_inv := by
    intro y hy
    change β.toFun (α.toFun (α.invFun (β.invFun y))) = y
    rw [α.right_inv (β.inv_maps_to hy)]; exact β.right_inv hy

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

-- ─── Class KL ─────────────────────────────────────────────────────────────────

/-! ### Class KL

A *class KL* function `β(r, s)` is class K in `r` for each fixed `s`, and for each
fixed `r` it is strictly decreasing in `s` and tends to zero as `s → ∞`.
It arises as the bound in asymptotic stability estimates: `‖x(t)‖ ≤ β(‖x₀‖, t)`. -/

/-- A class KL function `β : [0,a) × [0,∞) → ℝ`:
    class K in the first argument, antitone and tending to 0 in the second. -/
@[blueprint "def:isClassKL"
  (statement := /-- A \emph{class $\mathcal{KL}$} function on $[0,a) \times [0,\infty)$
    is continuous, class $\mathcal{K}$ in the first argument, and for each fixed $r > 0$
    is strictly decreasing and tends to $0$ as $s \to \infty$. It arises as the bound
    $\|x(t)\| \le \beta(\|x_0\|, t)$ in asymptotic stability estimates. -/)]
structure ClassKL (a : ℝ) where
  ha : 0 < a
  /-- The forward function of a class KL function. -/
  toFun : ℝ → ℝ → ℝ
  map_zero      : ∀ s ≥ 0, toFun 0 s = 0
  continuous_r  : ∀ s ≥ 0, ContinuousOn (fun r => toFun r s) (Set.Ico 0 a)
  strict_mono_r : ∀ s ≥ 0, StrictMonoOn (fun r => toFun r s) (Set.Ico 0 a)
  nonneg        : ∀ r ∈ Set.Ico 0 a, ∀ s ≥ 0, 0 ≤ toFun r s
  anti_s        : ∀ r ∈ Set.Ico 0 a, AntitoneOn (fun s => toFun r s) (Set.Ici 0)
  tendsto_zero  : ∀ r ∈ Set.Ico 0 a,
      Filter.Tendsto (fun s => toFun r s) Filter.atTop (nhds 0)

/-- Post-composing a class KL function with a class K∞ function yields class KL.
    (Applies `α` to the output of `β`.) -/
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

/-- Pre-composing a class KL function with a class K function yields class KL.
    (Applies `α` to the first argument of `β`.) -/
def ClassKL.comp_right {a b : ℝ} (β : ClassKL b) (α : ClassK a b) : ClassKL a where
  ha            := α.ha
  toFun r s     := β.toFun (α.toFun r) s
  map_zero s hs := by simp only [α.map_zero, β.map_zero s hs]
  continuous_r s hs  := (β.continuous_r s hs).comp α.continuous α.maps_to
  strict_mono_r s hs x hx y hy hxy :=
    β.strict_mono_r s hs (α.maps_to hx) (α.maps_to hy) (α.strict_mono hx hy hxy)
  nonneg r hr s hs   := β.nonneg (α.toFun r) (α.maps_to hr) s hs
  anti_s r hr        := β.anti_s (α.toFun r) (α.maps_to hr)
  tendsto_zero r hr  := β.tendsto_zero (α.toFun r) (α.maps_to hr)

-- ─── Predicate and Stability Structure ────────────────────────────────────────

/-- Predicate: `f` is the forward map of some `ClassKInfty` instance. -/
def IsClassKInfty (f : ℝ → ℝ) : Prop := ∃ α : ClassKInfty, α.toFun = f

/-- A global Lyapunov function certificate for dynamics `f` at equilibrium `x_eq`:
    - `V` is continuously differentiable,
    - sandwiched by two class K∞ functions of `‖x − x_eq‖`,
    - Lie derivative `dV/dt = ∇V · f` is non-positive everywhere. -/
structure IsGlobalLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont       : Continuous V
  hV_diff     : Differentiable ℝ V
  halphas     : ∃ α₁ α₂ : ℝ → ℝ, IsClassKInfty α₁ ∧ IsClassKInfty α₂ ∧
                  ∀ x : ℝⁿ, α₁ ‖x - x_eq‖ ≤ V x ∧ V x ≤ α₂ ‖x - x_eq‖
  hLie_nonpos : ∀ x : ℝⁿ, fderiv ℝ V x (f x) ≤ 0

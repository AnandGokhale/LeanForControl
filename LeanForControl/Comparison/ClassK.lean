import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue
import LeanForControl.axioms
import Architect

open Set Filter Topology MeasureTheory intervalIntegral

/-!
# `Stability.ComparisonFunctions`

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


@[fun_prop]
theorem ClassK.continuousOn {a b : ℝ} (α : ClassK a b) :
    ContinuousOn α.toFun (Set.Ico 0 a) := α.continuous


-- ─── ClassK Basic API ─────────────────────────────────────────────────────────

@[simp]
theorem ClassK.zero_iff {a b : ℝ} (α : ClassK a b) {x : ℝ} (hx : x ∈ Set.Ico 0 a) :
    α.toFun x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h0 : (0 : ℝ) ∈ Set.Ico 0 a := ⟨le_refl 0, α.ha⟩
    exact α.strict_mono.injOn hx h0 (by rw [h, α.map_zero])
  · rintro rfl; exact α.map_zero

@[simp]
theorem ClassK.pos_iff {a b : ℝ} (α : ClassK a b) {x : ℝ} (hx : x ∈ Set.Ico 0 a) :
    0 < α.toFun x ↔ 0 < x := by
  constructor
  · intro h
    rcases eq_or_lt_of_le hx.1 with rfl | hpos
    · rw [α.map_zero] at h; exact absurd h (lt_irrefl 0)
    · exact hpos
  · intro hpos
    have h0 : (0 : ℝ) ∈ Set.Ico 0 a := ⟨le_refl 0, α.ha⟩
    have := α.strict_mono h0 hx hpos
    rwa [α.map_zero] at this

@[simp]
theorem ClassK.strict_mono_iff {a b : ℝ} (α : ClassK a b) {x y : ℝ}
    (hx : x ∈ Set.Ico 0 a) (hy : y ∈ Set.Ico 0 a) :
    α.toFun x < α.toFun y ↔ x < y :=
  α.strict_mono.lt_iff_lt hx hy

@[simp]
theorem ClassK.mono_iff {a b : ℝ} (α : ClassK a b) {x y : ℝ}
    (hx : x ∈ Set.Ico 0 a) (hy : y ∈ Set.Ico 0 a) :
    α.toFun x ≤ α.toFun y ↔ x ≤ y :=
  α.strict_mono.le_iff_le hx hy

@[simp]
theorem ClassK.left_inv_apply {a b : ℝ} (α : ClassK a b) {x : ℝ} (hx : x ∈ Set.Ico 0 a) :
    α.invFun (α.toFun x) = x :=
  α.left_inv hx

@[simp]
theorem ClassK.right_inv_apply {a b : ℝ} (α : ClassK a b) {y : ℝ} (hy : y ∈ Set.Ico 0 b) :
    α.toFun (α.invFun y) = y :=
  α.right_inv hy

@[simp]
theorem ClassK.inv_mono_iff {a b : ℝ} (α : ClassK a b) {x y : ℝ}
    (hx : x ∈ Set.Ico 0 b) (hy : y ∈ Set.Ico 0 b) :
    α.invFun x ≤ α.invFun y ↔ x ≤ y := by
  rw [← α.strict_mono.le_iff_le (α.inv_maps_to hx) (α.inv_maps_to hy),
      α.right_inv hx, α.right_inv hy]




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

/-- Restrict a class K function `α : [0, a) → [0, b)` to the smaller domain `[0, c)`,
producing a class K function `[0, c) → [0, α(c))`. -/
noncomputable def ClassK.restrict {a b : ℝ} (α : ClassK a b) {c : ℝ}
    (hc_pos : 0 < c) (hc_lt : c < a) : ClassK c (α.toFun c) := by
  have hd_pos : 0 < α.toFun c := by
    calc 0 = α.toFun 0 := α.map_zero.symm
         _ < α.toFun c := α.strict_mono ⟨le_rfl, α.ha⟩ ⟨hc_pos.le, hc_lt⟩ hc_pos
  have h_sub : Set.Icc 0 c ⊆ Set.Ico 0 a := fun x hx => ⟨hx.1, hx.2.trans_lt hc_lt⟩
  exact ClassK.of_strictMono hc_pos hd_pos α.toFun α.map_zero rfl
    (α.continuous.mono h_sub) (α.strict_mono.mono h_sub)

/-- Variant of `ClassK.restrict` where the upper bound `e` is given explicitly via a proof
that `α(c) = e`, avoiding a type-level `Eq.rec`. -/
noncomputable def ClassK.restrictTo {a b : ℝ} (α : ClassK a b) {c e : ℝ}
    (hc_pos : 0 < c) (hc_lt : c < a) (h_eq : α.toFun c = e) : ClassK c e :=
  h_eq ▸ α.restrict hc_pos hc_lt


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

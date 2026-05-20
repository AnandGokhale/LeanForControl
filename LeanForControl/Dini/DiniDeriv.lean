import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.ENNReal
import Architect

/-!
# Upper Right Dini Derivative

## Main Definitions

* `diniDerivRight f t` : the upper right Dini derivative of `f` at `t`,
  defined as `limsup_{h→0⁺} (f(t+h) - f(t)) / h`.

## Main Results

* `diniDerivRight_eq_deriv`         : agrees with `deriv` when `f` is differentiable
* `diniDerivRight_add_linear`       : D⁺(f + c·id)(t) = D⁺f(t) + c
* `diniDerivRight_const_mul_pos`    : D⁺(c·f)(t) = c · D⁺f(t) for c > 0
* `diniDerivRight_le_iff`           : characterisation via eventually-bounded quotients

## Notes

`diniDerivRight` returns a value in `ℝ` via `Filter.limsup`. When the difference
quotients are unbounded above the filter, `Filter.limsup` returns the `sInf` of the
empty set, which in `ℝ` is `0` by convention — callers should keep this edge case in
mind when `f` is not locally bounded.
-/

open Filter Set Topology

noncomputable section

/-- The upper right Dini derivative of `f` at `t`:
$$D^+ f(t) \;=\; \limsup_{h \to 0^+} \frac{f(t+h) - f(t)}{h}$$
-/
@[blueprint "def:diniDerivRight"
  (statement := /-- The \emph{upper right Dini derivative} of $f : \mathbb{R} \to \mathbb{R}$
    at $t$ is
    \[
      D^{+} f(t) \;=\; \limsup_{h \to 0^{+}} \frac{f(t+h)-f(t)}{h}.
    \]
    When $f$ is differentiable at $t$ this equals $f'(t)$. -/)]
def diniDerivRight (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  limsup (fun h => (f (t + h) - f t) / h) (𝓝[Ioi 0] 0)

/-- Notation `D⁺ f` for the upper right Dini derivative of `f`. -/
notation "D⁺" => diniDerivRight


/-! ### Relationship to the classical derivative -/


/-- If `f` has a right derivative `L` at `t` (in the sense of `HasDerivWithinAt` on `Ici t`),
then `D⁺ f t = L`. -/
theorem diniDerivRight_of_hasDerivWithinAt {f : ℝ → ℝ} {t L : ℝ}
    (hf : HasDerivWithinAt f L (Ici t) t) :
    D⁺ f t = L := by
  rw [diniDerivRight]
  have h_tendsto : Tendsto (fun h => (f (t + h) - f t) / h) (𝓝[>] 0) (𝓝 L) := by
    -- 1. Extract the slope limit using the slope-specific lemma
    -- This ensures the domain filter is exactly 𝓝[Ici t \ {t}] t
    rw [hasDerivWithinAt_iff_tendsto_slope] at hf
    -- 2. Define the shift map h ↦ t + h and prove it maps to the punctured domain
    have h_shift : Tendsto (fun h => t + h) (𝓝[>] 0) (𝓝[Ici t \ {t}] t) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h_cont : Continuous (fun h => t + h) := continuous_const.add continuous_id
        have h_tendsto_0 := h_cont.tendsto 0
        rw [add_zero] at h_tendsto_0
        exact h_tendsto_0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        rw [mem_Ioi] at hh
        simp only [mem_diff, mem_Ici, mem_singleton_iff]
        exact ⟨by linarith, by linarith⟩
    -- 3. Now the filters match perfectly: 𝓝[>] 0 → 𝓝[Ici t \ {t}] t → 𝓝 L
    have h_comp := hf.comp h_shift
    -- 4. Clean up the denominator: (t + h - t) becomes h
    apply Tendsto.congr' _ h_comp
    filter_upwards with h
    rw [Function.comp_apply, slope_def_field]
    ring
  -- Since the limit exists and the filter 𝓝[>] 0 is nontrivial (NeBot),
  -- the limsup evaluates exactly to the limit.
  exact Tendsto.limsup_eq h_tendsto




/-! ### Characterisation lemmas -/

/--
Establishes the epsilon-neighborhood definition for the upper right Dini derivative (`D⁺ f t`).

This theorem proves that `D⁺ f t ≤ L` if and only if for every `ε > 0`, the right-sided
difference quotient `(f(t+h) - f(t))/h` is eventually bounded by `L + ε` as `h → 0⁺`.

Note: Because this is formalized over standard reals (`ℝ`) rather than the extended real line,
it explicitly assumes the difference quotient is both eventually bounded above (`hbdd`)
and frequently bounded below (`hcobdd`). This rules out degenerate cases (like the derivative
shooting to `-∞`) where Lean's empty infimum would default to a mathematically false `0`.
-/
theorem diniDerivRight_le_iff {f : ℝ → ℝ} {t L : ℝ}
    (hbdd : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (f (t + h) - f t) / h))
    (hcobdd : IsCoboundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (f (t + h) - f t) / h)) :
    D⁺ f t ≤ L ↔
    ∀ ε > 0, ∀ᶠ h in 𝓝[>] 0, (f (t + h) - f t) / h ≤ L + ε := by
  unfold diniDerivRight
  set q : ℝ → ℝ := fun h => (f (t + h) - f t) / h
  have h₂ : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) q := by simpa [q] using hbdd
  have h₁ : IsCoboundedUnder (· ≤ ·) (𝓝[>] 0) q := by simpa [q] using hcobdd
  change limsup q (𝓝[>] 0) ≤ L ↔ ∀ ε > 0, ∀ᶠ h in 𝓝[>] 0, q h ≤ L + ε
  rw [Filter.limsup_le_iff h₁ h₂]
  constructor
  · intro h_lim ε hε
    have h_lt := h_lim (L + ε) (by linarith)
    filter_upwards [h_lt] with h hh
    exact hh.le
  · intro h_eps y hy
    have h_pos : (y - L) / 2 > 0 := by linarith
    have h_le := h_eps ((y - L) / 2) h_pos
    filter_upwards [h_le] with h hh
    linarith



/-- `L ≤ D⁺ f t` iff for every `ε > 0`, the difference quotient exceeds `L - ε`
on some set in the filter (frequently). -/
theorem le_diniDerivRight_iff {f : ℝ → ℝ} {t L : ℝ}
    (hbdd : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (f (t + h) - f t) / h))
    (hcobdd : IsCoboundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (f (t + h) - f t) / h)) :
    L ≤ D⁺ f t ↔
    ∀ ε > 0, ∃ᶠ h in 𝓝[>] 0, L - ε < (f (t + h) - f t) / h := by
  unfold diniDerivRight
  set q : ℝ → ℝ := fun h => (f (t + h) - f t) / h
  -- 1. Setup the explicit bounds
  have h₂ : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) q := by simpa [q] using hbdd
  have h₁ : IsCoboundedUnder (· ≤ ·) (𝓝[>] 0) q := by simpa [q] using hcobdd
  -- 2. Tidy up the goal and rewrite using the Mathlib iff lemma
  change L ≤ limsup q (𝓝[>] 0) ↔ ∀ ε > 0, ∃ᶠ h in 𝓝[>] 0, L - ε < q h
  rw [Filter.le_limsup_iff h₁ h₂]
  -- 3. Prove the equivalence between `< y` and `L - ε <` bounds
  constructor
  · -- Forward direction
    intro h_lim ε hε
    -- The theorem gives us `∀ y < L`, so we plug in `y = L - ε`
    exact h_lim (L - ε) (by linarith)
  · -- Backward direction
    intro h_eps y hy
    -- Choose our strictly positive ε
    have h_pos : L - y > 0 := by linarith
    have h_freq := h_eps (L - y) h_pos
    -- Use .mono to open the `∃ᶠ` binder, apply linarith, and close it
    exact h_freq.mono (fun h hh => by linarith)



/-! ### Linearity properties -/

/-- Subadditivity of the upper right Dini derivative.
`D⁺(f + g)(t) ≤ D⁺f(t) + D⁺g(t)`.
Requires both difference quotients to be bounded above to avoid empty infimums in `ℝ`. -/
theorem diniDerivRight_add_le {f g : ℝ → ℝ} {t : ℝ}
    (hf_bdd_below : IsBoundedUnder (· ≥ ·) (𝓝[>] 0) (fun h => (f (t + h) - f t) / h))
    (hf_bdd_above : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (f (t + h) - f t) / h))
    (hg_cobdd_below : IsCoboundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (g (t + h) - g t) / h))
    (hg_bdd_above : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (g (t + h) - g t) / h)) :
    D⁺ (fun s => f s + g s) t ≤ D⁺ f t + D⁺ g t := by
  unfold diniDerivRight
  set q_f : ℝ → ℝ := fun h => (f (t + h) - f t) / h
  set q_g : ℝ → ℝ := fun h => (g (t + h) - g t) / h
  -- 1. Split the difference quotient algebraically
  have h_eq : (fun h => ((f (t + h) + g (t + h)) - (f t + g t)) / h) = q_f + q_g := by
    ext h
    simp [q_f, q_g]
    ring
  -- 2. Substitute the split quotient into the goal
  rw [h_eq]
  -- 3. Apply the limsup addition rule, explicitly passing all 4 required bounds
  exact limsup_add_le hf_bdd_below hf_bdd_above hg_cobdd_below hg_bdd_above


lemma limsup_add_tendsto_zero {ι : Type*} {f g : ι → ℝ} {l : Filter ι} [l.NeBot]
    (hbdd_below : IsBoundedUnder (· ≥ ·) l f)
    (hbdd_above : IsBoundedUnder (· ≤ ·) l f)
    (hg : Tendsto g l (𝓝 0)) :
    limsup (f + g) l = limsup f l := by
  apply le_antisymm
  · have h1 : limsup (f + g) l ≤ limsup f l + limsup g l :=
      limsup_add_le hbdd_below hbdd_above hg.isCoboundedUnder_le hg.isBoundedUnder_le
    rwa [hg.limsup_eq, add_zero] at h1
  · have hneg : Tendsto (fun i => -g i) l (𝓝 0) := by simpa using hg.neg
    have hrw : f = fun i => (f i + g i) + (-g i) := by ext i; ring
    have hfg_bdd_below : IsBoundedUnder (· ≥ ·) l (f + g) := by
      obtain ⟨bf, hbf⟩ := hbdd_below
      obtain ⟨bg, hbg⟩ := hg.isBoundedUnder_ge
      refine ⟨bf + bg, ?_⟩
      simp only [Filter.eventually_map] at *
      filter_upwards [hbf, hbg] with i h1 h2
      simp [ge_iff_le] at *
      linarith
    have hfg_bdd_above : IsBoundedUnder (· ≤ ·) l (f + g) := by
      obtain ⟨bf, hbf⟩ := hbdd_above
      obtain ⟨bg, hbg⟩ := hg.isBoundedUnder_le
      refine ⟨bf + bg, ?_⟩
      simp only [Filter.eventually_map] at *
      filter_upwards [hbf, hbg] with i h1 h2
      simp only [Pi.add_apply]
      linarith
    have h2 : limsup (fun i => (f i + g i) + (-g i)) l ≤
              limsup (f + g) l + limsup (fun i => -g i) l :=
      limsup_add_le
        hfg_bdd_below
        hfg_bdd_above
        hneg.isCoboundedUnder_le
        hneg.isBoundedUnder_le
    rw [hneg.limsup_eq, add_zero] at h2
    rwa [← hrw] at h2


/-- Equality version when `g` is differentiable: `D⁺(f + g)(t) = D⁺f(t) + g'(t)`.
Requires bounds on `f` to avoid empty infimum contradictions in `ℝ`. -/
theorem diniDerivRight_add_differentiable {f g : ℝ → ℝ} {t : ℝ}
    (hf_bdd_below : IsBoundedUnder (· ≥ ·) (𝓝[>] 0)
      (fun h => (f (t + h) - f t) / h))
    (hf_bdd_above : IsBoundedUnder (· ≤ ·) (𝓝[>] 0)
      (fun h => (f (t + h) - f t) / h))
    (hg : DifferentiableAt ℝ g t) :
    D⁺ (fun s => f s + g s) t = D⁺ f t + deriv g t := by
  classical
  simp only [diniDerivRight]
  set q_f : ℝ → ℝ := fun h => (f (t + h) - f t) / h
  set q_g : ℝ → ℝ := fun h => (g (t + h) - g t) / h
  have h_split :
      (fun h => ((f (t + h) + g (t + h)) - (f t + g t)) / h)
        = q_f + q_g := by
    ext h
    simp [q_f, q_g]
    ring
  rw [h_split]
  have hq_g_tendsto : Tendsto q_g (𝓝[>] 0) (𝓝 (deriv g t)) := by
    have hslope := hg.hasDerivAt.tendsto_slope_zero_right
    simp only [Set.Ioi] at hslope
    refine hslope.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h (hh : h > 0)
    have h_eq : g (t + h) - g t = (g (t + h) - g t) := rfl
    rw [h_eq]
    ring
  have hq_g_bdd : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) q_g :=
    hq_g_tendsto.isBoundedUnder_le
  have hq_g_bdd_below : IsBoundedUnder (· ≥ ·) (𝓝[>] 0) q_g :=
    hq_g_tendsto.isBoundedUnder_ge
  have hzero : Tendsto (fun h => q_g h - deriv g t) (𝓝[>] 0) (𝓝 0) := by
    simpa using hq_g_tendsto.sub_const (deriv g t)
  have hrw : q_f + q_g = fun h => (q_f h + (q_g h - deriv g t)) + deriv g t := by
    ext h; simp [q_f, q_g]; ring
  have hcobdd : IsCoboundedUnder (· ≤ ·) (𝓝[>] 0) q_f :=
    hf_bdd_below.isCoboundedUnder_le
  rw [hrw, limsup_add_const]
  · -- main goal: limsup (fun h => q_f h + (q_g h - deriv g t)) = limsup q_f
    congr 1
    convert limsup_add_tendsto_zero hf_bdd_below hf_bdd_above hzero using 2
  · -- IsBoundedUnder (· ≤ ·) for q_f + (q_g - deriv g t)
    have hzero_bdd : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => q_g h - deriv g t) :=
      hzero.isBoundedUnder_le
    obtain ⟨bf, hbf⟩ := hf_bdd_above
    obtain ⟨bg, hbg⟩ := hzero_bdd
    refine ⟨bf + bg, ?_⟩
    simp only [Filter.eventually_map] at *
    filter_upwards [hbf, hbg] with h h1 h2
    linarith
  have hzero_bdd_below : IsBoundedUnder (· ≥ ·) (𝓝[>] 0) (fun h => q_g h - deriv g t) :=
    hzero.isBoundedUnder_ge
  apply IsBoundedUnder.isCoboundedUnder_le
  obtain ⟨bf, hbf⟩ := hf_bdd_below
  obtain ⟨bg, hbg⟩ := hzero_bdd_below
  refine ⟨bf + bg, ?_⟩
  simp only [IsBoundedUnder, IsBounded, eventually_map] at *
  filter_upwards [hbf, hbg] with h h1 h2
  linarith


/-- Shifting by a linear function shifts `D⁺` by the slope:
`D⁺(f + c·id)(t) = D⁺f(t) + c`. -/
theorem diniDerivRight_add_linear (f : ℝ → ℝ) (c t : ℝ)
    (hf_bdd_below : IsBoundedUnder (· ≥ ·) (𝓝[>] 0) (fun h => (f (t + h) - f t) / h))
    (hf_bdd_above : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (f (t + h) - f t) / h)) :
    D⁺ (fun s => f s + c * s) t = D⁺ f t + c := by
  have hg : DifferentiableAt ℝ (fun s => c * s) t := by
    have : (fun s => c * s) = (fun s => s * c) := by ext; ring
    rw [this]
    exact (hasDerivAt_mul_const c).differentiableAt
  have hderiv : deriv (fun s => c * s) t = c := by
    have : (fun s => c * s) = (fun s => s * c) := by ext; ring
    rw [this]
    exact (hasDerivAt_mul_const c).deriv
  have := diniDerivRight_add_differentiable hf_bdd_below hf_bdd_above hg
  rw [hderiv] at this
  exact this

/-- Scaling by a positive constant: `D⁺(c·f)(t) = c · D⁺f(t)` for `c > 0`. -/
theorem diniDerivRight_const_mul_pos {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (t : ℝ)
    (hbdd : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (f (t + h) - f t) / h))
    (hcobdd : IsCoboundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (f (t + h) - f t) / h)) :
    D⁺ (fun s => c * f s) t = c * D⁺ f t := by
  simp only [diniDerivRight]
  set q : ℝ → ℝ := fun h => (f (t + h) - f t) / h with hq_def
  have hrw : (fun h => (c * f (t + h) - c * f t) / h) = fun h => c * q h := by
    ext h; simp [q]; ring
  rw [hrw]
  have hq_bdd : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) q := by simpa [q] using hbdd
  have hq_cobdd : IsCoboundedUnder (· ≤ ·) (𝓝[>] 0) q := by simpa [q] using hcobdd
  -- 1. Construct the Order Isomorphism for multiplying by c > 0
  let e : ℝ ≃o ℝ :=
    { toFun := fun x => c * x
      invFun := fun x => c⁻¹ * x
      left_inv := fun x => by
        dsimp
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]
      right_inv := fun x => by
        dsimp
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul]
      map_rel_iff' := by
        intro x y
        dsimp
        constructor
        · intro h
          -- Multiply both sides by c⁻¹ to go backwards
          have h2 := mul_le_mul_of_nonneg_left h (inv_pos.mpr hc).le
          rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul,
               ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul] at h2
        · intro h
          exact mul_le_mul_of_nonneg_left h hc.le }
  have hgu : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (e ∘ q) := by
    obtain ⟨b, hb_bdd⟩ := hq_bdd
    use e b
    exact hb_bdd.mono (fun x hx => e.le_iff_le.mpr hx)
  have hgu_co : IsCoboundedUnder (· ≤ ·) (𝓝[>] 0) (e ∘ q) := by
      obtain ⟨b, hb_cobdd⟩ := hq_cobdd
      use e b
      intro a' ha'
      -- ha' : ∀ᶠ x in 𝓝[>] 0, c * q x ≤ a'
      have ha_inv : ∀ᶠ x in 𝓝[>] 0, q x ≤ c⁻¹ * a' := by
        filter_upwards [ha'] with x hx
        change c * q x ≤ a' at hx
        -- Multiply both sides of the inequality by c⁻¹
        have h1 := mul_le_mul_of_nonneg_left hx (inv_pos.mpr hc).le
        rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul] at h1
      -- Apply the original coboundedness hypothesis to our scaled bound
      have h_bound := hb_cobdd (c⁻¹ * a') ha_inv
      change c * b ≤ a'
      -- Multiply both sides of the result by c to finish
      have h3 := mul_le_mul_of_nonneg_left h_bound hc.le
      rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul] at h3
  -- 2. Use the OrderIso to pull `c` out of the limsup, bypassing sInf entirely
  change limsup (e ∘ q) (𝓝[>] 0) = e (limsup q (𝓝[>] 0))
  apply Eq.symm
  exact OrderIso.limsup_apply e
    (hu := hq_bdd)
    (hu_co := hq_cobdd)
    (hgu := hgu)
    (hgu_co := hgu_co)

/-- D⁺ is ≥ its negation's lower bound: `-(D⁺(-f)(t)) ≤ D⁺f(t)`
Requires the quotient to be bounded above and below to avoid junk values. -/
theorem neg_diniDerivRight_neg_le (f : ℝ → ℝ) (t : ℝ)
    (hbdd_above : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (f (t + h) - f t) / h))
    (hbdd_below : IsBoundedUnder (· ≥ ·) (𝓝[>] 0) (fun h => (f (t + h) - f t) / h)) :
    -(D⁺ (fun s => -f s) t) ≤ D⁺ f t := by
  simp only [diniDerivRight]
  set q : ℝ → ℝ := fun h => (f (t + h) - f t) / h
  have hrw : (fun h => (-f (t + h) - -f t) / h) = fun h => -q h := by
    ext h; simp [q]; ring
  rw [hrw]
  have hq_above : IsBoundedUnder (· ≤ ·) (𝓝[>] 0) q := by simpa [q] using hbdd_above
  have hq_below : IsBoundedUnder (· ≥ ·) (𝓝[>] 0) q := by simpa [q] using hbdd_below
  rw [Filter.limsup_eq, Filter.limsup_eq]
  -- Define the sets of upper bounds for readability
  set S := {a | ∀ᶠ x in 𝓝[>] 0, q x ≤ a}
  set T := {b' | ∀ᶠ x in 𝓝[>] 0, -q x ≤ b'}
  -- Goal: -(sInf T) ≤ sInf S
  apply le_csInf
  · -- 1. Prove S is nonempty
    obtain ⟨a, ha⟩ := hq_above
    exact ⟨a, ha⟩
  · -- 2. Prove -(sInf T) is a valid lower bound for S
    rintro a ha
    have h_lower : -a ≤ sInf T := by
      apply le_csInf
      · -- 2a. Prove T is nonempty
        obtain ⟨b, hb⟩ := hq_below
        use -b
        -- Strip away the '∈ T' set membership from the goal
        change ∀ᶠ x in 𝓝[>] 0, -q x ≤ -b
        have hb_ev : ∀ᶠ x in 𝓝[>] 0, b ≤ q x := hb
        exact hb_ev.mono (fun x hx => by linarith)
      · -- 2b. Prove -a is a lower bound for T
        rintro b' hb'
        -- Strip away the '∈ S' and '∈ T' wrappers from the hypotheses
        have ha_ev : ∀ᶠ x in 𝓝[>] 0, q x ≤ a := ha
        have hb_ev : ∀ᶠ x in 𝓝[>] 0, -q x ≤ b' := hb'
        -- Now .and works perfectly
        have h_inter : ∀ᶠ x in 𝓝[>] 0, q x ≤ a ∧ -q x ≤ b' := ha_ev.and hb_ev
        haveI : (𝓝[>] (0:ℝ)).NeBot := inferInstance
        obtain ⟨x, hx⟩ := Filter.Eventually.exists h_inter
        linarith
    linarith


end

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

import Architect

open MeasureTheory intervalIntegral Set Filter Topology

/-- Additivity of the interval integral in subtraction form: continuity on `[a, t]` supplies the
integrability side conditions, so the caller only has to supply `s ∈ [a, t]`. -/
@[blueprint "lem:integral-sub-adjacent-intervals"
  (title := "Difference of integrals over adjacent intervals")
  (latexEnv := "lemma")
  (statement := /-- For $\mu$ continuous on $[a, t]$ and $s \in [a, t]$,
    \[
      \int_a^t \mu - \int_a^s \mu = \int_s^t \mu .
    \] -/)]
lemma ContinuousOn.integral_sub_adjacent_intervals {a t : ℝ} {μ : ℝ → ℝ} {s : ℝ}
    (hμ_t : ContinuousOn μ (Icc a t))
    (hs : s ∈ Icc a t) :
    (∫ τ in a..t, μ τ) - ∫ τ in a..s, μ τ = ∫ τ in s..t, μ τ := by
  linarith [intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hμ_t.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1)
    ((hμ_t.mono (Icc_subset_Icc_left hs.1)).intervalIntegrable_of_Icc hs.2)]


/-- A pointwise bound `‖u s‖ ≤ L * v s` by a scalar multiple of a real function integrates to
`‖∫ u‖ ≤ L * ∫ v`. The comparison form used whenever a vector-valued estimate is transferred to
a scalar one, as in Grönwall arguments. -/
@[blueprint "lem:norm-integral-le-of-norm-le-mul"
  (title := "Integral bound from a pointwise multiplicative bound")
  (latexEnv := "lemma")
  (statement := /-- Let $u$ take values in a normed space and $v$ be real, both integrable on
    $[a,b]$ with $a \le b$. If $\|u(s)\| \le L\, v(s)$ for all $s \in [a,b]$, then
    \[
      \Bigl\| \int_a^b u \Bigr\| \le L \int_a^b v .
    \] -/)]
lemma intervalIntegral.norm_integral_le_of_norm_le_mul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → E} {v : ℝ → ℝ} {a b L : ℝ}
    (hab : a ≤ b)
    (hu_norm_int : IntervalIntegrable (fun s => ‖u s‖) volume a b)
    (hv_int : IntervalIntegrable v volume a b)
    (h_bound : ∀ s ∈ Icc a b, ‖u s‖ ≤ L * v s) :
    ‖∫ s in a..b, u s‖ ≤ L * ∫ s in a..b, v s := by
  calc ‖∫ s in a..b, u s‖
    _ ≤ ∫ s in a..b, ‖u s‖   := norm_integral_le_integral_norm hab
    _ ≤ ∫ s in a..b, L * v s := integral_mono_on hab hu_norm_int (hv_int.const_mul L) h_bound
    _ = L * ∫ s in a..b, v s := integral_const_mul L v

/-- `‖∫ a..b, u‖ ≤ C * (b - a)` from a uniform pointwise bound `‖u s‖ ≤ C` on `Icc a b`.
Hides the `uIoc`-to-`Icc` membership conversion required by Mathlib's
`norm_integral_le_of_norm_le_const`. -/
@[blueprint "lem:norm-integral-le-const-mul"
  (title := "Integral bound from a constant pointwise bound")
  (latexEnv := "lemma")
  (statement := /-- If $\|u(s)\| \le C$ for all $s \in [a,b]$ with $a \le b$, then
    \[
      \Bigl\| \int_a^b u \Bigr\| \le C\,(b-a).
    \] -/)]
lemma intervalIntegral.norm_integral_le_const_mul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → E} {C : ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (h : ∀ s ∈ Icc a b, ‖u s‖ ≤ C) :
    ‖∫ s in a..b, u s‖ ≤ C * (b - a) := by
  have key : ‖∫ s in a..b, u s‖ ≤ C * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [uIoc_of_le hab] at hs
    exact h s ⟨hs.1.le, hs.2⟩
  rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at key

/-- The interval integral of a real constant equals `(b - a) * C`.
Convenience form of `intervalIntegral.integral_const` for `ℝ`, avoiding `•` notation. -/
@[blueprint "lem:integral-const-eq"
  (title := "Integral of a constant")
  (latexEnv := "lemma")
  (statement := /-- $\int_a^b C \,\mathrm{d}s = (b-a)\,C$ for a real constant $C$. -/)]
lemma intervalIntegral.integral_const_eq {a b C : ℝ} :
    ∫ _ in a..b, C = (b - a) * C := by
  rw [intervalIntegral.integral_const, smul_eq_mul]


/-- The composition `s ↦ f(s, z(s))` is interval-integrable between `t₀` and `t₁` (in either
    order) when `f` is jointly continuous and `z` is continuous on the segment between them.

No ordering of `t₀` and `t₁` is required: `uIcc` is the segment either way, which is also the
interval the integral itself is taken over. -/
@[blueprint "lem:intervalIntegrable-comp"
  (title := "Interval integrability of a continuous composition")
  (latexEnv := "lemma")
  (statement := /-- If $f$ is jointly continuous and $z$ is continuous on the segment between
    $t_0$ and $t_1$, then $s \mapsto f(s, z(s))$ is interval-integrable between them.  This is
    the integrability side condition every integral-form solution argument needs. -/)]
lemma Continuous.intervalIntegrable_comp {t₀ t₁ : ℝ}
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E → E} {z : ℝ → E}
    (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hz : ContinuousOn z (uIcc t₀ t₁)) :
    IntervalIntegrable (fun s => f s (z s)) volume t₀ t₁ :=
  (hf_cont.comp_continuousOn
    (ContinuousOn.prodMk continuous_id.continuousOn hz)).intervalIntegrable



/-! ## The primitive of a continuous function -/

/-- The primitive `x ↦ ∫ τ in a..x, μ τ` of a continuous `μ` has derivative `μ t` at every
    interior point of `[a, b]`. A packaging of the fundamental theorem of calculus that supplies
    the three side conditions from a single `ContinuousOn` hypothesis. -/
@[blueprint "lem:hasDerivAt-integral"
  (title := "Differentiating an integral in its upper limit")
  (latexEnv := "lemma")
  (statement := /-- For $\mu$ continuous on $[a,b]$ and $t \in (a,b)$,
    \[
      \frac{\mathrm{d}}{\mathrm{d}x}\Big|_{x=t} \int_{a}^{x} \mu(\tau)\,\mathrm{d}\tau
        \;=\; \mu(t).
    \] -/)]
lemma hasDerivAt_integral {a b : ℝ} {μ : ℝ → ℝ}
    (hμ : ContinuousOn μ (Icc a b)) (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun x ↦ ∫ τ in a..x, μ τ) (μ t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((hμ.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
    ((hμ.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
    (hμ.continuousAt (Icc_mem_nhds ht.1 ht.2))

/-- The primitive `s ↦ ∫ τ in a..s, f τ` of an integrable `f` is continuous on `[a, t]`.

Mathlib's `continuousOn_primitive_interval` is stated on the unordered `uIcc`; requiring `a ≤ t`
explicitly lets callers stay in `Icc` throughout. -/
@[blueprint "lem:continuousOn-integral-Icc"
  (title := "Continuity of an integral in its upper limit")
  (latexEnv := "lemma")
  (statement := /-- If $f$ is integrable on $[a,t]$ with $a \le t$, then
    $s \mapsto \int_{a}^{s} f(\tau)\,\mathrm{d}\tau$ is continuous on $[a,t]$. -/)]
lemma continuousOn_integral_Icc {a t : ℝ} {f : ℝ → ℝ} (h : a ≤ t)
    (hf_int : IntegrableOn f (Icc a t) volume) :
    ContinuousOn (fun s ↦ ∫ τ in a..s, f τ) (Icc a t) := by
  have hu : Set.uIcc a t = Set.Icc a t := Set.uIcc_of_le h
  rw [← hu] at hf_int ⊢
  exact intervalIntegral.continuousOn_primitive_interval hf_int


/-! ## Integrals with moving endpoints -/

/-- The integral of a locally integrable `f` between two continuously varying positive endpoints
is continuous. -/
@[blueprint "lem:continuousOn-integral-endpoints"
  (title := "Continuity of an integral in both endpoints")
  (latexEnv := "lemma")
  (statement := /-- Let $f$ be locally integrable on $(0,\infty)$, and let $a, b$ be continuous on
    a set $S$ with $a(\eta), b(\eta) > 0$ in $S$. Then
    \[
      \eta \;\longmapsto\; \int_{a(\eta)}^{b(\eta)} f(x)\,\mathrm{d}x
    \]
    is continuous on $S$. -/)]
lemma continuousOn_integral_endpoints {f : ℝ → ℝ} {S : Set ℝ} {a b : ℝ → ℝ}
    (hf_int : ∀ x y, 0 < x → 0 < y → IntervalIntegrable f volume x y)
    (ha : ContinuousOn a S) (hb : ContinuousOn b S)
    (ha_pos : ∀ η ∈ S, 0 < a η) (hb_pos : ∀ η ∈ S, 0 < b η) :
    ContinuousOn (fun η => ∫ x in (a η)..(b η), f x) S := by
  intro η₀ hη₀
  have ha₀ : 0 < a η₀ := ha_pos η₀ hη₀
  have hb₀ : 0 < b η₀ := hb_pos η₀ hη₀
  -- A fixed window `[A, B]` straddling both endpoints, on which the primitive is continuous.
  obtain ⟨A, hA_pos, hAa, hAb⟩ : ∃ A : ℝ, 0 < A ∧ A < a η₀ ∧ A < b η₀ :=
    ⟨min (a η₀) (b η₀) / 2, half_pos (lt_min ha₀ hb₀),
      by linarith [min_le_left (a η₀) (b η₀), lt_min ha₀ hb₀],
      by linarith [min_le_right (a η₀) (b η₀), lt_min ha₀ hb₀]⟩
  obtain ⟨B, haB, hbB⟩ : ∃ B : ℝ, a η₀ < B ∧ b η₀ < B :=
    ⟨max (a η₀) (b η₀) + 1, by linarith [le_max_left (a η₀) (b η₀)],
      by linarith [le_max_right (a η₀) (b η₀)]⟩
  have h_prim : ContinuousOn (fun x => ∫ y in A..x, f y) (Set.Icc A B) := by
    have h := continuousOn_primitive_interval'
      (hf_int A B hA_pos (by linarith)) (left_mem_uIcc (b := B))
    rwa [uIcc_of_le (by linarith)] at h
  have contA : ContinuousWithinAt (fun η => ∫ y in A..(a η), f y) S η₀ :=
    (h_prim.continuousAt (Icc_mem_nhds hAa haB)).comp_continuousWithinAt (ha η₀ hη₀)
  have contB : ContinuousWithinAt (fun η => ∫ y in A..(b η), f y) S η₀ :=
    (h_prim.continuousAt (Icc_mem_nhds hAb hbB)).comp_continuousWithinAt (hb η₀ hη₀)
  -- Splitting at `A` is exactly the difference of the two primitives.
  have key : ∀ η ∈ S,
      (∫ x in (a η)..(b η), f x) = (∫ y in A..(b η), f y) - ∫ y in A..(a η), f y := by
    intro η hη
    linarith [integral_add_adjacent_intervals (hf_int A (a η) hA_pos (ha_pos η hη))
      (hf_int (a η) (b η) (ha_pos η hη) (hb_pos η hη))]
  exact (contB.sub contA).congr key (key η₀ hη₀)



/-! ## Mean values over moving windows

Normalizing by the window length `b η - a η` rather than by a factor tied to `η` makes the
quantity a genuine mean value, and then monotone endpoints are all that antitonicity needs — no
proportionality, and no rescaling substitution. Monotonicity of *both* endpoints is essential:
`a η < b η` alone permits a window that jumps leftwards into a steeper region, which raises the
mean. -/

/-- Moving the **right** endpoint right does not raise the mean value of an antitone `f`: the
material added on `[b₁, b₂]` lies below `f b₁`, which already lies below the old mean. -/
private lemma average_antitone_right {f : ℝ → ℝ} {a b₁ b₂ : ℝ}
    (hf_anti : AntitoneOn f (Set.Ioi 0))
    (hf_int : ∀ x y, 0 < x → 0 < y → IntervalIntegrable f volume x y)
    (ha : 0 < a) (hab : a < b₁) (hb : b₁ ≤ b₂) :
    (∫ x in a..b₂, f x) / (b₂ - a) ≤ (∫ x in a..b₁, f x) / (b₁ - a) := by
  have hb₁ : 0 < b₁ := ha.trans hab
  have hb₂ : 0 < b₂ := hb₁.trans_le hb
  -- `f b₁` is a lower bound for `f` on `[a, b₁]`, hence for the mean there.
  have hlow : (b₁ - a) * f b₁ ≤ ∫ x in a..b₁, f x := by
    have h := intervalIntegral.integral_mono_on (f := fun _ => f b₁) (g := f) hab.le
      intervalIntegral.intervalIntegrable_const (hf_int a b₁ ha hb₁)
      (fun x hx => hf_anti (Set.mem_Ioi.mpr (ha.trans_le hx.1)) (Set.mem_Ioi.mpr hb₁) hx.2)
    rwa [intervalIntegral.integral_const_eq] at h
  -- and an upper bound for `f` on `[b₁, b₂]`.
  have hhigh : (∫ x in b₁..b₂, f x) ≤ (b₂ - b₁) * f b₁ := by
    have h := intervalIntegral.integral_mono_on (f := f) (g := fun _ => f b₁) hb
      (hf_int b₁ b₂ hb₁ hb₂) intervalIntegral.intervalIntegrable_const
      (fun x hx => hf_anti (Set.mem_Ioi.mpr hb₁) (Set.mem_Ioi.mpr (hb₁.trans_le hx.1)) hx.1)
    rwa [intervalIntegral.integral_const_eq] at h
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hf_int a b₁ ha hb₁) (hf_int b₁ b₂ hb₁ hb₂)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [hlow, hhigh, hsplit]

/-- Moving the **left** endpoint right does not raise the mean value of an antitone `f`: the
material dropped from `[a₁, a₂]` lies above `f a₂`, which already lies above the new mean. -/
private lemma average_antitone_left {f : ℝ → ℝ} {a₁ a₂ b : ℝ}
    (hf_anti : AntitoneOn f (Set.Ioi 0))
    (hf_int : ∀ x y, 0 < x → 0 < y → IntervalIntegrable f volume x y)
    (ha : 0 < a₁) (ha₁₂ : a₁ ≤ a₂) (hab : a₂ < b) :
    (∫ x in a₂..b, f x) / (b - a₂) ≤ (∫ x in a₁..b, f x) / (b - a₁) := by
  have ha₂ : 0 < a₂ := ha.trans_le ha₁₂
  have hb : 0 < b := ha₂.trans hab
  -- `f a₂` is an upper bound for the mean on `[a₂, b]`.
  have hhigh : (∫ x in a₂..b, f x) ≤ (b - a₂) * f a₂ := by
    have h := intervalIntegral.integral_mono_on (f := f) (g := fun _ => f a₂) hab.le
      (hf_int a₂ b ha₂ hb) intervalIntegral.intervalIntegrable_const
      (fun x hx => hf_anti (Set.mem_Ioi.mpr ha₂) (Set.mem_Ioi.mpr (ha₂.trans_le hx.1)) hx.1)
    rwa [intervalIntegral.integral_const_eq] at h
  -- and a lower bound for `f` on `[a₁, a₂]`.
  have hlow : (a₂ - a₁) * f a₂ ≤ ∫ x in a₁..a₂, f x := by
    have h := intervalIntegral.integral_mono_on (f := fun _ => f a₂) (g := f) ha₁₂
      intervalIntegral.intervalIntegrable_const (hf_int a₁ a₂ ha ha₂)
      (fun x hx => hf_anti (Set.mem_Ioi.mpr (ha.trans_le hx.1)) (Set.mem_Ioi.mpr ha₂) hx.2)
    rwa [intervalIntegral.integral_const_eq] at h
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hf_int a₁ a₂ ha ha₂) (hf_int a₂ b ha₂ hb)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [hlow, hhigh, hsplit]

/-- The **mean value** of an antitone `f` over a window whose endpoints both move right is
antitone. Both endpoints must be monotone: `a η < b η` alone is not enough, since a window that
jumps leftwards into a steeper region raises the mean. -/
@[blueprint "lem:antitoneOn-integral-average"
  (title := "The sliding average of an antitone function is antitone")
  (latexEnv := "lemma")
  (statement := /-- Let $f$ be antitone and locally integrable on $(0,\infty)$, and let
    $a, b$ be monotone on a set $S$ with $0 < a(\eta) < b(\eta)$. Then the mean value
    \[
      \eta \;\longmapsto\; \frac{1}{b(\eta) - a(\eta)}\int_{a(\eta)}^{b(\eta)} f(x)\,\mathrm{d}x
    \]
    is antitone on $S$. -/)]
lemma antitoneOn_integral_average {f : ℝ → ℝ} {S : Set ℝ} {a b : ℝ → ℝ}
    (hf_anti : AntitoneOn f (Set.Ioi 0))
    (hf_int : ∀ x y, 0 < x → 0 < y → IntervalIntegrable f volume x y)
    (ha_pos : ∀ η ∈ S, 0 < a η) (hab : ∀ η ∈ S, a η < b η)
    (ha_mono : MonotoneOn a S) (hb_mono : MonotoneOn b S) :
    AntitoneOn (fun η => (∫ x in (a η)..(b η), f x) / (b η - a η)) S := by
  intro η₁ h₁ η₂ h₂ h₁₂
  -- Compose through the intermediate window `[a η₁, b η₂]`, which contains both.
  calc (∫ x in (a η₂)..(b η₂), f x) / (b η₂ - a η₂)
      ≤ (∫ x in (a η₁)..(b η₂), f x) / (b η₂ - a η₁) :=
        average_antitone_left hf_anti hf_int (ha_pos η₁ h₁) (ha_mono h₁ h₂ h₁₂) (hab η₂ h₂)
    _ ≤ (∫ x in (a η₁)..(b η₁), f x) / (b η₁ - a η₁) :=
        average_antitone_right hf_anti hf_int (ha_pos η₁ h₁) (hab η₁ h₁) (hb_mono h₁ h₂ h₁₂)


/-- The mean value of a nonneg antitone `f` that decays to `0` tends to `0`, provided the *left*
endpoint tends to `+∞`. -/
@[blueprint "lem:tendsto-integral-average-atTop-zero"
  (title := "Sliding average of an eventually vanishing function")
  (latexEnv := "lemma")
  (statement := /-- Let $f$ be nonneg, antitone and locally integrable on $(0,\infty)$ with
    $f(s) \to 0$ as $s \to +\infty$, and let $a(\eta) < b(\eta)$ with
    $a(\eta) \to +\infty$ as $\eta \to +\infty$. Then
    \[
      \frac{1}{b(\eta) - a(\eta)}\int_{a(\eta)}^{b(\eta)} f(x)\,\mathrm{d}x \;\longrightarrow\; 0
      \qquad (\eta \to +\infty).
    \]
    The mean is squeezed between $0$ and $f(a(\eta))$; no hypothesis relating $a$ to $b$ is
    needed. -/)]
lemma tendsto_integral_average_atTop_zero {f a b : ℝ → ℝ}
    (hf_nonneg : ∀ s > 0, 0 ≤ f s)
    (hf_anti : AntitoneOn f (Set.Ioi 0))
    (hf_int : ∀ x y, 0 < x → 0 < y → IntervalIntegrable f volume x y)
    (hf_tendsto : Filter.Tendsto f Filter.atTop (nhds 0))
    (hab : ∀ᶠ η in Filter.atTop, a η < b η)
    (ha_top : Filter.Tendsto a Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun η => (∫ x in (a η)..(b η), f x) / (b η - a η))
      Filter.atTop (nhds 0) := by
  have ha_pos : ∀ᶠ η in Filter.atTop, 0 < a η := ha_top.eventually_gt_atTop 0
  -- Squeeze between `0` and `f (a η)`, the largest value `f` takes on the window.
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (hf_tendsto.comp ha_top)
  · filter_upwards [ha_pos, hab] with η hη hlt
    exact div_nonneg (integral_nonneg hlt.le fun s hs => hf_nonneg s (hη.trans_le hs.1))
      (by linarith)
  · filter_upwards [ha_pos, hab] with η hη hlt
    rw [div_le_iff₀ (by linarith)]
    calc (∫ x in (a η)..(b η), f x)
        ≤ ∫ _ in (a η)..(b η), f (a η) :=
          integral_mono_on hlt.le (hf_int _ _ hη (hη.trans hlt))
            intervalIntegral.intervalIntegrable_const
            fun s hs => hf_anti hη (hη.trans_le hs.1) hs.1
      _ = f (a η) * (b η - a η) := by
          rw [intervalIntegral.integral_const_eq]; ring

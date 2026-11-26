import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Architect

/-!
# Absolutely continuous curves

Tools for Carathéodory solutions of differential equations.  A Carathéodory solution of
`ẋ = g(t)` on `[a, b]` is a curve with `x t - x a = ∫ τ in a..t, g τ` for an integrable `g`; it
is absolutely continuous and has derivative `g t` at almost every `t`, but in general no
derivative at any given point.  This file collects what the theory of such solutions needs about
raw functions; Mathlib's `AbsolutelyContinuousOnInterval` supplies the definition and the
fundamental theorem of calculus for real-valued functions.

Following Mathlib, absolute continuity is stated on the segment `uIcc a b`; almost-everywhere
hypotheses are stated on the open interval `Ioo a b`, the weakest form.

## Main declarations

* `IntervalIntegrable.absolutelyContinuousOnInterval_primitive` — the primitive of an integrable
  function with values in a normed space is absolutely continuous;
  `absolutelyContinuousOnInterval_of_sub_eq_integral` is the form for a curve given by an integral.
* `ae_hasDerivAt_of_sub_eq_integral` — such a curve has derivative `g t` at almost every `t`;
  `ae_mem_interior_imp_of_forall_Icc_subset` passes such a statement from the segments inside a
  set to its interior.
* `HasDerivAt.abs_le_norm_of_norm` — the derivative of `t ↦ ‖f t‖` is at most `‖f'‖` in absolute
  value.
* `AbsolutelyContinuousOnInterval.sub_le_integral_of_deriv_le` — an almost-everywhere bound on the
  derivative of an absolutely continuous real function integrates to a bound on its increment.
  Consequences: monotonicity (`antitoneOn_of_deriv_nonpos`, `monotoneOn_of_deriv_nonneg`), a
  level bound (`le_max_of_deriv_nonpos`) and Grönwall's inequality
  (`le_mul_exp_integral_of_deriv_le`, `le_mul_exp_of_deriv_le`, `le_gronwallBound_of_deriv_le`).
* `LocallyLipschitzOn.comp_absolutelyContinuousOnInterval` — a locally Lipschitz function of an
  absolutely continuous curve is absolutely continuous; `LocallyLipschitzOn.comp_snd` makes a
  locally Lipschitz `V(x)` a locally Lipschitz function of `(t, x)`, and
  `locallyLipschitzOn_of_contDiffAt` makes a `C¹` function locally Lipschitz.
* `AbsolutelyContinuousOnInterval.prodMk`, `.graph`, `.norm`, `.pow` — closure properties; e.g.
  `((hx.sub hy).norm.pow 2)` makes `t ↦ ‖x t - y t‖ ^ 2` absolutely continuous.
-/

open MeasureTheory Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}

/-! ## Closure properties -/

namespace AbsolutelyContinuousOnInterval

/-- A pair of absolutely continuous functions is absolutely continuous. -/
@[blueprint "lem:absolutelyContinuousOnInterval-prodMk"
  (title := "Absolute continuity of a pair")
  (latexEnv := "lemma")
  (statement := /-- If $f$ and $g$ are absolutely continuous on $[a, b]$, so is
    $t \mapsto (f(t), g(t))$. -/)
  (proof := /-- The distance in the product is at most the sum of the distances. -/)]
theorem prodMk {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {f : ℝ → X}
    {g : ℝ → Y} (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => (f t, g t)) a b := by
  unfold AbsolutelyContinuousOnInterval at *
  refine squeeze_zero (fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg) (fun I => ?_)
    (by simpa using hf.add hg)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ =>
    Prod.dist_eq.trans_le (max_le_add_of_nonneg dist_nonneg dist_nonneg)

/-- The norm of an absolutely continuous function is absolutely continuous. -/
@[blueprint "lem:absolutelyContinuousOnInterval-norm"
  (title := "Absolute continuity of the norm")
  (latexEnv := "lemma")
  (statement := /-- If $f$ is absolutely continuous on $[a, b]$, so is $t \mapsto \|f(t)\|$. -/)
  (proof := /-- The norm is $1$-Lipschitz. -/)]
theorem norm {G : Type*} [SeminormedAddCommGroup G] {f : ℝ → G}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => ‖f t‖) a b :=
  lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hf

/-- A power of an absolutely continuous real function is absolutely continuous. -/
@[blueprint "lem:absolutelyContinuousOnInterval-pow"
  (title := "Absolute continuity of a power")
  (latexEnv := "lemma")
  (statement := /-- If $f$ is real and absolutely continuous on $[a, b]$, so is $f^n$. -/)
  (proof := /-- Induction on $n$, since products of absolutely continuous functions are
    absolutely continuous. -/)]
theorem pow {f : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (n : ℕ) :
    AbsolutelyContinuousOnInterval (fun t => f t ^ n) a b := by
  induction n with
  | zero =>
    simpa using (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  | succ n ih => simpa [pow_succ] using ih.fun_mul hf

/-- The graph `t ↦ (t, x t)` of an absolutely continuous curve is absolutely continuous. -/
@[blueprint "lem:absolutelyContinuousOnInterval-graph"
  (title := "Absolute continuity of the graph")
  (latexEnv := "lemma")
  (statement := /-- If $x$ is absolutely continuous on $[a, b]$, so is $t \mapsto (t, x(t))$. -/)
  (proof := /-- The identity is Lipschitz; apply \cref{lem:absolutelyContinuousOnInterval-prodMk}.
    -/)]
theorem graph {X : Type*} [PseudoMetricSpace X] {x : ℝ → X}
    (hx : AbsolutelyContinuousOnInterval x a b) :
    AbsolutelyContinuousOnInterval (fun t => (t, x t)) a b :=
  LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval.prodMk hx

end AbsolutelyContinuousOnInterval

/-- A function of the second variable alone that is locally Lipschitz on `D` is locally Lipschitz,
as a function of the pair, on the pairs whose second component is in `D`.  This turns a
time-invariant `V(x)` into a time-varying `V(t, x)`. -/
@[blueprint "lem:locallyLipschitzOn-comp-snd"
  (title := "A locally Lipschitz function of the second variable")
  (latexEnv := "lemma")
  (statement := /-- If $f$ is locally Lipschitz on $D$, then $(a, x) \mapsto f(x)$ is locally
    Lipschitz on $\{(a, x) : x \in D\}$. -/)
  (proof := /-- The second projection is $1$-Lipschitz and continuous. -/)]
theorem LocallyLipschitzOn.comp_snd {α X Y : Type*} [PseudoEMetricSpace α]
    [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {f : X → Y} {D : Set X}
    (hf : LocallyLipschitzOn D f) :
    LocallyLipschitzOn (Prod.snd ⁻¹' D : Set (α × X)) fun p => f p.2 := by
  intro p hp
  obtain ⟨K, t, ht, hK⟩ := hf hp
  exact ⟨K, Prod.snd ⁻¹' t,
    continuous_snd.continuousWithinAt.tendsto_nhdsWithin (mapsTo_preimage _ _) ht, by
    simpa only [mul_one, Function.comp_def] using
      hK.comp LipschitzWith.prod_snd.lipschitzOnWith (mapsTo_preimage _ _)⟩

/-- A function that is `C¹` at every point of a set is locally Lipschitz on it.  No openness or
convexity of the set is needed; compare Mathlib's `ContDiff.locallyLipschitz` (the whole space)
and `ContDiffOn.locallyLipschitzOn` (a convex set). -/
@[blueprint "lem:locallyLipschitzOn-of-contDiffAt"
  (title := "Continuously differentiable functions are locally Lipschitz")
  (latexEnv := "lemma")
  (statement := /-- If $f$ is $C^1$ at every point of $D$, then $f$ is locally Lipschitz on
    $D$. -/)
  (proof := /-- A function that is $C^1$ at a point is Lipschitz on a neighbourhood of it. -/)]
theorem locallyLipschitzOn_of_contDiffAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {D : Set E} (hf : ∀ x ∈ D, ContDiffAt ℝ 1 f x) : LocallyLipschitzOn D f :=
  fun x hx =>
    let ⟨K, t, ht, hK⟩ := (hf x hx).exists_lipschitzOnWith
    ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

/-- A function that is locally Lipschitz on a set containing the image of an absolutely continuous
curve is absolutely continuous along it.  The curve's image is compact, and a locally Lipschitz
function is Lipschitz on compact sets. -/
@[blueprint "lem:locallyLipschitzOn-comp-absolutelyContinuousOnInterval"
  (title := "Locally Lipschitz functions preserve absolute continuity")
  (latexEnv := "lemma")
  (statement := /-- Let $\gamma$ be absolutely continuous on $[a, b]$ with values in $S$, and $f$
    locally Lipschitz on $S$.  Then $f \circ \gamma$ is absolutely continuous on $[a, b]$. -/)
  (proof := /-- $\gamma([a, b])$ is compact, so $f$ is Lipschitz on it, and a Lipschitz function
    of an absolutely continuous curve is absolutely continuous. -/)]
theorem LocallyLipschitzOn.comp_absolutelyContinuousOnInterval {X Y : Type*}
    [SeminormedAddCommGroup X] [PseudoMetricSpace Y] {f : X → Y} {S : Set X}
    (hf : LocallyLipschitzOn S f) {γ : ℝ → X} (hγS : MapsTo γ (uIcc a b) S)
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (f ∘ γ) a b := by
  obtain ⟨K, hK⟩ := (hf.mono hγS.image_subset).exists_lipschitzOnWith_of_compact
    (isCompact_uIcc.image_of_continuousOn hγ.continuousOn)
  exact hK.comp_absolutelyContinuousOnInterval (mapsTo_image _ _) hγ

/-! ## Curves given by an integral -/

/-- The primitive of an integrable function with values in a normed space is absolutely
continuous.  Mathlib's `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral` is the
real-valued case, to which this reduces: the increments of the primitive of `g` are bounded by
those of the primitive of `‖g‖`. -/
@[blueprint "lem:absolutelyContinuousOnInterval-primitive"
  (title := "The primitive of an integrable function is absolutely continuous")
  (latexEnv := "lemma")
  (statement := /-- If $g : \mathbb{R} \to E$ is integrable on $[a, b]$ and $c \in [a, b]$, then
    $t \mapsto \int_c^t g(\tau)\,\mathrm{d}\tau$ is absolutely continuous on $[a, b]$. -/)
  (proof := /-- $\bigl\|\int_s^t g\bigr\| \le \bigl|\int_s^t \|g\|\bigr|$, and the primitive of the
    real function $\|g\|$ is absolutely continuous. -/)]
theorem IntervalIntegrable.absolutelyContinuousOnInterval_primitive {g : ℝ → E} {c : ℝ}
    (hg : IntervalIntegrable g volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun t => ∫ τ in c..t, g τ) a b := by
  have h := absolutelyContinuousOnInterval_iff _ _ _ |>.mp
    (hg.norm.absolutelyContinuousOnInterval_intervalIntegral hc)
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  obtain ⟨δ, hδ, hE⟩ := h ε hε
  refine ⟨δ, hδ, fun E hE₁ hE₂ => (Finset.sum_le_sum fun i hi => ?_).trans_lt (hE E hE₁ hE₂)⟩
  have hint : ∀ t ∈ uIcc a b, IntervalIntegrable g volume c t := fun t ht =>
    hg.mono_set (uIcc_subset_uIcc hc ht)
  obtain ⟨hs, ht⟩ := hE₁.1 i hi
  rw [dist_eq_norm, Real.dist_eq, intervalIntegral.integral_interval_sub_left (hint _ hs)
    (hint _ ht), intervalIntegral.integral_interval_sub_left (hint _ hs).norm (hint _ ht).norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

/-- A curve given by an integral, `x t - x a = ∫ τ in a..t, g τ`, is absolutely continuous. -/
@[blueprint "lem:absolutelyContinuousOnInterval-of-sub-eq-integral"
  (title := "A curve given by an integral is absolutely continuous")
  (latexEnv := "lemma")
  (statement := /-- If $g$ is integrable on $[a, b]$ and
    $x(t) - x(a) = \int_a^t g(\tau)\,\mathrm{d}\tau$ for $t \in [a, b]$, then $x$ is absolutely
    continuous on $[a, b]$. -/)
  (proof := /-- $x$ is a translate of the primitive of $g$,
    \cref{lem:absolutelyContinuousOnInterval-primitive}. -/)]
theorem absolutelyContinuousOnInterval_of_sub_eq_integral {x g : ℝ → E}
    (hg : IntervalIntegrable g volume a b)
    (hx : ∀ t ∈ uIcc a b, x t - x a = ∫ τ in a..t, g τ) :
    AbsolutelyContinuousOnInterval x a b :=
  ((isometry_add_left (x a)).lipschitzWith.comp_absolutelyContinuousOnInterval
    (hg.absolutelyContinuousOnInterval_primitive left_mem_uIcc)).congr
    fun t ht => by simp [← hx t ht]

/-- A curve given by an integral, `x t - x a = ∫ τ in a..t, g τ`, has derivative `g t` at almost
every `t`: the Lebesgue differentiation theorem. -/
@[blueprint "lem:ae-hasDerivAt-of-sub-eq-integral"
  (title := "A curve given by an integral is differentiable almost everywhere")
  (latexEnv := "lemma")
  (statement := /-- If $g$ is integrable on $[a, b]$ and
    $x(t) - x(a) = \int_a^t g(\tau)\,\mathrm{d}\tau$ for $t \in [a, b]$, then $x$ has derivative
    $g(t)$ at almost every $t \in (a, b)$. -/)
  (proof := /-- The Lebesgue differentiation theorem: the primitive of $g$ has derivative $g(t)$
    at almost every $t$, and $x$ agrees with a translate of it near each $t \in (a, b)$. -/)]
theorem ae_hasDerivAt_of_sub_eq_integral [CompleteSpace E] {x g : ℝ → E}
    (hg : IntervalIntegrable g volume a b)
    (hx : ∀ t ∈ uIcc a b, x t - x a = ∫ τ in a..t, g τ) :
    ∀ᵐ t, t ∈ Ioo a b → HasDerivAt x (g t) t := by
  filter_upwards [hg.ae_hasDerivAt_integral] with t ht htab
  have hmem : t ∈ uIcc a b := Icc_subset_uIcc (Ioo_subset_Icc_self htab)
  refine ((ht hmem a left_mem_uIcc).const_add (x a)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds htab.1 htab.2] with s hs
  rw [← hx s (Icc_subset_uIcc (Ioo_subset_Icc_self hs)), add_sub_cancel]

/-- A property that holds at almost every point of `(a, b)` whenever `[a, b] ⊆ I` holds at almost
every point of the interior of `I`: the interior is covered by countably many such `(a, b)`, those
with rational endpoints.  This passes an almost-everywhere statement from segments to an arbitrary
set. -/
@[blueprint "lem:ae-mem-interior-imp-of-forall-Icc-subset"
  (title := "From almost everywhere on segments to almost everywhere on the interior")
  (latexEnv := "lemma")
  (statement := /-- Let $I \subseteq \mathbb{R}$ and let $p$ be a property of real numbers that
    holds at almost every point of $(a, b)$ whenever $a < b$ and $[a, b] \subseteq I$.  Then $p$
    holds at almost every point of the interior of $I$. -/)
  (proof := /-- The interior of $I$ is covered by the intervals $(q, r)$ with rational endpoints
    and $[q, r] \subseteq I$, which are countably many. -/)]
theorem ae_mem_interior_imp_of_forall_Icc_subset {p : ℝ → Prop} {I : Set ℝ}
    (h : ∀ a b : ℝ, a < b → Icc a b ⊆ I → ∀ᵐ t, t ∈ Ioo a b → p t) :
    ∀ᵐ t, t ∈ interior I → p t := by
  have h_seg : ∀ q r : ℚ, ∀ᵐ t, (q : ℝ) < r → Icc (q : ℝ) r ⊆ I → t ∈ Ioo (q : ℝ) r → p t :=
    fun q r => eventually_imp_distrib_left.2 fun hqr => eventually_imp_distrib_left.2 (h q r hqr)
  filter_upwards [ae_all_iff.2 fun q => ae_all_iff.2 (h_seg q)] with t ht ht_int
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 ht_int)
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show t - ε < t by linarith)
  obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn (show t < t + ε by linarith)
  refine ht q r (hq₂.trans hr₁) (fun τ hτ => hball ?_) ⟨hq₂, hr₁⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hτ.1, hτ.2]

/-! ## The derivative of the norm of a curve -/

/-- The norm of a curve changes no faster than the curve: where both derivatives exist, the
derivative of `t ↦ ‖f t‖` is at most `‖f'‖` in absolute value. -/
@[blueprint "lem:hasDerivAt-abs-le-norm-of-norm"
  (title := "The norm of a curve changes no faster than the curve")
  (latexEnv := "lemma")
  (statement := /-- If $f : \mathbb{R} \to E$ has derivative $f'$ at $t$ and
    $s \mapsto \|f(s)\|$ has derivative $v'$ at $t$, then $|v'| \le \|f'\|$. -/)
  (proof := /-- By the reverse triangle inequality the difference quotients of $\|f\|$ are
    bounded in absolute value by the norms of those of $f$; pass to the limit. -/)]
theorem HasDerivAt.abs_le_norm_of_norm {f : ℝ → E} {f' : E} {v' t : ℝ} (hf : HasDerivAt f f' t)
    (hv : HasDerivAt (fun s => ‖f s‖) v' t) : |v'| ≤ ‖f'‖ := by
  refine le_of_tendsto_of_tendsto (hasDerivAt_iff_tendsto_slope.1 hv).abs
    (hasDerivAt_iff_tendsto_slope.1 hf).norm (Eventually.of_forall fun s => ?_)
  simp only [slope, vsub_eq_sub, smul_eq_mul, abs_mul, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) (abs_nonneg _)

/-! ## Integrating a bound on the derivative -/

namespace AbsolutelyContinuousOnInterval

/-- An almost-everywhere bound `deriv v t ≤ g t` on the derivative of an absolutely continuous
real function integrates to `v b - v a ≤ ∫ t in a..b, g t`. -/
@[blueprint "lem:absolutelyContinuousOnInterval-sub-le-integral-of-deriv-le"
  (title := "Integrating an almost-everywhere bound on the derivative")
  (latexEnv := "lemma")
  (statement := /-- Let $v$ be real and absolutely continuous on $[a, b]$, $a \le b$, and $g$
    integrable on $[a, b]$.  If $v'(t) \le g(t)$ for almost every $t \in (a, b)$, then
    \[
      v(b) - v(a) \le \int_a^b g(t)\,\mathrm{d}t.
    \] -/)
  (proof := /-- $v(b) - v(a) = \int_a^b v'$ by the fundamental theorem of calculus for absolutely
    continuous functions; integrate the bound. -/)]
theorem sub_le_integral_of_deriv_le {v g : ℝ → ℝ} (hab : a ≤ b)
    (hv : AbsolutelyContinuousOnInterval v a b) (hg : IntervalIntegrable g volume a b)
    (h : ∀ᵐ t, t ∈ Ioo a b → deriv v t ≤ g t) :
    v b - v a ≤ ∫ t in a..b, g t := by
  rw [← hv.integral_deriv_eq_sub]
  refine intervalIntegral.integral_mono_ae_restrict hab hv.intervalIntegrable_deriv hg ?_
  rw [EventuallyLE, ← Measure.restrict_congr_set Ioo_ae_eq_Icc, ae_restrict_iff' measurableSet_Ioo]
  exact h

/-- An absolutely continuous real function whose derivative is almost everywhere nonpositive is
nonincreasing. -/
@[blueprint "lem:absolutelyContinuousOnInterval-antitoneOn-of-deriv-nonpos"
  (title := "Nonpositive derivative almost everywhere")
  (latexEnv := "lemma")
  (statement := /-- If $v$ is real and absolutely continuous on $[a, b]$ and $v'(t) \le 0$ for
    almost every $t \in (a, b)$, then $v$ is nonincreasing on $[a, b]$. -/)
  (proof := /-- Apply \cref{lem:absolutelyContinuousOnInterval-sub-le-integral-of-deriv-le} with
    $g = 0$ on each subinterval. -/)]
theorem antitoneOn_of_deriv_nonpos {v : ℝ → ℝ} (hv : AbsolutelyContinuousOnInterval v a b)
    (h : ∀ᵐ t, t ∈ Ioo a b → deriv v t ≤ 0) : AntitoneOn v (Icc a b) := by
  intro s hs t ht hst
  simpa using (hv.mono (uIcc_subset_uIcc (Icc_subset_uIcc hs) (Icc_subset_uIcc ht)))
    |>.sub_le_integral_of_deriv_le hst intervalIntegrable_const
      (h.mono fun τ hτ hmem => hτ (Ioo_subset_Ioo hs.1 ht.2 hmem))

/-- An absolutely continuous real function whose derivative is almost everywhere nonnegative is
nondecreasing. -/
@[blueprint "lem:absolutelyContinuousOnInterval-monotoneOn-of-deriv-nonneg"
  (title := "Nonnegative derivative almost everywhere")
  (latexEnv := "lemma")
  (statement := /-- If $v$ is real and absolutely continuous on $[a, b]$ and $v'(t) \ge 0$ for
    almost every $t \in (a, b)$, then $v$ is nondecreasing on $[a, b]$. -/)
  (proof := /-- Apply \cref{lem:absolutelyContinuousOnInterval-antitoneOn-of-deriv-nonpos} to
    $-v$. -/)]
theorem monotoneOn_of_deriv_nonneg {v : ℝ → ℝ} (hv : AbsolutelyContinuousOnInterval v a b)
    (h : ∀ᵐ t, t ∈ Ioo a b → 0 ≤ deriv v t) : MonotoneOn v (Icc a b) :=
  fun s hs t ht hst => neg_le_neg_iff.mp (hv.neg.antitoneOn_of_deriv_nonpos
    (h.mono fun t ht hmem => by simpa [deriv.neg] using ht hmem) hs ht hst)

/-- **Level form.**  If an absolutely continuous real function has an almost everywhere
nonpositive derivative wherever it exceeds the level `η`, it never exceeds `max (v a) η`. -/
@[blueprint "lem:absolutelyContinuousOnInterval-le-max-of-deriv-nonpos"
  (title := "Nonpositive derivative above a level")
  (latexEnv := "lemma")
  (statement := /-- Let $v$ be real and absolutely continuous on $[a, b]$.  If $v'(t) \le 0$ for
    almost every $t \in (a, b)$ with $v(t) > \eta$, then $v(t) \le \max(v(a), \eta)$ for all
    $t \in [a, b]$. -/)
  (proof := /-- With $m = \max(v(a), \eta)$, the function $w = \max(v, m)$ is absolutely
    continuous, and $w'(t) \le 0$ almost everywhere: where $v(t) > m$, $w = v$ near $t$; where
    $v(t) \le m$, $w$ attains its minimum $m$ at $t$.  So $w$ is nonincreasing
    (\cref{lem:absolutelyContinuousOnInterval-antitoneOn-of-deriv-nonpos}) and
    $v(t) \le w(t) \le w(a) = m$. -/)]
theorem le_max_of_deriv_nonpos {v : ℝ → ℝ} {η : ℝ} (hv : AbsolutelyContinuousOnInterval v a b)
    (h : ∀ᵐ t, t ∈ Ioo a b → η < v t → deriv v t ≤ 0) :
    ∀ t ∈ Icc a b, v t ≤ max (v a) η := by
  set m := max (v a) η
  have hw : AbsolutelyContinuousOnInterval (fun t => max (v t) m) a b :=
    (LipschitzWith.id.max_const m).comp_absolutelyContinuousOnInterval hv
  intro t ht
  refine (le_max_left _ _).trans ((hw.antitoneOn_of_deriv_nonpos ?_ ⟨le_rfl, ht.1.trans ht.2⟩
    ht ht.1).trans (max_eq_right (le_max_left _ _)).le)
  filter_upwards [h] with s hs hmem
  rcases lt_or_ge m (v s) with hlt | hle
  · have hvs : ∀ᶠ r in 𝓝 s, m < v r := continuousAt_const.eventually_lt
      (hv.continuousOn.continuousAt (mem_of_superset (Icc_mem_nhds hmem.1 hmem.2)
        Icc_subset_uIcc)) hlt
    rw [Filter.EventuallyEq.deriv_eq (hvs.mono fun r hr => max_eq_left hr.le)]
    exact hs hmem ((le_max_right _ _).trans_lt hlt)
  · exact (IsLocalMin.deriv_eq_zero (f := fun r => max (v r) m) (Eventually.of_forall fun r =>
      (max_eq_right hle).trans_le (le_max_right (v r) m))).le

/-- **Grönwall's inequality**, almost-everywhere differential form: if
`deriv v t ≤ β t * v t` almost everywhere, then `v t ≤ v a * exp (∫ τ in a..t, β τ)`. -/
@[blueprint "lem:absolutelyContinuousOnInterval-le-mul-exp-integral-of-deriv-le"
  (title := "Grönwall's inequality for absolutely continuous functions")
  (latexEnv := "lemma")
  (statement := /-- Let $v$ be real and absolutely continuous on $[a, b]$ and $\beta$ integrable
    on $[a, b]$.  If $v'(t) \le \beta(t)\, v(t)$ for almost every $t \in (a, b)$, then
    \[
      v(t) \le v(a) \exp\Bigl(\int_a^t \beta(\tau)\,\mathrm{d}\tau\Bigr)
      \qquad (t \in [a, b]).
    \] -/)
  (proof := /-- With $B(t) = \int_a^t \beta$, the function $w = v\, e^{-B}$ is absolutely
    continuous and $w' = e^{-B}(v' - \beta v) \le 0$ almost everywhere, so
    $w(t) \le w(a) = v(a)$ by
    \cref{lem:absolutelyContinuousOnInterval-antitoneOn-of-deriv-nonpos}. -/)]
theorem le_mul_exp_integral_of_deriv_le {v β : ℝ → ℝ} (hv : AbsolutelyContinuousOnInterval v a b)
    (hβ : IntervalIntegrable β volume a b) (h : ∀ᵐ t, t ∈ Ioo a b → deriv v t ≤ β t * v t) :
    ∀ t ∈ Icc a b, v t ≤ v a * Real.exp (∫ τ in a..t, β τ) := by
  have hB : AbsolutelyContinuousOnInterval (fun t => ∫ τ in a..t, β τ) a b :=
    hβ.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hw : AbsolutelyContinuousOnInterval
      (fun t => v t * Real.exp (-∫ τ in a..t, β τ)) a b :=
    hv.fun_mul (Real.contDiff_exp.locallyLipschitz.locallyLipschitzOn
      |>.comp_absolutelyContinuousOnInterval (mapsTo_univ _ _) hB.neg)
  intro t ht
  have key := hw.antitoneOn_of_deriv_nonpos ?_ ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  · rw [intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one, Real.exp_neg,
      ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)] at key
    exact key
  filter_upwards [h, ae_hasDerivAt_of_sub_eq_integral hβ (x := fun t => ∫ τ in a..t, β τ)
    (fun t _ => by simp), hv.ae_differentiableAt] with s hs hBs hvs hmem
  have hmem' : s ∈ uIcc a b := Icc_subset_uIcc (Ioo_subset_Icc_self hmem)
  have hd : HasDerivAt (fun t => v t * Real.exp (-∫ τ in a..t, β τ)) _ s :=
    (hvs hmem').hasDerivAt.mul (hBs hmem).neg.exp
  rw [hd.deriv, Pi.neg_apply]
  nlinarith [mul_le_mul_of_nonneg_left (hs hmem) (Real.exp_pos (-∫ τ in a..s, β τ)).le]

/-- Exponential decay: if `deriv v t ≤ -c * v t` almost everywhere, then
`v t ≤ v a * exp (-c * (t - a))`.  The constant-rate case of Grönwall's inequality. -/
@[blueprint "lem:absolutelyContinuousOnInterval-le-mul-exp-of-deriv-le"
  (title := "Exponential bound from a linear differential inequality")
  (latexEnv := "lemma")
  (statement := /-- Let $v$ be real and absolutely continuous on $[a, b]$ and $c \in \mathbb{R}$.
    If $v'(t) \le -c\, v(t)$ for almost every $t \in (a, b)$, then
    $v(t) \le v(a)\, e^{-c (t - a)}$ for all $t \in [a, b]$. -/)
  (proof := /-- \cref{lem:absolutelyContinuousOnInterval-le-mul-exp-integral-of-deriv-le} with
    $\beta = -c$. -/)]
theorem le_mul_exp_of_deriv_le {v : ℝ → ℝ} {c : ℝ} (hv : AbsolutelyContinuousOnInterval v a b)
    (h : ∀ᵐ t, t ∈ Ioo a b → deriv v t ≤ -c * v t) :
    ∀ t ∈ Icc a b, v t ≤ v a * Real.exp (-c * (t - a)) := by
  intro t ht
  have key := hv.le_mul_exp_integral_of_deriv_le intervalIntegrable_const h t ht
  rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm (t - a)] at key

/-- **Grönwall's inequality with forcing**: if `deriv v t ≤ K * v t + ε` almost everywhere, then
`v t ≤ gronwallBound (v a) K ε (t - a)`, the solution of `y' = K y + ε`, `y(0) = v a`, at time
`t - a`.  The almost-everywhere counterpart of Mathlib's
`le_gronwallBound_of_liminf_deriv_right_le`. -/
@[blueprint "lem:absolutelyContinuousOnInterval-le-gronwallBound-of-deriv-le"
  (title := "Grönwall's inequality with constant forcing")
  (latexEnv := "lemma")
  (statement := /-- Let $v$ be real and absolutely continuous on $[a, b]$ and $K, \varepsilon \in
    \mathbb{R}$.  If $v'(t) \le K v(t) + \varepsilon$ for almost every $t \in (a, b)$, then
    $v(t) \le y(t - a)$ for all $t \in [a, b]$, where $y$ solves $y' = K y + \varepsilon$,
    $y(0) = v(a)$. -/)
  (proof := /-- $w(t) = v(t) - y(t - a)$ satisfies $w' \le K w$ almost everywhere and $w(a) = 0$,
    so $w \le 0$ by \cref{lem:absolutelyContinuousOnInterval-le-mul-exp-of-deriv-le}. -/)]
theorem le_gronwallBound_of_deriv_le {v : ℝ → ℝ} {K ε : ℝ}
    (hv : AbsolutelyContinuousOnInterval v a b)
    (h : ∀ᵐ t, t ∈ Ioo a b → deriv v t ≤ K * v t + ε) :
    ∀ t ∈ Icc a b, v t ≤ gronwallBound (v a) K ε (t - a) := by
  have hy : AbsolutelyContinuousOnInterval (fun t => gronwallBound (v a) K ε (t - a)) a b := by
    refine ContDiffOn.absolutelyContinuousOnInterval (ContDiff.contDiffOn ?_)
    unfold gronwallBound
    split_ifs <;> fun_prop
  intro t ht
  have key := (hv.sub hy).le_mul_exp_of_deriv_le (c := -K) ?_ t ht
  · simpa [gronwallBound_x0] using key
  filter_upwards [h, hv.ae_differentiableAt] with s hs hvs hmem
  rw [((hvs (Icc_subset_uIcc (Ioo_subset_Icc_self hmem))).hasDerivAt.sub
    (hasDerivAt_gronwallBound_shift (v a) K ε s a)).deriv, Pi.sub_apply]
  linarith [hs hmem]

end AbsolutelyContinuousOnInterval

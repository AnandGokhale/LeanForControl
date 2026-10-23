import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.Transform
import Mathlib.Order.Interval.Set.UnorderedInterval
import LeanForControl.Analysis.Integrals
import Architect

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Real Interval Pointwise Topology

/-!
# Integral curves and the integral form of an ODE

The integral (Volterra) formulation `x t = x₀ + ∫_{t₀}^{t} F s (x s) ds` of an ODE, and its
dictionary with Mathlib's differential formulation `IsIntegralCurveOn`.

Nothing here is specific to control theory: these are the two directions of the fundamental
theorem of calculus for ODE solutions, plus the reparametrizations (re-anchoring, time
reflection, time translation) that both formulations are closed under. The control content —
existence, continuous dependence, stability — lives in `ODEs/` and `Stability/`.

## Main declarations

* `IsIntegralSolution` — integral formulation of an ODE solution on a time interval.
* `isIntegralSolution_iff_isIntegralCurveOn` — the two formulations agree, given integrability.
* `IsIntegralSolution.reanchor`, `IsIntegralSolution.reflect` — re-anchoring the initial
  condition anywhere on the segment, and reversing time.
* `IsIntegralCurveOn.comp_add_autonomous`, `IsIntegralCurveOn.shift_to_zero` — time translation
  of an autonomous integral curve.

Integrability of `s ↦ F s (x s)` from joint continuity is `Continuous.intervalIntegrable_comp`,
in `Analysis/Integrals.lean`.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An *integral solution* of `ẋ = F(t, x)` on the segment between `t₀` and `t₁` (in either
    order) with initial value `x₀`: for every `t` on that segment,
    `x(t) = x₀ + ∫_{t₀}^{t} F(s, x(s)) ds`. -/
@[blueprint "def:isIntegralSolution"
  (title := "Integral solution")
  (statement := /-- A function $x$, defined on the segment between $t_0$ and $t_1$, is an
    \emph{integral solution} of $\dot{x} = F(t,x)$ with initial value $x_0$ when
    \[
      x(t) \;=\; x_0 + \int_{t_0}^{t} F(s,\, x(s))\,\mathrm{d}s
    \]
    for every $t$ between $t_0$ and $t_1$. -/)]
def IsIntegralSolution (t₀ t₁ : ℝ) (x : ℝ → E) (x₀ : E) (F : ℝ → E → E) : Prop :=
  ∀ t ∈ Set.uIcc t₀ t₁, x t = x₀ + ∫ s in t₀..t, F s (x s)

variable {t₀ t₁ : ℝ}
variable {f g : ℝ → E → E}
variable {y z : ℝ → E}
variable {y₀ z₀ : E}
variable {L μ : ℝ}

/-- Re-anchoring an integral solution: if `x` solves `ẋ = F(t, x)` on the segment between `t₀`
    and `t₁` with initial value `x₀`, then for *any* two points `s`, `r` of that segment it also
    solves it on the segment between them, anchored at `x s`.

Both endpoints are free, so the re-anchored domain need not shrink: taking `s` and `r` to be the
two original endpoints re-anchors at one end while keeping the whole segment, which is what the
state-transition matrix's invertibility argument needs. -/
@[blueprint "lem:isIntegralSolution-reanchor"
  (title := "Re-anchoring an integral solution")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be a continuous integral solution of $\dot x = F(t,x)$ with initial
    value $x_0$ on the segment between $t_0$ and $t_1$, with $F$ jointly continuous.  Then for
    any $s, r$ on that segment, $x$ is an integral solution on the segment between $s$ and $r$,
    with initial value $x(s)$:
    \[
      x(t) \;=\; x(s) + \int_{s}^{t} F(w, x(w))\,\mathrm{d}w
      \qquad \text{for } t \text{ between } s \text{ and } r .
    \]
    Leaving both endpoints free means the domain need not shrink — taking $s = t_1$ and
    $r = t_0$ re-anchors at one end of the original segment while retaining all of it. -/)
  (proof := /-- Subtract the defining equations at $t$ and at $s$ and split the integral at $s$,
    which is legitimate because $w \mapsto F(w, x(w))$ is interval-integrable on each piece. -/)]
lemma IsIntegralSolution.reanchor {t₀ t₁ : ℝ} {x : ℝ → E} {x₀ : E} {F : ℝ → E → E}
    (hx : IsIntegralSolution t₀ t₁ x x₀ F) (hF_cont : Continuous (fun p : ℝ × E => F p.1 p.2))
    (hx_cont : ContinuousOn x (uIcc t₀ t₁)) {s r : ℝ}
    (hs : s ∈ uIcc t₀ t₁) (hr : r ∈ uIcc t₀ t₁) :
    IsIntegralSolution s r x (x s) F := by
  intro t ht
  have ht' : t ∈ uIcc t₀ t₁ := uIcc_subset_uIcc hs hr ht
  have hint1 : IntervalIntegrable (fun w => F w (x w)) volume t₀ s :=
    hF_cont.intervalIntegrable_comp (hx_cont.mono (uIcc_subset_uIcc left_mem_uIcc hs))
  have hint2 : IntervalIntegrable (fun w => F w (x w)) volume s t :=
    hF_cont.intervalIntegrable_comp (hx_cont.mono (uIcc_subset_uIcc hs ht'))
  rw [hx t ht', hx s hs, add_assoc, intervalIntegral.integral_add_adjacent_intervals hint1 hint2]

/-- **Time reflection.** Running an integral solution backwards through the midpoint of its own
interval, `σ ↦ x (t₀ + t₁ - σ)`, gives an integral solution of the negated, reflected field
`(r, y) ↦ -F (t₀ + t₁ - r) y` on the reversed interval, with the same initial value.

The reflection is an involution on the segment, so this swaps the two endpoints and nothing else:
it converts a statement anchored at `t₀` and running to `t₁` into one anchored at `t₁` and running
to `t₀`. That is what lets a forward-time argument be reused verbatim in backward time. -/
@[blueprint "lem:isIntegralSolution-reflect"
  (title := "Time reflection of an integral solution")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be an integral solution of $\dot x = F(t,x)$ with initial value
    $x_0$ on the segment between $t_0$ and $t_1$.  Then
    $\sigma \mapsto x(t_0 + t_1 - \sigma)$ is an integral solution, with the same initial value
    $x_0$, of the reflected field
    \[
      (r, y) \;\longmapsto\; -F(t_0 + t_1 - r,\; y)
    \]
    on the segment between $t_1$ and $t_0$.

    The map $\sigma \mapsto t_0 + t_1 - \sigma$ is an involution exchanging the two endpoints, so
    reflection turns a statement anchored at $t_0$ into one anchored at $t_1$ and nothing more.
    Its purpose is to let an argument that is inherently forward-marching — a Gr\"onwall
    bootstrap, say — be applied unchanged in backward time. -/)
  (proof := /-- Substituting $r \mapsto t_0 + t_1 - r$ in the defining integral reverses the
    orientation of the interval, contributing one sign, and the negation of the field
    contributes another; the two cancel. -/)]
lemma IsIntegralSolution.reflect {t₀ t₁ : ℝ} {x : ℝ → E} {x₀ : E} {F : ℝ → E → E}
    (hx : IsIntegralSolution t₀ t₁ x x₀ F) :
    IsIntegralSolution t₁ t₀ (fun σ => x (t₀ + t₁ - σ)) x₀
      (fun r y => -F (t₀ + t₁ - r) y) := by
  -- Reflecting the integration variable flips the orientation of the interval.
  have hkey : ∀ (k : ℝ → E) (σ : ℝ),
      (∫ r in t₁..σ, k (t₀ + t₁ - r)) = -∫ w in t₀..(t₀ + t₁ - σ), k w := by
    intro k σ
    rw [intervalIntegral.integral_comp_sub_left k (t₀ + t₁),
      show t₀ + t₁ - t₁ = t₀ from by ring, intervalIntegral.integral_symm]
  intro σ hσ
  -- Reflection exchanges the two endpoints, so it preserves membership in the segment.
  have hmem : t₀ + t₁ - σ ∈ uIcc t₀ t₁ := by
    rcases Set.mem_uIcc.mp hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩)
    · exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
  dsimp only
  rw [hx _ hmem, intervalIntegral.integral_neg, hkey (fun w => F w (x w)) σ, neg_neg]

/-! ## Relation to Mathlib's integral curves

`IsIntegralSolution` is the *integral* (Volterra) formulation of `ẋ = F(t, x)`; Mathlib's
`IsIntegralCurveOn` is the *differential* one. Mathlib's public ODE API — Picard-Lindelöf
existence (`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`), Grönwall uniqueness
(`ODE_solution_unique_of_mem_Icc`) — is stated exclusively in the differential form, which is
therefore the canonical one; the integral form appears in Mathlib only as `ODE.picard`, an
internal proof device. The lemmas below are the two directions of the fundamental theorem of
calculus relating them, so that results proved against either formulation transfer to the other.

Note that `IsIntegralSolution` unfolds to exactly the statement that `x` is a fixed point of
Mathlib's Picard operator, and that the differential form is the weaker hypothesis to discharge
but the stronger one to assume: it carries no integrability side conditions, which is why the
Lyapunov track differentiates along it directly.
-/

section IntegralCurve

variable {x : ℝ → E} {x₀ : E} {F : ℝ → E → E}

variable [CompleteSpace E]

/-- **Differential form implies integral form.** An integral curve of `F` on the segment between
`t₀` and `t₁` is an integral solution there, anchored at its own initial value `x t₀`.

Continuity of `x` is not assumed: it follows from the differentiability hypothesis. -/
@[blueprint "lem:isIntegralCurveOn-isIntegralSolution"
  (title := "Integral curves are integral solutions")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be an integral curve of $F$ on the segment between $t_0$ and $t_1$,
    with $s \mapsto F(s, x(s))$ continuous there.  Then $x$ is an integral solution on that
    segment, anchored at its own value $x(t_0)$:
    \[
      x(t) \;=\; x(t_0) + \int_{t_0}^{t} F(s, x(s))\,\mathrm{d}s .
    \]
    Continuity of $x$ itself is not assumed — it follows from differentiability. -/)
  (proof := /-- The fundamental theorem of calculus.  The derivative hypothesis holds on an open
    neighbourhood of each interior point, so it yields the right-derivative form the theorem
    needs, and continuity of $F$ along $x$ gives the integrability side condition. -/)]
theorem IsIntegralCurveOn.isIntegralSolution
    (hcurve : IsIntegralCurveOn x F (uIcc t₀ t₁))
    (hFx : ContinuousOn (fun s => F s (x s)) (uIcc t₀ t₁)) :
    IsIntegralSolution t₀ t₁ x (x t₀) F := by
  intro t ht
  have hsub : uIcc t₀ t ⊆ uIcc t₀ t₁ := uIcc_subset_uIcc_left ht
  have hcont : ContinuousOn x (uIcc t₀ t) := fun s hs =>
    ((hcurve s (hsub hs)).continuousWithinAt).mono hsub
  have hderiv : ∀ s ∈ Ioo (min t₀ t) (max t₀ t), HasDerivWithinAt x (F s (x s)) (Ioi s) s := by
    intro s hs
    have hs' : s ∈ uIcc t₀ t := Ioo_subset_Icc_self hs
    have hmem : uIcc t₀ t₁ ∈ 𝓝 s :=
      mem_nhds_iff.2 ⟨Ioo (min t₀ t) (max t₀ t),
        fun r hr => hsub (Ioo_subset_Icc_self hr), isOpen_Ioo, hs⟩
    exact ((hcurve s (hsub hs')).hasDerivAt hmem).hasDerivWithinAt
  have hint : IntervalIntegrable (fun s => F s (x s)) volume t₀ t :=
    (hFx.mono hsub).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont hderiv hint
  rw [hFTC]
  abel

/-- **Integral form implies differential form.** An integral solution on the segment between `t₀`
and `t₁` is an integral curve there, provided `s ↦ F s (x s)` is continuous along it. -/
@[blueprint "lem:isIntegralSolution-isIntegralCurveOn"
  (title := "Integral solutions are integral curves")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be an integral solution of $\dot x = F(t,x)$ on the segment between
    $t_0$ and $t_1$, with $s \mapsto F(s, x(s))$ continuous there.  Then $x$ is an integral
    curve of $F$ on that segment: it is differentiable, with $\dot x(t) = F(t, x(t))$. -/)
  (proof := /-- Differentiating the primitive: the integral term has derivative $F(t, x(t))$ by
    the fundamental theorem of calculus, and the constant $x_0$ contributes nothing.  Transport
    that along the defining equation, which says $x$ agrees with the primitive. -/)]
theorem IsIntegralSolution.isIntegralCurveOn
    (hsol : IsIntegralSolution t₀ t₁ x x₀ F)
    (hFx : ContinuousOn (fun s => F s (x s)) (uIcc t₀ t₁)) :
    IsIntegralCurveOn x F (uIcc t₀ t₁) := by
  intro t ht
  haveI : Fact (t ∈ uIcc t₀ t₁) := ⟨ht⟩
  have hint : IntervalIntegrable (fun s => F s (x s)) volume t₀ t :=
    (hFx.mono (uIcc_subset_uIcc_left ht)).intervalIntegrable
  have hderiv : HasDerivWithinAt (fun u => ∫ s in t₀..u, F s (x s)) (F t (x t)) (uIcc t₀ t₁) t :=
    intervalIntegral.integral_hasDerivWithinAt_right hint
      (hFx.stronglyMeasurableAtFilter_nhdsWithin measurableSet_uIcc t) (hFx t ht)
  exact (hderiv.const_add x₀).congr (fun u hu => hsol u hu) (hsol t ht)

/-- The two formulations agree, given continuity of `F` along `x`. -/
@[blueprint "lem:isIntegralSolution-iff-isIntegralCurveOn"
  (title := "Integral and differential forms agree")
  (latexEnv := "lemma")
  (statement := /-- Given continuity of $s \mapsto F(s, x(s))$ on the segment between $t_0$ and
    $t_1$, the two formulations agree: $x$ is an integral solution anchored at $x(t_0)$ if and
    only if it is an integral curve of $F$ there.  Continuity of $F$ along $x$ is exactly the
    price of the equivalence — without it the integral form is the weaker notion. -/)
  (proof := /-- The two implications are
    \cref{lem:isIntegralSolution-isIntegralCurveOn} and
    \cref{lem:isIntegralCurveOn-isIntegralSolution}. -/)]
theorem isIntegralSolution_iff_isIntegralCurveOn
    (hFx : ContinuousOn (fun s => F s (x s)) (uIcc t₀ t₁)) :
    IsIntegralSolution t₀ t₁ x (x t₀) F ↔ IsIntegralCurveOn x F (uIcc t₀ t₁) :=
  ⟨fun h => h.isIntegralCurveOn hFx, fun h => h.isIntegralSolution hFx⟩

/-- The forward-time form of `isIntegralSolution_iff_isIntegralCurveOn`, stated over `Icc t₀ t₁`
rather than `uIcc t₀ t₁`. This is the form the finite-forward stability predicates are phrased
in (with `t₀ = 0`). -/
@[blueprint "lem:isIntegralSolution-iff-isIntegralCurveOn-Icc"
  (title := "Integral and differential forms agree, forward time")
  (latexEnv := "lemma")
  (statement := /-- \cref{lem:isIntegralSolution-iff-isIntegralCurveOn} in forward time: for
    $t_0 \le t_1$, the equivalence holds over $[t_0, t_1]$.  This is the interval the
    finite-forward stability predicates are phrased over, so this is the form the stability
    track would use to reach the results of this chapter. -/)]
theorem isIntegralSolution_iff_isIntegralCurveOn_Icc (hle : t₀ ≤ t₁)
    (hFx : ContinuousOn (fun s => F s (x s)) (Icc t₀ t₁)) :
    IsIntegralSolution t₀ t₁ x (x t₀) F ↔ IsIntegralCurveOn x F (Icc t₀ t₁) := by
  rw [← uIcc_of_le hle] at hFx ⊢
  exact isIntegralSolution_iff_isIntegralCurveOn hFx

omit [CompleteSpace E] in
/-- **Time invariance.** An autonomous vector field has no preferred time origin: translating
an integral curve translates its interval of definition and nothing else.

This is Mathlib's `IsIntegralCurveOn.comp_add` with the time-dependence removed — for
`fun _ y => g y` the translated field `v ∘ (· + dt)` is the field itself. -/
@[blueprint "lem:isIntegralCurveOn-comp-add-autonomous"
  (title := "Time invariance")
  (latexEnv := "lemma")
  (statement := /-- If $x$ is an integral curve of an autonomous
    field $g$ on a set $s$, then $t \mapsto x(t + \Delta t)$ is an integral curve of the same
    $g$ on $s - \Delta t$, for every $\Delta t$.

    An autonomous field has no preferred time origin, so translating a solution translates its
    interval of definition and changes nothing else.  For a time-varying field the translated
    solution would solve the \emph{translated} equation instead. -/)]
lemma IsIntegralCurveOn.comp_add_autonomous {g : E → E} {s : Set ℝ}
    (hx : IsIntegralCurveOn x (fun _ y => g y) s) (dt : ℝ) :
    IsIntegralCurveOn (fun t => x (t + dt)) (fun _ y => g y) (-dt +ᵥ s) :=
  hx.comp_add dt

omit [CompleteSpace E] in
/-- Time invariance in the form the finite-segment predicates need: a segment on `[t₀, t₁]`
re-anchored to `[0, t₁ - t₀]`. -/
@[blueprint "lem:isIntegralCurveOn-shift-to-zero"
  (title := "Shifting a solution segment to the origin")
  (latexEnv := "lemma")
  (statement := /-- \cref{lem:isIntegralCurveOn-comp-add-autonomous} in the form the
    finite-segment predicates need: a solution segment of an autonomous field on $[t_0, t_1]$
    becomes one on $[0, t_1 - t_0]$ under $s \mapsto x(s + t_0)$.

    This is why the autonomous stability predicates may fix the initial time at $0$ without
    loss: any segment can be shifted there. -/)]
lemma IsIntegralCurveOn.shift_to_zero {g : E → E} {t₀ t₁ : ℝ}
    (hx : IsIntegralCurveOn x (fun _ y => g y) (Icc t₀ t₁)) :
    IsIntegralCurveOn (fun s => x (s + t₀)) (fun _ y => g y) (Icc 0 (t₁ - t₀)) := by
  have h := hx.comp_add_autonomous t₀
  have hset : -t₀ +ᵥ Icc t₀ t₁ = Icc 0 (t₁ - t₀) := by
    simp [Set.vadd_Icc, neg_add_eq_sub]
  rwa [hset] at h

/-- An integral curve of an autonomous field on `[t₀, t₁]` is an integral solution there.

The continuity of `x` that the integral formulation needs comes for free from the curve
hypothesis; only continuity of the field is assumed. Specializes
`isIntegralSolution_iff_isIntegralCurveOn_Icc`. -/
@[blueprint "lem:isIntegralCurveOn-isIntegralSolution-of-continuous"
  (title := "Integral form for an autonomous field")
  (latexEnv := "lemma")
  (statement := /-- Let $g$ be a continuous \emph{autonomous} field and let $x$ be an integral
    curve of $g$ on $[t_0,t_1]$, $t_0 \le t_1$.  Then $x$ is an integral solution there,
    anchored at $x(t_0)$.

    This is the autonomous, forward-time specialization of
    \cref{lem:isIntegralSolution-iff-isIntegralCurveOn-Icc}, and so the shape a trajectory of an
    autonomous system has: continuity of the field is the only hypothesis, the continuity of $x$
    along which $F$ must be continuous being supplied by the curve itself. -/)]
lemma IsIntegralCurveOn.isIntegralSolution_of_continuous {g : E → E} {t₀ t₁ : ℝ}
    (hle : t₀ ≤ t₁) (hx : IsIntegralCurveOn x (fun _ y => g y) (Icc t₀ t₁))
    (hg : Continuous g) :
    IsIntegralSolution t₀ t₁ x (x t₀) (fun _ y => g y) :=
  (isIntegralSolution_iff_isIntegralCurveOn_Icc hle
    (hg.comp_continuousOn (fun s hs => (hx s hs).continuousWithinAt))).mpr hx

end IntegralCurve

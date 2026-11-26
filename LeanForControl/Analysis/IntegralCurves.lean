import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Transform
import Mathlib.Order.Interval.Set.UnorderedInterval
import LeanForControl.Analysis.Integrals
import LeanForControl.Analysis.OrderTopology
import Architect

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Real Interval Pointwise Topology

/-!
# Integral curves and the integral form of an ODE

The integral (Volterra) formulation `x t = x₀ + ∫_{t₀}^{t} F s (x s) ds` of an ODE, and its
dictionary with Mathlib's differential formulation `IsIntegralCurveOn`.

Nothing here is specific to control theory: these are the two directions of the fundamental
theorem of calculus for ODE solutions, plus the reparametrizations (re-anchoring, time
reflection) of the integral formulation; time translation of an integral curve is Mathlib's
`IsIntegralCurveOn.comp_add`. The control content — existence, continuous dependence,
stability — lives in `ODEs/` and `Stability/`.

## Main declarations

* `IsIntegralSolution` — integral formulation of an ODE solution on a time interval.
* `isIntegralSolution_iff_isIntegralCurveOn` — the two formulations agree, given integrability.
* `IsIntegralSolution.reanchor`, `IsIntegralSolution.reflect` — re-anchoring the initial
  condition anywhere on the segment, and reversing time.
* `isIntegralSolution_const`, `isIntegralCurveOn_const` — an equilibrium is a constant solution,
  in either formulation.

Integrability of `s ↦ F s (x s)` from joint continuity is `Continuous.intervalIntegrable_comp`,
in `Analysis/Integrals.lean`.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An *integral solution* of `ẋ = F(t, x)` on the segment between `t₀` and `t₁` (in either
    order) with initial value `x₀`: for every `t` on that segment, `s ↦ F(s, x(s))` is integrable
    between `t₀` and `t` and `x(t) = x₀ + ∫_{t₀}^{t} F(s, x(s)) ds`.

    Integrability is part of the definition, and `E` is complete: otherwise the Bochner integral is
    `0`, and the definition would silently make a constant `x` a solution. -/
@[blueprint "def:isIntegralSolution"
  (title := "Integral solution")
  (statement := /-- A function $x$, defined on the segment between $t_0$ and $t_1$, is an
    \emph{integral solution} of $\dot{x} = F(t,x)$ with initial value $x_0$ when
    \[
      x(t) \;=\; x_0 + \int_{t_0}^{t} F(s,\, x(s))\,\mathrm{d}s
    \]
    for every $t$ between $t_0$ and $t_1$, the integrand being integrable. -/),
  -- `CompleteSpace E` is unused in the body on purpose: see the docstring
  nolint unusedArguments]
def IsIntegralSolution [CompleteSpace E] (t₀ t₁ : ℝ) (x : ℝ → E) (x₀ : E) (F : ℝ → E → E) :
    Prop :=
  ∀ t ∈ Set.uIcc t₀ t₁,
    IntervalIntegrable (fun s => F s (x s)) volume t₀ t ∧ x t = x₀ + ∫ s in t₀..t, F s (x s)

variable {t₀ t₁ : ℝ}
variable {f g : ℝ → E → E}
variable {y z : ℝ → E}
variable {y₀ z₀ : E}
variable {L μ : ℝ}

section Reparametrization

variable [CompleteSpace E]

/-- Re-anchoring an integral solution: if `x` solves `ẋ = F(t, x)` on the segment between `t₀`
    and `t₁` with initial value `x₀`, then for *any* two points `s`, `r` of that segment it also
    solves it on the segment between them, anchored at `x s`.

Both endpoints are free, so the re-anchored domain need not shrink: taking `s` and `r` to be the
two original endpoints re-anchors at one end while keeping the whole segment, which is what the
state-transition matrix's invertibility argument needs. -/
@[blueprint "lem:isIntegralSolution-reanchor"
  (title := "Re-anchoring an integral solution")
  (latexEnv := "lemma")
  (statement := /-- Let $x$ be an integral solution of $\dot x = F(t,x)$ with initial
    value $x_0$ on the segment between $t_0$ and $t_1$.  Then for
    any $s, r$ on that segment, $x$ is an integral solution on the segment between $s$ and $r$,
    with initial value $x(s)$:
    \[
      x(t) \;=\; x(s) + \int_{s}^{t} F(w, x(w))\,\mathrm{d}w
      \qquad \text{for } t \text{ between } s \text{ and } r .
    \]
    Leaving both endpoints free means the domain need not shrink — taking $s = t_1$ and
    $r = t_0$ re-anchors at one end of the original segment while retaining all of it. -/)
  (proof := /-- Subtract the defining equations at $t$ and at $s$ and split the integral at $s$,
    which is legitimate because $w \mapsto F(w, x(w))$ is integrable on each piece, by the
    definition of an integral solution. -/)]
lemma IsIntegralSolution.reanchor {t₀ t₁ : ℝ} {x : ℝ → E} {x₀ : E} {F : ℝ → E → E}
    (hx : IsIntegralSolution t₀ t₁ x x₀ F) {s r : ℝ} (hs : s ∈ uIcc t₀ t₁) (hr : r ∈ uIcc t₀ t₁) :
    IsIntegralSolution s r x (x s) F := by
  intro t ht
  have ht' : t ∈ uIcc t₀ t₁ := uIcc_subset_uIcc hs hr ht
  have hint : IntervalIntegrable (fun w => F w (x w)) volume s t :=
    (hx s hs).1.symm.trans (hx t ht').1
  refine ⟨hint, ?_⟩
  rw [(hx t ht').2, (hx s hs).2, add_assoc,
    intervalIntegral.integral_add_adjacent_intervals (hx s hs).1 hint]

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
  refine ⟨?_, ?_⟩
  · have h := ((hx _ hmem).1.comp_sub_left (t₀ + t₁)).neg
    simpa only [show t₀ + t₁ - t₀ = t₁ by ring, show t₀ + t₁ - (t₀ + t₁ - σ) = σ by ring,
      Pi.neg_def] using h
  · dsimp only
    rw [(hx _ hmem).2, intervalIntegral.integral_neg, hkey (fun w => F w (x w)) σ, neg_neg]

/-- An integral solution is continuous on its segment: it is its initial value plus a primitive of
an integrable function. -/
@[blueprint "lem:isIntegralSolution-continuousOn"
  (title := "Integral solutions are continuous")
  (latexEnv := "lemma")
  (statement := /-- An integral solution (\cref{def:isIntegralSolution}) on the segment between
    $t_0$ and $t_1$ is continuous on that segment. -/)
  (proof := /-- It is $x_0$ plus the primitive $t \mapsto \int_{t_0}^{t} F(s, x(s))\,\mathrm{d}s$
    of a function integrable on the segment, and such a primitive is continuous. -/)]
lemma IsIntegralSolution.continuousOn {t₀ t₁ : ℝ} {x : ℝ → E} {x₀ : E} {F : ℝ → E → E}
    (hx : IsIntegralSolution t₀ t₁ x x₀ F) : ContinuousOn x (uIcc t₀ t₁) :=
  (continuousOn_const.add (intervalIntegral.continuousOn_primitive_interval'
    (hx t₁ right_mem_uIcc).1 left_mem_uIcc)).congr fun t ht => (hx t ht).2

/-- **An equilibrium is a constant integral solution**: if `F(t, p) = 0` on the segment, then
`t ↦ p` is an integral solution from `p` there. -/
@[blueprint "lem:isIntegralSolution-const"
  (title := "Constant integral solutions at equilibria")
  (latexEnv := "lemma")
  (statement := /-- If $F(t, p) = 0$ for every $t$ between $t_0$ and $t_1$, the constant curve
    $t \mapsto p$ is an integral solution (\cref{def:isIntegralSolution}) of $\dot x = F(t, x)$
    there, with initial value $p$. -/)]
lemma isIntegralSolution_const {t₀ t₁ : ℝ} {F : ℝ → E → E} {p : E}
    (h : ∀ t ∈ uIcc t₀ t₁, F t p = 0) : IsIntegralSolution t₀ t₁ (fun _ => p) p F := by
  intro t ht
  have h_zero : EqOn (fun s => F s p) 0 (uIcc t₀ t) := fun s hs => h s (uIcc_subset_uIcc_left ht hs)
  exact ⟨(intervalIntegrable_const (c := (0 : E))).congr fun s hs =>
    (h_zero (uIoc_subset_uIcc hs)).symm, by rw [intervalIntegral.integral_congr h_zero]; simp⟩

end Reparametrization

/-! ## Relation to Mathlib's integral curves

`IsIntegralSolution` is the *integral* (Volterra) formulation of `ẋ = F(t, x)`; Mathlib's
`IsIntegralCurveOn` is the *differential*, classical one, in which Mathlib states Picard-Lindelöf
existence (`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`) and Grönwall uniqueness
(`ODE_solution_unique_of_mem_Icc`). The lemmas below are the two directions of the fundamental
theorem of calculus relating them: the two formulations agree when `F` is continuous along the
curve, so results proved against either one transfer to the other.

The integral form asks no derivative of `x` at any given time, only integrability of
`s ↦ F s (x s)`: it is the Carathéodory notion of solution, and the one by which the trajectories
of a system (`ContinuousSystem.IsTrajectoryOn`) are defined.
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
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont hderiv hint]
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
  have : Fact (t ∈ uIcc t₀ t₁) := ⟨ht⟩
  have hint : IntervalIntegrable (fun s => F s (x s)) volume t₀ t :=
    (hFx.mono (uIcc_subset_uIcc_left ht)).intervalIntegrable
  have hderiv : HasDerivWithinAt (fun u => ∫ s in t₀..u, F s (x s)) (F t (x t)) (uIcc t₀ t₁) t :=
    intervalIntegral.integral_hasDerivWithinAt_right hint
      (hFx.stronglyMeasurableAtFilter_nhdsWithin measurableSet_uIcc t) (hFx t ht)
  exact (hderiv.const_add x₀).congr (fun u hu => (hsol u hu).2) (hsol t ht).2

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
rather than `uIcc t₀ t₁`. -/
@[blueprint "lem:isIntegralSolution-iff-isIntegralCurveOn-Icc"
  (title := "Integral and differential forms agree, forward time")
  (latexEnv := "lemma")
  (statement := /-- \cref{lem:isIntegralSolution-iff-isIntegralCurveOn} in forward time: for
    $t_0 \le t_1$ and $s \mapsto F(s, x(s))$ continuous on $[t_0, t_1]$, $x$ is an integral
    solution on $[t_0, t_1]$ anchored at $x(t_0)$ if and only if it is an integral curve of $F$
    on $[t_0, t_1]$. -/)]
theorem isIntegralSolution_iff_isIntegralCurveOn_Icc (hle : t₀ ≤ t₁)
    (hFx : ContinuousOn (fun s => F s (x s)) (Icc t₀ t₁)) :
    IsIntegralSolution t₀ t₁ x (x t₀) F ↔ IsIntegralCurveOn x F (Icc t₀ t₁) := by
  rw [← uIcc_of_le hle] at hFx ⊢
  exact isIntegralSolution_iff_isIntegralCurveOn hFx

end IntegralCurve

/-- **An equilibrium is a constant integral curve**: if `v(t, p) = 0` for `t ∈ s`, then
`t ↦ p` is an integral curve of `v` on `s`. -/
@[blueprint "lem:isIntegralCurveOn-const"
  (title := "Constant integral curves at equilibria")
  (latexEnv := "lemma")
  (statement := /-- If $v(t, p) = 0$ for every $t \in s$, then the constant curve $t \mapsto p$
    is an integral curve of $\dot x = v(t, x)$ on $s$. -/)]
lemma isIntegralCurveOn_const {v : ℝ → E → E} {p : E} {s : Set ℝ} (h : ∀ t ∈ s, v t p = 0) :
    IsIntegralCurveOn (fun _ => p) v s := fun t ht =>
  (hasDerivWithinAt_const t s p).congr_deriv (h t ht).symm

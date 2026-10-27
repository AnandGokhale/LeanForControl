import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Instances.EReal.Lemmas

import Architect

/-!
# Upper right Dini derivative

## Main definitions

* `diniDerivRight f t` (notation `D⁺ f t`) : the upper right Dini derivative
  `limsup_{h→0⁺} (f(t+h) - f(t)) / h`, valued in the extended reals `EReal = [-∞, +∞]`.

## Main results

* `diniDerivRight_le_iff` : `D⁺ f t ≤ L` iff the forward quotients are eventually below `L + ε`
  for every `ε > 0`.
* `diniDerivRight_of_hasDerivWithinAt` : `D⁺ f t` is the right derivative where one exists.
* `diniDerivRight_mono` : `D⁺` is monotone among functions that agree at the point.
* `le_mul_exp_of_diniDerivRight_le` : Grönwall's inequality in Dini form, `D⁺ v ≤ K v`.
* `diniDerivRight_le_of_add_integral_le` : a dissipation inequality `f(z) + ∫_r^z g ≤ f(r)` gives
  `D⁺ f(r) ≤ -g(r)`.

## Why `EReal`

The upper right Dini derivative is classically extended-real valued: the forward quotients may be
unbounded (`√t` at `0` has `D⁺ = +∞`).  Valued in `EReal`, a complete lattice, `limsup` always
exists and needs no boundedness side conditions.  Bounds are stated against real numbers,
`D⁺ f t ≤ (L : EReal)`, and `diniDerivRight_le_iff` turns them into statements about the real
difference quotients, where the arithmetic is done.
-/

open Filter Set Topology

noncomputable section

/-- The upper right Dini derivative of `f` at `t`, in the extended reals:
$$D^+ f(t) \;=\; \limsup_{h \to 0^+} \frac{f(t+h) - f(t)}{h} \in [-\infty, +\infty].$$ -/
@[blueprint "def:diniDerivRight"
  (title := "Upper right Dini derivative")
  (statement := /-- The \emph{upper right Dini derivative} of $f : \mathbb{R} \to \mathbb{R}$
    at $t$ is
    \[
      D^{+} f(t) \;=\; \limsup_{h \to 0^{+}} \frac{f(t+h)-f(t)}{h} \in [-\infty, +\infty].
    \]
    When $f$ is differentiable at $t$ this equals $f'(t)$. -/)]
def diniDerivRight (f : ℝ → ℝ) (t : ℝ) : EReal :=
  limsup (fun h => (((f (t + h) - f t) / h : ℝ) : EReal)) (𝓝[>] 0)

/-- Notation `D⁺ f` for the upper right Dini derivative of `f`. -/
notation "D⁺" => diniDerivRight

/-! ### Relationship to the classical derivative -/

/-- A right derivative at `x` is the limit of the forward difference quotients
`h⁻¹ • (f (x + h) - f x)` as `h → 0⁺`.  The one-sided version of Mathlib's
`HasDerivAt.tendsto_slope_zero_right`. -/
@[blueprint "lem:hasDerivWithinAt-tendsto-slope-zero-right"
  (title := "Forward difference quotients of a right-differentiable function")
  (latexEnv := "lemma")
  (statement := /-- If $f : \mathbb{R} \to E$ has right derivative $f'$ at $x$, then
    $h^{-1} (f(x+h) - f(x)) \to f'$ as $h \to 0^{+}$. -/)]
theorem HasDerivWithinAt.tendsto_slope_zero_right {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {f' : E} {x : ℝ} (hf : HasDerivWithinAt f f' (Ici x) x) :
    Tendsto (fun h => h⁻¹ • (f (x + h) - f x)) (𝓝[>] 0) (𝓝 f') := by
  have h_shift : Tendsto (fun h => x + h) (𝓝[>] 0) (𝓝[Ici x \ {x}] x) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_const.add continuous_id).tendsto' 0 x (add_zero x)
      ).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun h (hh : 0 < h) => ⟨by simp [hh.le], by simp [hh.ne']⟩⟩
  simpa [Function.comp_def, slope_def_module] using
    (hasDerivWithinAt_iff_tendsto_slope.1 hf).comp h_shift

/-- A left derivative at `x` is the limit of the difference quotients
`h⁻¹ • (f (x + h) - f x)` as `h → 0⁻`.  The one-sided version of Mathlib's
`HasDerivAt.tendsto_slope_zero_left`. -/
@[blueprint "lem:hasDerivWithinAt-tendsto-slope-zero-left"
  (title := "Backward difference quotients of a left-differentiable function")
  (latexEnv := "lemma")
  (statement := /-- If $f : \mathbb{R} \to E$ has left derivative $f'$ at $x$, then
    $h^{-1} (f(x+h) - f(x)) \to f'$ as $h \to 0^{-}$. -/)]
theorem HasDerivWithinAt.tendsto_slope_zero_left {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {f' : E} {x : ℝ} (hf : HasDerivWithinAt f f' (Iic x) x) :
    Tendsto (fun h => h⁻¹ • (f (x + h) - f x)) (𝓝[<] 0) (𝓝 f') := by
  have h_shift : Tendsto (fun h => x + h) (𝓝[<] 0) (𝓝[Iic x \ {x}] x) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_const.add continuous_id).tendsto' 0 x (add_zero x)
      ).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun h (hh : h < 0) => ⟨by simp [hh.le], by simp [hh.ne]⟩⟩
  simpa [Function.comp_def, slope_def_module] using
    (hasDerivWithinAt_iff_tendsto_slope.1 hf).comp h_shift

/-- If `f` has a right derivative `L` at `t`, then `D⁺ f t = L`. -/
@[blueprint "lem:diniDerivRight-of-hasDerivWithinAt"
  (title := "Dini derivative of a differentiable function")
  (latexEnv := "lemma")
  (statement := /-- If $f$ has right derivative $L$ at $t$, then $D^{+}f(t) = L$: the Dini
    derivative agrees with the classical one wherever the latter exists. -/)]
theorem diniDerivRight_of_hasDerivWithinAt {f : ℝ → ℝ} {t L : ℝ}
    (hf : HasDerivWithinAt f L (Ici t) t) : D⁺ f t = L :=
  ((continuous_coe_real_ereal.tendsto L).comp
    (by simpa [div_eq_inv_mul] using hf.tendsto_slope_zero_right)).limsup_eq

/-! ### Upper bounds -/

/-- `D⁺ f t ≤ L` if and only if, for every `ε > 0`, the forward difference quotient
`(f (t + h) - f t) / h` is eventually at most `L + ε` as `h → 0⁺`. -/
@[blueprint "lem:diniDerivRight-le-iff"
  (title := "Upper bound on the Dini derivative")
  (latexEnv := "lemma")
  (statement := /-- $D^{+}f(t) \le L$ if and only if for every $\varepsilon > 0$ the quotient
    $\frac{f(t+h)-f(t)}{h}$ is eventually at most $L + \varepsilon$ as $h \to 0^{+}$. -/)]
theorem diniDerivRight_le_iff {f : ℝ → ℝ} {t L : ℝ} :
    D⁺ f t ≤ L ↔ ∀ ε > 0, ∀ᶠ h in 𝓝[>] 0, (f (t + h) - f t) / h ≤ L + ε := by
  rw [diniDerivRight, limsup_le_iff]
  constructor
  · intro h ε hε
    filter_upwards [h (L + ε : ℝ) (EReal.coe_lt_coe_iff.2 (by linarith))] with x hx
    exact (EReal.coe_lt_coe_iff.1 hx).le
  · intro h y hy
    induction y using EReal.rec with
    | bot => exact absurd hy (not_lt_bot)
    | coe r =>
      filter_upwards [h ((r - L) / 2) (by linarith [EReal.coe_lt_coe_iff.1 hy])] with x hx
      exact EReal.coe_lt_coe_iff.2 (by linarith [EReal.coe_lt_coe_iff.1 hy])
    | top => exact Eventually.of_forall fun _ => EReal.coe_lt_top _

/-- **The norm grows no faster than the velocity.**  If `x` has right derivative `v` at `t` and
`f` changes no faster than `‖x‖` does, `f s - f t ≤ ‖x s - x t‖`, then `D⁺ f t ≤ ‖v‖`.  Both
`f = ‖x‖` and `f = -‖x‖` qualify. -/
@[blueprint "lem:diniDerivRight-le-norm-of-hasDerivWithinAt"
  (title := "Dini derivative of a norm")
  (latexEnv := "lemma")
  (statement := /-- If $x$ has right derivative $v$ at $t$ and $f(s) - f(t) \le \|x(s) - x(t)\|$
    for all $s$, then $D^{+}f(t) \le \|v\|$; in particular for $f = \pm\|x\|$. -/)
  (proof := /-- For $h > 0$ the forward quotient of $f$ is at most
    $\|h^{-1}(x(t + h) - x(t))\|$, which tends to $\|v\|$. -/)]
theorem diniDerivRight_le_norm_of_hasDerivWithinAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → ℝ} {x : ℝ → E} {v : E} {t : ℝ}
    (hx : HasDerivWithinAt x v (Ici t) t) (hf : ∀ s, f s - f t ≤ ‖x s - x t‖) :
    D⁺ f t ≤ (‖v‖ : ℝ) := by
  rw [diniDerivRight_le_iff]
  intro ε hε
  filter_upwards [hx.tendsto_slope_zero_right.norm.eventually
      (gt_mem_nhds (lt_add_of_pos_right ‖v‖ hε)), self_mem_nhdsWithin] with h hh (hpos : 0 < h)
  calc (f (t + h) - f t) / h
      ≤ ‖x (t + h) - x t‖ / h := div_le_div_of_nonneg_right (hf _) hpos.le
    _ = ‖h⁻¹ • (x (t + h) - x t)‖ := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, inv_mul_eq_div]
    _ ≤ ‖v‖ + ε := hh.le

/-- **Monotonicity.**  If `f` and `g` agree at `a` and `f ≤ g` just to the right of `a`, then
`D⁺ f a ≤ D⁺ g a`. -/
@[blueprint "lem:diniDerivRight-mono"
  (title := "Monotonicity of the Dini derivative")
  (latexEnv := "lemma")
  (statement := /-- If $f(a) = g(a)$ and $f \le g$ on a right neighbourhood of $a$, then
    $D^{+}f(a) \le D^{+}g(a)$. -/)
  (proof := /-- The forward quotients of $f$ at $a$ are eventually below those of $g$, and
    $\limsup$ is monotone. -/)]
theorem diniDerivRight_mono {f g : ℝ → ℝ} {a : ℝ} (h_eq : f a = g a)
    (h_le : ∀ᶠ x in 𝓝[>] a, f x ≤ g x) : D⁺ f a ≤ D⁺ g a := by
  refine limsup_le_limsup ?_
  have h_shift : Tendsto (a + ·) (𝓝[>] 0) (𝓝[>] a) := by
    unfold Tendsto; rw [Filter.map_add_left_nhdsGT, add_zero]
  filter_upwards [h_shift.eventually h_le, self_mem_nhdsWithin] with h hh (h_pos : 0 < h)
  rw [h_eq]
  exact EReal.coe_le_coe_iff.2 (div_le_div_of_nonneg_right (by linarith) h_pos.le)

/-! ### Grönwall's inequality in Dini form -/

/-- **Grönwall's inequality, Dini form.**  If `v` is continuous on `[a, b]` and `D⁺ v ≤ K v` on
`[a, b)`, then `v(t) ≤ v(a) e^{K (t - a)}`.  A wrapper of Mathlib's
`le_gronwallBound_of_liminf_deriv_right_le`. -/
@[blueprint "thm:le-mul-exp-of-diniDerivRight-le"
  (title := "Grönwall's inequality, Dini form")
  (statement := /-- Let $v$ be continuous on $[a, b]$ with $D^{+} v(t) \le K\, v(t)$ for
    $t \in [a, b)$.  Then $v(t) \le v(a)\, e^{K (t - a)}$ on $[a, b]$. -/)]
theorem le_mul_exp_of_diniDerivRight_le {v : ℝ → ℝ} {K a b : ℝ} (hv : ContinuousOn v (Icc a b))
    (hD : ∀ t ∈ Ico a b, D⁺ v t ≤ (K * v t : ℝ)) :
    ∀ t ∈ Icc a b, v t ≤ v a * Real.exp (K * (t - a)) := by
  simpa [gronwallBound_ε0] using le_gronwallBound_of_liminf_deriv_right_le (f' := fun t => K * v t)
    (ε := 0) hv (fun t ht r hr => by
      -- Pull the quotient bound in `h` back to `z = t + h`.
      have h_shift : Tendsto (fun z => z - t) (𝓝[>] t) (𝓝[>] 0) := by
        unfold Tendsto
        simp only [sub_eq_add_neg]
        rw [Filter.map_add_right_nhdsGT, add_neg_cancel]
      refine (h_shift.eventually (diniDerivRight_le_iff.1 (hD t ht) ((r - K * v t) / 2)
        (by linarith))).frequently.mono fun z hz => ?_
      rw [add_sub_cancel] at hz
      rw [← div_eq_inv_mul]
      linarith)
    le_rfl (fun _ _ => by simp)

/-- **Dini derivative from a dissipation inequality.**  If `f(z) + ∫_r^z g ≤ f(r)` for `z` just
to the right of `r` and `g` is continuous on `[r, ∞)`, then `D⁺ f(r) ≤ -g(r)`. -/
@[blueprint "lem:diniDerivRight-le-of-add-integral-le"
  (title := "Dini derivative from a dissipation inequality")
  (latexEnv := "lemma")
  (statement := /-- If $g$ is continuous on $[r, \infty)$ and
    $f(z) + \int_r^z g \le f(r)$ for $z$ in a right neighbourhood of $r$, then
    $D^{+} f(r) \le -g(r)$. -/)
  (proof := /-- $\frac{f(r+h) - f(r)}{h} \le -\frac1h \int_r^{r+h} g \to -g(r)$. -/)]
theorem diniDerivRight_le_of_add_integral_le {f g : ℝ → ℝ} {r : ℝ} (hg : ContinuousOn g (Ici r))
    (hf : ∀ᶠ z in 𝓝[>] r, f z + ∫ u in r..z, g u ≤ f r) : D⁺ f r ≤ (-g r : ℝ) := by
  refine diniDerivRight_le_iff.2 fun ε hε => ?_
  -- The average of `g` over `[r, r + h]` tends to `g(r)`.
  have h_avg := (intervalIntegral.integral_hasDerivWithinAt_right (s := Ici r) (t := Ioi r)
    IntervalIntegrable.refl ((hg.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin
      measurableSet_Ioi r) ((hg r self_mem_Ici).mono Ioi_subset_Ici_self)).tendsto_slope_zero_right
  have h_shift : Tendsto (r + ·) (𝓝[>] 0) (𝓝[>] r) := by
    unfold Tendsto; rw [Filter.map_add_left_nhdsGT, add_zero]
  filter_upwards [h_avg.eventually (eventually_gt_nhds (by linarith : g r - ε < g r)),
    h_shift.eventually hf, self_mem_nhdsWithin] with h hh_avg hh_f (hh : 0 < h)
  simp only [intervalIntegral.integral_same, sub_zero, smul_eq_mul] at hh_avg
  rw [inv_mul_eq_div] at hh_avg
  calc (f (r + h) - f r) / h ≤ -(∫ u in r..r + h, g u) / h := by gcongr; linarith
    _ = -((∫ u in r..r + h, g u) / h) := neg_div _ _
    _ ≤ -g r + ε := by linarith

end

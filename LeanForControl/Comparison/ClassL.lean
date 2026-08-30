import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue

import LeanForControl.axioms
import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKInfty
import Architect

open Set Filter Topology MeasureTheory intervalIntegral


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
structure ClassL where
  /-- The forward function of a class L function. -/
  toFun : ℝ → ℝ
  continuous   : ContinuousOn toFun (Set.Ici 0)
  pos          : ∀ s ≥ 0, 0 < toFun s
  anti         : AntitoneOn toFun (Set.Ici 0)
  tendsto_zero : Filter.Tendsto toFun Filter.atTop (nhds 0)

/-! ### Class L Singular

A *singular class L* function is like class L but defined only on `(0, ∞)`:
it is continuous, positive, antitone, tends to `0` at `+∞`, and blows up near `0`.
This arises naturally as the inverse of the sliding-window function `W_fn` in
the KL characterization of asymptotic stability. -/

/-- A *singular class L* function is continuous, positive, and antitone on `(0, ∞)`,
tends to `0` at `+∞`, and is allowed to blow up near `0`. Arises as the inverse of
the sliding-window function in the KL characterization of asymptotic stability. -/
structure ClassLSingular where
  /-- The forward function, defined on `(0, ∞)`. -/
  toFun : ℝ → ℝ
  continuous   : ContinuousOn toFun (Set.Ioi 0)
  pos          : ∀ s > 0, 0 < toFun s
  anti         : AntitoneOn toFun (Set.Ioi 0)
  tendsto_zero : Filter.Tendsto toFun Filter.atTop (nhds 0)
  tendsto_top  : Filter.Tendsto toFun (𝓝[>] 0) Filter.atTop

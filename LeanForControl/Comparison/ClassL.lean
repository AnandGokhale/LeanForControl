import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue

import LeanForControl.axioms
import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKInfty
import Architect

open Set Filter Topology MeasureTheory intervalIntegral


-- ─── Class L ──────────────────────────────────────────────────────────────────

/-! ### Class L

A *class L* function `σ(s)` is continuous, positive and strictly decreasing on `[0, ∞)`, and
tends to zero as `s → ∞`. It is the pure time-decay factor of an asymptotic stability
estimate: multiplying one by a class K function gives a class KL bound
(`ClassKL.mk_mul`). -/

/-- A class L function `σ : [0,∞) → ℝ`: continuous, strictly positive, strictly decreasing,
    and tending to `0` at `+∞`. -/
@[blueprint "def:isClassL"
  (statement := /-- A \emph{class $\mathcal{L}$} function on $[0,\infty)$ is continuous,
    strictly positive, and strictly decreasing, and satisfies $\sigma(s) \to 0$ as
    $s \to \infty$. It carries the time decay of an asymptotic stability estimate: the
    product of a class $\mathcal{K}$ function of the initial deviation with a class
    $\mathcal{L}$ function of elapsed time is a class $\mathcal{KL}$ bound. -/)]
structure ClassL where
  /-- The forward function of a class L function. -/
  toFun : ℝ → ℝ
  continuous   : ContinuousOn toFun (Set.Ici 0)
  pos          : ∀ s ≥ 0, 0 < toFun s
  anti         : StrictAntiOn toFun (Set.Ici 0)
  tendsto_zero : Filter.Tendsto toFun Filter.atTop (nhds 0)

/-! ### Class L Singular

A *singular class L* function is like class L but defined only on `(0, ∞)`:
it is continuous, positive, antitone, tends to `0` at `+∞`, and blows up near `0`.
This arises naturally as the inverse of the sliding-window function `W_fn` in
the KL characterization of asymptotic stability. -/

/-- A *singular class L* function is continuous, positive, and antitone on `(0, ∞)`,
tends to `0` at `+∞`, and is allowed to blow up near `0`. Arises as the inverse of
the sliding-window function in the KL characterization of asymptotic stability. -/
@[blueprint "def:isClassLSingular"
  (statement := /-- A \emph{singular class $\mathcal{L}$} function on $(0,\infty)$ is
    continuous, strictly positive and antitone, with $U(s) \to 0$ as $s \to \infty$ and
    $U(s) \to \infty$ as $s \to 0^{+}$.  It differs from class $\mathcal{L}$ in two ways: the
    domain excludes $0$, where the function is instead required to blow up, and the decrease is
    only required to be weak.  It arises as the inverse of the sliding-window function in the
    class $\mathcal{KL}$ characterization of asymptotic stability. -/)]
structure ClassLSingular where
  /-- The forward function, defined on `(0, ∞)`. -/
  toFun : ℝ → ℝ
  continuous   : ContinuousOn toFun (Set.Ioi 0)
  pos          : ∀ s > 0, 0 < toFun s
  anti         : AntitoneOn toFun (Set.Ioi 0)
  tendsto_zero : Filter.Tendsto toFun Filter.atTop (nhds 0)
  tendsto_top  : Filter.Tendsto toFun (𝓝[>] 0) Filter.atTop

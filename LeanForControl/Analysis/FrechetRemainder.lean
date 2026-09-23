import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.MetricSpace.Basic
import Architect

/-!
# Fréchet-derivative remainder bounds

This file packages the first-order remainder characterization of a Fréchet derivative
in a form convenient for nonlinear linearization arguments.

Reference: the standard Fréchet-derivative remainder characterization.
-/

open Filter Asymptotics
open scoped Topology

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A Fréchet derivative gives an arbitrarily small linear bound on the centered
first-order remainder near the base point.

Reference: the standard Fréchet-derivative remainder characterization. -/
@[blueprint "thm:frechet-centered-remainder-bound"
  (statement := /-- If $A$ is the Fréchet derivative of $f$ at $x_0$, then for
    every $\varepsilon>0$ the centered remainder satisfies
    \[
      \|f(x)-f(x_0)-A(x-x_0)\| \leq \varepsilon\|x-x_0\|
    \]
    throughout a sufficiently small neighborhood of $x_0$. -/)]
theorem HasFDerivAt.exists_centered_remainder_bound
    {f : E → F} {A : E →L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f A x₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x, ‖x - x₀‖ < δ →
      ‖f x - f x₀ - A (x - x₀)‖ ≤ ε * ‖x - x₀‖ := by
  have hsmall := hf.isLittleO.bound hε
  rw [Metric.eventually_nhds_iff] at hsmall
  rcases hsmall with ⟨δ, hδ, hbound⟩
  refine ⟨δ, hδ, fun x hx ↦ hbound ?_⟩
  simpa [dist_eq_norm] using hx

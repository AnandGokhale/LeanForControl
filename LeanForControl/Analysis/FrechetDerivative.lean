import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.MetricSpace.Basic
import Architect

/-!
# The Fréchet derivative

Facts about `HasFDerivAt` stated in the `ε`–`δ` form that nonlinear arguments consume, rather
than the little-o form Mathlib states them in. The linearization error
`f x - f x₀ - A (x - x₀)` is the object of interest: Lyapunov's indirect method works because
it is `o (‖x - x₀‖)`, and what the proofs need is an explicit radius on which it is small.
-/

open Filter Asymptotics
open scoped Topology

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Differentiability, in `ε`–`δ` form: the linearization error is bounded by `ε ‖x - x₀‖` on
an explicit ball around `x₀`. -/
@[blueprint "thm:frechet-linearization-error-bound"
  (title := "Quantitative linearization error bound")
  (statement := /-- Let $A$ be the Fréchet derivative of $f$ at $x_0$. For every
    $\varepsilon > 0$ there exists $\delta > 0$ such that
    \[
      \|x - x_0\| < \delta \;\Longrightarrow\;
        \|f(x) - f(x_0) - A(x - x_0)\| \le \varepsilon\,\|x - x_0\|.
    \]
    This is the $\varepsilon$--$\delta$ form of $f(x) - f(x_0) - A(x-x_0) = o(\|x-x_0\|)$. -/)]
theorem HasFDerivAt.exists_linearization_error_bound
    {f : E → F} {A : E →L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f A x₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x, ‖x - x₀‖ < δ →
      ‖f x - f x₀ - A (x - x₀)‖ ≤ ε * ‖x - x₀‖ := by
  have hsmall := hf.isLittleO.bound hε
  rw [Metric.eventually_nhds_iff] at hsmall
  rcases hsmall with ⟨δ, hδ, hbound⟩
  refine ⟨δ, hδ, fun x hx ↦ hbound ?_⟩
  simpa [dist_eq_norm] using hx

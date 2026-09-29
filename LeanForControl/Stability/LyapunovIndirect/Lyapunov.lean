import LeanForControl.MatrixAlgebra.QuadraticForm
import LeanForControl.Analysis.FrechetDerivative
import Mathlib.Analysis.InnerProductSpace.Calculus
import Architect

/-!
# The shared remainder-absorption step of Lyapunov's indirect method

This file has one declaration: the bound on how much the nonlinear remainder of `f` can
perturb the derivative of a quadratic Lyapunov function, used by both branches of the
indirect method (see its docstring).

Reference: Khalil, *Nonlinear Systems*.
-/

namespace LinearSystems

open Matrix MatrixAlgebra
open scoped RealInnerProductSpace

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Near an equilibrium, the derivative of a centered matrix quadratic form applied to the
first-order remainder of `f` is dominated by any prescribed positive multiple of the
squared distance to the equilibrium.

This is the shared "remainder absorption" step of both branches of Lyapunov's indirect
method: the stable branch (`exists_centeredQuadraticForm_decay`) uses it to bound the
error term against the certificate's own decay rate, and the unstable branch
(`unstable_of_quadratic_certificate`) uses it to bound the error term against the
shifted certificate's growth rate.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.7 (the quadratic-Lyapunov proof of
Lyapunov's indirect method). -/
@[blueprint "lem:exists-abs-fderiv-centeredQuadraticForm-remainder-le"
  (title := "Absorbing the linearization remainder")
  (latexEnv := "lemma")
  (statement := /-- Let $f$ be $C^{1}$ with $Df(x_{\mathrm{eq}}) = A$, let $M$ be a matrix, and
    let $c > 0$.  Then there is $r > 0$ such that for every $x$ with
    $\|x - x_{\mathrm{eq}}\| < r$,
    \[
      \bigl|\,D\,q_{M}(x)\,[\,f(x) - f(x_{\mathrm{eq}}) - A(x - x_{\mathrm{eq}})\,]\,\bigr|
        \le c\,\|x - x_{\mathrm{eq}}\|^{2},
    \]
    where $q_{M}$ is the centred quadratic form $q_{M}(x) = \langle M(x - x_{\mathrm{eq}}),\,
    x - x_{\mathrm{eq}}\rangle$.

    The bracket is the first-order remainder of $f$ at $x_{\mathrm{eq}}$.  The point is that
    $c$ is \emph{arbitrary}: near enough to the equilibrium the remainder perturbs
    $\dot{q}_{M}$ by less than any prescribed multiple of
    $\|x - x_{\mathrm{eq}}\|^{2}$, which is the order of $\dot{q}_{M}$ itself.  This is why
    the linearization decides stability.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.7 (the quadratic-Lyapunov proof
    of Lyapunov's indirect method).
  -/)
  (proof := /-- Write $y = x - x_{\mathrm{eq}}$ and $e$ for the remainder.  Differentiability of
    $f$ at $x_{\mathrm{eq}}$ gives, for any $\eta > 0$, a radius within which
    $\|e\| \le \eta\|y\|$.  The derivative of a centred quadratic form is bounded by
    $|Dq_{M}(x)[e]| \le 2\|M\|\,\|y\|\,\|e\|$, so the product is at most
    $2\|M\|\eta\,\|y\|^{2}$.  Choosing $\eta = c / (4(\|M\| + 1))$ makes
    $2\|M\|\eta \le c$. -/)]
theorem exists_abs_fderiv_centeredQuadraticForm_remainder_le
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (A M : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    {c : ℝ} (hc : 0 < c) :
    ∃ r > 0, ∀ x : ℝⁿ, ‖x - x_eq‖ < r →
      |fderiv ℝ (centeredQuadraticForm M x_eq) x
          (f x - f x_eq - Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (x - x_eq))| ≤
        c * ‖x - x_eq‖ ^ 2 := by
  let p : ℝⁿ →L[ℝ] ℝⁿ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M
  let η : ℝ := c / (4 * (‖p‖ + 1))
  have hp_nonneg : 0 ≤ ‖p‖ := norm_nonneg p
  have hp_one_pos : 0 < ‖p‖ + 1 := by positivity
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hderiv : HasFDerivAt f
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) x_eq := by
    simpa only [hJac] using (hf.differentiable (by norm_num) x_eq).hasFDerivAt
  obtain ⟨r, hr, hrem⟩ := hderiv.exists_linearization_error_bound hη_pos
  refine ⟨r, hr, ?_⟩
  intro x hx
  let y : ℝⁿ := x - x_eq
  let e : ℝⁿ := f x - f x_eq - Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A y
  have he_norm : ‖e‖ ≤ η * ‖y‖ := hrem x (by simpa [y] using hx)
  have herror_abs :
      |fderiv ℝ (centeredQuadraticForm M x_eq) x e| ≤ 2 * ‖p‖ * ‖y‖ * ‖e‖ := by
    simpa [p, y] using abs_fderiv_centeredQuadraticForm_le M x_eq x e
  have hcoef : 2 * ‖p‖ * η ≤ c := by
    dsimp [η]
    rw [show 2 * ‖p‖ * (c / (4 * (‖p‖ + 1))) =
      (2 * ‖p‖ * c) / (4 * (‖p‖ + 1)) by ring]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc
    |fderiv ℝ (centeredQuadraticForm M x_eq) x e| ≤ 2 * ‖p‖ * ‖y‖ * ‖e‖ := herror_abs
    _ ≤ 2 * ‖p‖ * ‖y‖ * (η * ‖y‖) := by
      exact mul_le_mul_of_nonneg_left he_norm
        (mul_nonneg (mul_nonneg (by norm_num) hp_nonneg) (norm_nonneg y))
    _ = (2 * ‖p‖ * η) * ‖y‖ ^ 2 := by ring
    _ ≤ c * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖y‖)

end LinearSystems

import Mathlib.Analysis.Normed.Module.Basic
import Architect

/-!
# `Contraction.Norms.Defs` — regular pairings

A *regular pairing* on a normed space replaces the inner product in contraction analysis for norms
that come from no inner product (`ℓ¹`, `ℓ∞`, weighted and polyhedral norms).  Every contraction
result is stated for an arbitrary regular pairing; a norm then needs only its pairing.

* `RegularPairing E` — a real-valued `⟦x, y⟧` on `E`, compatible with the norm (`⟦x, x⟧ = ‖x‖²`),
  subadditive and nonnegatively homogeneous, bounded by `‖x‖ ‖y‖`, and with the straight-angle
  property `⟦-x, x⟧ = -‖x‖²`.  The last condition is what makes the pairing measure how the norm
  changes: it is equivalent to the curve norm derivative formula
  `½ d/dt ‖x(t)‖² = ⟦ẋ(t), x(t)⟧`, to Lumer's equality `μ(A) = sup_{‖x‖ = 1} ⟦A x, x⟧`, and to
  Deimling's inequality (Proskurnikov and Bullo, Theorem 3.5).

Without the straight-angle property the axioms are those of a *weak pairing*; weak pairings appear
only in the characterization of regularity, not elsewhere in the library.

Differences from the references: a regular pairing is one structure rather than a weak pairing
with an extra property; the norm of `E` is given and the pairing compatible with it, so positive
definiteness is not an axiom; the Cauchy–Schwarz inequality is one-sided, as in Proskurnikov and
Bullo, the two-sided form following from subadditivity; continuity in the first argument, part of
Bullo's (WP1), is not assumed (Proskurnikov and Bullo, Lemma 2.6, show that it follows).

References: Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), Definitions 2.16
and 2.17; A. V. Proskurnikov and F. Bullo, *Regular Pairings for Nonquadratic Lyapunov
Functions and Contraction Analysis*, SIAM J. Control Optim. 64(1):496–521 (2026),
doi:10.1137/24M1689685, Definitions 2.5 and 3.8 and Theorem 3.5.
-/

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A **regular pairing** on a normed space `E`, compatible with its norm: a real-valued
`⟦x, y⟧`, subadditive and nonnegatively homogeneous in its first argument, with `⟦x, x⟧ = ‖x‖²`,
`⟦x, y⟧ ≤ ‖x‖ ‖y‖`, and the straight-angle property `⟦-x, x⟧ = -‖x‖²`.

References: Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), Definitions 2.16
and 2.17; Proskurnikov and Bullo, SIAM J. Control Optim. (2026), Definitions 2.5 and 3.8. -/
@[blueprint "def:regularPairing"
  (title := "Regular pairing")
  (statement := /-- A \emph{regular pairing} on a real normed space $E$, compatible with its norm,
    is a map $\pair{\cdot}{\cdot} : E \times E \to \mathbb{R}$ such that, for all
    $x, x_1, x_2, y \in E$ and $\alpha \ge 0$,
    \begin{itemize}
      \item $\pair{x_1 + x_2}{y} \le \pair{x_1}{y} + \pair{x_2}{y}$ (subadditivity);
      \item $\pair{\alpha x}{y} = \pair{x}{\alpha y} = \alpha \pair{x}{y}$ and
        $\pair{-x}{-y} = \pair{x}{y}$ (weak homogeneity);
      \item $\pair{x}{x} = \|x\|^2$ (compatibility with the norm);
      \item $\pair{x}{y} \le \|x\| \, \|y\|$ (Cauchy--Schwarz);
      \item $\pair{-x}{x} = -\|x\|^2$ (straight angle).
    \end{itemize}
    The first four make $\pair{\cdot}{\cdot}$ a \emph{weak pairing}.  For a weak pairing, the
    straight-angle property is equivalent to the curve norm derivative formula
    $\tfrac12 \tfrac{d}{dt} \|x(t)\|^2 = \pair{\dot x(t)}{x(t)}$, to Lumer's equality
    $\mu(A) = \sup_{\|x\| = 1} \pair{A x}{x}$, and to Deimling's inequality.

    References: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0, 2022),
    Definitions 2.16 and 2.17; Proskurnikov and Bullo, SIAM J. Control Optim. (2026),
    Definitions 2.5 and 3.8 and Theorem 3.5.  Differences: one structure rather than a weak
    pairing with an extra property; the norm is given and the pairing compatible with it, so
    positive definiteness is not an axiom; Cauchy--Schwarz is one-sided; continuity in the first
    argument is not assumed. -/)]
structure RegularPairing where
  /-- The pairing `⟦x, y⟧`. -/
  toFun : E → E → ℝ
  /-- Subadditivity in the first argument. -/
  add_left_le : ∀ x₁ x₂ y, toFun (x₁ + x₂) y ≤ toFun x₁ y + toFun x₂ y
  /-- Homogeneity in the first argument, for nonnegative scalars. -/
  smul_left : ∀ a : ℝ, 0 ≤ a → ∀ x y, toFun (a • x) y = a * toFun x y
  /-- Homogeneity in the second argument, for nonnegative scalars. -/
  smul_right : ∀ a : ℝ, 0 ≤ a → ∀ x y, toFun x (a • y) = a * toFun x y
  /-- Negating both arguments changes nothing. -/
  neg_neg : ∀ x y, toFun (-x) (-y) = toFun x y
  /-- Compatibility with the norm. -/
  self : ∀ x, toFun x x = ‖x‖ ^ 2
  /-- The Cauchy–Schwarz inequality. -/
  le_norm_mul_norm : ∀ x y, toFun x y ≤ ‖x‖ * ‖y‖
  /-- The straight-angle property. -/
  neg_self : ∀ x, toFun (-x) x = -‖x‖ ^ 2

namespace RegularPairing

variable {E}

instance : CoeFun (RegularPairing E) (fun _ => E → E → ℝ) := ⟨RegularPairing.toFun⟩

end RegularPairing

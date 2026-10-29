import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Architect

/-!
# `Contraction.Norms.Defs` — definitions and notation

Every definition of `Contraction/Norms`, with its notation; the results about them are in the other
files.  After `open scoped LogNorm`:

| Notation | Definition | Meaning |
|---|---|---|
| `⟦x; y⟧_p`, `⟦x; y⟧` | `RegularPairing`, `ofNorm` | a regular pairing; the norm's pairing |
| `μ A` | `logNorm` | log norm of a bounded operator |
| `μ[R] A` | `WeightedNorm.logNorm` | log norm in `‖x‖_R = ‖R x‖` (`WeightedNorm R`) |
| `μ_{p} A` | `Matrix.logNormLp` | ℓᵖ log norm of a matrix |
| `μ_{p, R} A` | `Matrix.logNormLpWeight` | log norm of a matrix in `‖R x‖_p` |
| `μ_{2,P^½} A` | `Matrix.logNormL2PosDef` | log norm of a matrix in `√(xᵀ P x)` |
| `osL F on C` | `oneSidedLipschitz` | one-sided Lipschitz constant of a map on `C` |
| `osL[R] F`, `osL_{p} F`, … | `WeightedNorm.oneSidedLipschitz`, … | the same, in the norms above |

Each `osL` form takes an optional `on C`; without it, `C` is the whole space.

Also: `RegularPairing`, `WeightedNorm.opNorm` (`‖A‖_R`), `Matrix.toWeight` (a matrix weight),
`Matrix.WeightedEuclidean` (`ℝⁿ` with `√(xᵀ P x)`),
`Matrix.IsMetzler` and `Matrix.metzlerMajorant` (`|A|_M`).

## Regular pairings

A *regular pairing* on a normed space replaces the inner product in contraction analysis for norms
that come from no inner product (`ℓ¹`, `ℓ∞`, weighted and polyhedral norms).  Every contraction
result is stated for an arbitrary regular pairing; a norm then needs only its pairing.

* `RegularPairing E` — a real-valued `⟦x; y⟧` on `E`, compatible with the norm (`⟦x; x⟧ = ‖x‖²`),
  subadditive and nonnegatively homogeneous, bounded by `‖x‖ ‖y‖`, and with the straight-angle
  property `⟦-x; x⟧ = -‖x‖²`.  The last condition is what makes the pairing measure how the norm
  changes: it is equivalent to the curve norm derivative formula
  `½ d/dt ‖x(t)‖² = ⟦ẋ(t); x(t)⟧`, to Lumer's equality `μ(A) = sup_{‖x‖ = 1} ⟦A x; x⟧`, and to
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
`⟦x; y⟧`, subadditive and nonnegatively homogeneous in its first argument, with `⟦x; x⟧ = ‖x‖²`,
`⟦x; y⟧ ≤ ‖x‖ ‖y‖`, and the straight-angle property `⟦-x; x⟧ = -‖x‖²`.

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
  /-- The pairing `⟦x; y⟧`. -/
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

namespace LogNorm

/-- `⟦x; y⟧_p` for the regular pairing `p` at `x, y`; available after `open scoped LogNorm`.
Without the subscript, `⟦x; y⟧` is the pairing of the norm, `RegularPairing.ofNorm`. -/
scoped syntax:max "⟦" term "; " term "⟧_" term:max : term

scoped macro_rules
  | `(⟦$x; $y⟧_$p) => `(RegularPairing.toFun $p $x $y)

end LogNorm

/-! ### The logarithmic norm -/

section LogNorm

open Set

variable {E}

/-- **The logarithmic norm** of a bounded operator, `μ(A) = lim_{h → 0⁺} (‖I + h A‖ - 1) / h`: the
right derivative of the operator norm at the identity in the direction `A`. -/
@[blueprint "def:logNorm"
  (title := "Logarithmic norm")
  (statement := /-- The \emph{logarithmic norm} of a bounded linear operator $A$ on a real normed
    space is
    \[ \mu(A) = \lim_{h \to 0^+} \frac{\|I + h A\| - 1}{h}, \]
    the right derivative of the induced norm at $I$ in the direction $A$; the limit exists by
    \cref{lem:hasDerivWithinAt-norm-add-smul}.

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0), equation (2.22)
    and Remark 2.9. -/)]
noncomputable def logNorm (A : E →L[ℝ] E) : ℝ :=
  derivWithin (fun h : ℝ => ‖(1 : E →L[ℝ] E) + h • A‖) (Ioi 0) 0

/-- `μ A` for the log norm of `A`; available after `open scoped LogNorm`. -/
scoped[LogNorm] notation "μ" => logNorm

end LogNorm

open scoped LogNorm

/-! ### One-sided Lipschitz maps -/

section OneSidedLipschitz

open Set

variable {E}

/-- **The pairing of the norm**, `⟦x; y⟧ = ‖y‖ · d⁺/dh ‖y + h x‖ |_{h = 0}`, as a function.  It is
a regular pairing, `RegularPairing.ofNorm`, whose axioms are proved in `RegularPairing.lean`. -/
noncomputable def normPairing (x y : E) : ℝ :=
  ‖y‖ * derivWithin (fun h : ℝ => ‖y + h • x‖) (Ioi 0) 0

/-- **The one-sided Lipschitz constant** of `F` on `C`,
`osL(F) = sup_{x ≠ y ∈ C} ⟦F x - F y; x - y⟧ / ‖x - y‖²`, for the pairing of the norm
(`normPairing`, the regular pairing `RegularPairing.ofNorm`).  It extends the log norm from linear
to nonlinear maps; it can be negative, and it is `+∞` when the quotients are unbounded (`F x = x³`),
so it takes values in `EReal`.  As in the book, `C` has at least two points: the proof
`C.Nontrivial` is an argument, found automatically from the context (or from `Nontrivial E` for
`C = univ`). -/
@[blueprint "def:oneSidedLipschitz"
  (title := "One-sided Lipschitz constant")
  (statement := /-- On a real normed space $E$, the \emph{one-sided Lipschitz constant} of a map
    $F : E \to E$ on $C \subseteq E$ is
    \[ \operatorname{osL}(F) = \sup_{x \ne y \in C} \frac{\pair{F(x) - F(y)}{x - y}}{\|x - y\|^2}
      \in \mathbb{R} \cup \{+\infty\}, \]
    for a set $C$ with at least two points and the regular pairing of the norm
    (\cref{def:regularPairing-ofNorm}).  For a linear map it is the log norm
    (\cref{def:logNorm}).

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Chapter 3. -/)]
noncomputable def oneSidedLipschitz (C : Set E) (F : E → E)
    (_hC : C.Nontrivial := by
      first
        | assumption
        | exact Set.nontrivial_univ
        | fail "osL on C needs `hC : C.Nontrivial` (two points or more) in context") : EReal :=
  ⨆ (x ∈ C) (y ∈ C) (_ : x ≠ y), ((normPairing (F x - F y) (x - y) / ‖x - y‖ ^ 2 : ℝ) : EReal)

end OneSidedLipschitz

/-! ### Weighted norms -/

section Weighted

variable {E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The weighted norm** `‖x‖_R = ‖R x‖`, for an invertible linear weight `R : E → F`:
`WeightedNorm R` is `E` equipped with it. -/
@[blueprint "def:weightedNorm"
  (title := "Weighted norm")
  (statement := /-- Given an invertible bounded linear map $R : E \to F$, the \emph{weighted norm}
    on $E$ is $\|x\|_R = \|R x\|$.  It is a norm because $R$ is linear and injective.

    Reference: Bullo, \emph{Contraction Theory for Dynamical Systems} (ed.~1.0),
    Section 2.3. -/)]
def WeightedNorm (_R : E ≃L[ℝ] F) : Type _ := E

namespace WeightedNorm

variable (R : E ≃L[ℝ] F)

instance : AddCommGroup (WeightedNorm R) := inferInstanceAs (AddCommGroup E)

instance : Module ℝ (WeightedNorm R) := inferInstanceAs (Module ℝ E)

instance [Nontrivial E] : Nontrivial (WeightedNorm R) := inferInstanceAs (Nontrivial E)

/-- `R` on the weighted space, as a linear map: the norm is pulled back along it.  Its source is
`WeightedNorm R`, not `E`, which an ascription on `R.toLinearEquiv` would not achieve. -/
private def weightₗ : WeightedNorm R ≃ₗ[ℝ] F := R.toLinearEquiv

noncomputable instance : NormedAddCommGroup (WeightedNorm R) :=
  NormedAddCommGroup.induced _ _ (weightₗ R) (weightₗ R).injective

noncomputable instance : NormedSpace ℝ (WeightedNorm R) :=
  NormedSpace.induced ℝ _ _ (weightₗ R)

/-- `R`, from the weighted space onto `F`: it preserves the norm, `‖R x‖ = ‖x‖_R`. -/
noncomputable def weight : WeightedNorm R ≃L[ℝ] F :=
  (LinearIsometryEquiv.mk (weightₗ R) fun _ => rfl).toContinuousLinearEquiv

lemma norm_weight (x : WeightedNorm R) : ‖weight R x‖ = ‖x‖ := rfl

/-- The identity from `E` to the weighted space: the vector `x`, measured in the weighted norm. -/
noncomputable def equiv : E ≃L[ℝ] WeightedNorm R := R.trans (weight R).symm

/-- `‖x‖_R = ‖R x‖`. -/
lemma norm_equiv (x : E) : ‖equiv R x‖ = ‖R x‖ := by
  rw [← norm_weight, equiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]

/-- `‖A‖_R`: the operator norm of `A`, measured in the weighted norm. -/
noncomputable def opNorm (A : E →L[ℝ] E) : ℝ :=
  ‖(equiv R ∘L A ∘L (equiv R).symm : WeightedNorm R →L[ℝ] WeightedNorm R)‖

/-- `μ_R(A)`: the log norm of `A`, measured in the weighted norm. -/
noncomputable def logNorm (A : E →L[ℝ] E) : ℝ :=
  μ (equiv R ∘L A ∘L (equiv R).symm : WeightedNorm R →L[ℝ] WeightedNorm R)

/-- `μ[R] A` for the log norm of `A` in the weighted norm; available after
`open scoped LogNorm`. -/
scoped[LogNorm] notation:max "μ[" R "]" => WeightedNorm.logNorm R

/-- `osL[R](F)`: the one-sided Lipschitz constant of `F` on `C`, measured in the weighted norm. -/
noncomputable def oneSidedLipschitz (C : Set E) (F : E → E)
    (hC : C.Nontrivial := by
      first
        | assumption
        | exact Set.nontrivial_univ
        | fail "osL on C needs `hC : C.Nontrivial` (two points or more) in context") : EReal :=
  _root_.oneSidedLipschitz (equiv R '' C) (fun x => equiv R (F ((equiv R).symm x)))
    (hC.image (equiv R).injective)

end WeightedNorm

end Weighted

/-! ### Matrix log norms -/

namespace Matrix

open WithLp (toLp ofLp)
open scoped RealInnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

section Lp

variable (p : ENNReal) [Fact (1 ≤ p)]

/-- **An invertible matrix as a weight** on `ℝⁿ` with the ℓᵖ norm: `x ↦ R x`. -/
noncomputable def toWeight {R : Matrix n n ℝ} (hR : IsUnit R) :
    WithLp p (n → ℝ) ≃L[ℝ] WithLp p (n → ℝ) :=
  have hdet := (isUnit_iff_isUnit_det R).1 hR
  LinearEquiv.toContinuousLinearEquiv
    { toLpLin p p R with
      invFun := toLpLin p p R⁻¹
      left_inv := fun x => by simp [toLpLin_apply, mulVec_mulVec, nonsing_inv_mul R hdet]
      right_inv := fun x => by simp [toLpLin_apply, mulVec_mulVec, mul_nonsing_inv R hdet] }

@[simp] lemma toWeight_apply {R : Matrix n n ℝ} (hR : IsUnit R) (x : WithLp p (n → ℝ)) :
    toWeight p hR x = toLp p (R *ᵥ ofLp x) := rfl

@[simp] lemma toWeight_symm_apply {R : Matrix n n ℝ} (hR : IsUnit R) (x : WithLp p (n → ℝ)) :
    (toWeight p hR).symm x = toLp p (R⁻¹ *ᵥ ofLp x) := rfl

/-- `A` as an operator on `ℝⁿ` with the ℓᵖ norm. -/
noncomputable def toLpCLM (A : Matrix n n ℝ) : WithLp p (n → ℝ) →L[ℝ] WithLp p (n → ℝ) :=
  LinearMap.toContinuousLinearMap (toLpLin p p A)

/-- `μ_{p} A`: the log norm of the matrix `A` on `ℝⁿ` with the ℓᵖ norm. -/
noncomputable def logNormLp (A : Matrix n n ℝ) : ℝ := μ (toLpCLM p A)

open Classical in
/-- `μ_{p, R} A`: the log norm of the matrix `A` in the weighted norm `‖x‖_{p,R} = ‖R x‖_p`.  It is
meaningful for an invertible weight `R`; for a singular `R`, which is not a weight, it is `0`. -/
noncomputable def logNormLpWeight (R A : Matrix n n ℝ) : ℝ :=
  if hR : IsUnit R then μ[toWeight p hR] (toLpCLM p A) else 0

/-- `osL_{p}(F)`: the one-sided Lipschitz constant on `C` of a map `F` of `ℝⁿ`, in the ℓᵖ norm. -/
noncomputable def oneSidedLipschitzLp (C : Set (n → ℝ)) (F : (n → ℝ) → n → ℝ)
    (hC : C.Nontrivial := by
      first
        | assumption
        | exact Set.nontrivial_univ
        | fail "osL on C needs `hC : C.Nontrivial` (two points or more) in context") : EReal :=
  _root_.oneSidedLipschitz (toLp p '' C) (fun x => toLp p (F (ofLp x)))
    (hC.image (WithLp.toLp_injective p))

open Classical in
/-- `osL_{p,R}(F)`: the one-sided Lipschitz constant on `C` of a map `F` of `ℝⁿ`, in the weighted
norm `‖R x‖_p`.  It is meaningful for an invertible `R`; otherwise it is `0`. -/
noncomputable def oneSidedLipschitzLpWeight (R : Matrix n n ℝ) (C : Set (n → ℝ))
    (F : (n → ℝ) → n → ℝ)
    (hC : C.Nontrivial := by
      first
        | assumption
        | exact Set.nontrivial_univ
        | fail "osL on C needs `hC : C.Nontrivial` (two points or more) in context") : EReal :=
  if hR : IsUnit R then
    WeightedNorm.oneSidedLipschitz (toWeight p hR) (toLp p '' C) (fun x => toLp p (F (ofLp x)))
      (hC.image (WithLp.toLp_injective p))
  else 0

/-- `μ_{p} A` for the ℓᵖ log norm of a matrix; available after `open scoped LogNorm`. -/
scoped[LogNorm] notation:max "μ_{" p "}" => Matrix.logNormLp p

/-- `μ_{p, R} A` for the weighted ℓᵖ log norm of a matrix; available after `open scoped LogNorm`. -/
scoped[LogNorm] notation:max "μ_{" p ", " R "}" => Matrix.logNormLpWeight p R

end Lp

/-- **Metzler matrix**: every off-diagonal entry is nonnegative. -/
def IsMetzler (A : Matrix n n ℝ) : Prop := ∀ i j, i ≠ j → 0 ≤ A i j

/-- **The Metzler majorant** `|A|_M`: the diagonal of `A`, and `|aᵢⱼ|` off the diagonal. -/
def metzlerMajorant (A : Matrix n n ℝ) : Matrix n n ℝ := fun i j => if i = j then A i i else |A i j|

/-! ### The weighted Euclidean norm `‖x‖_{2,P^½} = √(xᵀ P x)` -/

/-- `ℝⁿ` with the inner product `xᵀ P y` and its norm `‖x‖ = √(xᵀ P x)`, for `P ≻ 0`. -/
def WeightedEuclidean {P : Matrix n n ℝ} (_hP : P.PosDef) : Type _ := n → ℝ

namespace WeightedEuclidean

variable {P : Matrix n n ℝ} (hP : P.PosDef)

noncomputable instance : NormedAddCommGroup (WeightedEuclidean hP) := P.toNormedAddCommGroup hP

noncomputable instance : InnerProductSpace ℝ (WeightedEuclidean hP) :=
  P.toInnerProductSpace hP.posSemidef

instance : FiniteDimensional ℝ (WeightedEuclidean hP) :=
  inferInstanceAs (FiniteDimensional ℝ (n → ℝ))

instance [Nonempty n] : Nontrivial (WeightedEuclidean hP) := inferInstanceAs (Nontrivial (n → ℝ))

/-- The identity of `ℝⁿ`, from the sup norm of `n → ℝ` to the norm `√(xᵀ P x)`. -/
noncomputable def equiv : (n → ℝ) ≃L[ℝ] WeightedEuclidean hP :=
  let e : (n → ℝ) ≃ₗ[ℝ] WeightedEuclidean hP :=
    { toFun := fun x => x, invFun := fun x => x, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  { e with
    continuous_toFun := e.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun := e.symm.toLinearMap.continuous_of_finiteDimensional }

/-- `A` as an operator on `ℝⁿ` with the norm `√(xᵀ P x)`. -/
noncomputable def toCLM (A : Matrix n n ℝ) : WeightedEuclidean hP →L[ℝ] WeightedEuclidean hP :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

omit [DecidableEq n] in
lemma inner_def (x y : WeightedEuclidean hP) :
    ⟪x, y⟫ = (x : n → ℝ) ⬝ᵥ (P *ᵥ (y : n → ℝ)) := by
  change (P *ᵥ y) ⬝ᵥ star x = _
  rw [star_trivial, dotProduct_comm]

end WeightedEuclidean

open Classical in
/-- `μ_{2,P^½} A`: the log norm of the matrix `A` in the norm `‖x‖ = √(xᵀ P x)`.  It is meaningful
for `P ≻ 0`; otherwise it is `0`. -/
noncomputable def logNormL2PosDef (P A : Matrix n n ℝ) : ℝ :=
  if hP : P.PosDef then μ (WeightedEuclidean.toCLM hP A) else 0

open Classical in
/-- `osL_{2,P^½}(F)`: the one-sided Lipschitz constant on `C` of a map `F` of `ℝⁿ`, in the norm
`√(xᵀ P x)`.  It is meaningful for `P ≻ 0`; otherwise it is `0`. -/
noncomputable def oneSidedLipschitzL2PosDef (P : Matrix n n ℝ) (C : Set (n → ℝ))
    (F : (n → ℝ) → n → ℝ)
    (hC : C.Nontrivial := by
      first
        | assumption
        | exact Set.nontrivial_univ
        | fail "osL on C needs `hC : C.Nontrivial` (two points or more) in context") : EReal :=
  if hP : P.PosDef then @_root_.oneSidedLipschitz (WeightedEuclidean hP) _ _ C F hC else 0

end Matrix

namespace LogNorm

/-- `μ_{2,P^½} A` for the log norm of `A` in `‖x‖ = √(xᵀ P x)`; available after
`open scoped LogNorm`.  It shares its opening `μ_{` with `μ_{p, R}`, so that `μ_{2, R}` still
parses as the weighted ℓ² log norm. -/
scoped syntax:max "μ_{" num "," term "^½}" : term

scoped macro_rules
  | `(μ_{$p:num, $P^½}) =>
    if p.getNat = 2 then `(Matrix.logNormL2PosDef $P)
    else Lean.Macro.throwError "`μ_{p,P^½}` is defined only for p = 2"

/-- Print `logNormL2PosDef P A` as `μ_{2,P^½} A`. -/
@[scoped app_unexpander Matrix.logNormL2PosDef]
def unexpandLogNormL2PosDef : Lean.PrettyPrinter.Unexpander
  | `($_ $P:ident $A) => `(μ_{2, $P^½} $A)
  | `($_ $P $A) => `(μ_{2, ($P)^½} $A)
  | `($_ $P:ident) => `(μ_{2, $P^½})
  | `($_ $P) => `(μ_{2, ($P)^½})
  | _ => throw ()

/-! #### One-sided Lipschitz constants

`osL F`, `osL[R] F`, `osL_{p} F`, `osL_{p, R} F` and `osL_{2,P^½} F` mirror the log norms: the
one-sided Lipschitz constant on all of the space.  Appending `on C` restricts it to `C`, which needs
a proof `C.Nontrivial` in the context. -/

/-- `osL F` and `osL F on C`: the one-sided Lipschitz constant. -/
scoped syntax:max "osL " term:max (" on " term:max)? : term

/-- `osL[R] F` and `osL[R] F on C`: the one-sided Lipschitz constant in the weighted norm. -/
scoped syntax:max "osL[" term "] " term:max (" on " term:max)? : term

/-- `osL_{p} F`, `osL_{p, R} F`, `osL_{2,P^½} F`, each with an optional `on C`. -/
scoped syntax:max "osL_{" term "} " term:max (" on " term:max)? : term

@[inherit_doc LogNorm.«termOsL_{_}_On_»]
scoped syntax:max "osL_{" term ", " term "} " term:max (" on " term:max)? : term

@[inherit_doc LogNorm.«termOsL_{_}_On_»]
scoped syntax:max "osL_{" num "," term "^½} " term:max (" on " term:max)? : term

scoped macro_rules
  | `(osL $F on $C) => `(oneSidedLipschitz $C $F)
  | `(osL $F) => `(oneSidedLipschitz Set.univ $F)
  | `(osL[$R] $F on $C) => `(WeightedNorm.oneSidedLipschitz $R $C $F)
  | `(osL[$R] $F) => `(WeightedNorm.oneSidedLipschitz $R Set.univ $F)
  | `(osL_{$p} $F on $C) => `(Matrix.oneSidedLipschitzLp $p $C $F)
  | `(osL_{$p} $F) => `(Matrix.oneSidedLipschitzLp $p Set.univ $F)
  | `(osL_{$p, $R} $F on $C) => `(Matrix.oneSidedLipschitzLpWeight $p $R $C $F)
  | `(osL_{$p, $R} $F) => `(Matrix.oneSidedLipschitzLpWeight $p $R Set.univ $F)
  | `(osL_{$p:num, $P^½} $F on $C) =>
    if p.getNat = 2 then `(Matrix.oneSidedLipschitzL2PosDef $P $C $F)
    else Lean.Macro.throwError "`osL_{p,P^½}` is defined only for p = 2"
  | `(osL_{$p:num, $P^½} $F) =>
    if p.getNat = 2 then `(Matrix.oneSidedLipschitzL2PosDef $P Set.univ $F)
    else Lean.Macro.throwError "`osL_{p,P^½}` is defined only for p = 2"

end LogNorm

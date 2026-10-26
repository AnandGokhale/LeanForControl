import Mathlib.Analysis.CStarAlgebra.Matrix
import LeanForControl.Analysis.Continuity
import LeanForControl.LinearSystems.Continuous
import LeanForControl.LinearSystems.Solutions.PeanoBaker
import LeanForControl.ODEs.ODE_properties
import Architect

/-!
# Continuous-time solutions: the Peano-Baker series

Theorems about the state transition matrix, building on the Banach-algebra theory in
`PeanoBaker.lean` and leading up to Theorem 5.1 (Peano-Baker series): `x(t) := Φ(t, t₀) *ᵥ x₀`
is the unique solution of `ẋ = A(t) x`, `x(t₀) = x₀`.

The final section restates the solution for the `ContinuousLTV` object: the forced
response is a *trajectory* in the sense of `ContinuousLTV.IsTrajectoryOn`, which is the
predicate the stability theory quantifies over. Everything before it works with the coefficient
maps `A` and `B` directly, which is where the analysis lives.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5.
-/

namespace LinearSystems

open scoped Matrix.Norms.Operator Nat
open Matrix MeasureTheory intervalIntegral WithLp

variable {X : Type*} [Fintype X] [DecidableEq X] {A : ℝ → Matrix X X ℝ}

/-- **Peano-Baker series: existence** (Hespanha, Theorem 5.1).
`x(t) := Φ(t, t₀) *ᵥ x₀` solves the
initial value problem `ẋ = A(t) x` — this is `hasDerivAt_stateTransitionMatrix` pushed through
the fixed linear map `M ↦ M *ᵥ x₀` (continuous, since the domain is finite-dimensional).

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Theorem 5.1. -/
@[blueprint "thm:hasDerivAt-stateTransitionMatrix-mulVec"
  (title := "Peano--Baker series: existence")
  (statement := /-- Hespanha, Theorem 5.1.  $x(t) := \Phi(t,t_0)\, x_0$ solves
    \[
      \dot x(t) = A(t)\, x(t).
    \] -/)
  (proof := /-- Push \cref{thm:hasDerivAt-stateTransitionMatrix} through the fixed linear map
    $M \mapsto M x_0$ (continuous, since the domain is finite-dimensional). -/)]
theorem hasDerivAt_stateTransitionMatrix_mulVec (hA : Continuous A) (t t₀ : ℝ) (x₀ : X → ℝ) :
    HasDerivAt (fun z => stateTransitionMatrix A z t₀ *ᵥ x₀)
      (A t *ᵥ (stateTransitionMatrix A t t₀ *ᵥ x₀)) t := by
  -- The fixed linear map `M ↦ M *ᵥ x₀`, as a continuous linear map (automatic: the domain
  -- `Matrix X X ℝ` is finite-dimensional).
  set L : Matrix X X ℝ →L[ℝ] (X → ℝ) :=
    LinearMap.toContinuousLinearMap ((Matrix.mulVecBilin ℝ ℝ).flip x₀)
  have hL_apply : ∀ M' : Matrix X X ℝ, L M' = M' *ᵥ x₀ := fun M' => rfl
  have hderiv := (L.hasFDerivAt (x := stateTransitionMatrix A t t₀)).comp_hasDerivAt t
    (hasDerivAt_stateTransitionMatrix hA _ _)
  simpa [hL_apply, Matrix.mulVec_mulVec] using hderiv

/-- Shrinking the far endpoint of an open segment: if `t` lies between `t₀` and `t₁`, then the
open segment between `t₀` and `t` sits inside the one between `t₀` and `t₁`. -/
private lemma uIoo_subset_uIoo_of_mem_uIcc {t₀ t₁ t : ℝ} (ht : t ∈ Set.uIcc t₀ t₁) :
    Set.uIoo t₀ t ⊆ Set.uIoo t₀ t₁ := by
  rw [← Set.Ioo_min_max, ← Set.Ioo_min_max]
  exact Set.Ioo_subset_Ioo (le_min (min_le_left t₀ t₁) ht.1) (max_le (le_max_left t₀ t₁) ht.2)

/-- **Integral solutions from derivatives.** A path `x`, continuous on the closed segment between
`t₀` and `t₁`, with `ẋ(t) = F(t, x(t))` at every interior point, a continuous right-hand side
`s ↦ F(s, x(s))`, and initial value `x(t₀) = x₀`, is an integral solution of `ẋ = F(t, x)`. -/
private lemma isIntegralSolution_of_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {t₀ t₁ : ℝ} {x : ℝ → E} {x₀ : E} {F : ℝ → E → E}
    (hx_cont : ContinuousOn x (Set.uIcc t₀ t₁))
    (hF_cont : ContinuousOn (fun s => F s (x s)) (Set.uIcc t₀ t₁))
    (hderiv : ∀ t ∈ Set.uIoo t₀ t₁, HasDerivAt x (F t (x t)) t) (hx₀ : x t₀ = x₀) :
    IsIntegralSolution t₀ t₁ x x₀ F := by
  -- The fundamental theorem of calculus on the sub-segment between `t₀` and `t`.
  intro t ht
  have huIcc_sub : Set.uIcc t₀ t ⊆ Set.uIcc t₀ t₁ := Set.uIcc_subset_uIcc_left ht
  have hderiv_right : ∀ z ∈ Set.uIoo t₀ t, HasDerivWithinAt x (F z (x z)) (Set.Ioi z) z :=
    fun z hz => (hderiv z (uIoo_subset_uIoo_of_mem_uIcc ht hz)).hasDerivWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right (hx_cont.mono huIcc_sub)
    hderiv_right (hF_cont.mono huIcc_sub).intervalIntegrable
  rw [hx₀] at hFTC
  rw [hFTC]
  abel

/-- The matrix analogue of `isIntegralSolution_stateTransitionMatrix_mulVec`: for a constant
matrix `C`, `Y(t) := Φ(t, t₀) * C` is an integral solution of `Ẏ = A(t) Y` on the segment
between `t₀` and `t₁` with initial value `C`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "lem:isIntegralSolution-stateTransitionMatrix-mul"
  (title := "Integral form, matrix-valued")
  (latexEnv := "lemma")
  (statement := /-- For a constant matrix $C$, $Y(t) := \Phi(t,t_0)\, C$ satisfies the integral
    equation
    \[
      Y(t) = C + \int_{t_0}^{t} A(s)\, Y(s)\,\mathrm{d}s
    \]
    for every $t$ between $t_0$ and $t_1$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5.
  -/)
  (proof := /-- The fundamental theorem of calculus applied to
    \cref{thm:hasDerivAt-stateTransitionMatrix}, using $\Phi(t_0,t_0) = I$
    (\cref{thm:stateTransitionMatrix-self}) to fix the initial value. -/)]
theorem isIntegralSolution_stateTransitionMatrix_mul (hA : Continuous A) {t₀ t₁ : ℝ}
    (C : Matrix X X ℝ) :
    IsIntegralSolution t₀ t₁ (fun t => stateTransitionMatrix A t t₀ * C) C
      (fun s Y => A s * Y) := by
  have hx_cont : ContinuousOn (fun t => stateTransitionMatrix A t t₀ * C) (Set.uIcc t₀ t₁) :=
    (continuous_fst.mul continuous_snd).comp_continuousOn
      (((continuous_stateTransitionMatrix hA _).continuousOn).prodMk continuousOn_const)
  have hrhs_cont : ContinuousOn (fun s => A s * (stateTransitionMatrix A s t₀ * C))
      (Set.uIcc t₀ t₁) :=
    (continuous_fst.mul continuous_snd).comp_continuousOn (hA.continuousOn.prodMk hx_cont)
  have hx₀ : stateTransitionMatrix A t₀ t₀ * C = C := by
    rw [stateTransitionMatrix_self, Matrix.one_mul]
  exact isIntegralSolution_of_hasDerivAt hx_cont hrhs_cont
    (fun t _ => by
      simpa [mul_assoc] using (hasDerivAt_stateTransitionMatrix hA t t₀).mul_const C) hx₀

/-- `x(t) := Φ(t, t₀) *ᵥ x₀` is an *integral solution* (`IsIntegralSolution`, from
`ODEs/ODE_properties.lean`) of `ẋ = A(t) x` on the segment between `t₀` and `t₁` — the
integral-equation reformulation of `hasDerivAt_stateTransitionMatrix_mulVec`, via the
fundamental theorem of calculus. This is what lets uniqueness reuse `continuous_dependence_ODE`
(Theorem 3.4), which is stated in terms of `IsIntegralSolution` rather than `HasDerivAt`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "lem:isIntegralSolution-stateTransitionMatrix-mulVec"
  (title := "Integral form, vector-valued")
  (latexEnv := "lemma")
  (statement := /-- $x(t) := \Phi(t,t_0)\, x_0$ satisfies the integral equation
    \[
      x(t) = x_0 + \int_{t_0}^{t} A(s)\, x(s)\,\mathrm{d}s
    \]
    for every $t$ between $t_0$ and $t_1$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5.
  -/)
  (proof := /-- The fundamental theorem of calculus applied to
    \cref{thm:hasDerivAt-stateTransitionMatrix-mulVec}, using $\Phi(t_0,t_0) = I$
    (\cref{thm:stateTransitionMatrix-self}) to fix the initial value. -/)]
theorem isIntegralSolution_stateTransitionMatrix_mulVec (hA : Continuous A) {t₀ t₁ : ℝ}
    (x₀ : X → ℝ) :
    IsIntegralSolution t₀ t₁ (fun t => stateTransitionMatrix A t t₀ *ᵥ x₀) x₀
      (fun s v => A s *ᵥ v) := by
  have hx_cont : ContinuousOn (fun t => stateTransitionMatrix A t t₀ *ᵥ x₀) (Set.uIcc t₀ t₁) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (((continuous_stateTransitionMatrix hA _).continuousOn).prodMk continuousOn_const)
  have hrhs_cont : ContinuousOn (fun s => A s *ᵥ (stateTransitionMatrix A s t₀ *ᵥ x₀))
      (Set.uIcc t₀ t₁) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (hA.continuousOn.prodMk hx_cont)
  have hx₀ : stateTransitionMatrix A t₀ t₀ *ᵥ x₀ = x₀ := by
    rw [stateTransitionMatrix_self, Matrix.one_mulVec]
  exact isIntegralSolution_of_hasDerivAt hx_cont hrhs_cont
    (fun t _ => hasDerivAt_stateTransitionMatrix_mulVec hA t t₀ x₀) hx₀

/-- **Uniqueness of integral solutions under a Lipschitz bound.** Two continuous integral
solutions `y`, `z` of `ẋ = F(t, x)` with the same initial value `x₀` agree on the segment between
`t₀` and `t₁`, provided `F` is jointly continuous and `‖F t v - F t w‖ ≤ M * ‖v - w‖` for every
`t` on the segment. This is the common core of `stateTransitionMatrix_mulVec_unique`,
`stateTransitionMatrix_mul_unique` and `variationOfConstants_unique`. -/
private lemma eq_of_isIntegralSolution_of_norm_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {t₀ t₁ M : ℝ} {F : ℝ → E → E} {x₀ : E} {y z : ℝ → E}
    (hF_cont : Continuous (fun p : ℝ × E => F p.1 p.2))
    (hF_lip : ∀ t ∈ Set.uIcc t₀ t₁, ∀ v w : E, ‖F t v - F t w‖ ≤ M * ‖v - w‖)
    (hy : IsIntegralSolution t₀ t₁ y x₀ F) (hz : IsIntegralSolution t₀ t₁ z x₀ F)
    (hy_cont : ContinuousOn y (Set.uIcc t₀ t₁)) (hz_cont : ContinuousOn z (Set.uIcc t₀ t₁)) :
    ∀ t ∈ Set.uIcc t₀ t₁, y t = z t := by
  -- Feed `continuous_dependence_ODE` (Theorem 3.4) the zero perturbation `g := 0`: with equal
  -- initial values, its bound on `‖y t - z t‖` collapses to `0`.
  -- First, a positive Lipschitz constant `L := max M 1`, as Theorem 3.4 requires.
  set L : ℝ := max M 1
  have hL_pos : (0 : ℝ) < L := lt_of_lt_of_le one_pos (le_max_right M 1)
  have hLip : ∀ t ∈ Set.uIcc t₀ t₁, LipschitzWith ⟨L, hL_pos.le⟩ (F t) := by
    intro t ht
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    calc dist (F t v) (F t w) = ‖F t v - F t w‖ := dist_eq_norm _ _
      _ ≤ M * ‖v - w‖ := hF_lip t ht v w
      _ ≤ L * dist v w := by rw [dist_eq_norm]; gcongr; exact le_max_left M 1
  have hbound := continuous_dependence_ODE (g := fun _ _ => (0 : E)) (μ := 0) hL_pos
    hy (by simpa using hz) hy_cont hz_cont hF_cont intervalIntegrable_const hLip
    (fun _ _ _ => by simp)
  intro t ht
  have hnorm_le_zero : ‖y t - z t‖ ≤ 0 := by simpa using hbound t ht
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hnorm_le_zero)

/-- **Peano-Baker series: uniqueness** (Hespanha, Theorem 5.1).
Any integral solution `z` of
`ẋ = A(t) x`, `x(t₀) = x₀` on the segment between `t₀` and `t₁` coincides with
`x(t) := Φ(t, t₀) *ᵥ x₀`.

Proof: apply `continuous_dependence_ODE` (Theorem 3.4) with zero perturbation `g := 0`. Since
both solutions share the initial value `x₀` and the perturbation bound is `μ = 0`, the bound it
gives collapses to `‖x t - z t‖ ≤ 0`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Theorem 5.1. -/
@[blueprint "thm:stateTransitionMatrix-mulVec-unique"
  (title := "Peano--Baker series: uniqueness")
  (statement := /-- Hespanha, Theorem 5.1.  Any solution
    $z$ of $\dot x = A(t)\, x$, $x(t_0) = x_0$, for $t$ between $t_0$ and $t_1$, coincides with
    $x(t) := \Phi(t,t_0)\, x_0$. -/)
  (proof := /-- Apply the continuous-dependence bound of Theorem 3.4 with zero perturbation:
    since both solutions share the initial value $x_0$, the resulting bound on
    $\|x(t) - z(t)\|$ collapses to $0$. -/)]
theorem stateTransitionMatrix_mulVec_unique (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (x₀ : X → ℝ)
    {z : ℝ → X → ℝ} (hz : IsIntegralSolution t₀ t₁ z x₀ (fun s v => A s *ᵥ v))
    (hz_cont : ContinuousOn z (Set.uIcc t₀ t₁)) :
    ∀ t ∈ Set.uIcc t₀ t₁, z t = stateTransitionMatrix A t t₀ *ᵥ x₀ := by
  -- `v ↦ A t *ᵥ v` is `M`-Lipschitz on the segment, by the operator-norm bound on `A t`.
  have hrhs_lip : ∀ t ∈ Set.uIcc t₀ t₁, ∀ v w : X → ℝ,
      ‖A t *ᵥ v - A t *ᵥ w‖ ≤ M * ‖v - w‖ := by
    intro t ht v w
    calc ‖A t *ᵥ v - A t *ᵥ w‖ = ‖A t *ᵥ (v - w)‖ := by rw [Matrix.mulVec_sub]
      _ ≤ ‖A t‖ * ‖v - w‖ := Matrix.linfty_opNorm_mulVec _ _
      _ ≤ M * ‖v - w‖ := by gcongr; exact hA_le t ht
  have hx_cont : ContinuousOn (fun t => stateTransitionMatrix A t t₀ *ᵥ x₀) (Set.uIcc t₀ t₁) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (((continuous_stateTransitionMatrix hA _).continuousOn).prodMk continuousOn_const)
  exact eq_of_isIntegralSolution_of_norm_sub_le
    ((hA.comp continuous_fst).matrix_mulVec continuous_snd) hrhs_lip hz
    (isIntegralSolution_stateTransitionMatrix_mulVec hA x₀) hz_cont hx_cont

/-- **Columns of the state transition matrix** (Hespanha, P5.2).
For a fixed standard basis vector `e_i`, `stateTransitionMatrix_mulVec_unique`
specializes to: any integral solution `z` of `ẋ = A(t) x`, `x(t₀) = e_i` on the segment between
`t₀` and `t₁` coincides with the `i`-th column of `Φ(t, t₀)` — via
`Φ(t, t₀) *ᵥ e_i = (Φ(t, t₀)).col i` (`Matrix.mulVec_single_one`).

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.2. -/
@[blueprint "thm:stateTransitionMatrix-col-unique"
  (title := "Columns of the state transition matrix")
  (statement := /-- Hespanha, P5.2.  For every fixed $i$, the $i$-th column of $\Phi(t,t_0)$ is
    the unique solution of $\dot x = A(t)\, x$, $x(t_0) = e_i$, where $e_i$ is the $i$-th
    standard basis vector. -/)
  (proof := /-- Restatement of \cref{thm:stateTransitionMatrix-mulVec-unique} at
    $x_0 := e_i$, using $\Phi(t,t_0)\, e_i = (\Phi(t,t_0))_{\cdot,i}$
    (\texttt{Matrix.mulVec\_single\_one}). -/)]
theorem stateTransitionMatrix_col_unique (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (i : X)
    {z : ℝ → X → ℝ} (hz : IsIntegralSolution t₀ t₁ z (Pi.single i 1) (fun s v => A s *ᵥ v))
    (hz_cont : ContinuousOn z (Set.uIcc t₀ t₁)) :
    ∀ t ∈ Set.uIcc t₀ t₁, z t = (stateTransitionMatrix A t t₀).col i := by
  intro t ht
  rw [← Matrix.mulVec_single_one]
  exact stateTransitionMatrix_mulVec_unique hA hA_le (Pi.single i 1) hz hz_cont t ht

/-- The matrix analogue of `stateTransitionMatrix_mulVec_unique`: any integral solution `Y` of
`Ẏ = A(t) Y`, `Y(t₀) = C` on the segment between `t₀` and `t₁` coincides with `Φ(t, t₀) * C`.
Unlike the vector case, the Lipschitz bound on `M ↦ A t * M` comes from submultiplicativity of
the operator norm (`norm_mul_le`) rather than `Matrix.linfty_opNorm_mulVec`, but the rest of the
argument — feeding `continuous_dependence_ODE` (Theorem 3.4) the zero perturbation `g := 0` —
is identical.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "thm:stateTransitionMatrix-mul-unique"
  (title := "Uniqueness of matrix-valued solutions")
  (statement := /-- Any solution $Y$ of $\dot Y = A(t)\, Y$, $Y(t_0) = C$, for $t$ between $t_0$
    and $t_1$, coincides with $\Phi(t,t_0)\, C$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5.
  -/)
  (proof := /-- Apply the continuous-dependence bound of Theorem 3.4 with zero perturbation:
    since both solutions share the initial value $C$, the resulting bound on
    $\|Y(t) - Z(t)\|$ collapses to $0$. -/)]
theorem stateTransitionMatrix_mul_unique (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (C : Matrix X X ℝ)
    {Y : ℝ → Matrix X X ℝ} (hY : IsIntegralSolution t₀ t₁ Y C (fun s M' => A s * M'))
    (hY_cont : ContinuousOn Y (Set.uIcc t₀ t₁)) :
    ∀ t ∈ Set.uIcc t₀ t₁, Y t = stateTransitionMatrix A t t₀ * C := by
  -- `M' ↦ A t * M'` is `M`-Lipschitz on the segment, by submultiplicativity of the norm.
  have hrhs_lip : ∀ t ∈ Set.uIcc t₀ t₁, ∀ M₁ M₂ : Matrix X X ℝ,
      ‖A t * M₁ - A t * M₂‖ ≤ M * ‖M₁ - M₂‖ := by
    intro t ht M₁ M₂
    calc ‖A t * M₁ - A t * M₂‖ = ‖A t * (M₁ - M₂)‖ := by rw [mul_sub]
      _ ≤ ‖A t‖ * ‖M₁ - M₂‖ := norm_mul_le _ _
      _ ≤ M * ‖M₁ - M₂‖ := by gcongr; exact hA_le t ht
  have hΦC_cont : ContinuousOn (fun t => stateTransitionMatrix A t t₀ * C) (Set.uIcc t₀ t₁) :=
    (continuous_fst.mul continuous_snd).comp_continuousOn
      (((continuous_stateTransitionMatrix hA _).continuousOn).prodMk continuousOn_const)
  exact eq_of_isIntegralSolution_of_norm_sub_le
    ((hA.comp continuous_fst).mul continuous_snd) hrhs_lip hY
    (isIntegralSolution_stateTransitionMatrix_mul hA C) hY_cont hΦC_cont

/-- Auxiliary re-anchoring fact: `Y(z) := Φ(z, a) * C`, an integral solution of the matrix ODE
anchored at `a`, also satisfies the integral equation anchored at the *other* endpoint `b`, with
the whole segment between `a` and `b` still as the domain — what `stateTransitionMatrix_inv`
needs to compare `Φ(·, a)` against `Φ(·, b) * Φ(b, a)` using `stateTransitionMatrix_mul_unique`
anchored at `b`.

This is `IsIntegralSolution.reanchor` at the two endpoints, `s := b` and `r := a`. -/
private lemma isIntegralSolution_stateTransitionMatrix_mul_reanchor (hA : Continuous A) {a b : ℝ}
    (C : Matrix X X ℝ) :
    IsIntegralSolution b a (fun z => stateTransitionMatrix A z a * C)
      (stateTransitionMatrix A b a * C) (fun s Y => A s * Y) :=
  (isIntegralSolution_stateTransitionMatrix_mul hA C).reanchor
    ((hA.comp continuous_fst).mul continuous_snd)
    ((continuous_fst.mul continuous_snd).comp_continuousOn
      (((continuous_stateTransitionMatrix hA _).continuousOn).prodMk continuousOn_const))
    Set.right_mem_uIcc Set.left_mem_uIcc

/-- **Semigroup property** (Hespanha, P5.3).
`Φ(t,s) * Φ(s,τ) = Φ(t,τ)` for `τ ≤ s < t`, with `A`
continuous and bounded by `M` on the segment between `τ` and `t`.

Proof: `Φ(·,τ)`, re-anchored at `s` (`IsIntegralSolution.reanchor`), is an integral solution of
the matrix ODE on the segment between `s` and `t` with initial value `Φ(s,τ)`, hence coincides
with `Φ(·,s) * Φ(s,τ)` there by `stateTransitionMatrix_mul_unique`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.3. -/
@[blueprint "thm:stateTransitionMatrix-semigroup"
  (title := "Semigroup property")
  (statement := /-- Hespanha, P5.3.  For $A$ continuous and bounded on
    $[\tau, t]$, and any $\tau \le s < t$,
    \[
      \Phi(t,s)\,\Phi(s,\tau) = \Phi(t,\tau).
    \] -/)
  (proof := /-- $\Phi(\cdot,\tau)$, re-anchored at $s$, is an integral solution of the matrix
    ODE on the segment between $s$ and $t$ with initial value $\Phi(s,\tau)$, hence coincides
    with $\Phi(\cdot,s)\,\Phi(s,\tau)$ there by \cref{thm:stateTransitionMatrix-mul-unique}. -/)]
theorem stateTransitionMatrix_semigroup (hA : Continuous A) {τ s t M : ℝ} (hτs : τ ≤ s)
    (hst : s < t) (hA_le : ∀ r ∈ Set.Icc τ t, ‖A r‖ ≤ M) :
    stateTransitionMatrix A t s * stateTransitionMatrix A s τ = stateTransitionMatrix A t τ := by
  have hτt : τ < t := hτs.trans_lt hst
  have hA_le_u : ∀ r ∈ Set.uIcc τ t, ‖A r‖ ≤ M := by rw [Set.uIcc_of_le hτt.le]; exact hA_le
  have hs_mem : s ∈ Set.uIcc τ t := by rw [Set.uIcc_of_le hτt.le]; exact ⟨hτs, hst.le⟩
  have hA_le'_u : ∀ r ∈ Set.uIcc s t, ‖A r‖ ≤ M := by
    rw [Set.uIcc_of_le hst.le]
    exact fun r hr => hA_le r (Set.Icc_subset_Icc hτs le_rfl hr)
  have hF_cont : Continuous (fun p : ℝ × Matrix X X ℝ => A p.1 * p.2) :=
    (hA.comp continuous_fst).mul continuous_snd
  have hbase : IsIntegralSolution τ t (fun z => stateTransitionMatrix A z τ)
      (1 : Matrix X X ℝ) (fun r Y => A r * Y) := by
    simpa using isIntegralSolution_stateTransitionMatrix_mul hA 1
  have hre := hbase.reanchor hF_cont ((continuous_stateTransitionMatrix hA _).continuousOn) hs_mem
    Set.right_mem_uIcc
  have hunique := stateTransitionMatrix_mul_unique hA hA_le'_u (stateTransitionMatrix A s τ) hre
    ((continuous_stateTransitionMatrix hA _).continuousOn.mono
      (Set.uIcc_subset_uIcc_right hs_mem))
    t Set.right_mem_uIcc
  exact hunique.symm

/-- **Invertibility of the state transition matrix** (Hespanha, P5.4).
`Φ(t,τ)` is nonsingular, with `Φ(t,τ)⁻¹ = Φ(τ,t)`, for `A` continuous and bounded
by `M` on the segment between `τ` and `t`.

Proof: `Φ(·,τ)`, re-anchored at `t` (`isIntegralSolution_stateTransitionMatrix_mul_reanchor`), is
an integral solution of the matrix ODE on the segment between `t` and `τ` with initial value
`Φ(t,τ)`, hence coincides with `Φ(·,t) * Φ(t,τ)` there (`stateTransitionMatrix_mul_unique`).
Evaluating at `τ` gives `Φ(τ,t) * Φ(t,τ) = Φ(τ,τ) = I`, so `Φ(τ,t)` is a left inverse of
`Φ(t,τ)`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.4. -/
@[blueprint "thm:stateTransitionMatrix-inv"
  (title := "Invertibility of the state transition matrix")
  (statement := /-- Hespanha, P5.4.  For $A$ continuous and bounded on the segment between $\tau$
    and $t$, $\Phi(t,\tau)$ is nonsingular and
    \[
      \Phi(t,\tau)^{-1} = \Phi(\tau,t).
    \] -/)
  (proof := /-- From \cref{thm:stateTransitionMatrix-semigroup}, generalized to arbitrary order
    by re-anchoring $\Phi(\cdot,\tau)$ at $t$ and invoking uniqueness there,
    $\Phi(\tau,t)\Phi(t,\tau) = \Phi(\tau,\tau) = I$, so $\Phi(t,\tau)$ and $\Phi(\tau,t)$ are
    mutual inverses. -/)]
theorem stateTransitionMatrix_inv (hA : Continuous A) {t τ M : ℝ}
    (hA_le : ∀ r ∈ Set.uIcc τ t, ‖A r‖ ≤ M) :
    IsUnit (stateTransitionMatrix A t τ) ∧
      (stateTransitionMatrix A t τ)⁻¹ = stateTransitionMatrix A τ t := by
  -- `Φ(·,τ)`, re-anchored at `t`, coincides with `Φ(·,t) * Φ(t,τ)` on `[t,τ]` by uniqueness;
  -- evaluating at `τ` gives `Φ(τ,t) * Φ(t,τ) = Φ(τ,τ) = I`.
  have hmul : stateTransitionMatrix A τ t * stateTransitionMatrix A t τ = 1 := by
    have hY : IsIntegralSolution t τ (fun z => stateTransitionMatrix A z τ)
        (stateTransitionMatrix A t τ) (fun s Y => A s * Y) := by
      simpa using isIntegralSolution_stateTransitionMatrix_mul_reanchor hA
        (1 : Matrix X X ℝ)
    have huniq := stateTransitionMatrix_mul_unique hA
      (show ∀ r ∈ Set.uIcc t τ, ‖A r‖ ≤ M by rwa [Set.uIcc_comm])
      (stateTransitionMatrix A t τ) hY
      (show ContinuousOn (fun z => stateTransitionMatrix A z τ) (Set.uIcc t τ) by
        rw [Set.uIcc_comm]; exact (continuous_stateTransitionMatrix hA _).continuousOn)
      τ Set.right_mem_uIcc
    rwa [stateTransitionMatrix_self, eq_comm] at huniq
  exact ⟨IsUnit.of_mul_eq_one_right _ hmul, Matrix.inv_eq_left_inv hmul⟩

/-- Composition of the state transition matrix, varying the *first* argument: `Φ(z,a) =
Φ(z,b) * Φ(b,a)` for every `z` on the segment between `a` and `b`. This is the general form of
the fact used inside `stateTransitionMatrix_inv` (which only needed it at `z = τ`); kept general
here because `stateTransitionMatrix_comp` below needs it at an arbitrary point.

Proof: identical to `stateTransitionMatrix_inv`'s — `Φ(·,a)`, re-anchored at `b`
(`isIntegralSolution_stateTransitionMatrix_mul_reanchor`), coincides with `Φ(·,b) * Φ(b,a)` on
`[b,a]` by uniqueness (`stateTransitionMatrix_mul_unique`). -/
@[blueprint "lem:stateTransitionMatrix-comp-of-mem"
  (title := "Composition on a subinterval")
  (latexEnv := "lemma")
  (statement := /-- For every $z$ on the segment between $a$ and $b$,
    $\Phi(z, a) = \Phi(z, b)\,\Phi(b, a)$.  Composition with the \emph{first} argument free. -/)
  (proof := /-- $\Phi(\cdot, a)$, re-anchored at $b$, is an integral solution of
    $\dot Y = A(r)Y$ with value $\Phi(b,a)$ at $b$; so is $\Phi(\cdot, b)\Phi(b,a)$.  They agree
    by \cref{thm:stateTransitionMatrix-mul-unique}. -/)]
theorem stateTransitionMatrix_comp_of_mem (hA : Continuous A) {a b M : ℝ}
    (hA_le : ∀ r ∈ Set.uIcc a b, ‖A r‖ ≤ M) {z : ℝ} (hz : z ∈ Set.uIcc a b) :
    stateTransitionMatrix A z a = stateTransitionMatrix A z b * stateTransitionMatrix A b a := by
  have hY : IsIntegralSolution b a (fun z => stateTransitionMatrix A z a)
      (stateTransitionMatrix A b a) (fun r Y => A r * Y) := by
    simpa using isIntegralSolution_stateTransitionMatrix_mul_reanchor hA
      (1 : Matrix X X ℝ)
  exact stateTransitionMatrix_mul_unique hA (show ∀ r ∈ Set.uIcc b a, ‖A r‖ ≤ M by
      rwa [Set.uIcc_comm]) (stateTransitionMatrix A b a) hY
    (show ContinuousOn (fun z => stateTransitionMatrix A z a) (Set.uIcc b a) by
      rw [Set.uIcc_comm]; exact (continuous_stateTransitionMatrix hA _).continuousOn)
    z (by rwa [Set.uIcc_comm] at hz)

/-- **Semigroup property, order-free** (Hespanha, P5.3).
`Φ(t,s) * Φ(s,τ) = Φ(t,τ)` for *any* `s` on the segment between `τ`
and `t` — the order-free generalization of `stateTransitionMatrix_semigroup`, whose `τ ≤ s < t`
restriction was an artifact of matching the textbook's literal statement, not a genuine
requirement. Needed by the variation-of-constants existence proof, where `s = t₀` is fixed and
`τ` ranges over the *whole* segment `[t₀,t]`, not just points strictly after `t₀`.

Proof: `Φ(s,τ) = Φ(s,t) * Φ(t,τ)` by `stateTransitionMatrix_comp_of_mem`; left-multiply by
`Φ(t,s)` and simplify via `Φ(t,s) * Φ(s,t) = I` (P5.4, `stateTransitionMatrix_inv`).

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.3. -/
@[blueprint "thm:stateTransitionMatrix-comp"
  (title := "Semigroup property, order-free")
  (statement := /-- Hespanha, P5.3.  For \emph{any} $s$ on the segment between $\tau$
    and $t$,
    \[
      \Phi(t, s)\,\Phi(s, \tau) = \Phi(t, \tau).
    \]
    The $\tau \le s < t$ ordering in \cref{thm:stateTransitionMatrix-semigroup} matches the
    textbook's literal statement but is not a genuine requirement; the variation-of-constants
    proof needs the unordered form, where $s = t_0$ is fixed and $\tau$ ranges over the whole
    segment. -/)
  (proof := /-- \cref{lem:stateTransitionMatrix-comp-of-mem} gives
    $\Phi(s,\tau) = \Phi(s,t)\Phi(t,\tau)$; left-multiply by $\Phi(t,s)$ and cancel using
    $\Phi(t,s)\Phi(s,t) = I$ (\cref{thm:stateTransitionMatrix-inv}). -/)]
theorem stateTransitionMatrix_comp (hA : Continuous A) {τ t M : ℝ}
    (hA_le : ∀ r ∈ Set.uIcc τ t, ‖A r‖ ≤ M) {s : ℝ} (hs : s ∈ Set.uIcc τ t) :
    stateTransitionMatrix A t s * stateTransitionMatrix A s τ = stateTransitionMatrix A t τ := by
  have hcomp := stateTransitionMatrix_comp_of_mem hA hA_le hs
  have hA_le' : ∀ r ∈ Set.uIcc s t, ‖A r‖ ≤ M := fun r hr =>
    hA_le r (Set.uIcc_subset_uIcc_right hs hr)
  obtain ⟨hunit, hinv⟩ := stateTransitionMatrix_inv hA hA_le'
  rw [hcomp, ← mul_assoc, ← hinv, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
    hunit), Matrix.one_mul]

/-- Composition of the state transition matrix through a fixed *base* point: `Φ(t,t₀) *
Φ(t₀,τ) = Φ(t,τ)` for every `τ` on the segment between `t₀` and `t`. This is the shape needed by
variation-of-constants, where `t₀` and `t` are the fixed integration endpoints and `τ` is the
integration variable — unlike `stateTransitionMatrix_comp`, which needs the *middle* point of the
three (there, `τ` would have to lie between the two fixed points, not the reverse).

Proof: `stateTransitionMatrix_comp` (with `τ` itself as the middle point) gives
`Φ(t,τ) * Φ(τ,t₀) = Φ(t,t₀)`; solve for `Φ(t,τ)` by right-multiplying by `Φ(t₀,τ)` and
cancelling `Φ(τ,t₀) * Φ(t₀,τ) = I` (P5.4). -/
@[blueprint "lem:stateTransitionMatrix-comp-base"
  (title := "Change of base time")
  (latexEnv := "lemma")
  (statement := /-- For every $\tau$ on the segment between $t_0$ and $t$,
    $\Phi(t, t_0)\,\Phi(t_0, \tau) = \Phi(t, \tau)$: composition through a fixed \emph{base}
    point.  This differs from \cref{thm:stateTransitionMatrix-comp} in which of the three times
    is required to lie between the others — here the two fixed integration endpoints are the
    outer ones and $\tau$ is free, which is the shape variation of constants needs. -/)
  (proof := /-- \cref{thm:stateTransitionMatrix-comp} with $\tau$ itself as the middle point
    gives $\Phi(t,\tau)\Phi(\tau,t_0) = \Phi(t,t_0)$; right-multiply by $\Phi(t_0,\tau)$ and
    cancel $\Phi(\tau,t_0)\Phi(t_0,\tau) = I$. -/)]
theorem stateTransitionMatrix_comp_base (hA : Continuous A) {t₀ t M : ℝ}
    (hA_le : ∀ r ∈ Set.uIcc t₀ t, ‖A r‖ ≤ M) {τ : ℝ} (hτ : τ ∈ Set.uIcc t₀ t) :
    stateTransitionMatrix A t t₀ * stateTransitionMatrix A t₀ τ = stateTransitionMatrix A t τ := by
  have hcomp := stateTransitionMatrix_comp hA hA_le hτ
  obtain ⟨hunit, hinv⟩ := stateTransitionMatrix_inv hA
    (fun r hr => hA_le r (Set.uIcc_subset_uIcc_left hτ hr))
  rw [← hcomp, mul_assoc, ← hinv,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit), mul_one]

/-- Continuity of the state transition matrix in its *second* argument, with the first held
fixed — the mirror image of `continuousOn_stateTransitionMatrix` (which varies the first
argument, base fixed). Needed whenever `Φ(t, ·)` appears as an integrand, as in the
variation-of-constants formula.

Proof: `Φ(τ,t)⁻¹ = Φ(t,τ)` by P5.4 (`stateTransitionMatrix_inv`), so `τ ↦ Φ(t,τ)` is the
composition of `τ ↦ Φ(τ,t)` (continuous by `continuousOn_stateTransitionMatrix`) with matrix
inversion, continuous at every unit (`continuousAt_matrix_inv`). -/
@[blueprint "lem:continuousOn-stateTransitionMatrix-snd"
  (title := "Continuity in the initial time")
  (latexEnv := "lemma")
  (statement := /-- With the first argument held fixed, $\tau \mapsto \Phi(t, \tau)$ is
    continuous on the segment between $t$ and $t_1$ — the mirror of
    \cref{lem:continuous-stateTransitionMatrix}, which varies the first argument.  Needed
    wherever $\Phi(t, \cdot)$ is an integrand, as in variation of constants. -/)
  (proof := /-- By \cref{thm:stateTransitionMatrix-inv}, $\Phi(t,\tau) = \Phi(\tau,t)^{-1}$, so
    the map is $\tau \mapsto \Phi(\tau,t)$ — continuous in its first argument — followed by
    matrix inversion, which is continuous at every unit. -/)]
theorem continuousOn_stateTransitionMatrix_snd (hA : Continuous A) {t t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t t₁, ‖A s‖ ≤ M) :
    ContinuousOn (fun τ => stateTransitionMatrix A t τ) (Set.uIcc t t₁) := by
  intro τ hτ
  have hA_le' : ∀ r ∈ Set.uIcc t τ, ‖A r‖ ≤ M := fun r hr =>
    hA_le r (Set.uIcc_subset_uIcc_left hτ hr)
  obtain ⟨hunit, hinv⟩ := stateTransitionMatrix_inv hA hA_le'
  -- `hunit : IsUnit (Φ(τ,t))`, `hinv : (Φ(τ,t))⁻¹ = Φ(t,τ)`.
  have hdet_unit : IsUnit (stateTransitionMatrix A τ t).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hring_cont : ContinuousAt Ring.inverse (stateTransitionMatrix A τ t).det := by
    rw [← hdet_unit.unit_spec]
    exact NormedRing.inverse_continuousAt hdet_unit.unit
  have hcont_swap : ContinuousWithinAt (fun τ' => stateTransitionMatrix A τ' t)
      (Set.uIcc t t₁) τ :=
    (continuous_stateTransitionMatrix hA _).continuousOn τ hτ
  refine ((continuousAt_matrix_inv _ hring_cont).comp_continuousWithinAt
    (f := fun τ' => stateTransitionMatrix A τ' t) hcont_swap).congr
    (fun τ' hτ' => ?_) hinv.symm
  exact (stateTransitionMatrix_inv hA
    (fun r hr => hA_le r (Set.uIcc_subset_uIcc_left hτ' hr))).2.symm

variable {U Y : Type*} [Fintype U] [Fintype Y] {B : ℝ → Matrix X U ℝ} {u : ℝ → U → ℝ}
variable {C : ℝ → Matrix Y X ℝ} {D : ℝ → Matrix Y U ℝ}

/-- **Integrating-factor step 1.** `w(t) := x₀ + ∫ τ in t₀..t, Φ(t₀,τ) *ᵥ (B(τ) *ᵥ u(τ))` has
derivative `Φ(t₀,t) *ᵥ (B(t) *ᵥ u(t))` — an *ordinary* FTC fact, since `t₀` (unlike the outer `t`
in `hasDerivAt_forcedResponse`) is fixed throughout the integrand: only the upper limit
depends on the differentiation variable. This avoids ever needing to differentiate `Φ` in its
second argument, only integrate it (`continuousOn_stateTransitionMatrix_snd`). -/
private lemma hasDerivAt_forcedResponse_w (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M)
    {t : ℝ} (ht : t ∈ Set.uIoo t₀ t₁) (x₀ : X → ℝ) :
    HasDerivAt (fun z => x₀ + ∫ τ in t₀..z, stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))
      (stateTransitionMatrix A t₀ t *ᵥ (B t *ᵥ u t)) t := by
  have hF_cont : ContinuousOn (fun τ => stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))
      (Set.uIcc t₀ t₁) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix_snd hA hA_le).prodMk
        (hB.matrix_mulVec hu).continuousOn)
  have hopen : IsOpen (Set.uIoo t₀ t₁) := by rw [← Set.Ioo_min_max]; exact isOpen_Ioo
  have hF_cont_at : ContinuousAt (fun τ => stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ)) t :=
    (hF_cont.mono Set.uIoo_subset_uIcc_self).continuousAt (hopen.mem_nhds ht)
  have hint : IntervalIntegrable (fun τ => stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))
      volume t₀ t :=
    (hF_cont.mono (Set.uIcc_subset_uIcc_left (Set.uIoo_subset_uIcc_self ht))).intervalIntegrable
  have hderiv := intervalIntegral.integral_hasDerivAt_right hint
    (ContinuousOn.stronglyMeasurableAtFilter (μ := volume) hopen
      (hF_cont.mono Set.uIoo_subset_uIcc_self) t ht)
    hF_cont_at
  exact hderiv.const_add x₀

/-- **Integrating-factor step 2.** `x(z) = Φ(z,t₀) *ᵥ w(z)`, algebraically, for `w` as in
`hasDerivAt_forcedResponse_w` — this is what lets differentiating `x` reduce to an ordinary
product rule on `Φ(·,t₀) *ᵥ w(·)` instead of a Leibniz rule.

Proof: push `Φ(z,t₀)` through the integral defining `w` (as a fixed continuous linear map), then
use `stateTransitionMatrix_comp_base` pointwise: `Φ(z,t₀) *ᵥ (Φ(t₀,τ) *ᵥ v) = Φ(z,τ) *ᵥ v`. -/
private lemma forcedResponse_eq_mulVec (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (x₀ : X → ℝ)
    {z : ℝ} (hz : z ∈ Set.uIcc t₀ t₁) :
    stateTransitionMatrix A z t₀ *ᵥ x₀ +
        ∫ τ in t₀..z, stateTransitionMatrix A z τ *ᵥ (B τ *ᵥ u τ) =
      stateTransitionMatrix A z t₀ *ᵥ
        (x₀ + ∫ τ in t₀..z, stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ)) := by
  rw [Matrix.mulVec_add]
  congr 1
  set L : (X → ℝ) →L[ℝ] (X → ℝ) :=
    LinearMap.toContinuousLinearMap (stateTransitionMatrix A z t₀).mulVecLin
  have hL_apply : ∀ v : X → ℝ, L v = stateTransitionMatrix A z t₀ *ᵥ v :=
    fun v => Matrix.mulVecLin_apply _ v
  have hA_le' : ∀ s ∈ Set.uIcc t₀ z, ‖A s‖ ≤ M := fun s hs =>
    hA_le s (Set.uIcc_subset_uIcc_left hz hs)
  have hcont : ContinuousOn (fun τ => stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))
      (Set.uIcc t₀ z) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix_snd hA hA_le').prodMk
        (hB.matrix_mulVec hu).continuousOn)
  have hL_comm := L.intervalIntegral_comp_comm (μ := volume) hcont.intervalIntegrable
  simp only [hL_apply] at hL_comm
  rw [← hL_comm]
  refine intervalIntegral.integral_congr fun τ hτ => ?_
  rw [Matrix.mulVec_mulVec (B τ *ᵥ u τ), stateTransitionMatrix_comp_base hA hA_le' hτ]

/-- **Integrating-factor step 3, matrix→CLM transport.** `M ↦ (v ↦ M *ᵥ v)`, as a continuous
linear map from matrices into `(X → ℝ) →L[ℝ] X → ℝ`. Needed to turn a *matrix*-valued
`HasDerivAt` (`hasDerivAt_stateTransitionMatrix`) into a `ContinuousLinearMap`-valued one, so
`HasDerivAt.clm_apply` can differentiate `z ↦ Φ(z,t₀) *ᵥ w(z)` as a product of two moving paths.

Built from `Matrix.mulVecBilin`, the curried linear (not yet continuous) version of `*ᵥ`, by
applying `LinearMap.toContinuousLinearMap` twice — once to continuify each value
`v ↦ M *ᵥ v` (inner map, domain `X → ℝ` is finite-dimensional), once to continuify the whole
assignment `M ↦ (that CLM)` (outer map, domain `Matrix X X ℝ` is finite-dimensional
too). -/
private noncomputable def matrixMulVecCLM :
    Matrix X X ℝ →L[ℝ] (X → ℝ) →L[ℝ] X → ℝ :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (Matrix.mulVecBilin ℝ ℝ))

omit [DecidableEq X] in
private lemma matrixMulVecCLM_apply (M : Matrix X X ℝ) (v : X → ℝ) :
    matrixMulVecCLM M v = M *ᵥ v := rfl

/-- **Integrating-factor step 3+4.** `z ↦ Φ(z,t₀) *ᵥ w(z)` solves `ẋ = A(t)x + B(t)u(t)` at
`t` — the ordinary product rule (`HasDerivAt.clm_apply`, via `matrixMulVecCLM`) applied to
`hasDerivAt_stateTransitionMatrix` and `hasDerivAt_forcedResponse_w`, simplified using
`Φ(t,t₀) * Φ(t₀,t) = Φ(t,t) = I` (`stateTransitionMatrix_comp_base`,
`stateTransitionMatrix_self`) to cancel the forcing term down to `B(t) *ᵥ u(t)`. -/
private lemma hasDerivAt_forcedResponse_mulVec (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M)
    {t : ℝ} (ht : t ∈ Set.uIoo t₀ t₁) (x₀ : X → ℝ) :
    HasDerivAt (fun z => stateTransitionMatrix A z t₀ *ᵥ
        (x₀ + ∫ τ in t₀..z, stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ)))
      (A t *ᵥ (stateTransitionMatrix A t t₀ *ᵥ
          (x₀ + ∫ τ in t₀..t, stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))) + B t *ᵥ u t) t := by
  have hΦ_deriv := (matrixMulVecCLM.hasFDerivAt
    (x := stateTransitionMatrix A t t₀)).comp_hasDerivAt t
    (hasDerivAt_stateTransitionMatrix hA _ _)
  have hderiv := hΦ_deriv.clm_apply (hasDerivAt_forcedResponse_w hA hB hu hA_le ht x₀)
  simp only [Function.comp_apply, matrixMulVecCLM_apply] at hderiv
  have hcancel : stateTransitionMatrix A t t₀ * stateTransitionMatrix A t₀ t = 1 := by
    rw [stateTransitionMatrix_comp_base hA
      (fun r hr => hA_le r (Set.uIcc_subset_uIcc_left (Set.uIoo_subset_uIcc_self ht) hr))
      Set.right_mem_uIcc, stateTransitionMatrix_self]
  rwa [Matrix.mulVec_mulVec (B t *ᵥ u t), hcancel, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec] at hderiv

/-- **Variation of constants: existence** (Hespanha, Theorem 5.2).
`x(t) := Φ(t,t₀) *ᵥ x₀ +
∫ τ in t₀..t, Φ(t,τ) *ᵥ (B(τ) *ᵥ u(τ))` solves the initial value problem
`ẋ = A(t) x + B(t) u(t)`, `x(t₀) = x₀`.

Proof: transfer `hasDerivAt_forcedResponse_mulVec` (the derivative of `Φ(·,t₀) *ᵥ w(·)`)
across the pointwise equality `x(z) = Φ(z,t₀) *ᵥ w(z)` (`forcedResponse_eq_mulVec`), valid
on the neighborhood `Set.uIcc t₀ t₁ ∈ 𝓝 t` since `t` is interior to it.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Theorem 5.2. -/
@[blueprint "thm:hasDerivAt-forcedResponse"
  (title := "Variation of constants: existence")
  (statement := /-- Hespanha, Theorem 5.2.  For continuous $A$, $B$ and $u$, the
    function
    \[
      x(t) := \Phi(t, t_0)x_0 + \int_{t_0}^{t} \Phi(t, \tau)B(\tau)u(\tau)\,d\tau
    \]
    satisfies $\dot x(t) = A(t)x(t) + B(t)u(t)$ at every interior $t$. -/)
  (proof := /-- The obstacle is that $t$ appears in both the upper limit and the integrand.
    Factor it out: with
    $w(t) := x_0 + \int_{t_0}^{t}\Phi(t_0,\tau)B(\tau)u(\tau)\,d\tau$, whose integrand does not
    depend on $t$, the fundamental theorem of calculus gives $w$ directly, and
    \cref{lem:stateTransitionMatrix-comp-base} shows $x(t) = \Phi(t,t_0)w(t)$.  Differentiating
    that product and cancelling $\Phi(t,t_0)\Phi(t_0,t) = I$ leaves the claim.  $\Phi$ is thus
    only ever integrated in its second argument, never differentiated there. -/)]
theorem hasDerivAt_forcedResponse (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M)
    {t : ℝ} (ht : t ∈ Set.uIoo t₀ t₁) (x₀ : X → ℝ) :
    HasDerivAt (fun z => stateTransitionMatrix A z t₀ *ᵥ x₀ +
        ∫ τ in t₀..z, stateTransitionMatrix A z τ *ᵥ (B τ *ᵥ u τ))
      (A t *ᵥ (stateTransitionMatrix A t t₀ *ᵥ x₀ +
          ∫ τ in t₀..t, stateTransitionMatrix A t τ *ᵥ (B τ *ᵥ u τ)) + B t *ᵥ u t) t := by
  have hopen : IsOpen (Set.uIoo t₀ t₁) := by rw [← Set.Ioo_min_max]; exact isOpen_Ioo
  have hderiv0 := hasDerivAt_forcedResponse_mulVec hA hB hu hA_le ht x₀
  rw [← forcedResponse_eq_mulVec hA hB hu hA_le x₀ (Set.uIoo_subset_uIcc_self ht)] at hderiv0
  refine hderiv0.congr_of_eventuallyEq ?_
  filter_upwards [Filter.mem_of_superset (hopen.mem_nhds ht) Set.uIoo_subset_uIcc_self] with z hz
  exact forcedResponse_eq_mulVec hA hB hu hA_le x₀ hz

/-- The forced response matches the initial value `x₀` at `t = t₀`: the forcing integral is over
the degenerate interval `[t₀,t₀]`, and `Φ(t₀,t₀) = I`. -/
@[blueprint "lem:forcedResponse-self"
  (title := "The forced response at the initial time")
  (latexEnv := "lemma")
  (statement := /-- The forced response (\cref{def:forcedResponse}) takes the value $x_0$ at
    $t = t_0$: the forcing integral is over the degenerate interval and $\Phi(t_0,t_0) = I$.
    Together with \cref{thm:hasDerivAt-forcedResponse} this makes it a solution of the initial
    value problem, not merely of the differential equation. -/)]
theorem forcedResponse_self (t₀ : ℝ) (x₀ : X → ℝ) :
    forcedResponse A B u t₀ x₀ t₀ = x₀ := by
  simp [forcedResponse, stateTransitionMatrix_self]

/-- **Variation of constants: uniqueness** (Hespanha, Theorem 5.2).
Any two integral solutions of the
forced LTV system `ẋ = A(t) x + B(t) u(t)` sharing the same initial value `x₀` coincide on the
segment between `t₀` and `t₁`.

Unlike the existence half, this needs no new machinery: for fixed `t`, `v ↦ A(t) v + B(t) u(t)`
is affine, hence globally Lipschitz, in `v`, so `continuous_dependence_ODE` (Theorem 3.4) applies
directly with zero perturbation `g := 0`, exactly as in `stateTransitionMatrix_mulVec_unique`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Theorem 5.2. -/
@[blueprint "thm:variationOfConstants-unique"
  (title := "Variation of constants: uniqueness")
  (statement := /-- Hespanha, Theorem 5.2.  Any two continuous integral solutions of
    the forced system $\dot x = A(t)x + B(t)u(t)$ with the same initial value $x_0$ agree on the
    segment between $t_0$ and $t_1$. -/)
  (proof := /-- For fixed $t$ the right-hand side $v \mapsto A(t)v + B(t)u(t)$ is affine in $v$,
    hence Lipschitz with constant $\max(M, 1)$ where $\|A\| \le M$.  Continuous dependence on
    initial conditions with zero perturbation then bounds $\|z_1(t) - z_2(t)\|$ by $0$.  The
    forcing term $B(t)u(t)$ is common to both solutions and cancels in the difference, so it
    never enters the Lipschitz estimate. -/)]
theorem variationOfConstants_unique (hA : Continuous A) (hB : Continuous B) (hu : Continuous u)
    {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) {x₀ : X → ℝ}
    {z₁ z₂ : ℝ → X → ℝ}
    (hz₁ : IsIntegralSolution t₀ t₁ z₁ x₀ (fun s v => A s *ᵥ v + B s *ᵥ u s))
    (hz₂ : IsIntegralSolution t₀ t₁ z₂ x₀ (fun s v => A s *ᵥ v + B s *ᵥ u s))
    (hz₁_cont : ContinuousOn z₁ (Set.uIcc t₀ t₁)) (hz₂_cont : ContinuousOn z₂ (Set.uIcc t₀ t₁)) :
    ∀ t ∈ Set.uIcc t₀ t₁, z₁ t = z₂ t := by
  -- The forcing term `B t *ᵥ u t` cancels in the difference, leaving the bound on `A t`.
  have hrhs_lip : ∀ t ∈ Set.uIcc t₀ t₁, ∀ v w : X → ℝ,
      ‖(A t *ᵥ v + B t *ᵥ u t) - (A t *ᵥ w + B t *ᵥ u t)‖ ≤ M * ‖v - w‖ := by
    intro t ht v w
    calc ‖(A t *ᵥ v + B t *ᵥ u t) - (A t *ᵥ w + B t *ᵥ u t)‖ = ‖A t *ᵥ (v - w)‖ := by
          rw [add_sub_add_right_eq_sub, Matrix.mulVec_sub]
      _ ≤ ‖A t‖ * ‖v - w‖ := Matrix.linfty_opNorm_mulVec _ _
      _ ≤ M * ‖v - w‖ := by gcongr; exact hA_le t ht
  exact eq_of_isIntegralSolution_of_norm_sub_le
    (((hA.comp continuous_fst).matrix_mulVec continuous_snd).add
      ((hB.comp continuous_fst).matrix_mulVec (hu.comp continuous_fst)))
    hrhs_lip hz₁ hz₂ hz₁_cont hz₂_cont

/-- **Variation of constants: output equation** (Hespanha, equation (5.8)).
`y(t) := C(t) x(t) + D(t)
u(t)`, for `x(t)` as in `hasDerivAt_forcedResponse`, splits into the *homogeneous response*
`C(t) Φ(t,t₀) x₀` and the *forced response* `∫ τ in t₀..t, C(t) Φ(t,τ) B(τ) u(τ) + D(t) u(t)`. -/
@[blueprint "lem:forcedResponse-output"
  (title := "Variation of constants: output equation")
  (latexEnv := "lemma")
  (statement := /-- (Hespanha, equation (5.8)).
    With $x$ as in
    \cref{thm:hasDerivAt-forcedResponse}, the output $y(t) = C(t)x(t) + D(t)u(t)$ splits
    into the homogeneous response and the forced response:
    \[
      y(t) = C(t)\Phi(t,t_0)x_0
             + \int_{t_0}^{t} C(t)\Phi(t,\tau)B(\tau)u(\tau)\,d\tau
             + D(t)u(t).
    \] -/)
  (proof := /-- $v \mapsto C(t)v$ is a continuous linear map and so commutes with the interval
    integral; the integrand is continuous by
    \cref{lem:continuousOn-stateTransitionMatrix-snd}. -/)]
theorem forcedResponse_output (hA : Continuous A) (hB : Continuous B) (hu : Continuous u)
    {t₀ t M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t, ‖A s‖ ≤ M) (x₀ : X → ℝ) :
    C t *ᵥ (stateTransitionMatrix A t t₀ *ᵥ x₀ +
        ∫ τ in t₀..t, stateTransitionMatrix A t τ *ᵥ (B τ *ᵥ u τ)) + D t *ᵥ u t =
      C t *ᵥ (stateTransitionMatrix A t t₀ *ᵥ x₀) +
        (∫ τ in t₀..t, C t *ᵥ (stateTransitionMatrix A t τ *ᵥ (B τ *ᵥ u τ))) + D t *ᵥ u t := by
  rw [Matrix.mulVec_add, add_assoc, add_assoc]
  congr 2
  -- `v ↦ C t *ᵥ v`, as a continuous linear map, commutes with the interval integral.
  set L : (X → ℝ) →L[ℝ] (Y → ℝ) := LinearMap.toContinuousLinearMap (C t).mulVecLin
  have hΦ_cont : ContinuousOn (fun τ => stateTransitionMatrix A t τ) (Set.uIcc t₀ t) := by
    rw [Set.uIcc_comm]
    exact continuousOn_stateTransitionMatrix_snd hA (by rwa [Set.uIcc_comm])
  have hcont : ContinuousOn (fun τ => stateTransitionMatrix A t τ *ᵥ (B τ *ᵥ u τ))
      (Set.uIcc t₀ t) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (hΦ_cont.prodMk (hB.matrix_mulVec hu).continuousOn)
  have hL_apply : ∀ v : X → ℝ, L v = C t *ᵥ v := fun v => Matrix.mulVecLin_apply (C t) v
  simpa [hL_apply] using
    (L.intervalIntegral_comp_comm (μ := volume) hcont.intervalIntegrable).symm

/-- The forced response is continuous on the closed segment between `t₀` and `t₁`, endpoints
included.

Proof: `forcedResponse_eq_mulVec` rewrites the response as `Φ(z,t₀) *ᵥ w(z)` with
`w(z) = x₀ + ∫ τ in t₀..z, Φ(t₀,τ) *ᵥ (B τ *ᵥ u τ)`, whose integrand does not depend on `z` —
only the limit does. Continuity of `w` is then the ordinary continuity of a primitive. -/
@[blueprint "lem:continuousOn-forcedResponse"
  (title := "Continuity of the forced response")
  (latexEnv := "lemma")
  (statement := /-- For continuous $A$, $B$ and $u$, the forced response
    (\cref{def:forcedResponse}) is continuous on the closed segment between $t_0$ and $t_1$,
    endpoints included. -/)
  (proof := /-- The integrating-factor identity rewrites the response as
    $\Phi(z,t_0)\,w(z)$ with
    $w(z) = x_0 + \int_{t_0}^{z}\Phi(t_0,\tau)B(\tau)u(\tau)\,\mathrm{d}\tau$, whose
    integrand does not depend on $z$ --- only the limit does.  Continuity of $w$ is then the
    ordinary continuity of a primitive, and $\Phi(\cdot,t_0)$ is continuous by
    \cref{lem:continuous-stateTransitionMatrix}. -/)]
theorem continuousOn_forcedResponse (hA : Continuous A) (hB : Continuous B) (hu : Continuous u)
    {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (x₀ : X → ℝ) :
    ContinuousOn (forcedResponse A B u t₀ x₀) (Set.uIcc t₀ t₁) := by
  have hg : ContinuousOn (fun τ => stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))
      (Set.uIcc t₀ t₁) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix_snd hA hA_le).prodMk
        (hB.matrix_mulVec hu).continuousOn)
  have hw : ContinuousOn
      (fun z => x₀ + ∫ τ in t₀..z, stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))
      (Set.uIcc t₀ t₁) :=
    continuousOn_const.add
      (intervalIntegral.continuousOn_primitive_interval (hg.integrableOn_compact isCompact_uIcc))
  have hprod : ContinuousOn
      (fun z => stateTransitionMatrix A z t₀ *ᵥ
        (x₀ + ∫ τ in t₀..z, stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))) (Set.uIcc t₀ t₁) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (((continuous_stateTransitionMatrix hA _).continuousOn).prodMk hw)
  exact hprod.congr fun z hz => forcedResponse_eq_mulVec hA hB hu hA_le x₀ hz

/-- **Variation of constants, integral form.** The forced response satisfies the integral
equation `x(t) = x₀ + ∫ s in t₀..t, (A(s) x(s) + B(s) u(s))` on the whole closed segment.

This is the differential statement `hasDerivAt_forcedResponse` upgraded to include the
endpoints, which the differential form cannot reach: its window has `t₀` as an endpoint for
every choice of `t₁`, so `t₀` is never interior to it. The integral form has no such
restriction, and `IsIntegralSolution.isIntegralCurveOn` converts it back into a derivative
statement valid at `t₀` itself. -/
@[blueprint "thm:isIntegralSolution-forcedResponse"
  (title := "Variation of constants, integral form")
  (statement := /-- The forced response (\cref{def:forcedResponse}) satisfies
    \[
      x(t) = x_0 + \int_{t_0}^{t}\bigl(A(s)x(s) + B(s)u(s)\bigr)\,\mathrm{d}s
    \]
    for every $t$ on the closed segment between $t_0$ and $t_1$.

    This is \cref{thm:hasDerivAt-forcedResponse} upgraded to include the endpoints, which
    the differential form cannot reach: its window has $t_0$ as an endpoint for every choice of
    $t_1$, so $t_0$ is never interior to it. -/)
  (proof := /-- The fundamental theorem of calculus, applied to the derivative on the open
    interval (\cref{thm:hasDerivAt-forcedResponse}) together with continuity on the
    closed one (\cref{lem:continuousOn-forcedResponse}), with
    \cref{lem:forcedResponse-self} fixing the initial value. -/)]
theorem isIntegralSolution_forcedResponse (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (x₀ : X → ℝ) :
    IsIntegralSolution t₀ t₁ (forcedResponse A B u t₀ x₀) x₀
      (fun s v => A s *ᵥ v + B s *ᵥ u s) := by
  have hx_cont := continuousOn_forcedResponse hA hB hu hA_le x₀
  have hrhs_cont : ContinuousOn
      (fun s => A s *ᵥ forcedResponse A B u t₀ x₀ s + B s *ᵥ u s) (Set.uIcc t₀ t₁) :=
    ((continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (hA.continuousOn.prodMk hx_cont)).add (hB.matrix_mulVec hu).continuousOn
  exact isIntegralSolution_of_hasDerivAt hx_cont hrhs_cont
    (fun t ht => hasDerivAt_forcedResponse hA hB hu hA_le ht x₀) (forcedResponse_self t₀ x₀)

/-- The homogeneous response starts at `x₀`: `Φ(t₀, t₀) = I`. -/
@[simp, blueprint "lem:homogeneousResponse-self"
  (title := "The homogeneous response at the initial time")
  (latexEnv := "lemma")
  (statement := /-- The homogeneous response (\cref{def:homogeneousResponse}) takes the value
    $x_{0}$ at $t = t_{0}$, since $\Phi(t_{0},t_{0}) = I$. -/)]
theorem homogeneousResponse_self (A : ℝ → Matrix X X ℝ) (t₀ : ℝ) (x₀ : X → ℝ) :
    homogeneousResponse A t₀ x₀ t₀ = x₀ := by
  simp [homogeneousResponse, stateTransitionMatrix_self]

/-- With the input switched off the forced response is the homogeneous response: the forcing
integral has a zero integrand. -/
@[simp, blueprint "lem:forcedResponse-zero-input"
  (title := "Zero input gives the homogeneous response")
  (latexEnv := "lemma")
  (statement := /-- With $u = 0$ the forced response (\cref{def:forcedResponse}) is the
    homogeneous response (\cref{def:homogeneousResponse}):
    $\Phi(t,t_0)x_0 + \int_{t_0}^{t}\Phi(t,\tau)B(\tau)\cdot 0\,\mathrm{d}\tau
      = \Phi(t,t_0)x_0$. -/)]
theorem forcedResponse_zero_input (B : ℝ → Matrix X U ℝ) (t₀ : ℝ) (x₀ : X → ℝ) :
    forcedResponse A B 0 t₀ x₀ = homogeneousResponse A t₀ x₀ := by
  funext t
  simp [forcedResponse, homogeneousResponse]

/-- A continuous `A` is bounded on every compact time segment. -/
private lemma exists_norm_le_uIcc (hA : Continuous A) (a b : ℝ) :
    ∃ M : ℝ, ∀ s ∈ Set.uIcc a b, ‖A s‖ ≤ M :=
  isCompact_uIcc.exists_bound_of_continuousOn hA.continuousOn

/-- Every solution of `ẋ = A(t) x` on a segment `[t₀, t₁]` is the homogeneous response from its
own initial state there.

Uniqueness, repackaged from `stateTransitionMatrix_mulVec_unique` in the differential rather
than the integral formulation. This is where Grönwall enters: together with
`isIntegralCurve_homogeneousResponse` it says the solutions from `t₀` are *exactly* the
responses `Φ(·, t₀) x₀`. -/
@[blueprint "thm:eq-homogeneousResponse-of-isIntegralCurveOn"
  (title := "Solutions are homogeneous responses")
  (statement := /-- Let $A$ be continuous and let $x$ solve $\dot x = A(t)x$ on
    $[t_{0}, t_{1}]$.  Then
    \[
      x(t) = \Phi(t, t_{0})\, x(t_{0}), \qquad \forall\, t \in [t_{0}, t_{1}].
    \] -/)
  (proof := /-- On $[t_{0}, t]$ the solution satisfies the integral equation
    (\cref{lem:isIntegralCurveOn-isIntegralSolution}), so uniqueness for the Peano--Baker
    solution (\cref{thm:stateTransitionMatrix-mulVec-unique}) identifies it with
    $\Phi(\cdot, t_{0}) x(t_{0})$ there. -/)]
theorem eq_homogeneousResponse_of_isIntegralCurveOn (hA : Continuous A) {z : ℝ → X → ℝ}
    {t₀ t₁ : ℝ} (hz : IsIntegralCurveOn z (fun t v => A t *ᵥ v) (Set.Icc t₀ t₁)) {t : ℝ}
    (ht : t ∈ Set.Icc t₀ t₁) : z t = homogeneousResponse A t₀ (z t₀) t := by
  obtain ⟨M, hM⟩ := exists_norm_le_uIcc hA t₀ t
  have hcurve : IsIntegralCurveOn z (fun r v => A r *ᵥ v) (Set.uIcc t₀ t) := by
    rw [Set.uIcc_of_le ht.1]
    exact hz.mono (Set.Icc_subset_Icc_right ht.2)
  have hz_cont : ContinuousOn z (Set.uIcc t₀ t) := fun r hr => (hcurve r hr).continuousWithinAt
  have hFx : ContinuousOn (fun r => A r *ᵥ z r) (Set.uIcc t₀ t) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (hA.continuousOn.prodMk hz_cont)
  exact stateTransitionMatrix_mulVec_unique hA hM (z t₀) (hcurve.isIntegralSolution hFx)
    hz_cont t Set.right_mem_uIcc

/-! ## The solution as a trajectory of the system

`ContinuousLTV` (`LinearSystems/Continuous.lean`) bundles the coefficient maps and
says what equation they satisfy. The results above are stated on `A` and `B` directly; this
section is the thin skin that restates them for the bundled object. -/

/-- **The forced response solves the state equation for all time**, as a function into coordinates:
`ż = A(t) z + B(t) u(t)` holds at every `t`, with a two-sided derivative.

Away from `t₀` this is `hasDerivAt_forcedResponse` on a window with `t` in its interior. At `t₀`
the two one-sided derivatives come from the integral form on `[t₀, t₀ + 1]` and `[t₀ - 1, t₀]`
and are glued. -/
theorem isIntegralCurve_forcedResponse (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) (t₀ : ℝ) (x₀ : X → ℝ) :
    IsIntegralCurve (forcedResponse A B u t₀ x₀) (fun t z => A t *ᵥ z + B t *ᵥ u t) := by
  -- A one-sided derivative at every point of any compact window, from the integral form.
  have key : ∀ t₁ : ℝ, ∀ t ∈ Set.uIcc t₀ t₁,
      HasDerivWithinAt (forcedResponse A B u t₀ x₀)
        ((A t *ᵥ forcedResponse A B u t₀ x₀ t + B t *ᵥ u t)) (Set.uIcc t₀ t₁) t := by
    intro t₁ t ht
    obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn (f := A)
      (s := Set.uIcc t₀ t₁) hA.continuousOn
    have hFx : ContinuousOn
        (fun r => A r *ᵥ forcedResponse A B u t₀ x₀ r + B r *ᵥ u r)
        (Set.uIcc t₀ t₁) :=
      ((continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
        (hA.continuousOn.prodMk (continuousOn_forcedResponse hA hB hu hM x₀))).add
        (hB.matrix_mulVec hu).continuousOn
    exact (isIntegralSolution_forcedResponse hA hB hu hM x₀).isIntegralCurveOn hFx t ht
  intro t
  rcases lt_trichotomy t t₀ with hlt | heq | hgt
  · obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn (f := A)
      (s := Set.uIcc t₀ (t - 1)) hA.continuousOn
    have hmem : t ∈ Set.uIoo t₀ (t - 1) := by
      rw [← Set.Ioo_min_max, min_eq_right (by linarith), max_eq_left (by linarith)]
      exact ⟨by linarith, hlt⟩
    exact hasDerivAt_forcedResponse hA hB hu hM hmem x₀
  · subst heq
    have hR : HasDerivWithinAt (forcedResponse A B u t x₀)
        ((A t *ᵥ forcedResponse A B u t x₀ t + B t *ᵥ u t)) (Set.Ici t) t := by
      refine (key (t + 1) t Set.left_mem_uIcc).mono_of_mem_nhdsWithin ?_
      rw [Set.uIcc_of_le (by linarith : t ≤ t + 1)]
      exact mem_nhdsWithin.2
        ⟨Set.Iio (t + 1), isOpen_Iio, Set.mem_Iio.2 (by linarith),
          fun r hr => ⟨hr.2, hr.1.le⟩⟩
    have hL : HasDerivWithinAt (forcedResponse A B u t x₀)
        ((A t *ᵥ forcedResponse A B u t x₀ t + B t *ᵥ u t)) (Set.Iic t) t := by
      refine (key (t - 1) t Set.left_mem_uIcc).mono_of_mem_nhdsWithin ?_
      rw [Set.uIcc_comm, Set.uIcc_of_le (by linarith : t - 1 ≤ t)]
      exact mem_nhdsWithin.2
        ⟨Set.Ioi (t - 1), isOpen_Ioi, Set.mem_Ioi.2 (by linarith),
          fun r hr => ⟨hr.1.le, hr.2⟩⟩
    have hunion := hR.union hL
    rw [Set.Ici_union_Iic] at hunion
    exact hunion.hasDerivAt Filter.univ_mem
  · obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn (f := A)
      (s := Set.uIcc t₀ (t + 1)) hA.continuousOn
    have hmem : t ∈ Set.uIoo t₀ (t + 1) := by
      rw [← Set.Ioo_min_max, min_eq_left (by linarith), max_eq_right (by linarith)]
      exact ⟨hgt, by linarith⟩
    exact hasDerivAt_forcedResponse hA hB hu hM hmem x₀

/-- **The homogeneous response solves `ż = A(t) z` for all time.** -/
theorem isIntegralCurve_homogeneousResponse (hA : Continuous A) (t₀ : ℝ) (x₀ : X → ℝ) :
    IsIntegralCurve (homogeneousResponse A t₀ x₀) (fun t z => A t *ᵥ z) := by
  have h := isIntegralCurve_forcedResponse (B := fun _ => (0 : Matrix X Unit ℝ))
    (u := (0 : ℝ → Unit → ℝ)) hA continuous_const continuous_const t₀ x₀
  rw [forcedResponse_zero_input] at h
  simpa using h

/-- `toEuclideanCLM`, which reads a matrix as an operator on Euclidean space, is continuous: it is
linear on a finite-dimensional space. -/
theorem continuous_toEuclideanCLM : Continuous (toEuclideanCLM (n := X) (𝕜 := ℝ)) :=
  LinearMap.continuous_of_finiteDimensional
    (toEuclideanCLM (n := X) (𝕜 := ℝ)).toAlgEquiv.toLinearMap

namespace ContinuousLTV

omit [Fintype U] [Fintype Y] in
/-- The **state transition operator** of a real LTV system: the Peano-Baker series `Φ(t, t₀)` of
the state matrix read as an operator `A(t)` on the Euclidean state space, in the Banach algebra
of continuous linear operators on that space (`PeanoBaker.lean`). -/
@[blueprint "def:continuousLTV-stateTransition"
  (title := "State transition operator of an LTV system")
  (statement := /-- The state transition matrix $\Phi(t, t_0)$ (\cref{def:stateTransitionMatrix})
    of $A$, acting on the Euclidean state space $\mathbb{R}^X$. -/)]
noncomputable def stateTransition (s : ContinuousLTV X U Y ℝ) (t t₀ : ℝ) :
    EuclideanSpace ℝ X →L[ℝ] EuclideanSpace ℝ X :=
  stateTransitionMatrix (fun t => toEuclideanCLM (n := X) (𝕜 := ℝ) (s.A t)) t t₀

omit [Fintype U] [Fintype Y] in
@[simp] lemma stateTransition_self (s : ContinuousLTV X U Y ℝ) (t : ℝ) (x : EuclideanSpace ℝ X) :
    s.stateTransition t t x = x := by
  simp [stateTransition, stateTransitionMatrix_self]

omit [Fintype U] [Fintype Y] in
/-- **The semigroup property**, on states: `Φ(t, σ) Φ(σ, τ) x = Φ(t, τ) x`, for all times in any
order. -/
@[blueprint "thm:continuousLTV-stateTransition-comp"
  (title := "Semigroup property of the state transition operator")
  (statement := /-- For $A$ continuous, $\Phi(t, \sigma)\,\Phi(\sigma, \tau)\,x = \Phi(t, \tau)\,x$
    for all $t, \sigma, \tau$ and every state $x$. -/)
  (proof := /-- \cref{thm:stateTransitionMatrix-mul} in the algebra of operators. -/)]
lemma stateTransition_comp (s : ContinuousLTV X U Y ℝ) (hA : Continuous s.A) (t σ τ : ℝ)
    (x : EuclideanSpace ℝ X) :
    s.stateTransition t σ (s.stateTransition σ τ x) = s.stateTransition t τ x := by
  rw [stateTransition, stateTransition, stateTransition,
    ← stateTransitionMatrix_mul (A := fun r => toEuclideanCLM (n := X) (𝕜 := ℝ) (s.A r))
      (continuous_toEuclideanCLM.comp hA) t σ τ]
  rfl

variable [DecidableEq U]

omit [Fintype Y] in
/-- The forced response of a system is a trajectory of that system — at every time, with a
two-sided derivative.

Nothing is assumed beyond continuity of `A`, `B` and `u`, and that is global, so the formula
solves the state equation on the whole line: for `t < t₀` the forcing integral simply runs
backwards. Restricting to an interval — `Set.Ici t₀`, the ray the stability predicates quantify
over — is `IsTrajectory.isTrajectoryOn`.

Away from `t₀` this is `hasDerivAt_forcedResponse` on a window with `t` in its interior,
which `uIoo` being unordered already supplies on both sides. At `t₀` itself no such window
exists, since the formula is anchored there; the two one-sided derivatives are taken from the
integral form on `[t₀, t₀+1]` and `[t₀-1, t₀]` and glued. -/
@[blueprint "thm:isTrajectory-forcedResponse"
  (title := "The forced response is a trajectory")
  (statement := /-- Let $s$ be a continuous-time linear system with continuous coefficients
    $A$ and $B$, and let $u$ be a continuous input.  Then the forced response
    (\cref{def:forcedResponse}) from any state $x_0$ at any time $t_0$ is a trajectory of $s$
    (\cref{def:continuousLTV-isTrajectory}) — it satisfies the state equation at every
    $t \in \mathbb{R}$, with a two-sided derivative.

    Restriction to an interval, in particular to the ray $[t_0,\infty)$ that the stability
    predicates quantify over, is \cref{lem:continuousSystem-isTrajectory-isTrajectoryOn}.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, Theorem 5.2.
  -/)
  (proof := /-- For $t \ne t_0$, apply \cref{thm:hasDerivAt-forcedResponse} on a window
    having $t$ in its interior; since the window is unordered this covers $t < t_0$ as well as
    $t > t_0$, and continuity of $A$ supplies the bound on the compact segment.

    At $t = t_0$ no such window exists, because the formula is anchored there and $t_0$ is an
    endpoint of every window.  Instead take the integral form
    (\cref{thm:isIntegralSolution-forcedResponse}) on $[t_0, t_0+1]$ and on $[t_0-1, t_0]$; each
    yields a one-sided derivative at $t_0$ (\cref{lem:isIntegralSolution-isIntegralCurveOn}),
    and the two glue to a two-sided one. -/)]
theorem isTrajectory_forcedResponse (s : ContinuousLTV X U Y ℝ) (hA : Continuous s.A)
    (hB : Continuous s.B) {u : ℝ → EuclideanSpace ℝ U} (hu : Continuous u) (t₀ : ℝ)
    (x₀ : X → ℝ) :
    s.IsTrajectory u (fun t => toLp 2 (forcedResponse s.A s.B (fun t => (u t).ofLp) t₀ x₀ t)) :=
  ContinuousSystem.isTrajectoryOn_univ.1 <| isTrajectoryOn_iff_ofLp.2 <| by
    simpa using (isIntegralCurve_forcedResponse hA hB
      ((PiLp.continuous_ofLp 2 _).comp hu) t₀ x₀).isIntegralCurveOn Set.univ

omit [Fintype Y] in
/-- The homogeneous response is a trajectory of the system under zero input.

No hypothesis on `B` appears: the forcing term is switched off, so only `A` is involved.
Hespanha's Definition 8.1 is stated about this map, so this is the form in which the solution
theory reaches the stability theory. -/
@[blueprint "thm:isTrajectory-homogeneousResponse"
  (title := "The homogeneous response is a trajectory")
  (statement := /-- For a continuous-time linear system with continuous coefficients, the
    homogeneous response (\cref{def:homogeneousResponse}) from any state $x_0$ at any time
    $t_0$ is a trajectory (\cref{def:continuousLTV-isTrajectory}) under zero input.

    Definition 8.1 is stated about this map, so this is the form in which the solution theory
    reaches the stability theory. -/)
  (proof := /-- Apply \cref{thm:hasDerivAt-stateTransitionMatrix} to the fixed state $x_0$. -/)]
theorem isTrajectory_homogeneousResponse (s : ContinuousLTV X U Y ℝ)
    (hA : Continuous s.A) (t₀ : ℝ) (x₀ : EuclideanSpace ℝ X) :
    s.IsTrajectory 0 (fun t => s.stateTransition t t₀ x₀) := fun t => by
  simpa [stateTransition] using
    (hasDerivAt_stateTransitionMatrix (A := fun r => toEuclideanCLM (n := X) (𝕜 := ℝ) (s.A r))
      (continuous_toEuclideanCLM.comp hA) t t₀).clm_apply
      (hasDerivAt_const t x₀)

omit [Fintype Y] in
/-- The homogeneous response is a trajectory of the unforced system on the forward ray.

`isTrajectory_homogeneousResponse` restricted to `[t₀, ∞)`, which is the interval the stability
predicates quantify over. -/
@[blueprint "thm:isTrajectoryOn-homogeneousResponse"
  (title := "The homogeneous response is a trajectory on the forward ray")
  (statement := /-- The homogeneous response (\cref{def:homogeneousResponse}) is a trajectory
    of the unforced system (\cref{def:continuousLTV-isTrajectoryOn}) on $[t_{0}, \infty)$. -/)
  (proof := /-- \cref{thm:isTrajectory-homogeneousResponse}, restricted to the ray by
    \cref{lem:continuousSystem-isTrajectory-isTrajectoryOn}. -/)]
theorem isTrajectoryOn_homogeneousResponse (s : ContinuousLTV X U Y ℝ)
    (hA : Continuous s.A) (t₀ : ℝ) (x₀ : EuclideanSpace ℝ X) :
    s.IsTrajectoryOn 0 (fun t => s.stateTransition t t₀ x₀) (Set.Ici t₀) :=
  (isTrajectory_homogeneousResponse s hA t₀ x₀).isTrajectoryOn _

omit [Fintype Y] in
/-- Every trajectory of the unforced system is its own homogeneous response.

The integrating factor: along a trajectory `x`, `Φ(t₀, r) x(r)` has derivative
`-Φ(t₀, r) A(r) x(r) + Φ(t₀, r) A(r) x(r) = 0` (`hasDerivAt_stateTransitionMatrix_snd`), so it
is constant, equal to `x(t₀)`; apply `Φ(t, t₀)`. -/
@[blueprint "thm:eq-homogeneousResponse-of-isTrajectoryOn"
  (title := "Trajectories of the unforced system are homogeneous responses")
  (statement := /-- Let $s$ have continuous $A$ and let $\varphi$ be a trajectory of the
    unforced system on $[t_{0}, t_{1}]$ (\cref{def:continuousLTV-isTrajectoryOn}).  Then
    $\varphi(t) = \Phi(t, t_{0})\,\varphi(t_{0})$ for every $t \in [t_{0}, t_{1}]$
    (\cref{def:continuousLTV-stateTransition}). -/)
  (proof := /-- $r \mapsto \Phi(t_0, r)\,\varphi(r)$ has derivative
    $-\Phi(t_0, r) A(r) \varphi(r) + \Phi(t_0, r) A(r) \varphi(r) = 0$
    (\cref{thm:hasDerivAt-stateTransitionMatrix-snd}), so it is constant on $[t_0, t_1]$, equal
    to $\varphi(t_0)$.  Apply $\Phi(t, t_0)$ and use
    \cref{thm:continuousLTV-stateTransition-comp}. -/)]
theorem eq_homogeneousResponse_of_isTrajectoryOn (s : ContinuousLTV X U Y ℝ)
    (hA : Continuous s.A) {x : ℝ → EuclideanSpace ℝ X} {t₀ t₁ : ℝ}
    (hx : s.IsTrajectoryOn 0 x (Set.Icc t₀ t₁)) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    x t = s.stateTransition t t₀ (x t₀) := by
  have hd : ∀ r ∈ Set.Icc t₀ t₁,
      HasDerivWithinAt (fun r => s.stateTransition t₀ r (x r)) 0 (Set.Icc t₀ t₁) r := by
    intro r hr
    convert ((hasDerivAt_stateTransitionMatrix_snd
      (A := fun r => toEuclideanCLM (n := X) (𝕜 := ℝ) (s.A r))
      (continuous_toEuclideanCLM.comp hA) t₀ r).hasDerivWithinAt).clm_apply
        (hx r hr) using 1
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_mul', Function.comp_apply,
      ContinuousSystem.vectorField_apply, Pi.zero_apply, toContinuousSystem_F, map_zero, add_zero]
    rw [eq_comm, neg_add_eq_zero]
    rfl
  have h_const : s.stateTransition t₀ t (x t) = x t₀ := by
    simpa using constant_of_has_deriv_right_zero (fun r hr => (hd r hr).continuousWithinAt)
      (fun r hr => (hd r (Set.Ico_subset_Icc_self hr)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hr)) t ht
  rw [← h_const, stateTransition_comp s hA, stateTransition_self]

omit [Fintype Y] in
/-- **The unforced system of an LTV system is forward complete.**  Every trajectory segment is
the restriction of a homogeneous response, which is a trajectory for all time. -/
@[blueprint "thm:continuousLTV-isForwardComplete-zeroInput"
  (title := "Linear systems are forward complete")
  (statement := /-- If $A$ is continuous, the unforced system
    (\cref{def:continuousSystem-zeroInput}) of \cref{def:continuousLTV-toContinuousSystem} is
    forward complete (\cref{def:continuousSystem-isForwardComplete}). -/)
  (proof := /-- A trajectory on $[t_0, t_1]$ agrees there with the homogeneous response from its
    initial state (\cref{thm:eq-homogeneousResponse-of-isTrajectoryOn}), which is a trajectory
    on $[t_0, \infty)$ (\cref{thm:isTrajectoryOn-homogeneousResponse}). -/)]
theorem isForwardComplete_zeroInput (s : ContinuousLTV X U Y ℝ) (hA : Continuous s.A) :
    s.toContinuousSystem.zeroInput.IsForwardComplete (fun _ => ()) :=
  fun t₀ _ x _ hx _ => ⟨fun t => s.stateTransition t t₀ (x t₀),
    isTrajectoryOn_homogeneousResponse s hA t₀ (x t₀),
    fun _ ht => (eq_homogeneousResponse_of_isTrajectoryOn s hA hx ht).symm⟩

omit [Fintype Y] in
/-- **The unforced system of an LTV system has unique solutions**: two trajectories on a segment
that agree at its start are both the homogeneous response from that state. -/
@[blueprint "thm:continuousLTV-hasUniqueSolutions-zero"
  (title := "Linear systems have unique solutions")
  (statement := /-- If $A$ is continuous, the system of \cref{def:continuousLTV-toContinuousSystem}
    has unique solutions (\cref{def:continuousSystem-hasUniqueSolutions}) under zero input. -/)
  (proof := /-- Both trajectories are the homogeneous response from their common initial state
    (\cref{thm:eq-homogeneousResponse-of-isTrajectoryOn}). -/)]
theorem hasUniqueSolutions_zero (s : ContinuousLTV X U Y ℝ) (hA : Continuous s.A) :
    s.toContinuousSystem.HasUniqueSolutions 0 := fun _ _ x y hx hy h₀ _ ht => by
  rw [eq_homogeneousResponse_of_isTrajectoryOn s hA hx ht,
    eq_homogeneousResponse_of_isTrajectoryOn s hA hy ht, h₀]

omit [Fintype Y] in
/-- **The state transition map of a linear system is its state transition operator**: under zero
input, the general state transition map `φ(t; t₀, x₀)` of `s`
(`ContinuousSystem.stateTransitionMap`) is `Φ(t, t₀) x₀`, for `t ≥ t₀`.

The general theory of continuous-time systems therefore applies to linear systems with no
translation layer. -/
@[blueprint "thm:continuousLTV-stateTransitionMap-zero"
  (title := "The state transition map of a linear system")
  (statement := /-- If $A$ is continuous, then under zero input the state transition map
    (\cref{def:continuousSystem-stateTransitionMap}) of the system of
    \cref{def:continuousLTV-toContinuousSystem} is
    \[
      \varphi(t; t_0, x_0) = \Phi(t, t_0)\,x_0, \qquad t \ge t_0,
    \]
    with $\Phi$ the state transition operator (\cref{def:continuousLTV-stateTransition}). -/)
  (proof := /-- The homogeneous response is a trajectory on $[t_0, t]$
    (\cref{thm:isTrajectoryOn-homogeneousResponse}) and solutions are unique
    (\cref{thm:continuousLTV-hasUniqueSolutions-zero}), so it is given by the state transition
    map (\cref{lem:continuousSystem-eq-stateTransitionMap}). -/)]
theorem stateTransitionMap_zero (s : ContinuousLTV X U Y ℝ) (hA : Continuous s.A) {t₀ t : ℝ}
    (ht : t₀ ≤ t) (x₀ : EuclideanSpace ℝ X) :
    s.toContinuousSystem.stateTransitionMap 0 t t₀ x₀ = s.stateTransition t t₀ x₀ := by
  have h := ContinuousSystem.eq_stateTransitionMap (hasUniqueSolutions_zero s hA)
    (IsIntegralCurveOn.mono (isTrajectoryOn_homogeneousResponse s hA t₀ x₀)
      Set.Icc_subset_Ici_self) t ⟨ht, le_rfl⟩
  rw [h, stateTransition_self]

end ContinuousLTV

end LinearSystems

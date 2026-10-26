import LeanForControl.Analysis.FrechetDerivative
import LeanForControl.MatrixAlgebra.QuadraticForm
import LeanForControl.MatrixAlgebra.Complex
import LeanForControl.LinearSystems.Stability.DefsStability
import LeanForControl.LinearSystems.Stability.Continuous.LyapunovEquation
import LeanForControl.LinearSystems.Stability.Continuous.InstabilityCertificate
import LeanForControl.Stability.Continuous.LyapunovTheorems
import LeanForControl.Stability.Continuous.Chetaev
import LeanForControl.Stability.Continuous.Converse
import LeanForControl.LinearSystems.Stability.Continuous.DifferentialLyapunov
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Architect

/-!
# `Stability.Continuous.Linearization` — Lyapunov's indirect method

The stability of an equilibrium of `ẋ = f(x)` is decided by its linearization `A = Df(x_eq)`,
except in the critical case.  Both branches build a quadratic certificate from `A` and absorb the
nonlinear remainder of `f` near `x_eq`
(`MatrixAlgebra.exists_abs_fderiv_centeredQuadraticForm_remainder_le`).

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.7; Hahn, *Stability of Motion*.

## Main results

* `hurwitz_linearization_locally_exponentially_stable` — the **stable branch**: if `A` is
  Hurwitz, `x_eq` is locally exponentially stable.  A positive-definite solution of the Lyapunov
  equation `AᵀP + PA = -I` gives the quadratic Lyapunov function `(x - x_eq)ᵀ P (x - x_eq)`.
* `unstable_of_exists_complex_eigenvalue_re_pos` — the **unstable branch**: if `A` has an
  eigenvalue with positive real part, `x_eq` is unstable.  A shifted Lyapunov inequality gives a
  quadratic Chetaev function (`Stability.Continuous.Chetaev`).
* `unstable_linear_of_eigenvalue_re_pos` — the unstable branch for a linear system `ẋ = A x`,
  which is its own linearization.

Both are stated for any system whose state equation is `ẋ = f(x)` (`s.F t x () = f x`).
-/

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## The stable branch -/

section Stable

open Filter Set Topology
open scoped RealInnerProductSpace
open LinearSystems MatrixAlgebra

/-- Near an equilibrium, a quadratic Lyapunov function solving the identity-forced
Lyapunov equation has a uniform negative quadratic Lie-derivative bound.

Reference: adapted from the quadratic-Lyapunov proof of the stable branch of Lyapunov's
indirect method; Khalil, *Nonlinear Systems*. -/
private theorem exists_centeredQuadraticForm_decay
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (A P : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hLyap : ContinuousLyapunovEquation A P 1) :
    ∃ r > 0, ∀ x : ℝⁿ, ‖x - x_eq‖ < r →
      fderiv ℝ (centeredQuadraticForm P x_eq) x (f x) ≤
        -(1 / 2 : ℝ) * ‖x - x_eq‖ ^ 2 := by
  obtain ⟨r, hr, hrem⟩ :=
    exists_abs_fderiv_centeredQuadraticForm_remainder_le A P hf hJac
      (c := 1 / 2) (by norm_num)
  refine ⟨r, hr, ?_⟩
  intro x hx
  let y : ℝⁿ := x - x_eq
  let e : ℝⁿ := f x - f x_eq -
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A y
  have herror : fderiv ℝ (centeredQuadraticForm P x_eq) x e ≤ (1 / 2 : ℝ) * ‖y‖ ^ 2 :=
    (le_abs_self _).trans (hrem x hx)
  have hf_split : f x =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A y + e := by
    dsimp [e]
    rw [heq]
    abel
  rw [hf_split, map_add]
  calc
    fderiv ℝ (centeredQuadraticForm P x_eq) x
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A y) +
        fderiv ℝ (centeredQuadraticForm P x_eq) x e
        ≤ -‖y‖ ^ 2 + (1 / 2 : ℝ) * ‖y‖ ^ 2 := by
          rw [fderiv_centeredQuadraticForm_linear hLyap]
          simpa [y] using add_le_add_left herror (-‖y‖ ^ 2)
    _ = -(1 / 2 : ℝ) * ‖y‖ ^ 2 := by ring
    _ = -(1 / 2 : ℝ) * ‖x - x_eq‖ ^ 2 := by rfl

/-- A positive-definite solution of the identity-forced Lyapunov equation for the linearization
makes the quadratic form `(x - x_eq)ᵀ P (x - x_eq)` an exponential Lyapunov function of the
nonlinear system on a small ball about `x_eq`, with exponent `2`: it is sandwiched between
`m‖x - x_eq‖²` and `(‖P‖ + 1)‖x - x_eq‖²` and decreases at rate `½‖x - x_eq‖²`. -/
private theorem isExponentialLyapunovFunction_of_continuousLyapunovEquation
    (hn : 0 < n) {Y : Type*} {sys : ContinuousSystem ℝⁿ Unit Y} {f : ℝⁿ → ℝⁿ}
    (hF : ∀ t x, sys.F t x () = f x) {x_eq : ℝⁿ}
    (A P : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hP : P.PosDef) (hLyap : ContinuousLyapunovEquation A P 1) :
    ∃ r > 0, sys.IsExponentialLyapunovFunction (fun _ => centeredQuadraticForm P x_eq) x_eq
      (Metric.ball x_eq r) 2 := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨r, hr, hdecay⟩ := exists_centeredQuadraticForm_decay A P hf heq hJac hLyap
  obtain ⟨m, hm, hm_lower⟩ := exists_pos_mul_norm_sq_le_quadraticForm P hP
  let p : ℝⁿ →L[ℝ] ℝⁿ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P
  have hV : ContDiff ℝ 1 (centeredQuadraticForm P x_eq) :=
    (centeredQuadraticForm_contDiff P x_eq).of_le (by norm_num)
  refine ⟨r, hr, Metric.ball_mem_nhds x_eq hr,
    fun t _ x _ => (hV.differentiable one_ne_zero x).comp (t, x) differentiableAt_snd,
    two_pos, m, hm, ‖p‖ + 1, by positivity, 1 / 2, by norm_num,
    fun t _ x hx => ⟨?_, ?_, ?_⟩⟩
  · rw [Real.rpow_two]
    simpa [centeredQuadraticForm] using hm_lower (x - x_eq)
  · rw [Real.rpow_two]
    calc centeredQuadraticForm P x_eq x ≤ ‖p‖ * ‖x - x_eq‖ ^ 2 := by
          simpa [centeredQuadraticForm, p] using quadraticForm_le_opNorm_mul_norm_sq P (x - x_eq)
      _ ≤ (‖p‖ + 1) * ‖x - x_eq‖ ^ 2 := by gcongr; linarith
  · rw [Real.rpow_two, ContinuousSystem.lieDerivative,
      lieDerivative_const ((hV.differentiable one_ne_zero) x)]
    simp only [hF]
    linarith [hdecay x (by simpa [Metric.mem_ball, dist_eq_norm] using hx)]

/-- **Stable branch of Lyapunov's indirect method.** If the Jacobian at a `C¹`
equilibrium is Hurwitz, then the equilibrium is locally exponentially stable on every
finite forward solution segment.

Reference: Khalil, *Nonlinear Systems*.
-/
@[blueprint "thm:hurwitz-linearization-locally-exponentially-stable"
  (title := "Lyapunov's indirect method, stable branch")
  (statement := /-- Let $f : \mathbb{R}^n \to \mathbb{R}^n$ be $C^1$, and let
    $x_{\rm eq}$ be an equilibrium. If its Jacobian $A$ at the equilibrium is
    Hurwitz, then $x_{\rm eq}$ is locally exponentially stable
    (\cref{def:continuousSystem-locallyExponentiallyStable}) for any system whose state
    equation is $\dot x = f(x)$.

    Reference: Khalil, \emph{Nonlinear Systems}.
  -/)
  (proof := /-- Solve the identity-forced Lyapunov equation for a positive-definite
    $P$; after absorbing the $o(\|x-x_{\rm eq}\|)$ linearization remainder on a small ball,
    $V(x)=(x-x_{\rm eq})^{\mathsf T}P(x-x_{\rm eq})$ is an exponential Lyapunov function with
    exponent $2$ there, so
    \cref{thm:continuousSystem-isExponentialLyapunovFunction-locallyExponentiallyStable}
    applies. -/)]
theorem hurwitz_linearization_locally_exponentially_stable {Y : Type*}
    {sys : ContinuousSystem ℝⁿ Unit Y} {f : ℝⁿ → ℝⁿ} (hF : ∀ t x, sys.F t x () = f x) {x_eq : ℝⁿ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hA : IsHurwitz A) :
    sys.LocallyExponentiallyStable x_eq := by
  by_cases hn0 : n = 0
  · subst n
    refine ⟨1, one_pos, 1, one_pos, 1, one_pos, fun t₀ _ t₁ φ _ _ t _ => ?_⟩
    rw [Subsingleton.elim (φ t) x_eq, Subsingleton.elim (φ t₀) x_eq]
    simp
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    obtain ⟨P, hP, hLyap, _⟩ :=
      hA.exists_posDef_unique_solution_continuous_lyapunov 1 Matrix.PosDef.one
    obtain ⟨r, -, hV⟩ :=
      isExponentialLyapunovFunction_of_continuousLyapunovEquation hn hF A P hf heq hJac hP hLyap
    exact hV.locallyExponentiallyStable

end Stable

/-! ## The unstable branch -/

section Unstable

open Filter Function Metric Set Topology
open scoped ContDiff NNReal Topology

open Matrix

/-- A positive value of a quadratic form gives positive points arbitrarily
close to its center by scaling the witnessing direction.

Supplies the seed point of the Chetaev cone: the certificate is positive somewhere in every
neighbourhood of the equilibrium. -/
private theorem exists_centered_quadratic_seed
    (H : Matrix (Fin n) (Fin n) ℝ) (x_eq w : ℝⁿ) (hw : w ≠ 0)
    (hHw : 0 < MatrixAlgebra.quadraticForm H w)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∃ x, ‖x - x_eq‖ < min δ ρ ∧
      0 < MatrixAlgebra.centeredQuadraticForm H x_eq x := by
  let d := min δ ρ
  have hd : 0 < d := lt_min hδ hρ
  have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let s := d / (2 * ‖w‖)
  have hs : 0 < s := div_pos hd (by positivity)
  refine ⟨x_eq + s • w, ?_, ?_⟩
  · simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    have hs_norm : s * ‖w‖ = d / 2 := by
      dsimp [s]
      field_simp
    rw [hs_norm]
    linarith
  · rw [MatrixAlgebra.centeredQuadraticForm]
    simp only [add_sub_cancel_left]
    rw [MatrixAlgebra.quadraticForm_smul]
    positivity

/-- A quadratic Chetaev certificate for the shifted linearization implies
forward instability of the nonlinear equilibrium.

The positive-definite shifted Lie matrix supplies strict growth on the cone
where the quadratic form is positive.  The `C¹` remainder is absorbed
on a sufficiently small ball.

Reference: Hahn, *Stability of Motion* (quadratic Chetaev construction).
-/
private theorem unstable_of_quadratic_certificate {Y : Type*} {s : ContinuousSystem ℝⁿ Unit Y}
    {f : ℝⁿ → ℝⁿ} (hF : ∀ t x, s.F t x () = f x) {x_eq : ℝⁿ}
    (A H : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hα : 0 < α)
    (hshift : (H * A + Aᵀ * H - (2 * α) • H).PosDef)
    (w : ℝⁿ) (hw : w ≠ 0)
    (hHw : 0 < MatrixAlgebra.quadraticForm H w) :
    s.Unstable x_eq := by
  have hn : n ≠ 0 := by
    intro hnzero
    subst n
    exact hw (Subsingleton.elim w 0)
  letI : NeZero n := ⟨hn⟩
  let G : Matrix (Fin n) (Fin n) ℝ := H * A + Aᵀ * H - (2 * α) • H
  have hG : G.PosDef := by simpa [G] using hshift
  obtain ⟨m, hm, hm_lower⟩ :=
    MatrixAlgebra.exists_pos_mul_norm_sq_le_quadraticForm G hG
  let p : ℝⁿ →L[ℝ] ℝⁿ :=
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H
  have hp_nonneg : 0 ≤ ‖p‖ := norm_nonneg p
  obtain ⟨r, hr, hrem⟩ :=
    MatrixAlgebra.exists_abs_fderiv_centeredQuadraticForm_remainder_le A H hf hJac
      (c := m / 2) (by linarith)
  let ρ : ℝ := r / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let V : ℝⁿ → ℝ := MatrixAlgebra.centeredQuadraticForm H x_eq
  apply ContinuousSystem.unstable_of_exponential_chetaev hF hf
    ((MatrixAlgebra.centeredQuadraticForm_contDiff H x_eq).of_le (by norm_num))
      hρ hα hp_nonneg
  · intro x hx
    simpa [V, MatrixAlgebra.centeredQuadraticForm, p] using
      MatrixAlgebra.abs_quadraticForm_le H (x - x_eq)
  · intro x hx
    let y : ℝⁿ := x - x_eq
    let e : ℝⁿ := f x - f x_eq -
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A y
    have hy_r : ‖y‖ < r := by
      have : ‖x - x_eq‖ ≤ r / 2 := by simpa [ρ] using hx
      dsimp [y]
      linarith
    have herror_bound : |fderiv ℝ V x e| ≤ (m / 2) * ‖y‖ ^ 2 := hrem x hy_r
    have hf_split : f x =
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A y + e := by
      dsimp [e]
      rw [heq]
      abel
    have hmatrix : H * A + Aᵀ * H = G + (2 * α) • H := by
      dsimp [G]
      abel
    have hlinear :
        fderiv ℝ V x
            (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A y) =
          MatrixAlgebra.quadraticForm G y + 2 * α * V x := by
      rw [show V = MatrixAlgebra.centeredQuadraticForm H x_eq by rfl]
      rw [MatrixAlgebra.fderiv_centeredQuadraticForm_apply_matrix]
      rw [hmatrix]
      rw [MatrixAlgebra.quadraticForm_matrix_add,
        MatrixAlgebra.quadraticForm_matrix_smul]
      rfl
    have hG_lower : m * ‖y‖ ^ 2 ≤ MatrixAlgebra.quadraticForm G y :=
      hm_lower y
    rw [hf_split, map_add, hlinear]
    have herr_lower : -(m / 2 * ‖y‖ ^ 2) ≤ fderiv ℝ V x e :=
      (neg_le_of_abs_le herror_bound)
    nlinarith [sq_nonneg ‖y‖]
  · intro δ hδ
    exact exists_centered_quadratic_seed H x_eq w hw hHw hρ hδ

open Matrix

/-- A `C¹` equilibrium is forward unstable if its Jacobian has some complex
eigenvalue with positive real part.

Here existence of an eigenvalue is stated concretely by a nonzero eigenvector,
matching the repository's matrix spectral API.

Reference: Khalil, *Nonlinear Systems* (Lyapunov's indirect method).
-/
@[blueprint "thm:positive-real-eigenvalue-unstable"
  (title := "Lyapunov's indirect method, unstable branch")
  (statement := /-- Let $f:\mathbb R^n\to\mathbb R^n$ be $C^1$ with
    $f(x_{\rm eq})=0$.  If the Jacobian at $x_{\rm eq}$ has a complex
    eigenvalue with positive real part, then $x_{\rm eq}$ is unstable
    (\cref{def:continuousSystem-unstable}) for any system whose state equation is
    $\dot x = f(x)$.

    Reference: Khalil, \emph{Nonlinear Systems} (Lyapunov's indirect method).
  -/)
  (proof := /-- Build the real quadratic certificate supplied by
    \cref{thm:positive-real-eigenvalue-quadratic-certificate}, absorb the
    first-order nonlinear remainder on a small ball, and apply the exponential
    Chetaev criterion. -/)]
theorem unstable_of_exists_complex_eigenvalue_re_pos {Y : Type*}
    {s : ContinuousSystem ℝⁿ Unit Y} {f : ℝⁿ → ℝⁿ} (hF : ∀ t x, s.F t x () = f x) {x_eq : ℝⁿ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f)
    (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hunstable : ∃ (μ : ℂ) (v : Fin n → ℂ),
      v ≠ 0 ∧ A.complexify *ᵥ v = μ • v ∧ 0 < μ.re) :
    s.Unstable x_eq := by
  obtain ⟨μ, v, hv, heig, hμ⟩ := hunstable
  obtain ⟨α, H, w, hα, _hH, hw, hHw, hshift⟩ :=
    LinearSystems.exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos
      A hv heig hμ
  exact unstable_of_quadratic_certificate hF A H α hf heq hJac hα hshift w hw hHw

/-- A linear system `ẋ = A x` is unstable at the origin when `A` has a complex eigenvalue
with positive real part.  An equilibrium `x_eq` of the affine field `x ↦ A (x - x_eq)` is the
same statement in the coordinate `x - x_eq`.

It is the nonlinear theorem `unstable_of_exists_complex_eigenvalue_re_pos` for the linear
field, which is its own linearization.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.7.
-/
@[blueprint "thm:unstable-linear-of-eigenvalue-re-pos"
  (title := "Instability of a linear system")
  (statement := /-- If $A \in \mathbb{R}^{n \times n}$ has a complex eigenvalue $\mu$ with
    $\operatorname{Re}\mu > 0$, then the origin is unstable
    (\cref{def:continuousSystem-unstable}) for any system on $\mathbb{R}^n$ whose state
    equation is $\dot x = A x$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.7.
  -/)
  (proof := /-- The field $x \mapsto Ax$ is $C^1$, vanishes at $0$ and is its own Jacobian, so
    this is \cref{thm:positive-real-eigenvalue-unstable} at $x_{\mathrm{eq}} = 0$. -/)]
theorem unstable_linear_of_eigenvalue_re_pos {Y : Type*} {s : ContinuousSystem ℝⁿ Unit Y}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hF : ∀ t x, s.F t x () = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A x)
    (mu : ℂ) (v : Fin n → ℂ) (hv : v ≠ 0) (hAv : A.complexify *ᵥ v = mu • v)
    (hmu : 0 < mu.re) :
    s.Unstable 0 :=
  unstable_of_exists_complex_eigenvalue_re_pos hF A
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A).contDiff (map_zero _)
    (ContinuousLinearMap.fderiv _) ⟨mu, v, hv, hAv, hmu⟩

end Unstable

/-! ## Time-varying systems -/

section TimeVarying

open Set Metric Matrix LinearSystems MatrixAlgebra
open scoped NNReal

/-- **The linearization remainder is quadratic**: with `f(t, x_eq) = 0` and `∂f/∂x(t, ·)`
`L₁`-Lipschitz on the ball, `‖A(t)(x - x_eq) - f(t, x)‖ ≤ L₁ ‖x - x_eq‖²` there. -/
private lemma norm_linearization_remainder_le {Y : Type*} {s : ContinuousSystem ℝⁿ Unit Y}
    {x_eq : ℝⁿ} {r : ℝ} (hr : 0 < r) (h_eq : ∀ t : ℝ, s.F t x_eq () = 0)
    (hf : ContDiffOn ℝ 1 (fun p : ℝ × ℝⁿ => s.F p.1 p.2 ()) (univ ×ˢ ball x_eq r))
    {L₁ : ℝ≥0} (hL₁ : ∀ t : ℝ, LipschitzOnWith L₁ (fderiv ℝ (fun x => s.F t x ())) (ball x_eq r))
    (t : ℝ) {x : ℝⁿ} (hx : x ∈ ball x_eq r) :
    ‖fderiv ℝ (fun y => s.F t y ()) x_eq (x - x_eq) - s.F t x ()‖ ≤ L₁ * ‖x - x_eq‖ ^ 2 := by
  have h_diff : ∀ y ∈ ball x_eq r, HasFDerivWithinAt (fun x => s.F t x ())
      (fderiv ℝ (fun x => s.F t x ()) y) (ball x_eq r) y := fun y hy =>
    (((hf.contDiffAt (prod_mem_nhds Filter.univ_mem (isOpen_ball.mem_nhds hy))).differentiableAt
      one_ne_zero).comp y ((differentiableAt_const t).prodMk differentiableAt_id)).hasFDerivAt
      |>.hasFDerivWithinAt
  have h := (convex_ball x_eq r).norm_image_sub_sub_le_of_lipschitzOnWith h_diff (hL₁ t)
    (mem_ball_self hr) hx
  rw [norm_sub_rev]
  simp only [h_eq t, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_right (half_le_self L₁.coe_nonneg) (sq_nonneg _))

/-- **Exponential stability passes to the linearization** (Khalil, Theorem 4.15, the "only if"
direction).  Let `x_eq` be an equilibrium of `ẋ = f(t, x)` with `f` continuously
differentiable, Lipschitz, and with Lipschitz Jacobian on a ball `D`, uniformly in `t`.  If
`x_eq` is locally exponentially stable, so it is for the linearization
`ẋ = A(t)(x - x_eq)`, `A(t) = ∂f/∂x(t, x_eq)`.

The converse Lyapunov function of the nonlinear system (Theorem 4.14) serves for the
linearization near `x_eq`: the two vector fields differ by `O(‖x - x_eq‖²)` and `∂V/∂x` is
`O(‖x - x_eq‖)`, so the difference in `V̇` is cubic and is absorbed by `-c₃‖x - x_eq‖²`. -/
@[blueprint "thm:continuousSystem-locallyExponentiallyStable-linearization"
  (title := "Exponential stability passes to the linearization")
  (statement := /-- Let $x_{\mathrm{eq}}$ be an equilibrium of $\dot x = f(t, x)$ on
    $\mathbb{R}^n$, with $f$ continuously differentiable on $\mathbb{R} \times D$,
    $D = \{x : \|x - x_{\mathrm{eq}}\| < r\}$, and $f(t, \cdot)$ and
    $\partial f / \partial x(t, \cdot)$ Lipschitz on $D$, uniformly in $t$.  If $x_{\mathrm{eq}}$ is
    locally exponentially stable (\cref{def:continuousSystem-locallyExponentiallyStable}), then
    it is a locally exponentially stable equilibrium of the linearization
    \[
      \dot x = A(t)(x - x_{\mathrm{eq}}), \qquad
      A(t) = \frac{\partial f}{\partial x}(t, x_{\mathrm{eq}}).
    \]

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.15, "only if" direction.
    Khalil's bounded Jacobian is the Lipschitz bound on $f(t, \cdot)$. -/)
  (proof := /-- Let $V$ be the converse Lyapunov function of the nonlinear system
    (\cref{thm:continuousSystem-exists-quadraticLyapunov-of-exponentialEstimate}).  Along the
    linearization,
    \[
      \dot V_{\mathrm{lin}} = \dot V + \frac{\partial V}{\partial x}
        \bigl(A(t)(x - x_{\mathrm{eq}}) - f(t, x)\bigr)
      \le -c_3\|x - x_{\mathrm{eq}}\|^2 + c_4 L_1 \|x - x_{\mathrm{eq}}\|^3,
    \]
    by \cref{thm:convex-norm-image-sub-sub-le-of-lipschitzOnWith}.  On a small ball this is at most
    $-\tfrac{c_3}{2}\|x - x_{\mathrm{eq}}\|^2$, so $V$ is an exponential Lyapunov function for the
    linearization
    (\cref{thm:continuousSystem-isExponentialLyapunovFunction-locallyExponentiallyStable}). -/)]
theorem ContinuousSystem.locallyExponentiallyStable_linearization {Y : Type*}
    {s : ContinuousSystem ℝⁿ Unit Y} {x_eq : ℝⁿ} {r : ℝ} (hr : 0 < r)
    (h_eq : ∀ t : ℝ, s.F t x_eq () = 0)
    (hf : ContDiffOn ℝ 1 (fun p : ℝ × ℝⁿ => s.F p.1 p.2 ()) (univ ×ˢ ball x_eq r))
    (h_lip : ∃ L : ℝ≥0, ∀ t : ℝ, LipschitzOnWith L (fun x => s.F t x ()) (ball x_eq r))
    (h_jac_lip : ∃ L₁ : ℝ≥0, ∀ t : ℝ,
      LipschitzOnWith L₁ (fderiv ℝ (fun x => s.F t x ())) (ball x_eq r))
    (h_les : s.LocallyExponentiallyStable x_eq) :
    (ContinuousSystem.autonomous (fun t x => fderiv ℝ (fun y => s.F t y ()) x_eq (x - x_eq))
      (fun _ _ => ())).LocallyExponentiallyStable x_eq := by
  obtain ⟨L₁, hL₁⟩ := h_jac_lip
  obtain ⟨c, hc, k, hk, γ, hγ, h_est⟩ := h_les
  -- Step 1. The converse Lyapunov function of the nonlinear system, on `D₀ = ball x_eq r₀`.
  set r₀ := min c (r / (2 * k))
  have hr₀ : 0 < r₀ := lt_min hc (by positivity)
  have hr₀r : r₀ < r / k := (min_le_right _ _).trans_lt (by
    rw [div_lt_div_iff₀ (by positivity) hk]
    nlinarith)
  obtain ⟨V, hV, c₄, hc₄, h_grad⟩ := s.exists_quadraticLyapunov_of_exponentialEstimate h_eq hf
    h_lip hk hγ hr₀ hr₀r fun t₀ ht₀ t₁ x hx h_init =>
      h_est t₀ ht₀ t₁ x hx (h_init.trans_le (min_le_left _ _))
  obtain ⟨k₁, hk₁, k₂, hk₂, k₃, hk₃, h_bounds⟩ := hV.bounds
  -- Step 2. On a smaller ball the cubic error is at most half the decay rate.
  set ρ := min (min r₀ r) (k₃ / (2 * c₄ * (L₁ + 1)))
  have hρ : 0 < ρ := lt_min (lt_min hr₀ hr) (by positivity)
  have hρr₀ : ρ ≤ r₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hρr : ρ ≤ r := (min_le_left _ _).trans (min_le_right _ _)
  have h_in : ∀ x ∈ ball x_eq ρ, x ∈ ball x_eq r₀ := fun x hx =>
    ball_subset_ball hρr₀ hx
  -- Step 3. `V` is an exponential Lyapunov function for the linearization on `ball x_eq ρ`.
  refine IsExponentialLyapunovFunction.locallyExponentiallyStable
    (D := ball x_eq ρ) (a := 2) ⟨ball_mem_nhds x_eq hρ, fun t ht x hx =>
      hV.differentiableAt t ht x (h_in x hx), two_pos, k₁, hk₁, k₂, hk₂, k₃ / 2, by positivity,
      fun t ht x hx => ?_⟩
  obtain ⟨h_low, h_up, h_lie⟩ := h_bounds t ht x (h_in x hx)
  refine ⟨h_low, h_up, ?_⟩
  rw [Real.rpow_two] at h_lie ⊢
  have hx_r₀ := mem_ball_iff_norm.mp (h_in x hx)
  have hx_ρ := mem_ball_iff_norm.mp hx
  -- The linearization differs from `f` by the quadratic remainder; `∂V/∂x = O(‖x - x_eq‖)`.
  have h_pert := lieDerivative_le_add_norm_fderiv_mul (V := V) (v := fun t y => s.F t y ())
    (w := fun t y => fderiv ℝ (fun y => s.F t y ()) x_eq (y - x_eq))
    (hV.differentiableAt t ht x (h_in x hx))
  have h_small : c₄ * L₁ * ‖x - x_eq‖ ≤ k₃ / 2 :=
    calc c₄ * L₁ * ‖x - x_eq‖
        ≤ c₄ * (L₁ + 1) * (k₃ / (2 * c₄ * (L₁ + 1))) := by
          gcongr
          · linarith
          · exact hx_ρ.le.trans (min_le_right _ _)
      _ = k₃ / 2 := by field_simp
  calc _root_.lieDerivative V (fun t y => fderiv ℝ (fun y => s.F t y ()) x_eq (y - x_eq)) t x
      ≤ s.lieDerivative V t x () + ‖fderiv ℝ (V t) x‖ *
          ‖fderiv ℝ (fun y => s.F t y ()) x_eq (x - x_eq) - s.F t x ()‖ := h_pert
    _ ≤ -(k₃ * ‖x - x_eq‖ ^ 2) + (c₄ * ‖x - x_eq‖) * (L₁ * ‖x - x_eq‖ ^ 2) :=
        add_le_add h_lie (mul_le_mul (h_grad t ht x (h_in x hx))
          (norm_linearization_remainder_le hr h_eq hf hL₁ t (ball_subset_ball hρr hx))
          (norm_nonneg _) (mul_nonneg hc₄.le (norm_nonneg _)))
    _ = -(k₃ * ‖x - x_eq‖ ^ 2) + (c₄ * L₁ * ‖x - x_eq‖) * ‖x - x_eq‖ ^ 2 := by ring
    _ ≤ -(k₃ * ‖x - x_eq‖ ^ 2) + k₃ / 2 * ‖x - x_eq‖ ^ 2 := by gcongr
    _ = -(k₃ / 2 * ‖x - x_eq‖ ^ 2) := by ring

/-- **The gradient of a quadratic form**: `‖∂/∂x ⟪x, M x⟫‖ ≤ 2‖M‖‖x‖`. -/
theorem norm_fderiv_inner_apply_self_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (M : E →L[ℝ] E) (x : E) :
    ‖fderiv ℝ (fun y => inner ℝ y (M y)) x‖ ≤ 2 * ‖M‖ * ‖x‖ := by
  have h : HasFDerivAt (fun y => inner ℝ y (M y))
      ((fderivInnerCLM ℝ (x, M x)).comp ((ContinuousLinearMap.id ℝ E).prod M)) x :=
    (hasFDerivAt_id x).inner ℝ M.hasFDerivAt
  rw [h.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, fderivInnerCLM_apply, Real.norm_eq_abs]
  calc |inner ℝ x (M z) + inner ℝ z (M x)|
      ≤ ‖x‖ * ‖M z‖ + ‖z‖ * ‖M x‖ :=
        (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _)
          (abs_real_inner_le_norm _ _))
    _ ≤ ‖x‖ * (‖M‖ * ‖z‖) + ‖z‖ * (‖M‖ * ‖x‖) :=
        add_le_add (mul_le_mul_of_nonneg_left (M.le_opNorm z) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (M.le_opNorm x) (norm_nonneg _))
    _ = 2 * ‖M‖ * ‖x‖ * ‖z‖ := by ring

/-- **Lyapunov's indirect method for time-varying systems** (Khalil, Theorem 4.13).  Let the
origin be an equilibrium of `ẋ = f(t, x)`, with `f` continuously differentiable on `ℝ × D`,
`D = {‖x‖ < r}`, and `f(t, ·)` and its Jacobian Lipschitz on `D`, uniformly in `t`.  If the origin
is exponentially stable for the linear system `ẋ = A(t) x`, `A(t) = ∂f/∂x(t, 0)`, it is so for
`ẋ = f(t, x)`.

Khalil's proof: Theorem 4.12 gives `P(t)` for the linear system, and along `f = A(t)x + g`,
`V̇ = -xᵀQx + 2xᵀPg ≤ -c₃‖x‖² + 2c₂L‖x‖³`, negative definite for `‖x‖ < ρ`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.13. -/
@[blueprint "thm:continuousSystem-locallyExponentiallyStable-of-linearization-zero"
  (title := "Lyapunov's indirect method for time-varying systems")
  (statement := /-- Let the origin be an equilibrium of $\dot x = f(t, x)$ on $\mathbb{R}^n$, with
    $f$ continuously differentiable on $\mathbb{R} \times D$, $D = \{x : \|x\| < r\}$, and
    $f(t, \cdot)$ and $\partial f / \partial x(t, \cdot)$ Lipschitz on $D$, uniformly in $t$.  If
    the origin is an exponentially stable equilibrium of the linear system $\dot x = A(t)x$,
    $A(t) = \frac{\partial f}{\partial x}(t, 0)$, then it is an exponentially stable equilibrium
    of $\dot x = f(t, x)$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.13.  Khalil's bounded
    Jacobian is the Lipschitz bound on $f(t, \cdot)$. -/)
  (proof := /-- $A(t)$ is continuous and bounded, so
    \cref{thm:continuousLTV-exists-differentialLyapunovEquation} with $Q = I$ gives $P(t)$, and
    $V(t, x) = x^{\mathsf T}P(t)x$ is an exponential Lyapunov function for the linear system
    (\cref{thm:continuousLTV-isExponentialLyapunovFunction-of-differentialLyapunovEquation}).
    Writing $f(t, x) = A(t)x + g(t, x)$ with $\|g(t, x)\| \le L_1\|x\|^2$
    (\cref{thm:convex-norm-image-sub-sub-le-of-lipschitzOnWith}),
    \[
      \dot V \le -c_3\|x\|^2 + 2\|P\|L_1\|x\|^3,
    \]
    which is at most $-\tfrac{c_3}{2}\|x\|^2$ for $\|x\| < \rho$; conclude by
    \cref{thm:continuousSystem-isExponentialLyapunovFunction-locallyExponentiallyStable}. -/)]
theorem ContinuousSystem.locallyExponentiallyStable_of_linearization_zero {Y : Type*}
    {s : ContinuousSystem ℝⁿ Unit Y} {r : ℝ} (hr : 0 < r) (h_eq : ∀ t : ℝ, s.F t 0 () = 0)
    (hf : ContDiffOn ℝ 1 (fun p : ℝ × ℝⁿ => s.F p.1 p.2 ()) (univ ×ˢ ball 0 r))
    (h_lip : ∃ L : ℝ≥0, ∀ t : ℝ, LipschitzOnWith L (fun x => s.F t x ()) (ball 0 r))
    (h_jac_lip : ∃ L₁ : ℝ≥0, ∀ t : ℝ,
      LipschitzOnWith L₁ (fderiv ℝ (fun x => s.F t x ())) (ball 0 r))
    (h_lin : (ContinuousSystem.autonomous (fun t x => fderiv ℝ (fun y => s.F t y ()) 0 x)
      (fun _ _ => ())).LocallyExponentiallyStable 0) :
    s.LocallyExponentiallyStable 0 := by
  obtain ⟨L, hL⟩ := h_lip
  obtain ⟨L₁, hL₁⟩ := h_jac_lip
  set J : ℝ → ℝⁿ →L[ℝ] ℝⁿ := fun t => fderiv ℝ (fun y => s.F t y ()) 0
  -- Step 1. `A(t) = ∂f/∂x(t, 0)` is continuous and bounded, and the linear system `ẋ = A(t)x`
  -- is exponentially stable.
  have h_open : IsOpen ((univ : Set ℝ) ×ˢ ball (0 : ℝⁿ) r) := isOpen_univ.prod isOpen_ball
  have h_mem : ∀ t : ℝ, (t, (0 : ℝⁿ)) ∈ (univ : Set ℝ) ×ˢ ball (0 : ℝⁿ) r := fun t =>
    ⟨mem_univ t, mem_ball_self hr⟩
  have hJ_cont : Continuous J := by
    rw [show J = fun t => (fderiv ℝ (fun p : ℝ × ℝⁿ => s.F p.1 p.2 ()) (t, 0)).comp
        (ContinuousLinearMap.inr ℝ ℝ ℝⁿ) from funext fun t =>
      fderiv_eq_fderiv_uncurry_comp_inr (V := fun t x => s.F t x ())
        ((hf.contDiffAt (h_open.mem_nhds (h_mem t))).differentiableAt one_ne_zero)]
    exact ((hf.continuousOn_fderiv_of_isOpen h_open le_rfl).comp_continuous
      (continuous_id.prodMk continuous_const) h_mem).clm_comp continuous_const
  set sl : ContinuousLTV ℝⁿ ℝⁿ ℝⁿ := ⟨J, 0, 0, 0⟩
  have hF : ∀ t y, sl.toContinuousSystem.zeroInput.F t y () = J t y := fun t y => by
    change J t y + (0 : ℝ → ℝⁿ →L[ℝ] ℝⁿ) t 0 = J t y
    simp
  have h_sl : sl.toContinuousSystem.zeroInput.LocallyExponentiallyStable 0 :=
    h_lin.of_semiconj (x_eq := (0 : ℝⁿ)) (ContinuousLinearMap.id ℝ ℝⁿ) one_pos one_pos
      (fun v => by simp) (fun v => by simp) fun t v => by
        rw [hF]
        simp [J]
  -- Step 2. Theorem 4.12 with `Q = I` gives `P(t)`; `V(t, x) = ⟪x, P(t) x⟫` is an exponential
  -- Lyapunov function for the linear system (Example 4.21).
  have hQ_pos : ∀ v : ℝⁿ, 1 * ‖v‖ ^ 2 ≤ inner ℝ v ((1 : ℝⁿ →L[ℝ] ℝⁿ) v) := fun v => by
    rw [ContinuousLinearMap.one_apply, real_inner_self_eq_norm_sq, one_mul]
  obtain ⟨P, hP, -, ⟨p, hP_bdd⟩, c₁, hc₁, hP_low⟩ := exists_differentialLyapunovEquation sl
    hJ_cont (fun t => norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds 0 hr) (hL t))
    (Q := fun _ => 1) continuous_const (q := 1) (fun _ => ContinuousLinearMap.norm_id_le)
    (fun _ => IsSelfAdjoint.one _) one_pos (fun _ => hQ_pos) h_sl
  set V : ℝ → ℝⁿ → ℝ := fun t v => inner ℝ v (P t v)
  obtain ⟨-, hV_diff, -, c₁', hc₁', c₂, hc₂, k₃, hk₃, hV_bounds⟩ :=
    isExponentialLyapunovFunction_of_differentialLyapunovEquation sl hP hP_bdd hc₁
      (fun t _ x => hP_low t x) one_pos (fun _ _ => hQ_pos)
  have hp : 0 ≤ p := (norm_nonneg _).trans (hP_bdd 0 le_rfl)
  -- Step 3. `V̇ ≤ -c₃‖x‖² + 2‖P‖L₁‖x‖³ ≤ -(c₃/2)‖x‖²` for `‖x‖ < ρ`.
  set ρ := min r (k₃ / (4 * (p + 1) * (L₁ + 1)))
  have hρ : 0 < ρ := lt_min hr (by positivity)
  refine IsExponentialLyapunovFunction.locallyExponentiallyStable (D := ball 0 ρ) (a := 2)
    ⟨ball_mem_nhds 0 hρ, fun t ht x _ => hV_diff t ht x (mem_univ _), two_pos, c₁', hc₁', c₂,
      hc₂, k₃ / 2, by positivity, fun t ht x hx => ?_⟩
  obtain ⟨h_low, h_up, h_lie⟩ := hV_bounds t ht x (mem_univ _)
  simp only [sub_zero, Real.rpow_two] at h_low h_up h_lie ⊢
  refine ⟨h_low, h_up, ?_⟩
  -- `V̇` along `f` is `V̇` along the linear system plus `∂V/∂x · g`, `g = f - A(t)x`.
  have h_pert := lieDerivative_le_add_norm_fderiv_mul (V := V) (v := fun t y => J t y)
    (w := fun t y => s.F t y ()) (hV_diff t ht x (mem_univ _))
  have h_linear : _root_.lieDerivative V (fun t y => J t y) t x =
      sl.toContinuousSystem.zeroInput.lieDerivative V t x () := by
    change fderiv ℝ (Function.uncurry V) (t, x) (1, J t x) =
      fderiv ℝ (Function.uncurry V) (t, x) (1, sl.toContinuousSystem.zeroInput.F t x ())
    rw [hF]
  have h_grad : ‖fderiv ℝ (V t) x‖ ≤ 2 * p * ‖x‖ :=
    (norm_fderiv_inner_apply_self_le (P t) x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hP_bdd t ht) two_pos.le) (norm_nonneg _))
  have h_g : ‖s.F t x () - J t x‖ ≤ L₁ * ‖x‖ ^ 2 := by
    have h := norm_linearization_remainder_le hr h_eq hf hL₁ t
      (ball_subset_ball (min_le_left _ _) hx)
    rwa [norm_sub_rev, sub_zero] at h
  have h_small : 2 * p * L₁ * ‖x‖ ≤ k₃ / 2 :=
    calc 2 * p * L₁ * ‖x‖
        ≤ 2 * (p + 1) * (L₁ + 1) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith)
            two_pos.le) (by linarith) L₁.coe_nonneg (by positivity)) (norm_nonneg _)
      _ ≤ 2 * (p + 1) * (L₁ + 1) * (k₃ / (4 * (p + 1) * (L₁ + 1))) :=
          mul_le_mul_of_nonneg_left ((mem_ball_zero_iff.mp hx).le.trans (min_le_right _ _))
            (by positivity)
      _ = k₃ / 2 := by field_simp; ring
  calc s.lieDerivative V t x ()
      ≤ _root_.lieDerivative V (fun t y => J t y) t x +
          ‖fderiv ℝ (V t) x‖ * ‖s.F t x () - J t x‖ := h_pert
    _ ≤ -(k₃ * ‖x‖ ^ 2) + (2 * p * ‖x‖) * (L₁ * ‖x‖ ^ 2) := by
        rw [h_linear]
        exact add_le_add h_lie (mul_le_mul h_grad h_g (norm_nonneg _) (by positivity))
    _ = -(k₃ * ‖x‖ ^ 2) + (2 * p * L₁ * ‖x‖) * ‖x‖ ^ 2 := by ring
    _ ≤ -(k₃ * ‖x‖ ^ 2) + k₃ / 2 * ‖x‖ ^ 2 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right h_small (sq_nonneg _))
    _ = -(k₃ / 2 * ‖x‖ ^ 2) := by ring

/-- **Lyapunov's indirect method at any equilibrium**: Khalil's Theorem 4.13 for an equilibrium
`x_eq`, by translating it to the origin, `y = x - x_eq`. -/
@[blueprint "thm:continuousSystem-locallyExponentiallyStable-of-linearization"
  (title := "Lyapunov's indirect method at any equilibrium")
  (statement := /-- Let $x_{\mathrm{eq}}$ be an equilibrium of $\dot x = f(t, x)$, with $f$
    continuously differentiable on $\mathbb{R} \times D$,
    $D = \{x : \|x - x_{\mathrm{eq}}\| < r\}$, and $f(t, \cdot)$ and
    $\partial f / \partial x(t, \cdot)$ Lipschitz on $D$, uniformly in $t$.  If $x_{\mathrm{eq}}$
    is a locally exponentially stable equilibrium of the linearization
    $\dot x = A(t)(x - x_{\mathrm{eq}})$,
    $A(t) = \frac{\partial f}{\partial x}(t, x_{\mathrm{eq}})$, then it is locally exponentially
    stable for $\dot x = f(t, x)$. -/)
  (proof := /-- In the coordinates $y = x - x_{\mathrm{eq}}$ the system is
    $\dot y = f(t, y + x_{\mathrm{eq}})$, with the same hypotheses on $\|y\| < r$ and the same
    Jacobian at the origin; apply
    \cref{thm:continuousSystem-locallyExponentiallyStable-of-linearization-zero} and translate
    back (\cref{lem:continuousSystem-locallyExponentiallyStable-of-semiconj}). -/)]
theorem ContinuousSystem.locallyExponentiallyStable_of_linearization {Y : Type*}
    {s : ContinuousSystem ℝⁿ Unit Y} {x_eq : ℝⁿ} {r : ℝ} (hr : 0 < r)
    (h_eq : ∀ t : ℝ, s.F t x_eq () = 0)
    (hf : ContDiffOn ℝ 1 (fun p : ℝ × ℝⁿ => s.F p.1 p.2 ()) (univ ×ˢ ball x_eq r))
    (h_lip : ∃ L : ℝ≥0, ∀ t : ℝ, LipschitzOnWith L (fun x => s.F t x ()) (ball x_eq r))
    (h_jac_lip : ∃ L₁ : ℝ≥0, ∀ t : ℝ,
      LipschitzOnWith L₁ (fderiv ℝ (fun x => s.F t x ())) (ball x_eq r))
    (h_lin : (ContinuousSystem.autonomous
      (fun t x => fderiv ℝ (fun y => s.F t y ()) x_eq (x - x_eq))
      (fun _ _ => ())).LocallyExponentiallyStable x_eq) :
    s.LocallyExponentiallyStable x_eq := by
  obtain ⟨L, hL⟩ := h_lip
  obtain ⟨L₁, hL₁⟩ := h_jac_lip
  -- The system in the coordinates `y = x - x_eq`.
  set s' : ContinuousSystem ℝⁿ Unit Y := ⟨fun t y u => s.F t (y + x_eq) u,
    fun t y u => s.h t (y + x_eq) u⟩
  have h_maps : MapsTo (· + x_eq) (ball (0 : ℝⁿ) r) (ball x_eq r) := fun y hy => by
    simpa [mem_ball, dist_eq_norm] using hy
  have h_shift : LipschitzWith 1 (· + x_eq : ℝⁿ → ℝⁿ) :=
    LipschitzWith.of_dist_le_mul fun a b => by rw [dist_add_right, NNReal.coe_one, one_mul]
  have h_jac : ∀ t, fderiv ℝ (fun y => s'.F t y ()) = fun y =>
      fderiv ℝ (fun x => s.F t x ()) (y + x_eq) :=
    fun t => funext fun y => fderiv_comp_add_right (f := fun x => s.F t x ()) x_eq
  have h_zero := ContinuousSystem.locallyExponentiallyStable_of_linearization_zero (s := s') hr
    (fun t => by simpa [s'] using h_eq t)
    (hf.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const)).contDiffOn
      fun p hp => ⟨mem_univ _, h_maps hp.2⟩)
    ⟨L, fun t => by simpa using (hL t).comp h_shift.lipschitzOnWith h_maps⟩
    ⟨L₁, fun t => by rw [h_jac]; simpa using (hL₁ t).comp h_shift.lipschitzOnWith h_maps⟩
    (h_lin.of_semiconj (x_eq := (0 : ℝⁿ)) (ContinuousLinearMap.id ℝ ℝⁿ) one_pos one_pos
      (fun v => by simp) (fun v => by simp) fun t y => by
        change fderiv ℝ (fun x => s.F t x ()) x_eq (x_eq + (y - 0) - x_eq) =
          fderiv ℝ (fun z => s'.F t z ()) 0 y
        rw [h_jac]
        beta_reduce
        rw [zero_add, sub_zero, add_sub_cancel_left])
  exact h_zero.of_semiconj (ContinuousLinearMap.id ℝ ℝⁿ) one_pos one_pos (fun v => by simp)
    (fun v => by simp) fun t x => by
      change s.F t (0 + (x - x_eq) + x_eq) () = s.F t x ()
      rw [zero_add, sub_add_cancel]

/-- **Exponential stability is decided by the linearization** (Khalil's Theorem 4.15): under the
hypotheses of `ContinuousSystem.locallyExponentiallyStable_linearization`, `x_eq` is locally
exponentially stable for `ẋ = f(t, x)` if and only if it is so for the linearization. -/
@[blueprint "thm:continuousSystem-locallyExponentiallyStable-iff-linearization"
  (title := "Exponential stability and the linearization")
  (statement := /-- Under the hypotheses of
    \cref{thm:continuousSystem-locallyExponentiallyStable-linearization}, $x_{\mathrm{eq}}$ is
    locally exponentially stable for $\dot x = f(t, x)$ if and only if it is for the
    linearization.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.15. -/)
  (proof := /-- \Cref{thm:continuousSystem-locallyExponentiallyStable-linearization} and
    \cref{thm:continuousSystem-locallyExponentiallyStable-of-linearization}. -/)]
theorem ContinuousSystem.locallyExponentiallyStable_iff_linearization {Y : Type*}
    {s : ContinuousSystem ℝⁿ Unit Y} {x_eq : ℝⁿ} {r : ℝ} (hr : 0 < r)
    (h_eq : ∀ t : ℝ, s.F t x_eq () = 0)
    (hf : ContDiffOn ℝ 1 (fun p : ℝ × ℝⁿ => s.F p.1 p.2 ()) (univ ×ˢ ball x_eq r))
    (h_lip : ∃ L : ℝ≥0, ∀ t : ℝ, LipschitzOnWith L (fun x => s.F t x ()) (ball x_eq r))
    (h_jac_lip : ∃ L₁ : ℝ≥0, ∀ t : ℝ,
      LipschitzOnWith L₁ (fderiv ℝ (fun x => s.F t x ())) (ball x_eq r)) :
    s.LocallyExponentiallyStable x_eq ↔ (ContinuousSystem.autonomous
      (fun t x => fderiv ℝ (fun y => s.F t y ()) x_eq (x - x_eq))
      (fun _ _ => ())).LocallyExponentiallyStable x_eq :=
  ⟨s.locallyExponentiallyStable_linearization hr h_eq hf h_lip h_jac_lip,
    s.locallyExponentiallyStable_of_linearization hr h_eq hf h_lip h_jac_lip⟩

end TimeVarying

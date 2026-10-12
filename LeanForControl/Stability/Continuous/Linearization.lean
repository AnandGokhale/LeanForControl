import LeanForControl.Analysis.FrechetDerivative
import LeanForControl.MatrixAlgebra.QuadraticForm
import LeanForControl.MatrixAlgebra.Complex
import LeanForControl.LinearSystems.Stability.DefsStability
import LeanForControl.LinearSystems.Stability.Continuous.LyapunovEquation
import LeanForControl.LinearSystems.Stability.Continuous.InstabilityCertificate
import LeanForControl.Stability.Continuous.LyapunovTheorems
import LeanForControl.Stability.Continuous.Chetaev
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
      (Metric.ball x_eq r) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨r, hr, hdecay⟩ := exists_centeredQuadraticForm_decay A P hf heq hJac hLyap
  obtain ⟨m, hm, hm_lower⟩ := exists_pos_mul_norm_sq_le_quadraticForm P hP
  let p : ℝⁿ →L[ℝ] ℝⁿ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P
  have hV : ContDiff ℝ 1 (centeredQuadraticForm P x_eq) :=
    (centeredQuadraticForm_contDiff P x_eq).of_le (by norm_num)
  refine ⟨r, hr, Metric.ball_mem_nhds x_eq hr, (hV.differentiable one_ne_zero).comp
    differentiable_snd, m, hm, ‖p‖ + 1, by positivity, 1 / 2, by norm_num, 2, two_pos,
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

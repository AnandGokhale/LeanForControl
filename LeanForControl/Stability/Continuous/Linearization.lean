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
import LeanForControl.MatrixAlgebra.NormComparison
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
  have h_diff : ∀ y ∈ ball x_eq r, DifferentiableAt ℝ (fun x => s.F t x ()) y := fun y hy =>
    ((hf.contDiffAt (prod_mem_nhds Filter.univ_mem (isOpen_ball.mem_nhds hy))).differentiableAt
      one_ne_zero).comp y ((differentiableAt_const t).prodMk differentiableAt_id)
  rw [norm_sub_rev]
  simpa [h_eq t] using norm_sub_sub_fderiv_le_of_lipschitzOnWith (convex_ball x_eq r) h_diff
    (hL₁ t) (mem_ball_self hr) hx

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
    by \cref{thm:norm-sub-sub-fderiv-le-of-lipschitzOnWith}.  On a small ball this is at most
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

open scoped Matrix.Norms.Operator in
/-- **Lyapunov's indirect method for time-varying systems.**  Let `x_eq` be an equilibrium of
`ẋ = f(t, x)` with `f` continuously differentiable, Lipschitz, and with Lipschitz Jacobian on a
ball `D`, uniformly in `t`.  If `x_eq` is locally exponentially stable for the linearization
`ẋ = A(t)(x - x_eq)`, `A(t) = ∂f/∂x(t, x_eq)`, it is so for `ẋ = f(t, x)`.

The linearization, in coordinates, is a linear time-varying system with `A` continuous and
bounded.  Theorem 4.12 with `Q = I` gives `P(t)`, and `V(t, x) = (x - x_eq)ᵀ P(t) (x - x_eq)`
decreases along `f` as along the linearization, up to a cubic error.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.13. -/
@[blueprint "thm:continuousSystem-locallyExponentiallyStable-of-linearization"
  (title := "Lyapunov's indirect method for time-varying systems")
  (statement := /-- Under the hypotheses of
    \cref{thm:continuousSystem-locallyExponentiallyStable-linearization}, if
    $x_{\mathrm{eq}}$ is a locally exponentially stable equilibrium of the linearization
    $\dot x = A(t)(x - x_{\mathrm{eq}})$,
    $A(t) = \frac{\partial f}{\partial x}(t, x_{\mathrm{eq}})$,
    then it is locally exponentially stable for $\dot x = f(t, x)$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.13.  Khalil's bounded
    Jacobian is the Lipschitz bound on $f(t, \cdot)$. -/)
  (proof := /-- In coordinates the linearization is $\dot v = A(t)v$ with $A$ continuous and
    bounded, and exponentially stable
    (\cref{lem:continuousSystem-locallyExponentiallyStable-of-semiconj}).
    \Cref{thm:continuousLTV-exists-differentialLyapunovEquation} with $Q = I$ gives a bounded
    $P(t)$ with $c_1\|x\|^2 \le x^{\mathsf T}P(t)x \le c_2\|x\|^2$ and derivative
    $-x^{\mathsf T}x$ along the linearization.  Along $f$, $V = (x - x_{\mathrm{eq}})^{\mathsf T}
    P(t)(x - x_{\mathrm{eq}})$ has derivative
    \[
      \dot V \le -c_3\|x - x_{\mathrm{eq}}\|^2 + 2\|P\|L_1\|x - x_{\mathrm{eq}}\|^3,
    \]
    by \cref{thm:norm-sub-sub-fderiv-le-of-lipschitzOnWith}, which is at most
    $-\tfrac{c_3}{2}\|x - x_{\mathrm{eq}}\|^2$ on a small ball; conclude by
    \cref{thm:continuousSystem-isExponentialLyapunovFunction-locallyExponentiallyStable}. -/)]
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
  set J : ℝ → ℝⁿ →L[ℝ] ℝⁿ := fun t => fderiv ℝ (fun y => s.F t y ()) x_eq
  -- Coordinates: `e = ofLp`, from the Euclidean norm to the sup norm.
  set e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  set N : ℝ := n + 1
  have hN : 0 < N := by positivity
  have h_norm_sq : ∀ y : ℝⁿ, ‖y‖ ^ 2 ≤ N * ‖e y‖ ^ 2 := fun y => by
    have h := norm_le_sqrt_card_mul_norm_ofLp y
    rw [Fintype.card_fin] at h
    calc ‖y‖ ^ 2
        ≤ (√n * ‖e y‖) ^ 2 := by gcongr; exact h
      _ = n * ‖e y‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      _ ≤ N * ‖e y‖ ^ 2 := by gcongr; linarith
  -- Step 1. The linearization is `v̇ = A(t) v` on `Fin n → ℝ`, with `A` continuous and bounded.
  set A : ℝ → Matrix (Fin n) (Fin n) ℝ :=
    fun t => (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm (J t)
  have hJA : ∀ t, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (A t) = J t := fun t =>
    StarAlgEquiv.apply_symm_apply _ _
  have h_open : IsOpen ((univ : Set ℝ) ×ˢ ball x_eq r) := isOpen_univ.prod isOpen_ball
  have h_mem : ∀ t : ℝ, (t, x_eq) ∈ (univ : Set ℝ) ×ˢ ball x_eq r := fun t =>
    ⟨mem_univ t, mem_ball_self hr⟩
  have hJ_cont : Continuous J := by
    have hJ_joint : J = fun t => (fderiv ℝ (fun p : ℝ × ℝⁿ => s.F p.1 p.2 ()) (t, x_eq)).comp
        (ContinuousLinearMap.inr ℝ ℝ ℝⁿ) := funext fun t =>
      fderiv_eq_fderiv_uncurry_comp_inr (V := fun t x => s.F t x ())
        ((hf.contDiffAt (h_open.mem_nhds (h_mem t))).differentiableAt one_ne_zero)
    rw [hJ_joint]
    exact ((hf.continuousOn_fderiv_of_isOpen h_open le_rfl).comp_continuous
      (continuous_id.prodMk continuous_const) h_mem).clm_comp continuous_const
  have hA_cont : Continuous A :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm.toAlgEquiv.toLinearMap
      |>.continuous_of_finiteDimensional |>.comp hJ_cont
  have hA_bdd : ∀ t, ‖A t‖ ≤ √n * L := fun t =>
    calc ‖A t‖
        ≤ √(Fintype.card (Fin n)) * ‖J t‖ := norm_toEuclideanCLM_symm_le (J t)
      _ ≤ √n * L := by
          rw [Fintype.card_fin]
          gcongr
          exact norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds x_eq hr) (hL t)
  set sl : ContinuousLTV (Fin n) (Fin 0) (Fin 0) ℝ := ⟨A, 0, 0, 0⟩
  -- Step 2. It is exponentially stable: its trajectories are those of the linearization.
  have h_sl : sl.toContinuousSystem.zeroInput.LocallyExponentiallyStable 0 := by
    refine h_lin.of_semiconj (x_eq := (0 : Fin n → ℝ)) e.symm.toContinuousLinearMap
      (b := √n + 1) one_pos (by positivity) (fun v => ?_) (fun v => ?_) (fun t v => ?_)
    · simpa using norm_ofLp_le (WithLp.toLp 2 v)
    · have h := norm_le_sqrt_card_mul_norm_ofLp (WithLp.toLp 2 v)
      rw [Fintype.card_fin, WithLp.ofLp_toLp] at h
      calc ‖e.symm v‖
          ≤ √n * ‖v‖ := h
        _ ≤ (√n + 1) * ‖v‖ := by gcongr; linarith
    · change J t (x_eq + WithLp.toLp 2 (v - 0) - x_eq) =
        WithLp.toLp 2 (A t *ᵥ v + (0 : Matrix (Fin n) (Fin 0) ℝ) *ᵥ 0)
      rw [← hJA t]
      simp
  -- Step 3. Theorem 4.12 with `Q = I`: `W(t, v) = vᵀ P(t) v`.
  obtain ⟨P, -, -, ⟨p, hP_bdd⟩, hW⟩ := LinearSystems.exists_differentialLyapunovEquation sl
    hA_cont hA_bdd (Q := fun _ => 1) continuous_const (q := ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖)
    (fun _ => le_rfl) (fun _ => transpose_one) one_pos
    (fun _ v => by simpa using sq_norm_le_dotProduct_self v) h_sl
  set W : ℝ → (Fin n → ℝ) → ℝ := fun t v => v ⬝ᵥ (P t *ᵥ v)
  obtain ⟨-, hW_diff, -, c₁, hc₁, c₂, hc₂, k₃, hk₃, hW_bounds⟩ := hW
  set p' := √n * p
  have hp' : 0 ≤ p' := mul_nonneg (Real.sqrt_nonneg _) ((norm_nonneg _).trans (hP_bdd 0 le_rfl))
  have hP' : ∀ t, 0 ≤ t → ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (P t)‖ ≤ p' :=
    fun t ht => (norm_toEuclideanCLM_le (P t)).trans (by
      rw [Fintype.card_fin]
      exact mul_le_mul_of_nonneg_left (hP_bdd t ht) (Real.sqrt_nonneg _))
  -- Step 4. `V(t, x) = W(t, e(x - x_eq))`, so `DV = DW ∘ M` with `M(τ, y) = (τ, e y)`.
  set V : ℝ → ℝⁿ → ℝ := fun t x => centeredQuadraticForm (P t) x_eq x
  have hVW : ∀ t x, V t x = W t (e (x - x_eq)) := fun t x => quadraticForm_eq_dotProduct _ _
  set M : ℝ × ℝⁿ →L[ℝ] ℝ × (Fin n → ℝ) := (ContinuousLinearMap.fst ℝ ℝ ℝⁿ).prod
    ((e : ℝⁿ →L[ℝ] (Fin n → ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ ℝⁿ))
  have hV_fderiv : ∀ t, 0 ≤ t → ∀ x, HasFDerivAt (Function.uncurry V)
      ((fderiv ℝ (Function.uncurry W) (t, e (x - x_eq))).comp M) (t, x) := by
    intro t ht x
    have hM : HasFDerivAt (fun z : ℝ × ℝⁿ => (z.1, e (z.2 - x_eq))) M (t, x) :=
      hasFDerivAt_fst.prodMk (e.hasFDerivAt.comp (t, x) (hasFDerivAt_snd.sub_const x_eq))
    have h := (hW_diff t ht _ (mem_univ _)).hasFDerivAt.comp (t, x) hM
    convert h using 1
    funext z
    exact hVW z.1 z.2
  -- Step 5. On a small ball the cubic error is at most half the decay rate.
  set κ := k₃ / N
  set ρ := min r (κ / (4 * (p' + 1) * (L₁ + 1)))
  have hρ : 0 < ρ := lt_min hr (by positivity)
  refine IsExponentialLyapunovFunction.locallyExponentiallyStable (D := ball x_eq ρ) (a := 2)
    ⟨ball_mem_nhds x_eq hρ, fun t ht x _ => (hV_fderiv t ht x).differentiableAt, two_pos,
      c₁ / N, by positivity, c₂, hc₂, κ / 2, by positivity, fun t ht x hx => ?_⟩
  obtain ⟨h_low, h_up, h_lie⟩ := hW_bounds t ht (e (x - x_eq)) (mem_univ _)
  simp only [sub_zero, Real.rpow_two] at h_low h_up h_lie ⊢
  have hx_ρ := mem_ball_iff_norm.mp hx
  set y := x - x_eq
  set v := e y
  refine ⟨?_, ?_, ?_⟩
  · calc c₁ / N * ‖y‖ ^ 2
        ≤ c₁ / N * (N * ‖v‖ ^ 2) := by gcongr; exact h_norm_sq y
      _ = c₁ * ‖v‖ ^ 2 := by field_simp
      _ ≤ W t v := h_low
      _ = V t x := (hVW t x).symm
  · calc V t x
        = W t v := hVW t x
      _ ≤ c₂ * ‖v‖ ^ 2 := h_up
      _ ≤ c₂ * ‖y‖ ^ 2 := by gcongr; exact norm_ofLp_le y
  -- The decrease: along the linearization it is the LTV one, and `f` differs by `ε = O(‖y‖²)`.
  set D := fderiv ℝ (Function.uncurry V) (t, x)
  have h_lin_eq : D (1, J t y) = sl.toContinuousSystem.zeroInput.lieDerivative W t v () := by
    have hD : D = (fderiv ℝ (Function.uncurry W) (t, v)).comp M := (hV_fderiv t ht x).fderiv
    rw [hD]
    change fderiv ℝ (Function.uncurry W) (t, v) (1, e (J t y)) =
      fderiv ℝ (Function.uncurry W) (t, v) (1, A t *ᵥ v + (0 : Matrix (Fin n) (Fin 0) ℝ) *ᵥ 0)
    rw [← hJA t, Matrix.mulVec_zero, add_zero]
    rfl
  -- `f` differs from the linearization by `O(‖y‖²)`, and `‖∂V/∂x‖ ≤ 2‖P‖‖y‖`.
  have h_pert := lieDerivative_le_add_norm_fderiv_mul (V := V)
    (v := fun t x => fderiv ℝ (fun y => s.F t y ()) x_eq (x - x_eq)) (w := fun t x => s.F t x ())
    (hV_fderiv t ht x).differentiableAt
  have h_grad : ‖fderiv ℝ (V t) x‖ ≤ 2 * p' * ‖y‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg two_pos.le hp') (norm_nonneg _))
      fun z => by
        rw [Real.norm_eq_abs]
        exact (abs_fderiv_centeredQuadraticForm_le _ _ _ _).trans (by gcongr; exact hP' t ht)
  have h_rem : ‖s.F t x () - J t y‖ ≤ L₁ * ‖y‖ ^ 2 := by
    rw [norm_sub_rev]
    exact norm_linearization_remainder_le hr h_eq hf hL₁ t (ball_subset_ball (min_le_left _ _) hx)
  have h_small : 2 * p' * L₁ * ‖y‖ ≤ κ / 2 :=
    calc 2 * p' * L₁ * ‖y‖
        ≤ 2 * (p' + 1) * (L₁ + 1) * (κ / (4 * (p' + 1) * (L₁ + 1))) := by
          gcongr
          · linarith
          · linarith
          · exact hx_ρ.le.trans (min_le_right _ _)
      _ = κ / 2 := by field_simp; ring
  have h_decay : κ * ‖y‖ ^ 2 ≤ k₃ * ‖v‖ ^ 2 :=
    calc κ * ‖y‖ ^ 2
        ≤ κ * (N * ‖v‖ ^ 2) := by gcongr; exact h_norm_sq y
      _ = k₃ * ‖v‖ ^ 2 := by simp only [κ]; field_simp
  change D (1, s.F t x ()) ≤ -(κ / 2 * ‖y‖ ^ 2)
  calc D (1, s.F t x ())
      ≤ D (1, J t y) + ‖fderiv ℝ (V t) x‖ * ‖s.F t x () - J t y‖ := h_pert
    _ ≤ -(k₃ * ‖v‖ ^ 2) + (2 * p' * ‖y‖) * (L₁ * ‖y‖ ^ 2) := by
        rw [h_lin_eq]
        exact add_le_add h_lie (mul_le_mul h_grad h_rem (norm_nonneg _)
          (mul_nonneg (mul_nonneg two_pos.le hp') (norm_nonneg _)))
    _ ≤ -(κ * ‖y‖ ^ 2) + (2 * p' * L₁ * ‖y‖) * ‖y‖ ^ 2 := by nlinarith
    _ ≤ -(κ * ‖y‖ ^ 2) + κ / 2 * ‖y‖ ^ 2 := by gcongr
    _ = -(κ / 2 * ‖y‖ ^ 2) := by ring

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

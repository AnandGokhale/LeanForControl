import LeanForControl.Stability.LyapunovIndirect.Chetaev
import LeanForControl.Stability.LyapunovIndirect.FrechetRemainder
import LeanForControl.LinearSystems.Stability.Continuous.DefsHurwitz
import LeanForControl.Stability.LyapunovIndirect.InstabilityCertificate
import LeanForControl.Stability.LyapunovIndirect.Lyapunov
import Architect

/-!
# Nonlinear instability from an unstable linearization

This file develops the instability half of Lyapunov's indirect method for finite
forward solution segments.  In particular, solutions used to witness instability
need not be extendable to negative time or through a finite escape time.

Reference: Khalil, *Nonlinear Systems*; Hahn, *Stability of Motion*.
-/

open Filter Function Metric Set Topology
open scoped ContDiff NNReal Topology

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace NonlinearInstability

open Matrix

/-- A positive value of a quadratic form gives positive points arbitrarily
close to its center by scaling the witnessing direction.

Original: seed-point infrastructure for the Chetaev cone.
-/
private theorem exists_centered_quadratic_seed
    (H : Matrix (Fin n) (Fin n) ℝ) (x_eq w : ℝⁿ) (hw : w ≠ 0)
    (hHw : 0 < LinearSystems.matrixQuadratic H w)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∃ x, ‖x - x_eq‖ < min δ ρ ∧
      0 < LinearSystems.centeredMatrixQuadratic H x_eq x := by
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
  · rw [LinearSystems.centeredMatrixQuadratic]
    simp only [add_sub_cancel_left]
    rw [LinearSystems.matrixQuadratic_smul]
    positivity

/-- A quadratic Chetaev certificate for the shifted linearization implies
forward instability of the nonlinear equilibrium.

The positive-definite shifted Lie matrix supplies strict growth on the cone
where the quadratic form is positive.  The `C¹` remainder is absorbed
on a sufficiently small ball.

Reference: Hahn, *Stability of Motion* (quadratic Chetaev construction).
-/
theorem forwardUnstable_of_quadratic_certificate
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (A H : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hα : 0 < α)
    (hshift : (H * A + Aᵀ * H - (2 * α) • H).PosDef)
    (w : ℝⁿ) (hw : w ≠ 0)
    (hHw : 0 < LinearSystems.matrixQuadratic H w) :
    ForwardUnstable f x_eq := by
  have hn : n ≠ 0 := by
    intro hnzero
    subst n
    exact hw (Subsingleton.elim w 0)
  letI : NeZero n := ⟨hn⟩
  let G : Matrix (Fin n) (Fin n) ℝ := H * A + Aᵀ * H - (2 * α) • H
  have hG : G.PosDef := by simpa [G] using hshift
  obtain ⟨m, hm, hm_lower⟩ :=
    LinearSystems.exists_pos_mul_norm_sq_le_matrixQuadratic G hG
  let p : ℝⁿ →L[ℝ] ℝⁿ :=
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H
  let η : ℝ := m / (4 * (‖p‖ + 1))
  have hp_nonneg : 0 ≤ ‖p‖ := norm_nonneg p
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hderiv : HasFDerivAt f
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) x_eq := by
    simpa only [hJac] using (hf.differentiable (by norm_num) x_eq).hasFDerivAt
  obtain ⟨r, hr, hrem⟩ := hderiv.exists_centered_remainder_bound hη
  let ρ : ℝ := r / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hcoef : 2 * ‖p‖ * η ≤ m / 2 := by
    dsimp [η]
    rw [show 2 * ‖p‖ * (m / (4 * (‖p‖ + 1))) =
      (2 * ‖p‖ * m) / (4 * (‖p‖ + 1)) by ring]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  let V : ℝⁿ → ℝ := LinearSystems.centeredMatrixQuadratic H x_eq
  apply forwardUnstable_of_exponential_chetaev hf
    ((LinearSystems.centeredMatrixQuadratic_contDiff H x_eq).of_le (by norm_num))
      hρ hα hp_nonneg
  · intro x hx
    simpa [V, LinearSystems.centeredMatrixQuadratic, p] using
      LinearSystems.abs_matrixQuadratic_le H (x - x_eq)
  · intro x hx
    let y : ℝⁿ := x - x_eq
    let e : ℝⁿ := f x - f x_eq -
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A y
    have hy_r : ‖y‖ < r := by
      have : ‖x - x_eq‖ ≤ r / 2 := by simpa [ρ] using hx
      dsimp [y]
      linarith
    have he_norm : ‖e‖ ≤ η * ‖y‖ := hrem x (by simpa [y] using hy_r)
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
          LinearSystems.matrixQuadratic G y + 2 * α * V x := by
      rw [show V = LinearSystems.centeredMatrixQuadratic H x_eq by rfl]
      rw [LinearSystems.fderiv_centeredMatrixQuadratic_apply_matrix]
      rw [hmatrix]
      rw [LinearSystems.matrixQuadratic_matrix_add,
        LinearSystems.matrixQuadratic_matrix_smul]
      rfl
    have herror_abs : |fderiv ℝ V x e| ≤ 2 * ‖p‖ * ‖y‖ * ‖e‖ := by
      simpa [V, p, y] using
        LinearSystems.abs_fderiv_centeredMatrixQuadratic_le H x_eq x e
    have herror_bound : |fderiv ℝ V x e| ≤ (m / 2) * ‖y‖ ^ 2 := by
      calc
        |fderiv ℝ V x e| ≤ 2 * ‖p‖ * ‖y‖ * ‖e‖ := herror_abs
        _ ≤ 2 * ‖p‖ * ‖y‖ * (η * ‖y‖) := by
          exact mul_le_mul_of_nonneg_left he_norm
            (mul_nonneg (mul_nonneg (by norm_num) hp_nonneg) (norm_nonneg y))
        _ = (2 * ‖p‖ * η) * ‖y‖ ^ 2 := by ring
        _ ≤ (m / 2) * ‖y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖y‖)
    have hG_lower : m * ‖y‖ ^ 2 ≤ LinearSystems.matrixQuadratic G y :=
      hm_lower y
    rw [hf_split, map_add, hlinear]
    have herr_lower : -(m / 2 * ‖y‖ ^ 2) ≤ fderiv ℝ V x e :=
      (neg_le_of_abs_le herror_bound)
    nlinarith [sq_nonneg ‖y‖]
  · intro δ hδ
    exact exists_centered_quadratic_seed H x_eq w hw hHw hρ hδ

end NonlinearInstability

open Matrix

/-- A `C¹` equilibrium is forward unstable when its Jacobian has a nonzero
complex eigenvector whose eigenvalue has positive real part.

The spectral hypothesis is converted to an axiom-free real quadratic Chetaev
certificate, and the nonlinear first-order remainder is absorbed locally.

Reference: Khalil, *Nonlinear Systems* (Lyapunov's indirect method).
-/
theorem forwardUnstable_of_complex_eigenvalue_re_pos
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f)
    (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    {μ : ℂ} {v : Fin n → ℂ}
    (hv : v ≠ 0)
    (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v)
    (hμ : 0 < μ.re) :
    ForwardUnstable f x_eq := by
  obtain ⟨α, H, w, hα, _hH, hw, hHw, hshift⟩ :=
    LinearSystems.exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos
      A hv heig hμ
  exact NonlinearInstability.forwardUnstable_of_quadratic_certificate
    A H α hf heq hJac hα hshift w hw hHw

/-- A `C¹` equilibrium is forward unstable if its Jacobian has some complex
eigenvalue with positive real part.

Here existence of an eigenvalue is stated concretely by a nonzero eigenvector,
matching the repository's matrix spectral API.

Reference: Khalil, *Nonlinear Systems* (Lyapunov's indirect method).
-/
@[blueprint "thm:positive-real-eigenvalue-forward-unstable"
  (statement := /-- Let $f:\mathbb R^n\to\mathbb R^n$ be $C^1$ with
    $f(x_{\rm eq})=0$.  If the Jacobian at $x_{\rm eq}$ has a complex
    eigenvalue with positive real part, then $x_{\rm eq}$ is unstable when
    stability is quantified over every finite forward solution segment. -/)
  (proof := /-- Build the real quadratic certificate supplied by
    \cref{thm:positive-real-eigenvalue-quadratic-certificate}, absorb the
    first-order nonlinear remainder on a small ball, and apply the exponential
    Chetaev criterion. -/)]
theorem forwardUnstable_of_exists_complex_eigenvalue_re_pos
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f)
    (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hunstable : ∃ (μ : ℂ) (v : Fin n → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re) :
    ForwardUnstable f x_eq := by
  obtain ⟨μ, v, hv, heig, hμ⟩ := hunstable
  exact forwardUnstable_of_complex_eigenvalue_re_pos A hf heq hJac hv heig hμ

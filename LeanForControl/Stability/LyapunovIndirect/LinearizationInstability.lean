import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import LeanForControl.MatrixAlgebra.Exponential
import LeanForControl.Stability.LyapunovIndirect.DefsDynamics
import LeanForControl.LinearSystems.Stability.DefsStability
import LeanForControl.Stability.Autonomous
import Architect
import LeanForControl.MatrixAlgebra.Complex

/-!
# Unstable modes and finite forward segments

This file constructs real solution segments from complex eigenvectors.  In
particular, an affine-linear system whose state matrix has an eigenvalue in the
open right half-plane is unstable in the finite-forward-segment sense.

Reference: Khalil, *Nonlinear Systems*.
-/

open Set Filter Topology

open Matrix

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

private noncomputable def realEigenmode
    (q μ : ℂ) (v : Fin n → ℂ) (t : ℝ) : ℝⁿ :=
  WithLp.toLp 2 fun i => (q * Complex.exp (μ * (t : ℂ)) * v i).re

private noncomputable def realMulVec
    (A : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ) : ℝⁿ :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A x

private lemma hasDerivAt_realEigenmode
    (q μ : ℂ) (v : Fin n → ℂ) (t : ℝ) :
    HasDerivAt (realEigenmode q μ v)
      (WithLp.toLp 2 fun i =>
        (q * Complex.exp (μ * (t : ℂ)) * μ * v i).re) t := by
  have hraw : HasDerivAt
      (fun s : ℝ => fun i => (q * Complex.exp (μ * (s : ℂ)) * v i).re)
      (fun i => (q * Complex.exp (μ * (t : ℂ)) * μ * v i).re) t := by
    rw [hasDerivAt_pi]
    intro i
    have hcoe : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      simpa using Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)
    have hlin : HasDerivAt (fun s : ℝ => μ * (s : ℂ)) μ t := by
      simpa using hcoe.const_mul μ
    have hexp : HasDerivAt (fun s : ℝ => Complex.exp (μ * (s : ℂ)))
        (Complex.exp (μ * (t : ℂ)) * μ) t :=
      (Complex.hasDerivAt_exp _).comp t hlin
    have hcomplex : HasDerivAt
        (fun s : ℝ => q * Complex.exp (μ * (s : ℂ)) * v i)
        (q * (Complex.exp (μ * (t : ℂ)) * μ) * v i) t :=
      (hexp.const_mul q).mul_const (v i)
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomplex
    simpa [Complex.reCLM_apply, mul_assoc] using hre
  simpa [realEigenmode] using
    (PiLp.hasFDerivAt_toLp 2
      (fun i => (q * Complex.exp (μ * (t : ℂ)) * v i).re)).comp_hasDerivAt t hraw

private lemma realEigenmode_deriv_eq_mulVec
    (A : Matrix (Fin n) (Fin n) ℝ) (q μ : ℂ) (v : Fin n → ℂ)
    (hAv : A.complexify *ᵥ v = μ • v) (t : ℝ) :
    (WithLp.toLp 2 fun i => (q * Complex.exp (μ * (t : ℂ)) * μ * v i).re) =
      realMulVec A (realEigenmode q μ v t) := by
  have h := Matrix.complexify_mulVec_re_smul_eigenpair A μ
    (q * Complex.exp (μ * (t : ℂ))) v hAv
  simpa [realMulVec, realEigenmode] using congrArg (WithLp.toLp 2) h

private lemma hasDerivAt_realEigenmode_of_eigenvector
    (A : Matrix (Fin n) (Fin n) ℝ) (q μ : ℂ) (v : Fin n → ℂ)
    (hAv : A.complexify *ᵥ v = μ • v) (t : ℝ) :
    HasDerivAt (realEigenmode q μ v)
      (realMulVec A (realEigenmode q μ v t)) t := by
  rw [← realEigenmode_deriv_eq_mulVec A q μ v hAv t]
  exact hasDerivAt_realEigenmode q μ v t

private lemma norm_realPart_toLp_le (z : Fin n → ℂ) :
    ‖WithLp.toLp 2 (fun i => (z i).re)‖ ≤ ‖WithLp.toLp 2 z‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  simpa only [Real.norm_eq_abs, sq_abs, pow_two, Complex.normSq_eq_norm_sq] using
    Complex.re_sq_le_normSq (z i)

private lemma abs_apply_le_euclideanNorm (x : ℝⁿ) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs,
    EuclideanSpace.real_norm_sq_eq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

private lemma norm_realEigenmode_le
    (q μ : ℂ) (v : Fin n → ℂ) (t : ℝ) :
    ‖realEigenmode q μ v t‖ ≤
      ‖q‖ * Real.exp (μ.re * t) * ‖WithLp.toLp 2 v‖ := by
  let c := q * Complex.exp (μ * (t : ℂ))
  have hsmul : WithLp.toLp 2 (fun i => c * v i) = c • WithLp.toLp 2 v := by
    ext i
    rfl
  calc
    ‖realEigenmode q μ v t‖ ≤ ‖WithLp.toLp 2 (fun i => c * v i)‖ := by
      simpa [realEigenmode, c] using norm_realPart_toLp_le (fun i => c * v i)
    _ = ‖c‖ * ‖WithLp.toLp 2 v‖ := by rw [hsmul, norm_smul]
    _ = ‖q‖ * Real.exp (μ.re * t) * ‖WithLp.toLp 2 v‖ := by
      rw [Complex.norm_mul, Complex.norm_exp]
      congr 2
      simp

/-- With a real amplitude `q = ρ`, coordinate `i` of the real eigenmode at time `T` is
`ρ Re z`, where `z = e^{μT} vᵢ`. -/
private lemma realEigenmode_ofReal_apply (ρ : ℝ) (μ : ℂ) (v : Fin n → ℂ) (T : ℝ) (i : Fin n) :
    realEigenmode (ρ : ℂ) μ v T i = ρ * (Complex.exp (μ * (T : ℂ)) * v i).re := by
  simp only [realEigenmode, mul_assoc, Complex.re_ofReal_mul]

/-- With an imaginary amplitude `q = -iρ`, coordinate `i` of the real eigenmode at time `T`
is `ρ Im z`, where `z = e^{μT} vᵢ`. -/
private lemma realEigenmode_neg_I_apply (ρ : ℝ) (μ : ℂ) (v : Fin n → ℂ) (T : ℝ)
    (i : Fin n) :
    realEigenmode (-(ρ : ℂ) * Complex.I) μ v T i =
      ρ * (Complex.exp (μ * (T : ℂ)) * v i).im := by
  simp only [realEigenmode, mul_assoc, neg_mul, Complex.neg_re, Complex.re_ofReal_mul,
    Complex.I_mul_re]
  ring

/-- A real eigenmode whose coordinate `i` at time `T` is `ρ c`, with `1 ≤ ρ |c|`, lies outside
the open unit ball at time `T`. -/
private lemma one_le_norm_realEigenmode_of_apply {q μ : ℂ} {v : Fin n → ℂ} {T ρ c : ℝ}
    {i : Fin n} (hρ : 0 < ρ) (hcoord : realEigenmode q μ v T i = ρ * c)
    (hgrowth : 1 ≤ ρ * |c|) :
    1 ≤ ‖realEigenmode q μ v T‖ := by
  have hcoord_abs : 1 ≤ |realEigenmode q μ v T i| := by
    rw [hcoord, abs_mul, abs_of_pos hρ]
    exact hgrowth
  exact hcoord_abs.trans (abs_apply_le_euclideanNorm _ i)

/-- An affine-linear system is forward unstable when its state matrix has a
complex eigenvalue with positive real part.

The proof converts a growing complex eigenmode into one of two real modes.  At
each selected final time, either the real or imaginary component carries at
least half of the complex amplitude, which supplies a finite escaping solution
segment from an arbitrarily small initial perturbation.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.7.
-/
@[blueprint "thm:unstable-affineLinear-of-eigenvalue-re-pos"
  (title := "Instability of an affine-linear system")
  (statement := /-- If $A \in \mathbb{R}^{n \times n}$ has a complex eigenvalue $\mu$ with
    $\operatorname{Re}\mu > 0$, then $x_{\mathrm{eq}}$ is an unstable equilibrium
    (\cref{def:unstable}) of the affine-linear field $x \mapsto A(x - x_{\mathrm{eq}})$
    (\cref{def:affineLinearVectorField}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.7.
  -/)
  (proof := /-- Let $v \ne 0$ be an eigenvector for $\mu$, fix a coordinate $i$ with
    $v_i \ne 0$, and for $q \in \mathbb{C}$ consider the real eigenmode
    $t \mapsto x_{\mathrm{eq}} + \operatorname{Re}\bigl(q\,e^{\mu t} v\bigr)$, a genuine solution
    of the linear equation.  Given $\delta > 0$, put $\rho = \delta / (2\|v\|)$; for $|q| = \rho$
    the initial displacement is at most $\rho\|v\| = \delta/2 < \delta$.

    Since $\operatorname{Re}\mu > 0$, choose a single time $T \ge 0$ with
    $\rho\,e^{(\operatorname{Re}\mu)T}|v_i| \ge 2$, and let $z = e^{\mu T} v_i$, so
    $\rho|z| \ge 2$ and hence $\rho(|\operatorname{Re} z| + |\operatorname{Im} z|) \ge 2$.  One
    of the two components therefore carries at least half: either $\rho|\operatorname{Re} z|
    \ge 1$, and we take $q = \rho$, whose $i$-th coordinate at time $T$ is $\rho\operatorname{Re}
    z$; or $\rho|\operatorname{Im} z| \ge 1$, and we take $q = -i\rho$, whose $i$-th coordinate
    at time $T$ is $\rho\operatorname{Im} z$.  Either way the solution segment on $[0, T]$
    starts within $\delta$ of $x_{\mathrm{eq}}$ and reaches distance at least $1$ at time $T$, so
    no $\delta$ confines every solution segment to the unit ball. -/)]
theorem unstable_affineLinear_of_eigenvalue_re_pos
    (A : Matrix (Fin n) (Fin n) ℝ) (x_eq : ℝⁿ) (mu : ℂ) (v : Fin n → ℂ)
    (hv : v ≠ 0)
    (hAv : A.complexify *ᵥ v = mu • v)
    (hmu : 0 < mu.re) :
    Unstable (LinearSystems.affineLinearVectorField A x_eq) x_eq := by
  /- Some coordinate `vᵢ` of the eigenvector is nonzero, and `|e^{μT} vᵢ|` grows without
     bound.  At a time `T` where `ρ|e^{μT} vᵢ| ≥ 2`, its real or imaginary part carries at least
     half, and the matching real eigenmode (amplitude `ρ` or `-iρ`) escapes the unit ball. -/
  apply unstable_of_fixed_escape (by positivity : (0 : ℝ) < 1)
  intro delta hdelta
  have hvE : WithLp.toLp 2 v ≠ (0 : EuclideanSpace ℂ (Fin n)) := by
    intro h
    exact hv ((WithLp.toLp_eq_zero 2).mp h)
  have hvnorm : 0 < ‖WithLp.toLp 2 v‖ := norm_pos_iff.mpr hvE
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext j
    exact h j
  have hvinorm : 0 < ‖v i‖ := norm_pos_iff.mpr hi
  -- Step 1. The amplitude `ρ = δ / (2‖v‖)`, and a time `T ≥ 0` with `ρ e^{(Re μ) T} |vᵢ| ≥ 2`.
  let rho := delta / (2 * ‖WithLp.toLp 2 v‖)
  have hrho : 0 < rho := div_pos hdelta (mul_pos zero_lt_two hvnorm)
  have hexp_tendsto : Tendsto (fun t : ℝ => Real.exp (mu.re * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hmu)
  have hexp_event : ∀ᶠ t in atTop,
      2 / (rho * ‖v i‖) ≤ Real.exp (mu.re * t) :=
    hexp_tendsto.eventually_ge_atTop (2 / (rho * ‖v i‖))
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 hexp_event
  let T := max 0 t₀
  have hT : 0 ≤ T := le_max_left _ _
  have hgrowth_div : 2 / (rho * ‖v i‖) ≤ Real.exp (mu.re * T) :=
    ht₀ T (le_max_right _ _)
  have hden : 0 < rho * ‖v i‖ := mul_pos hrho hvinorm
  have hgrowth : 2 ≤ rho * Real.exp (mu.re * T) * ‖v i‖ := by
    rw [div_le_iff₀ hden] at hgrowth_div
    -- `2 ≤ e^{(Re μ) T} (ρ |vᵢ|)`, with the factors reordered.
    linarith
  -- Step 2. `z = e^{μT} vᵢ` has `ρ |z| ≥ 2`, hence `ρ (|Re z| + |Im z|) ≥ 2`.
  let z := Complex.exp (mu * (T : ℂ)) * v i
  have hznorm : ‖z‖ = Real.exp (mu.re * T) * ‖v i‖ := by
    dsimp [z]
    rw [Complex.norm_mul, Complex.norm_exp]
    congr 2
    simp
  have hcomponents : 2 ≤ rho * (|z.re| + |z.im|) := by
    calc
      2 ≤ rho * ‖z‖ := by rw [hznorm]; simpa [mul_assoc] using hgrowth
      _ ≤ rho * (|z.re| + |z.im|) := by
        gcongr
        exact Complex.norm_le_abs_re_add_abs_im z
  -- Step 3. The candidate solutions `x_eq + Re (q e^{μt} v)` with `|q| = ρ` solve the system
  -- on `[0, T]` and start within `δ` of `x_eq`.
  let phi (q : ℂ) : ℝ → ℝⁿ := fun t => x_eq + realEigenmode q mu v t
  have hphi_traj (q : ℂ) : IsTrajectoryOn (phi q)
      (LinearSystems.affineLinearVectorField A x_eq) 0 T := by
    intro t ht
    have hd := (hasDerivAt_realEigenmode_of_eigenvector A q mu v hAv t).const_add x_eq
    convert hd.hasDerivWithinAt using 1
    simp [phi, LinearSystems.affineLinearVectorField, realMulVec]
  have hphi_initial (q : ℂ) (hq : ‖q‖ = rho) :
      ‖phi q 0 - x_eq‖ < delta := by
    have hbound := norm_realEigenmode_le q mu v 0
    rw [hq] at hbound
    simp only [mul_zero, Real.exp_zero, mul_one] at hbound
    have hrho_eq : rho * ‖WithLp.toLp 2 v‖ = delta / 2 := by
      dsimp [rho]
      field_simp
    have hhalf : delta / 2 < delta := by linarith
    simpa [phi] using hbound.trans_lt (hrho_eq.trans_lt hhalf)
  have hphi_escape (q : ℂ) (h : 1 ≤ ‖realEigenmode q mu v T‖) : 1 ≤ ‖phi q T - x_eq‖ := by
    simpa [phi] using h
  -- Step 4. Whichever component of `z` carries half gives the escaping solution.
  by_cases hre : 1 ≤ rho * |z.re|
  · -- Real part carries half: take `q = ρ`, whose coordinate `i` at time `T` is `ρ Re z`.
    let qre : ℂ := rho
    have hqre_norm : ‖qre‖ = rho := by simp [qre, abs_of_pos hrho]
    refine ⟨T, phi qre, T, hphi_traj qre, hphi_initial qre hqre_norm, ⟨hT, le_rfl⟩, ?_⟩
    exact hphi_escape qre
      (one_le_norm_realEigenmode_of_apply hrho (realEigenmode_ofReal_apply rho mu v T i) hre)
  · -- Imaginary part carries half: take `q = -iρ`, whose coordinate `i` is `ρ Im z`.
    have him : 1 ≤ rho * |z.im| := by
      push Not at hre
      -- `ρ |Re z| < 1` and `ρ |Re z| + ρ |Im z| ≥ 2`.
      linarith
    let qim : ℂ := -(rho : ℂ) * Complex.I
    have hqim_norm : ‖qim‖ = rho := by simp [qim, hrho.le]
    refine ⟨T, phi qim, T, hphi_traj qim, hphi_initial qim hqim_norm, ⟨hT, le_rfl⟩, ?_⟩
    exact hphi_escape qim
      (one_le_norm_realEigenmode_of_apply hrho (realEigenmode_neg_I_apply rho mu v T i) him)

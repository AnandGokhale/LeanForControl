import LeanForControl.Analysis.FrechetDerivative
import LeanForControl.MatrixAlgebra.QuadraticForm
import LeanForControl.LinearSystems.Stability.Continuous.LyapunovEquation
import LeanForControl.Stability.LyapunovIndirect.Lyapunov
import LeanForControl.Stability.Autonomous
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Architect

/-!
# Stability from a Hurwitz linearization

This file proves the stable branch of Lyapunov's indirect method.  A positive-definite
solution of the continuous-time Lyapunov equation supplies a quadratic certificate, and
the Fréchet-derivative remainder is absorbed in a sufficiently small neighborhood of the
equilibrium.

Reference: Khalil, *Nonlinear Systems*.
-/

open Filter Set Topology
open scoped RealInnerProductSpace

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

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

/-- **Exponential decay from a linear differential inequality.** If `g` is continuous on
`[t₀, t₁]` and `g' ≤ -k g` on `(t₀, t₁)`, then `g t ≤ e^{-k(t - t₀)} g t₀` on `[t₀, t₁]`.

The weighted function `e^{ks} g(s)` has derivative `e^{ks} (k g + g') ≤ 0`, so it is
antitone.  (This is not an instance of `antitoneOn_V_add_linear`: the weight is
multiplicative, not additive, so the product rule rather than the sum rule drives the
derivative.) -/
private lemma le_exp_neg_mul_of_hasDerivAt {g g' : ℝ → ℝ} {k t₀ t₁ : ℝ}
    (hg_cont : ContinuousOn g (Icc t₀ t₁))
    (hg_deriv : ∀ s ∈ Ioo t₀ t₁, HasDerivAt g (g' s) s)
    (hg_decay : ∀ s ∈ Ioo t₀ t₁, k * g s + g' s ≤ 0) :
    ∀ t ∈ Icc t₀ t₁, g t ≤ Real.exp (-k * (t - t₀)) * g t₀ := by
  -- Step 1. The weighted function `W s = e^{ks} g(s)` has derivative `e^{ks} (k g s + g' s)`.
  set W : ℝ → ℝ := fun s => Real.exp (k * s) * g s with hW_def
  have hW_deriv : ∀ s ∈ Ioo t₀ t₁,
      HasDerivAt W (Real.exp (k * s) * (k * g s + g' s)) s := by
    intro s hs
    convert ((hasDerivAt_id s).const_mul k).exp.mul (hg_deriv s hs) using 1
    simp only [id_eq]
    ring
  -- Step 2. `W' ≤ 0` on the interior, so `W` is antitone on `[t₀, t₁]`.
  have hW_anti : AntitoneOn W (Icc t₀ t₁) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t₀ t₁)
    · exact (Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul continuousOn_id)).mul hg_cont
    · intro s hs
      rw [interior_Icc] at hs
      exact (hW_deriv s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hW_deriv s hs).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (hg_decay s hs)
  -- Step 3. Remove the weight: `g t = e^{-kt} W t ≤ e^{-kt} W t₀ = e^{-k(t - t₀)} g t₀`.
  intro t ht
  have hW_le : W t ≤ W t₀ := hW_anti (left_mem_Icc.mpr (ht.1.trans ht.2)) ht ht.1
  calc
    g t = Real.exp (-k * t) * W t := by
      rw [hW_def, ← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-k * t) * W t₀ := mul_le_mul_of_nonneg_left hW_le (Real.exp_pos _).le
    _ = Real.exp (-k * (t - t₀)) * g t₀ := by
      rw [hW_def, ← mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- **From a squared sandwich to an exponential bound.** If `m u² ≤ e^{-kτ} M v²` with
`0 < m ≤ M` and `u, v ≥ 0`, then `u ≤ (M/m) e^{-(k/2)τ} v`.

Dividing by `m` gives `u² ≤ (M/m) e^{-kτ} v²`; since `M/m ≥ 1` the factor `M/m` may be
enlarged to `(M/m)²`, which makes the right side a perfect square. -/
private lemma le_div_mul_exp_mul_of_mul_sq_le {m M k τ u v : ℝ} (hm : 0 < m) (hmM : m ≤ M)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (h : m * u ^ 2 ≤ Real.exp (-k * τ) * (M * v ^ 2)) :
    u ≤ M / m * Real.exp (-(k / 2) * τ) * v := by
  set C : ℝ := M / m with hC_def
  set rhs : ℝ := C * Real.exp (-(k / 2) * τ) * v
  have hC : 1 ≤ C := (le_div_iff₀ hm).2 (by simpa using hmM)
  have hrhs : 0 ≤ rhs := by positivity
  -- Step 1. Divide by `m`: `u² ≤ C e^{-kτ} v²`.
  have hsq : u ^ 2 ≤ C * Real.exp (-k * τ) * v ^ 2 := by
    calc
      u ^ 2 ≤ Real.exp (-k * τ) * (M * v ^ 2) / m := by
        apply (le_div_iff₀ hm).2
        simpa [mul_comm] using h
      _ = C * Real.exp (-k * τ) * v ^ 2 := by
        rw [hC_def]
        field_simp
  -- Step 2. `e^{-kτ}` is the square of `e^{-(k/2)τ}`.
  have hexp_sq : Real.exp (-k * τ) = Real.exp (-(k / 2) * τ) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  -- Step 3. `C ≤ C²`, so `u² ≤ rhs²`.
  have hsq_rhs : u ^ 2 ≤ rhs ^ 2 := by
    calc
      u ^ 2 ≤ C * Real.exp (-(k / 2) * τ) ^ 2 * v ^ 2 := by rw [← hexp_sq]; exact hsq
      _ ≤ C ^ 2 * Real.exp (-(k / 2) * τ) ^ 2 * v ^ 2 := by
        gcongr
        -- `C ≤ C²` because `1 ≤ C`.
        nlinarith [hC]
      _ = rhs ^ 2 := by ring
  -- Step 4. Both sides are nonnegative, so take square roots.
  exact (sq_le_sq₀ hu hrhs).1 hsq_rhs

/-- A positive-definite solution of the identity-forced Lyapunov equation for the
linearization gives local exponential stability of the nonlinear equilibrium on every
finite forward solution segment.

Reference: adapted from the quadratic-Lyapunov proof of the stable branch of Lyapunov's
indirect method; Khalil, *Nonlinear Systems*. -/
private theorem locallyExponentiallyStable_of_continuousLyapunovEquation
    (hn : 0 < n) {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (A P : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hP : P.PosDef) (hLyap : ContinuousLyapunovEquation A P 1) :
    LocallyExponentiallyStable f x_eq := by
  -- Idea: `V(x) = (x - x_eq)ᵀ P (x - x_eq)` is sandwiched between `m‖x - x_eq‖²` and
  -- `M‖x - x_eq‖²`, and near `x_eq` its Lie derivative is at most `-½‖x - x_eq‖² ≤ -k V`
  -- with `k = 1/(2M)`.  So `V` decays like `e^{-kt}` along solutions, and taking square roots
  -- gives `‖φ t - x_eq‖ ≤ C e^{-(k/2)(t - t₀)} ‖φ t₀ - x_eq‖` with `C = M/m`.
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  -- Step 1: `V` is a local Lyapunov function on `ball x_eq r`, so solutions starting within
  -- `ρ` of `x_eq` stay in that ball.
  obtain ⟨r, hr, hdecay⟩ :=
    exists_centeredQuadraticForm_decay A P hf heq hJac hLyap
  let V : ℝⁿ → ℝ := centeredQuadraticForm P x_eq
  let D : Set ℝⁿ := Metric.ball x_eq r
  have hlocal : IsLocalLyapunovFunction f V x_eq D := {
    hD_open := Metric.isOpen_ball
    hD_mem := by simp [D, hr]
    hcont := (centeredQuadraticForm_contDiff P x_eq).continuous
    hV_diff := (centeredQuadraticForm_contDiff P x_eq).differentiable (by norm_num)
    hzero := by simp [V, centeredQuadraticForm, quadraticForm]
    hpos := by
      intro x _ hx
      exact quadraticForm_pos P hP (sub_ne_zero.mpr hx)
    hLie_nonpos := by
      intro x hx
      have hx' : ‖x - x_eq‖ < r := by
        simpa [D, Metric.mem_ball, dist_eq_norm] using hx
      have hd := hdecay x hx'
      -- `-(1/2)‖x - x_eq‖² ≤ 0`, so the decay bound gives a nonpositive Lie derivative.
      nlinarith [sq_nonneg ‖x - x_eq‖] }
  have hstable : LyapunovStable f x_eq :=
    lyapunov_stable hn hlocal
  obtain ⟨ρ, hρ, hstay⟩ := hstable r hr
  -- Step 2: the constants.  `m‖y‖² ≤ yᵀPy ≤ M‖y‖²`, decay rate `k = 1/(2M)`, overshoot
  -- `C = M/m`, and norm decay rate `a = k/2`.
  obtain ⟨m, hm, hm_lower⟩ :=
    exists_pos_mul_norm_sq_le_quadraticForm P hP
  let p : ℝⁿ →L[ℝ] ℝⁿ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P
  let M : ℝ := ‖p‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hmM : m ≤ M := by
    let u : ℝⁿ := EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1
    have hu_norm : ‖u‖ = 1 := by simp [u, PiLp.norm_single]
    have hlower := hm_lower u
    have hupper := quadraticForm_le_opNorm_mul_norm_sq P u
    dsimp [p, M]
    rw [hu_norm, one_pow, mul_one] at hlower hupper
    linarith
  have hVupper (x : ℝⁿ) : V x ≤ M * ‖x - x_eq‖ ^ 2 := by
    calc
      V x ≤ ‖p‖ * ‖x - x_eq‖ ^ 2 := by
        simpa [V, centeredQuadraticForm, p] using
          quadraticForm_le_opNorm_mul_norm_sq P (x - x_eq)
      _ ≤ M * ‖x - x_eq‖ ^ 2 := by
        gcongr
        dsimp [M]
        linarith
  let k : ℝ := 1 / (2 * M)
  let C : ℝ := M / m
  let a : ℝ := k / 2
  have hk : 0 < k := by dsimp [k]; positivity
  have hC : 1 ≤ C := (le_div_iff₀ hm).2 (by simpa using hmM)
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨ρ, C, a, hρ, hC, ha, ?_⟩
  intro t₀ t₁ φ hφ hφ0 t ht
  have hstay' : ∀ s ∈ Icc t₀ t₁, ‖φ s - x_eq‖ < r :=
    hstay t₀ t₁ φ hφ hφ0
  -- Step 3: along the solution, `(V ∘ φ)' ≤ -½‖φ - x_eq‖² ≤ -k V(φ)`.
  have hVcurve : ∀ s ∈ Ioo t₀ t₁,
      HasDerivAt (V ∘ φ) (fderiv ℝ V (φ s) (f (φ s))) s := fun _ hs =>
    hasDerivAt_V_comp_traj
      ((centeredQuadraticForm_contDiff P x_eq).differentiable (by norm_num)) hφ hs
  have hVcurve_decay : ∀ s ∈ Ioo t₀ t₁,
      k * (V ∘ φ) s + fderiv ℝ V (φ s) (f (φ s)) ≤ 0 := by
    intro s hs
    have hdV : fderiv ℝ V (φ s) (f (φ s)) ≤ -(1 / 2 : ℝ) * ‖φ s - x_eq‖ ^ 2 :=
      hdecay (φ s) (hstay' s (Ioo_subset_Icc_self hs))
    have hkM : k * M = (1 / 2 : ℝ) := by
      dsimp [k]
      field_simp
    calc
      k * (V ∘ φ) s + fderiv ℝ V (φ s) (f (φ s))
          ≤ k * (M * ‖φ s - x_eq‖ ^ 2) - (1 / 2 : ℝ) * ‖φ s - x_eq‖ ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_left (hVupper (φ s)) hk.le)
              (by simpa only [neg_mul] using hdV)
      _ = 0 := by rw [← mul_assoc, hkM]; ring
  -- Step 4: hence `V` decays exponentially, `V(φ t) ≤ e^{-k(t - t₀)} V(φ t₀)`.
  have hVdecay : V (φ t) ≤ Real.exp (-k * (t - t₀)) * V (φ t₀) :=
    le_exp_neg_mul_of_hasDerivAt
      ((centeredQuadraticForm_contDiff P x_eq).continuous.comp_continuousOn hφ.continuousOn)
      hVcurve hVcurve_decay t ht
  -- Step 5: sandwich `V` between `m‖·‖²` and `M‖·‖²` and take square roots.
  have hsq_sandwich : m * ‖φ t - x_eq‖ ^ 2 ≤
      Real.exp (-k * (t - t₀)) * (M * ‖φ t₀ - x_eq‖ ^ 2) :=
    (hm_lower (φ t - x_eq)).trans (hVdecay.trans
      (mul_le_mul_of_nonneg_left (hVupper (φ t₀)) (Real.exp_pos _).le))
  exact le_div_mul_exp_mul_of_mul_sq_le hm hmM (norm_nonneg _) (norm_nonneg _) hsq_sandwich

/-- **Stable branch of Lyapunov's indirect method.** If the Jacobian at a `C¹`
equilibrium is Hurwitz, then the equilibrium is locally exponentially stable on every
finite forward solution segment.

Reference: Khalil, *Nonlinear Systems*.
-/
@[blueprint "thm:hurwitz-linearization-locally-exponentially-stable"
  (title := "Lyapunov's indirect method, stable branch")
  (statement := /-- Let $f : \mathbb{R}^n \to \mathbb{R}^n$ be $C^1$, and let
    $x_{\rm eq}$ be an equilibrium. If its Jacobian $A$ at the equilibrium is
    Hurwitz, then there are uniform local constants giving exponential decay
    along every finite forward solution segment that starts sufficiently close
    to $x_{\rm eq}$.

    Reference: Khalil, \emph{Nonlinear Systems}.
  -/)
  (proof := /-- Solve the identity-forced Lyapunov equation for a positive-definite
    $P$, use $V(x)=(x-x_{\rm eq})^{\mathsf T}P(x-x_{\rm eq})$, absorb the
    $o(\|x-x_{\rm eq}\|)$ linearization remainder on a small ball, and apply a
    weighted-energy estimate up to the first possible exit time. -/)]
theorem hurwitz_linearization_locally_exponentially_stable
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hA : IsHurwitz A) :
    LocallyExponentiallyStable f x_eq := by
  by_cases hn0 : n = 0
  · subst n
    refine ⟨1, 1, 1, zero_lt_one, le_rfl, zero_lt_one, ?_⟩
    intro t₀ t₁ φ _ _ t _
    rw [Subsingleton.elim (φ t) x_eq, Subsingleton.elim (φ t₀) x_eq]
    simp
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    obtain ⟨P, hP, hLyap, _⟩ :=
      hA.exists_posDef_unique_solution_continuous_lyapunov 1 Matrix.PosDef.one
    exact locallyExponentiallyStable_of_continuousLyapunovEquation
      hn A P hf heq hJac hP hLyap


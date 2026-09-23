import LeanForControl.Analysis.FrechetRemainder
import LeanForControl.MatrixAlgebra.QuadraticForm
import LeanForControl.LinearSystems.Stability.Continuous.LyapunovEquation
import LeanForControl.Stability.LyapunovIndirect.Lyapunov
import LeanForControl.Stability.LyapunovIndirect.Forward
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
theorem exists_centeredQuadraticForm_decay
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (A P : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hLyap : SolvesContinuousLyapunovEquation A P 1) :
    ∃ r > 0, ∀ x : ℝⁿ, ‖x - x_eq‖ < r →
      fderiv ℝ (centeredQuadraticForm P x_eq) x (f x) ≤
        -(1 / 2 : ℝ) * ‖x - x_eq‖ ^ 2 := by
  obtain ⟨r, hr, hrem⟩ :=
    exists_abs_fderiv_centeredQuadraticForm_remainder_le A P hf heq hJac
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

/-- A positive-definite solution of the identity-forced Lyapunov equation for the
linearization gives local exponential stability of the nonlinear equilibrium on every
finite forward solution segment.

Reference: adapted from the quadratic-Lyapunov proof of the stable branch of Lyapunov's
indirect method; Khalil, *Nonlinear Systems*. -/
theorem forwardLocallyExponentiallyStable_of_continuousLyapunovEquation
    (hn : 0 < n) {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (A P : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hP : P.PosDef) (hLyap : SolvesContinuousLyapunovEquation A P 1) :
    ForwardLocallyExponentiallyStable f x_eq := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
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
      nlinarith [sq_nonneg ‖x - x_eq‖] }
  have hstable : ForwardLyapunovStable f x_eq :=
    forwardLyapunovStable_of_isLocalLyapunovFunction hn hlocal
  obtain ⟨ρ, hρ, hstay⟩ := hstable r hr
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
  let k : ℝ := 1 / (2 * M)
  let C : ℝ := M / m
  let a : ℝ := k / 2
  have hk : 0 < k := by dsimp [k]; positivity
  have hC : 1 ≤ C := by
    dsimp [C]
    exact (le_div_iff₀ hm).2 (by simpa using hmM)
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨ρ, C, a, hρ, hC, ha, ?_⟩
  intro T φ hφ hφ0 t ht
  have hstay' : ∀ s ∈ Icc (0 : ℝ) T, ‖φ s - x_eq‖ < r :=
    hstay T φ hφ hφ0
  have hVupper (x : ℝⁿ) : V x ≤ M * ‖x - x_eq‖ ^ 2 := by
    calc
      V x ≤ ‖p‖ * ‖x - x_eq‖ ^ 2 := by
        simpa [V, centeredQuadraticForm, p] using
          quadraticForm_le_opNorm_mul_norm_sq P (x - x_eq)
      _ ≤ M * ‖x - x_eq‖ ^ 2 := by
        gcongr
        dsimp [M]
        linarith
  have hWanti : AntitoneOn
      (fun s : ℝ ↦ Real.exp (k * s) * V (φ s)) (Icc (0 : ℝ) T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) T)
    · exact
        ((Real.continuous_exp.comp_continuousOn
          (continuousOn_const.mul continuousOn_id)).mul
          ((centeredQuadraticForm_contDiff P x_eq).continuous.comp_continuousOn
            hφ.continuousOn))
    · intro s hs
      rw [interior_Icc] at hs
      have hsIcc : s ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hs
      have hcurve : HasDerivAt φ (f (φ s)) s :=
        (hφ s hsIcc).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
      have hVcurve : HasDerivAt (V ∘ φ)
          (fderiv ℝ V (φ s) (f (φ s))) s :=
        ((centeredQuadraticForm_contDiff P x_eq).differentiable (by norm_num) (φ s))
          |>.hasFDerivAt.comp_hasDerivAt s hcurve
      exact ((((hasDerivAt_id s).const_mul k).exp.mul hVcurve).differentiableAt)
        |>.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hsIcc : s ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hs
      have hcurve : HasDerivAt φ (f (φ s)) s :=
        (hφ s hsIcc).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
      have hVcurve : HasDerivAt (V ∘ φ)
          (fderiv ℝ V (φ s) (f (φ s))) s :=
        ((centeredQuadraticForm_contDiff P x_eq).differentiable (by norm_num) (φ s))
          |>.hasFDerivAt.comp_hasDerivAt s hcurve
      have hWderiv : HasDerivAt (fun q : ℝ ↦ Real.exp (k * q) * V (φ q))
          (Real.exp (k * s) *
            (k * V (φ s) + fderiv ℝ V (φ s) (f (φ s)))) s := by
        convert (((hasDerivAt_id s).const_mul k).exp.mul hVcurve) using 1
        simp only [id_eq, Function.comp_apply]
        ring
      rw [hWderiv.deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have hd := hdecay (φ s) (hstay' s hsIcc)
      have hdV : fderiv ℝ V (φ s) (f (φ s)) ≤
          -(1 / 2 : ℝ) * ‖φ s - x_eq‖ ^ 2 := by
        simpa [V] using hd
      have hv := hVupper (φ s)
      have hkM : k * M = (1 / 2 : ℝ) := by
        dsimp [k]
        field_simp
      calc
        k * V (φ s) + fderiv ℝ V (φ s) (f (φ s))
            ≤ k * (M * ‖φ s - x_eq‖ ^ 2) -
                (1 / 2 : ℝ) * ‖φ s - x_eq‖ ^ 2 := by
              exact add_le_add (mul_le_mul_of_nonneg_left hv hk.le)
                (by simpa only [neg_mul] using hdV)
        _ = 0 := by rw [← mul_assoc, hkM]; ring
  have hweighted : Real.exp (k * t) * V (φ t) ≤ V (φ 0) := by
    have hmono := hWanti (left_mem_Icc.mpr (ht.1.trans ht.2)) ht ht.1
    simpa using hmono
  have hVdecay : V (φ t) ≤ Real.exp (-k * t) * V (φ 0) := by
    calc
      V (φ t) = Real.exp (-k * t) * (Real.exp (k * t) * V (φ t)) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp (-k * t) * V (φ 0) :=
        mul_le_mul_of_nonneg_left hweighted (Real.exp_pos _).le
  have hlower := hm_lower (φ t - x_eq)
  have hupper0 := hVupper (φ 0)
  have hsq_mul : m * ‖φ t - x_eq‖ ^ 2 ≤
      Real.exp (-k * t) * (M * ‖φ 0 - x_eq‖ ^ 2) := by
    exact hlower.trans (hVdecay.trans
      (mul_le_mul_of_nonneg_left hupper0 (Real.exp_pos _).le))
  have hsq : ‖φ t - x_eq‖ ^ 2 ≤
      C * Real.exp (-k * t) * ‖φ 0 - x_eq‖ ^ 2 := by
    calc
      ‖φ t - x_eq‖ ^ 2 ≤
          (Real.exp (-k * t) * (M * ‖φ 0 - x_eq‖ ^ 2)) / m := by
        apply (le_div_iff₀ hm).2
        simpa [mul_comm] using hsq_mul
      _ = C * Real.exp (-k * t) * ‖φ 0 - x_eq‖ ^ 2 := by
        dsimp [C]
        field_simp
  have hexp_sq : Real.exp (-k * t) = Real.exp (-a * t) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    dsimp [a]
    ring
  let rhs : ℝ := C * Real.exp (-a * t) * ‖φ 0 - x_eq‖
  have hrhs : 0 ≤ rhs := by
    dsimp [rhs]
    positivity
  have hsq_rhs : ‖φ t - x_eq‖ ^ 2 ≤ rhs ^ 2 := by
    calc
      ‖φ t - x_eq‖ ^ 2 ≤
          C * Real.exp (-k * t) * ‖φ 0 - x_eq‖ ^ 2 := hsq
      _ = C * Real.exp (-a * t) ^ 2 * ‖φ 0 - x_eq‖ ^ 2 := by rw [hexp_sq]
      _ ≤ C ^ 2 * Real.exp (-a * t) ^ 2 * ‖φ 0 - x_eq‖ ^ 2 := by
        gcongr
        nlinarith [hC]
      _ = rhs ^ 2 := by simp [rhs]; ring
  have hnorm : ‖φ t - x_eq‖ ≤ rhs := by
    nlinarith [norm_nonneg (φ t - x_eq), hrhs]
  simpa [rhs] using hnorm

/-- A positive-definite solution of the identity-forced Lyapunov equation for the
linearization implies local asymptotic stability in the legacy global-trajectory API.

Original compatibility corollary of
`forwardLocallyExponentiallyStable_of_continuousLyapunovEquation`. -/
theorem localAsymptoticStable_of_continuousLyapunovEquation
    (hn : 0 < n) {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (A P : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hP : P.PosDef) (hLyap : SolvesContinuousLyapunovEquation A P 1) :
    LocalAsymptoticStable f x_eq :=
  (forwardLocallyExponentiallyStable_of_continuousLyapunovEquation
    hn A P hf heq hJac hP hLyap).localAsymptoticStable

/-- **Stable branch of Lyapunov's indirect method.** If the Jacobian at a `C¹`
equilibrium is Hurwitz, then the equilibrium is locally exponentially stable on every
finite forward solution segment.

Reference: Khalil, *Nonlinear Systems*.
-/
@[blueprint "thm:hurwitz-linearization-forward-locally-exponentially-stable"
  (statement := /-- Let $f : \mathbb{R}^n \to \mathbb{R}^n$ be $C^1$, and let
    $x_{\rm eq}$ be an equilibrium. If its Jacobian $A$ at the equilibrium is
    Hurwitz, then there are uniform local constants giving exponential decay
    along every finite forward solution segment that starts sufficiently close
    to $x_{\rm eq}$. -/)
  (proof := /-- Solve the identity-forced Lyapunov equation for a positive-definite
    $P$, use $V(x)=(x-x_{\rm eq})^{\mathsf T}P(x-x_{\rm eq})$, absorb the
    $o(\|x-x_{\rm eq}\|)$ linearization remainder on a small ball, and apply a
    weighted-energy estimate up to the first possible exit time. -/)]
theorem hurwitz_linearization_forward_locally_exponentially_stable
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hA : IsHurwitz A) :
    ForwardLocallyExponentiallyStable f x_eq := by
  by_cases hn0 : n = 0
  · subst n
    refine ⟨1, 1, 1, zero_lt_one, le_rfl, zero_lt_one, ?_⟩
    intro T φ _ _ t _
    rw [Subsingleton.elim (φ t) x_eq, Subsingleton.elim (φ 0) x_eq]
    simp
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    obtain ⟨P, hP, hLyap, _⟩ :=
      hA.exists_posDef_unique_solution_continuous_lyapunov 1 Matrix.PosDef.one
    exact forwardLocallyExponentiallyStable_of_continuousLyapunovEquation
      hn A P hf heq hJac hP hLyap

/-- **Lyapunov's indirect method, stable branch.** If the Jacobian at a `C¹`
equilibrium is Hurwitz, then the equilibrium is locally asymptotically stable for every
globally defined trajectory.  The stronger finite-forward-segment exponential theorem is
`hurwitz_linearization_forward_locally_exponentially_stable`.

Reference: Khalil, *Nonlinear Systems*.

Original compatibility corollary of
`hurwitz_linearization_forward_locally_exponentially_stable`.
-/
@[blueprint "thm:hurwitz-linearization-local-asymptotic-stable"
  (statement := /-- As a compatibility corollary of the finite-forward exponential
    theorem, a Hurwitz Jacobian makes the equilibrium locally asymptotically stable
    for the repository's legacy globally defined trajectory predicate. -/)
  (proof := /-- Restrict each globally defined trajectory to finite forward
    segments, apply the uniform exponential estimate, and pass from that estimate
    to the legacy stability and convergence clauses. -/)]
theorem hurwitz_linearization_local_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hA : IsHurwitz A) :
    LocalAsymptoticStable f x_eq :=
  (hurwitz_linearization_forward_locally_exponentially_stable
    A hf heq hJac hA).localAsymptoticStable

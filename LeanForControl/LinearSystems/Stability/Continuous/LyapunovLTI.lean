import LeanForControl.LinearSystems.Solutions.CtsLTI
import LeanForControl.LinearSystems.Stability.DefsStability
import LeanForControl.Analysis.SpectralRadius
import LeanForControl.MatrixAlgebra.Exponential
import LeanForControl.MatrixAlgebra.Spectrum
import LeanForControl.LinearSystems.Stability.Continuous.LyapunovLTV
import Architect

/-!
# `LinearSystems.Stability.Continuous.LyapunovLTI`

Hespanha's Theorem 8.1: for a *time-invariant* system `ẋ = A x`, each of the stability
notions of Definition 8.1 is an eigenvalue condition on `A`.

`LyapunovLTV.lean` already turned every clause of Definition 8.1 into a bound on the state
transition matrix `Φ(t, t₀)`. For a constant `A` that matrix is `e^{A(t-t₀)}`
(`stateTransitionMatrix_const`), so what is left is purely a matrix-algebra question: when
does `e^{At}` decay? This file is the bridge; the matrix algebra is the first section, which
knows nothing about systems and is destined to move to `MatrixAlgebra/`.

## Contents

* **Theorem 8.1(2)** — `ContinuousLinearSystem.timeInvariant.asymptoticStableNA_iff_isHurwitz`:
  asymptotic stability holds exactly when every eigenvalue of `A` has strictly negative real
  part.
* **Theorem 8.1(3)** — `ContinuousLinearSystem.timeInvariant.exponentiallyStableNA_iff_isHurwitz`:
  and so does exponential stability, under the same condition.

Both are in the `ContinuousLinearSystem.timeInvariant` namespace, so that with
`open ContinuousLinearSystem` they read `timeInvariant.asymptoticStableNA_iff_isHurwitz`.

## Scope

Clauses (1) and (4) ask that the Jordan blocks at eigenvalues on the imaginary axis be
`1 × 1`. Mathlib has no Jordan normal form, so those clauses need a Jordan-free
restatement — semisimplicity of `A` on its imaginary-axis spectrum — and are not attempted
here yet.

## On the eigenvalue condition

"Every eigenvalue of `A` has strictly negative real part" is `IsHurwitz`, from
`Stability/DefsStability.lean`. It is stated there through eigenpairs of the complexification
rather than through `spectrum`, which is both how it is produced here
(`MatrixAlgebra.exists_eigenpair_of_mem_spectrum_exp`) and how it is consumed.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.1.
-/

namespace LinearSystems

open Matrix Set Filter Topology NormedSpace ContinuousLinearSystem
open scoped Matrix.Norms.Operator

variable {X U Y : Type*} [Fintype X] [DecidableEq X] [Fintype U]

/-! ## The matrix algebra

`IsHurwitz A`, decay of `e^{At}` to zero, and an explicit exponential envelope for `‖e^{At}‖`
are proved equivalent, with no system semantics anywhere in the section. Everything is about
the real matrix `A`, with the spectral condition read off the complexification `A ⊗ ℂ`.
-/

section Matrices

variable (A : Matrix X X ℝ)

omit [Fintype X] [DecidableEq X] in
/-- The decay envelope `t ↦ K e^{-γ (t - t₀)}` vanishes at infinity, for `γ > 0`.

Nothing but `Real.tendsto_exp_atBot` composed with the affine map `t ↦ -γ (t - t₀)`, which
tends to `atBot` because `-γ < 0`. -/
private lemma tendsto_const_mul_exp_neg (K t₀ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun t : ℝ => K * Real.exp (-γ * (t - t₀))) atTop (𝓝 0) := by
  have haff : Tendsto (fun t : ℝ => -γ * (t - t₀)) atTop atBot :=
    Tendsto.const_mul_atTop_of_neg (by linarith)
      (by simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-t₀) tendsto_id)
  simpa using (Real.tendsto_exp_atBot.comp haff).const_mul K

/-- Under the Hurwitz condition the complexified exponential has spectral radius below one.

`spectralRadius` is defined from `spectrum`, which is purely algebraic, so this says nothing
about which norm is in play — but it is what Gelfand's formula consumes. -/
private lemma spectralRadius_exp_complexification_lt_one
    (hA : IsHurwitz A) :
    spectralRadius ℂ (exp (A.map (algebraMap ℝ ℂ))) < 1 := by
  rcases isEmpty_or_nonempty X with _ | _
  · rw [Subsingleton.elim (exp (A.map (algebraMap ℝ ℂ))) 0,
      spectrum.spectralRadius_zero]
    exact zero_lt_one
  · refine spectrum.spectralRadius_lt_of_forall_lt _ fun z hz => ?_
    have hz1 : ‖z‖ < 1 := by
      obtain ⟨μ, v, hv, hAv, rfl⟩ := MatrixAlgebra.exists_eigenpair_of_mem_spectrum_exp _ hz
      rw [Complex.norm_exp]
      exact Real.exp_lt_one_iff.mpr (hA μ v hv hAv)
    simpa only [ENNReal.coe_lt_coe] using hz1

/-- **The contractive block.**
Under the Hurwitz condition some positive integer time `m` has `‖e^{Am}‖ < 1`.

This is Gelfand's formula applied to the previous lemma. The contraction is in the `L∞`
operator norm, which is what makes it usable against `Matrix.linfty_opNorm_mulVec` later. -/
private lemma exists_norm_exp_nsmul_lt_one
    (hA : IsHurwitz A) :
    ∃ m : ℕ, 0 < m ∧ ‖exp ((m : ℝ) • A)‖ < 1 := by
  rcases isEmpty_or_nonempty X with _ | _
  · refine ⟨1, one_pos, ?_⟩
    rw [Subsingleton.elim (exp (((1 : ℕ) : ℝ) • A)) 0]
    simp
  · obtain ⟨m, hm0, hm⟩ := exists_pow_norm_lt_one_of_spectralRadius_lt_one
      (exp (A.map (algebraMap ℝ ℂ)))
      (spectralRadius_exp_complexification_lt_one A hA)
    refine ⟨m, hm0, ?_⟩
    calc ‖exp ((m : ℝ) • A)‖
        = ‖(exp ((m : ℝ) • A)).map (algebraMap ℝ ℂ)‖ := by
          simp [Matrix.linfty_opNorm_def]
      _ = ‖exp (((m : ℝ) • A).map (algebraMap ℝ ℂ))‖ := by
          rw [MatrixAlgebra.complexification_exp]
      _ = ‖exp (m • A.map (algebraMap ℝ ℂ))‖ := by
          congr 2
          ext i j
          simp
      _ = ‖exp (A.map (algebraMap ℝ ℂ)) ^ m‖ := by rw [Matrix.exp_nsmul]
      _ < 1 := hm

/-- `‖e^{Ar}‖` is bounded on the compact interval `[0, b]`, by at least `1`. -/
private lemma exists_norm_exp_le_on_Icc (b : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ r ∈ Set.Icc (0 : ℝ) b, ‖exp (r • A)‖ ≤ M := by
  have hcont : ContinuousOn (fun r : ℝ => exp (r • A)) (Set.Icc 0 b) :=
    (exp_continuous.comp (continuous_id.smul continuous_const)).continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨max C 1, le_max_right _ _, fun r hr => (hC r hr).trans (le_max_left _ _)⟩

/-- **Hurwitz implies uniform exponential decay.**
If every eigenvalue of `A` has strictly negative real part then `‖e^{At}‖` decays
exponentially.

The contractive block `‖e^{Am}‖ ≤ c < 1` decays geometrically along the arithmetic progression
`0, m, 2m, …`; writing `t = qm + r` with `r ∈ [0, m)` and bounding `‖e^{Ar}‖` by its maximum
`M` over the compact `[0, m]` spreads that into decay in `t`, at rate `γ = -log c / m` and
with constant `M / c`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.1. -/
theorem IsHurwitz.exists_norm_exp_le {A : Matrix X X ℝ} (hA : IsHurwitz A) :
    ∃ k > (0 : ℝ), ∃ γ > (0 : ℝ), ∀ t : ℝ, 0 ≤ t →
      ‖exp (t • A)‖ ≤ k * Real.exp (-γ * t) := by
  -- A contracting block of length `p`.
  obtain ⟨p, hp0, hpc⟩ : ∃ p : ℝ, 0 < p ∧ ‖exp (p • A)‖ < 1 := by
    obtain ⟨m, hm0, hm⟩ := exists_norm_exp_nsmul_lt_one A hA
    exact ⟨m, by exact_mod_cast hm0, hm⟩
  -- Its contraction factor `c`, kept away from `0` so that `Real.log c` is available.
  obtain ⟨c, hc0, hc1, hcle⟩ :
      ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ‖exp (p • A)‖ ≤ c :=
    ⟨max ‖exp (p • A)‖ (1 / 2),
      lt_of_lt_of_le (by norm_num) (le_max_right _ _),
      max_lt hpc (by norm_num), le_max_left _ _⟩
  -- A bound on one block, and the decay rate that `c` per block amounts to per unit time.
  obtain ⟨M, hM1, hMb⟩ := exists_norm_exp_le_on_Icc A p
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  obtain ⟨γ, hγ0, hγp⟩ : ∃ γ : ℝ, 0 < γ ∧ γ * p = -Real.log c :=
    ⟨-Real.log c / p, div_pos (neg_pos.2 (Real.log_neg hc0 hc1)) hp0,
      div_mul_cancel₀ (-Real.log c) hp0.ne'⟩
  refine ⟨M / c, by positivity, γ, hγ0, fun t ht => ?_⟩
  -- Split `t` into `q` whole blocks and a remainder `r ∈ [0, p)`.
  obtain ⟨q, r, hr0, hrlt, hqp⟩ :
      ∃ (q : ℕ) (r : ℝ), 0 ≤ r ∧ r < p ∧ (q : ℝ) * p = t - r := by
    have hpt : t / p * p = t := div_mul_cancel₀ t hp0.ne'
    refine ⟨⌊t / p⌋₊, t - (⌊t / p⌋₊ : ℝ) * p, ?_, ?_, by ring⟩
    · have hfl := mul_le_mul_of_nonneg_right
        (Nat.floor_le (div_nonneg ht hp0.le) (a := t / p)) hp0.le
      rw [hpt] at hfl
      linarith
    · have hfl := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (t / p)) hp0
      rw [hpt] at hfl
      have hexp : ((⌊t / p⌋₊ : ℝ) + 1) * p = (⌊t / p⌋₊ : ℝ) * p + p := by ring
      linarith [hexp ▸ hfl]
  calc ‖exp (t • A)‖
      = ‖exp (r • A) * exp (p • A) ^ q‖ := by
        -- `t = r + qp`, and the two exponents commute, so the exponential factors.
        congr 1
        have hq : exp (((q : ℝ) * p) • A) = exp (p • A) ^ q := by
          rw [← Matrix.exp_nsmul]
          congr 1
          ext i j
          simp [mul_assoc]
        rw [← hq, ← Matrix.exp_add_of_commute _ _
          (((Commute.refl A).smul_left r).smul_right _), ← add_smul]
        congr 2
        linarith
    _ ≤ M * c ^ q := by
        -- Each of the `q` blocks contributes a factor `c`; the remainder contributes `M`.
        have key : ∀ j : ℕ,
            ‖exp (r • A) * exp (p • A) ^ j‖ ≤ M * c ^ j := by
          intro j
          induction j with
          | zero => simpa using hMb r ⟨hr0, hrlt.le⟩
          | succ j ih =>
              calc ‖exp (r • A) * exp (p • A) ^ (j + 1)‖
                  = ‖exp (r • A) * exp (p • A) ^ j *
                      exp (p • A)‖ := by rw [pow_succ, mul_assoc]
                _ ≤ ‖exp (r • A) * exp (p • A) ^ j‖ *
                      ‖exp (p • A)‖ := norm_mul_le _ _
                _ ≤ M * c ^ j * c := mul_le_mul ih hcle (norm_nonneg _) (by positivity)
                _ = M * c ^ (j + 1) := by ring
        exact key q
    _ = M * Real.exp (-(γ * ((q : ℝ) * p))) := by
        -- `c = e^{-γp}`, so `c^q = e^{-γ q p}`.
        have hlogeq : Real.log c = -(γ * p) := by rw [hγp]; ring
        rw [show -(γ * ((q : ℝ) * p)) = (q : ℝ) * Real.log c by rw [hlogeq]; ring,
          Real.exp_nat_mul, Real.exp_log hc0]
    _ ≤ M * (Real.exp (-γ * t) * c⁻¹) := by
        -- `qp ≥ t - p`, since the remainder `r` is below `p`; the slack costs one factor `c⁻¹`.
        refine mul_le_mul_of_nonneg_left ?_ hM0.le
        have hshift : Real.exp (-(γ * (t - p))) = Real.exp (-γ * t) * c⁻¹ := by
          rw [show (c : ℝ)⁻¹ = Real.exp (γ * p) by
                rw [hγp, Real.exp_neg, Real.exp_log hc0],
            ← Real.exp_add]
          ring_nf
        have hstep : γ * (t - p) ≤ γ * ((q : ℝ) * p) :=
          mul_le_mul_of_nonneg_left (by linarith) hγ0.le
        rw [← hshift]
        exact Real.exp_le_exp.2 (by linarith)
    _ = M / c * Real.exp (-γ * t) := by field_simp

/-- The decay estimate applied to a state, which is the form Lyapunov stability consumes.

Separated from `IsHurwitz.exists_norm_exp_le` because the bound on the matrix is the real
content; this is one application of `Matrix.linfty_opNorm_mulVec`, and it is the step where
the choice of the `L∞` operator norm earns its keep. -/
theorem IsHurwitz.exists_norm_exp_mulVec_le {A : Matrix X X ℝ} (hA : IsHurwitz A) :
    ∃ k > (0 : ℝ), ∃ γ > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → ∀ x : X → ℝ,
      ‖exp (t • A) *ᵥ x‖ ≤ k * Real.exp (-γ * t) * ‖x‖ := by
  obtain ⟨k, hk, γ, hγ, hbd⟩ := hA.exists_norm_exp_le
  exact ⟨k, hk, γ, hγ, fun t ht x =>
    (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_right (hbd t ht) (norm_nonneg x))⟩

/-- Pointwise decay of `e^{At}` on real states upgrades to decay of the matrix itself.

Feeding the hypothesis the standard basis vectors returns the columns of `e^{At}`
(`Matrix.mulVec_single_one`), and convergence in `Matrix X X ℝ` is entrywise. -/
private lemma tendsto_exp_of_tendsto_exp_mulVec
    (h : ∀ x : X → ℝ,
      Tendsto (fun t : ℝ => exp (t • A) *ᵥ x) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => exp (t • A)) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hcol := tendsto_pi_nhds.1 (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using hcol

/-- **Decay implies Hurwitz.**
If `e^{At} → 0` then every eigenvalue of `A` has strictly negative real part.

Stated from mere convergence rather than from an exponential bound, so that it serves clause
(2) and clause (3) alike: asymptotic and exponential stability each imply it.

Complexification is continuous, so the limit carries across to the complex eigenvector `v` —
but `e^{At} v = e^{μ t} v` has norm `e^{t · Re μ} ‖v‖ ≥ ‖v‖ > 0` whenever `Re μ ≥ 0`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.1. -/
theorem isHurwitz_of_tendsto_exp
    (hmat : Tendsto (fun t : ℝ => exp (t • A)) atTop (𝓝 0)) :
    IsHurwitz A := by
  intro μ v hv hAv
  by_contra hre
  push Not at hre
  -- Complexifying and applying to `v` is continuous, so the limit carries across to `ℂ`.
  have hcx : Tendsto (fun t : ℝ =>
      ‖(exp (t • A)).map (algebraMap ℝ ℂ) *ᵥ v‖) atTop (𝓝 0) := by
    have hcont : Continuous fun M : Matrix X X ℝ => M.map (algebraMap ℝ ℂ) *ᵥ v :=
      Continuous.matrix_mulVec
        (continuous_id.matrix_map (by simpa using Complex.continuous_ofReal)) continuous_const
    simpa using ((hcont.tendsto 0).comp hmat).norm
  -- So some time past `0` has it below `‖v‖`. But it never drops below `‖v‖`.
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
  obtain ⟨t, ht, hlt⟩ :=
    ((eventually_ge_atTop (0 : ℝ)).and (hcx.eventually_lt_const hv0)).exists
  refine absurd hlt (not_lt.2 ?_)
  calc ‖v‖ = 1 * ‖v‖ := (one_mul _).symm
    _ ≤ Real.exp (t * μ.re) * ‖v‖ :=
        -- `Re μ ≥ 0` and `t ≥ 0`, so the scalar factor is at least one.
        mul_le_mul_of_nonneg_right
          (by simpa using Real.exp_le_exp.2 (mul_nonneg ht hre)) (norm_nonneg v)
    _ = ‖exp ((t : ℂ) * μ)‖ * ‖v‖ := by
        rw [← Complex.exp_eq_exp_ℂ, Complex.norm_exp]
        simp [Complex.mul_re]
    _ = ‖exp ((t : ℂ) • A.map (algebraMap ℝ ℂ)) *ᵥ v‖ := by
        -- `v` is an eigenvector of `tAℂ` with eigenvalue `tμ`, so of its exponential too.
        rw [MatrixAlgebra.exp_mulVec_of_mulVec_eq_smul _ _ _
            (show ((t : ℂ) • A.map (algebraMap ℝ ℂ)) *ᵥ v = ((t : ℂ) * μ) • v by
              rw [Matrix.smul_mulVec, hAv, smul_smul]),
          norm_smul]
    _ = ‖(exp (t • A)).map (algebraMap ℝ ℂ) *ᵥ v‖ := by
        have hmap : (exp (t • A)).map (algebraMap ℝ ℂ)
            = exp ((t : ℂ) • A.map (algebraMap ℝ ℂ)) := by
          rw [MatrixAlgebra.complexification_exp]
          congr 1
          ext i j
          simp
        rw [hmap]

/-! ### The equivalences

Hurwitz, decay of `e^{At}` to zero, and an explicit exponential envelope for it are the same
condition. Stated as two `Iff`s rather than a `List.TFAE` because each is used directly: the
first is what clause (2) of Theorem 8.1 needs, the second what clause (3) needs.
-/

/-- `A` is Hurwitz exactly when `e^{At} → 0`. -/
theorem isHurwitz_iff_tendsto_exp :
    IsHurwitz A ↔ Tendsto (fun t : ℝ => exp (t • A)) atTop (𝓝 0) := by
  refine ⟨fun hA => ?_, isHurwitz_of_tendsto_exp A⟩
  obtain ⟨k, hk, γ, hγ, hbd⟩ := hA.exists_norm_exp_le
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero_norm' ?_ (by simpa using tendsto_const_mul_exp_neg k 0 hγ)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simpa [abs_of_nonneg (norm_nonneg _)] using hbd t ht

/-- `A` is Hurwitz exactly when `‖e^{At}‖` admits an exponentially decaying envelope. -/
theorem isHurwitz_iff_exists_norm_exp_le :
    IsHurwitz A ↔ ∃ k > (0 : ℝ), ∃ γ > (0 : ℝ), ∀ t : ℝ, 0 ≤ t →
      ‖exp (t • A)‖ ≤ k * Real.exp (-γ * t) := by
  refine ⟨fun hA => hA.exists_norm_exp_le, fun h => ?_⟩
  obtain ⟨k, hk, γ, hγ, hbd⟩ := h
  rw [isHurwitz_iff_tendsto_exp, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero_norm' ?_ (by simpa using tendsto_const_mul_exp_neg k 0 hγ)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simpa [abs_of_nonneg (norm_nonneg _)] using hbd t ht

end Matrices

namespace ContinuousLinearSystem.timeInvariant

/-! ## Theorem 8.1(2): asymptotic stability -/

omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.1(2).**
The time-invariant system `ẋ = A x` is asymptotically stable if and only if every eigenvalue
of `A` has strictly negative real part.

That this is the *same* condition as exponential stability (Theorem 8.1(3)) is a genuine
feature of the time-invariant case; for a time-varying `A(t)` the two differ, as
`ẋ = -x / (1 + t)` shows. The equivalence between them is not recorded here — it belongs with
the Lyapunov-equation development of Theorem 8.2.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.1(2). -/
theorem asymptoticStableNA_iff_isHurwitz
    (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix Y X ℝ) (D : Matrix Y U ℝ) :
    AsymptoticStableNA ((timeInvariant A B C D).vectorField 0) (0 : X → ℝ) ↔
      IsHurwitz A := by
  classical
  have hcoeff : (timeInvariant A B C D).A = fun _ => A := rfl
  have hhr : ∀ (t₀ : ℝ) (x₀ : X → ℝ), homogeneousResponse (fun _ => A) t₀ x₀
      = fun t => exp ((t - t₀) • A) *ᵥ x₀ := by
    intro t₀ x₀
    funext t
    simp [homogeneousResponse, stateTransitionMatrix_const]
  rw [asymptoticStableNA_iff_decayingHomogeneousResponse _ (by simpa using continuous_const)]
  simp only [hcoeff, hhr]
  constructor
  · rintro ⟨-, hconv⟩
    refine isHurwitz_of_tendsto_exp A (tendsto_exp_of_tendsto_exp_mulVec A fun x => ?_)
    simpa using hconv 0 le_rfl x
  · intro hA
    obtain ⟨k, hk, γ, hγ, hbd⟩ := hA.exists_norm_exp_mulVec_le
    refine ⟨fun t₀ _ x₀ => ⟨k * ‖x₀‖, fun t ht => ?_⟩, fun t₀ _ x₀ => ?_⟩
    · calc ‖exp ((t - t₀) • A) *ᵥ x₀‖
          ≤ k * Real.exp (-γ * (t - t₀)) * ‖x₀‖ := hbd (t - t₀) (by linarith) x₀
        _ ≤ k * 1 * ‖x₀‖ := by
            gcongr
            exact Real.exp_le_one_iff.mpr
              (by simpa [neg_mul] using mul_nonneg hγ.le (sub_nonneg.2 ht))
        _ = k * ‖x₀‖ := by ring
    · refine squeeze_zero_norm' ?_ (tendsto_const_mul_exp_neg (k * ‖x₀‖) t₀ hγ)
      filter_upwards [eventually_ge_atTop t₀] with t ht
      simpa [mul_comm, mul_assoc, mul_left_comm] using hbd (t - t₀) (by linarith) x₀

/-! ## Theorem 8.1(3): exponential stability -/

-- `DecidableEq X` is needed only by the `L∞` operator norm inside the proof, not by the
-- statement, so it is reinstated there with `classical`.
omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.1(3).**
The time-invariant system `ẋ = A x` is exponentially stable if and only if every eigenvalue
of `A` has strictly negative real part.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.1(3). -/
theorem exponentiallyStableNA_iff_isHurwitz
    (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix Y X ℝ) (D : Matrix Y U ℝ) :
    ExponentiallyStableNA ((timeInvariant A B C D).vectorField 0) (0 : X → ℝ) ↔
      IsHurwitz A := by
  classical
  have hcoeff : (timeInvariant A B C D).A = fun _ => A := rfl
  rw [exponentiallyStableNA_iff_decayingStateTransition _ (by simpa using continuous_const)]
  simp only [hcoeff, stateTransitionMatrix_const]
  constructor
  · rintro ⟨k, hk, γ, hγ, hbd⟩
    refine isHurwitz_of_tendsto_exp A (tendsto_exp_of_tendsto_exp_mulVec A fun x => ?_)
    refine squeeze_zero_norm' ?_ (by simpa using tendsto_const_mul_exp_neg (k * ‖x‖) 0 hγ)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simpa [mul_comm, mul_assoc, mul_left_comm] using hbd 0 le_rfl t ht x
  · intro heig
    obtain ⟨k, hk, γ, hγ, hbd⟩ := heig.exists_norm_exp_mulVec_le
    exact ⟨k, hk, γ, hγ, fun t₀ _ t ht x => hbd (t - t₀) (by linarith) x⟩

end ContinuousLinearSystem.timeInvariant

end LinearSystems

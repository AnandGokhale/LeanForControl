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
does `e^{At}` decay? This file is the bridge; the matrix algebra is the two private lemmas
at the top.

## Contents

* **Theorem 8.1(3)** — `exponentiallyStableNA_timeInvariant_iff`: exponential stability
  holds exactly when every eigenvalue of `A` has strictly negative real part.

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

open Matrix Set Filter Topology ContinuousLinearSystem
open scoped Matrix.Norms.Operator

variable {X U Y : Type*} [Fintype X] [DecidableEq X] [Fintype U]

/-! ## The matrix algebra

Two facts about `e^{At}`, one in each direction, stated with no system semantics in them.
Both are about the real matrix `A`, with the spectral condition read off the
complexification `A ⊗ ℂ`.
-/

section Matrices

variable (A : Matrix X X ℝ)

omit [Fintype X] [DecidableEq X] in
/-- `t ↦ k e^{-γ t}` vanishes at infinity, for `γ > 0`. -/
private lemma tendsto_const_mul_exp_neg_atTop (k : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun t : ℝ => k * Real.exp (-γ * t)) atTop (𝓝 0) := by
  have hbot : Tendsto (fun t : ℝ => -γ * t) atTop atBot := by
    refine tendsto_atBot.2 fun b => ?_
    filter_upwards [eventually_ge_atTop (-b / γ)] with t ht
    nlinarith [(div_le_iff₀ hγ).1 ht]
  simpa using (Real.tendsto_exp_atBot.comp hbot).const_mul k

/-- The `L∞` operator norm is unchanged by entrywise complexification.

Mathlib has the Frobenius version (`Matrix.frobenius_norm_map_eq`) but not this one, and the
Frobenius norm is no use here: it does not satisfy `‖M *ᵥ x‖ ≤ ‖M‖ ‖x‖` for the sup norm on
`X → ℝ`. -/
private lemma linfty_opNorm_map_algebraMap (M : Matrix X X ℝ) :
    ‖M.map (algebraMap ℝ ℂ)‖ = ‖M‖ := by
  simp [Matrix.linfty_opNorm_def]

/-- Under the Hurwitz condition the complexified exponential has spectral radius below one.

`spectralRadius` is defined from `spectrum`, which is purely algebraic, so this says nothing
about which norm is in play — but it is what Gelfand's formula consumes. -/
private lemma spectralRadius_exp_complexification_lt_one
    (hA : IsHurwitz A) :
    spectralRadius ℂ (NormedSpace.exp (A.map (algebraMap ℝ ℂ))) < 1 := by
  rcases isEmpty_or_nonempty X with _ | _
  · rw [Subsingleton.elim (NormedSpace.exp (A.map (algebraMap ℝ ℂ))) 0,
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
    ∃ m : ℕ, 0 < m ∧ ‖NormedSpace.exp ((m : ℝ) • A)‖ < 1 := by
  rcases isEmpty_or_nonempty X with _ | _
  · refine ⟨1, one_pos, ?_⟩
    rw [Subsingleton.elim (NormedSpace.exp (((1 : ℕ) : ℝ) • A)) 0]
    simp
  · obtain ⟨m, hm0, hm⟩ := exists_pow_norm_lt_one_of_spectralRadius_lt_one
      (NormedSpace.exp (A.map (algebraMap ℝ ℂ)))
      (spectralRadius_exp_complexification_lt_one A hA)
    refine ⟨m, hm0, ?_⟩
    calc ‖NormedSpace.exp ((m : ℝ) • A)‖
        = ‖(NormedSpace.exp ((m : ℝ) • A)).map (algebraMap ℝ ℂ)‖ :=
          (linfty_opNorm_map_algebraMap _).symm
      _ = ‖NormedSpace.exp (((m : ℝ) • A).map (algebraMap ℝ ℂ))‖ := by
          rw [MatrixAlgebra.complexification_exp]
      _ = ‖NormedSpace.exp (m • A.map (algebraMap ℝ ℂ))‖ := by
          congr 2
          ext i j
          simp
      _ = ‖NormedSpace.exp (A.map (algebraMap ℝ ℂ)) ^ m‖ := by rw [Matrix.exp_nsmul]
      _ < 1 := hm

/-- `‖e^{Ar}‖` is bounded on the compact interval `[0, b]`, by at least `1`. -/
private lemma exists_norm_exp_le_on_Icc (b : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ r ∈ Set.Icc (0 : ℝ) b, ‖NormedSpace.exp (r • A)‖ ≤ M := by
  have hcont : ContinuousOn (fun r : ℝ => NormedSpace.exp (r • A)) (Set.Icc 0 b) :=
    (NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)).continuousOn
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
      ‖NormedSpace.exp (t • A)‖ ≤ k * Real.exp (-γ * t) := by
  obtain ⟨m, hm0, hm⟩ := exists_norm_exp_nsmul_lt_one A hA
  -- `p` is the length of the contracting block, `c` its contraction factor, kept away from
  -- `0` so that `log c` is available.
  set p : ℝ := (m : ℝ) with hpdef
  have hp0 : 0 < p := by rw [hpdef]; exact_mod_cast hm0
  set c : ℝ := max ‖NormedSpace.exp (p • A)‖ (1 / 2) with hcdef
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hc1 : c < 1 := max_lt hm (by norm_num)
  have hcle : ‖NormedSpace.exp (p • A)‖ ≤ c := le_max_left _ _
  obtain ⟨M, hM1, hMb⟩ := exists_norm_exp_le_on_Icc A p
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  set γ : ℝ := -Real.log c / p with hγdef
  have hlogc : Real.log c < 0 := Real.log_neg hc0 hc1
  have hγ0 : 0 < γ := div_pos (by linarith) hp0
  have hγp : γ * p = -Real.log c := by rw [hγdef]; field_simp
  -- A product `N · (e^{Ap})^j` contracts geometrically. Stated as a product rather than
  -- bounding `‖(e^{Ap})^j‖` alone because the `L∞` operator norm has no `NormOneClass`
  -- instance, so the `j = 0` case could not be discharged by `‖1‖ ≤ 1`.
  have hprod : ∀ (N : Matrix X X ℝ) (j : ℕ), ‖N‖ ≤ M →
      ‖N * NormedSpace.exp (p • A) ^ j‖ ≤ M * c ^ j := by
    intro N j hN
    induction j with
    | zero => simpa using hN
    | succ j ih =>
        calc ‖N * NormedSpace.exp (p • A) ^ (j + 1)‖
            = ‖N * NormedSpace.exp (p • A) ^ j * NormedSpace.exp (p • A)‖ := by
              rw [pow_succ, mul_assoc]
          _ ≤ ‖N * NormedSpace.exp (p • A) ^ j‖ * ‖NormedSpace.exp (p • A)‖ := norm_mul_le _ _
          _ ≤ M * c ^ j * c := by
              exact mul_le_mul ih hcle (norm_nonneg _) (by positivity)
          _ = M * c ^ (j + 1) := by ring
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
  have hsplit : NormedSpace.exp (t • A)
      = NormedSpace.exp (r • A) * NormedSpace.exp (p • A) ^ q := by
    have hcomm : Commute (r • A) (((q : ℝ) * p) • A) :=
      ((Commute.refl A).smul_left r).smul_right _
    have hq : NormedSpace.exp (((q : ℝ) * p) • A) = NormedSpace.exp (p • A) ^ q := by
      rw [← Matrix.exp_nsmul]
      congr 1
      ext i j
      simp [mul_assoc]
    rw [← hq, ← Matrix.exp_add_of_commute _ _ hcomm, ← add_smul]
    congr 2
    linarith
  -- Turn the geometric bound into an exponential one.
  have hlogeq : Real.log c = -(γ * p) := by rw [hγp]; ring
  have hcq : c ^ q = Real.exp (-(γ * ((q : ℝ) * p))) := by
    rw [show -(γ * ((q : ℝ) * p)) = (q : ℝ) * Real.log c by rw [hlogeq]; ring,
      Real.exp_nat_mul, Real.exp_log hc0]
  have hstep : γ * (t - p) ≤ γ * ((q : ℝ) * p) :=
    mul_le_mul_of_nonneg_left (by linarith) hγ0.le
  have hgp : Real.exp (γ * p) = c⁻¹ := by rw [hγp, Real.exp_neg, Real.exp_log hc0]
  have hshift : Real.exp (-(γ * (t - p))) = Real.exp (-γ * t) * c⁻¹ := by
    rw [← hgp, ← Real.exp_add]
    ring_nf
  calc ‖NormedSpace.exp (t • A)‖ ≤ M * c ^ q := by
        rw [hsplit]; exact hprod _ q (hMb r ⟨hr0, hrlt.le⟩)
    _ = M * Real.exp (-(γ * ((q : ℝ) * p))) := by rw [hcq]
    _ ≤ M * (Real.exp (-γ * t) * c⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ hM0.le
        rw [← hshift]
        exact Real.exp_le_exp.2 (by linarith)
    _ = M / c * Real.exp (-γ * t) := by field_simp

/-- The decay estimate applied to a state, which is the form Lyapunov stability consumes.

Separated from `IsHurwitz.exists_norm_exp_le` because the bound on the matrix is the real
content; this is one application of `Matrix.linfty_opNorm_mulVec`, and it is the step where
the choice of the `L∞` operator norm earns its keep. -/
theorem IsHurwitz.exists_norm_exp_mulVec_le {A : Matrix X X ℝ} (hA : IsHurwitz A) :
    ∃ k > (0 : ℝ), ∃ γ > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → ∀ x : X → ℝ,
      ‖NormedSpace.exp (t • A) *ᵥ x‖ ≤ k * Real.exp (-γ * t) * ‖x‖ := by
  obtain ⟨k, hk, γ, hγ, hbd⟩ := hA.exists_norm_exp_le
  exact ⟨k, hk, γ, hγ, fun t ht x =>
    (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_right (hbd t ht) (norm_nonneg x))⟩

/-- Pointwise decay of `e^{At}` on real states upgrades to decay of the matrix itself.

Feeding the hypothesis the standard basis vectors returns the columns of `e^{At}`
(`Matrix.mulVec_single_one`), and convergence in `Matrix X X ℝ` is entrywise. -/
private lemma tendsto_exp_of_tendsto_exp_mulVec
    (h : ∀ x : X → ℝ,
      Tendsto (fun t : ℝ => NormedSpace.exp (t • A) *ᵥ x) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => NormedSpace.exp (t • A)) atTop (𝓝 0) := by
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
    (hmat : Tendsto (fun t : ℝ => NormedSpace.exp (t • A)) atTop (𝓝 0)) :
    IsHurwitz A := by
  intro μ v hv hAv
  by_contra hre
  push Not at hre
  -- Complexifying and applying to `v` is continuous, so it carries the limit along.
  have hcont : Continuous fun M : Matrix X X ℝ => M.map (algebraMap ℝ ℂ) *ᵥ v := by
    refine Continuous.matrix_mulVec ?_ continuous_const
    exact continuous_id.matrix_map (by simpa using Complex.continuous_ofReal)
  have hcx : Tendsto (fun t : ℝ =>
      (NormedSpace.exp (t • A)).map (algebraMap ℝ ℂ) *ᵥ v) atTop (𝓝 0) := by
    simpa using (hcont.tendsto 0).comp hmat
  have hcxnorm : Tendsto (fun t : ℝ =>
      ‖(NormedSpace.exp (t • A)).map (algebraMap ℝ ℂ) *ᵥ v‖) atTop (𝓝 0) := by
    simpa using hcx.norm
  -- But along the eigenvector that quantity never drops below `‖v‖`.
  have hlb : ∀ t : ℝ, 0 ≤ t →
      ‖v‖ ≤ ‖(NormedSpace.exp (t • A)).map (algebraMap ℝ ℂ) *ᵥ v‖ := by
    intro t ht
    have hmap : (NormedSpace.exp (t • A)).map (algebraMap ℝ ℂ)
        = NormedSpace.exp ((t : ℂ) • A.map (algebraMap ℝ ℂ)) := by
      rw [MatrixAlgebra.complexification_exp]
      congr 1
      ext i j
      simp
    have heig : ((t : ℂ) • A.map (algebraMap ℝ ℂ)) *ᵥ v = ((t : ℂ) * μ) • v := by
      rw [Matrix.smul_mulVec, hAv, smul_smul]
    have hnormexp : ‖NormedSpace.exp ((t : ℂ) * μ)‖ = Real.exp (t * μ.re) := by
      rw [← Complex.exp_eq_exp_ℂ, Complex.norm_exp]
      simp [Complex.mul_re]
    have hone : (1 : ℝ) ≤ Real.exp (t * μ.re) := by
      simpa using Real.exp_le_exp.2 (mul_nonneg ht hre)
    rw [hmap, MatrixAlgebra.exp_mulVec_of_mulVec_eq_smul _ _ _ heig, norm_smul, hnormexp]
    nlinarith [norm_nonneg v]
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
  obtain ⟨t, ht0, hlt⟩ :=
    ((eventually_ge_atTop (0 : ℝ)).and (hcxnorm.eventually_lt_const hv0)).exists
  exact absurd (hlb t ht0) (not_le.2 hlt)

/-! ### The equivalences

Hurwitz, decay of `e^{At}` to zero, and an explicit exponential envelope for it are the same
condition. Stated as two `Iff`s rather than a `List.TFAE` because each is used directly: the
first is what clause (2) of Theorem 8.1 needs, the second what clause (3) needs.
-/

/-- `A` is Hurwitz exactly when `e^{At} → 0`. -/
theorem isHurwitz_iff_tendsto_exp :
    IsHurwitz A ↔ Tendsto (fun t : ℝ => NormedSpace.exp (t • A)) atTop (𝓝 0) := by
  refine ⟨fun hA => ?_, isHurwitz_of_tendsto_exp A⟩
  obtain ⟨k, hk, γ, hγ, hbd⟩ := hA.exists_norm_exp_le
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero_norm' ?_ (tendsto_const_mul_exp_neg_atTop k hγ)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simpa [abs_of_nonneg (norm_nonneg _)] using hbd t ht

/-- `A` is Hurwitz exactly when `‖e^{At}‖` admits an exponentially decaying envelope. -/
theorem isHurwitz_iff_exists_norm_exp_le :
    IsHurwitz A ↔ ∃ k > (0 : ℝ), ∃ γ > (0 : ℝ), ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • A)‖ ≤ k * Real.exp (-γ * t) := by
  refine ⟨fun hA => hA.exists_norm_exp_le, fun h => ?_⟩
  obtain ⟨k, hk, γ, hγ, hbd⟩ := h
  rw [isHurwitz_iff_tendsto_exp, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero_norm' ?_ (tendsto_const_mul_exp_neg_atTop k hγ)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simpa [abs_of_nonneg (norm_nonneg _)] using hbd t ht

end Matrices

/-! ## Theorem 8.1(3): exponential stability -/

-- `DecidableEq X` is needed only by the `L∞` operator norm inside the proof, not by the
-- statement, so it is reinstated there with `classical`.
omit [DecidableEq X] in
/-- **Hespanha, Theorem 8.1(3).**
The time-invariant system `ẋ = A x` is exponentially stable if and only if every eigenvalue
of `A` has strictly negative real part.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.1(3). -/
theorem exponentiallyStableNA_timeInvariant_iff
    (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix Y X ℝ) (D : Matrix Y U ℝ) :
    ExponentiallyStableNA ((timeInvariant A B C D).vectorField 0) (0 : X → ℝ) ↔
      IsHurwitz A := by
  classical
  have hcoeff : (timeInvariant A B C D).A = fun _ => A := rfl
  rw [exponentiallyStableNA_linear_iff _ (by simpa using continuous_const)]
  simp only [hcoeff, stateTransitionMatrix_const]
  constructor
  · rintro ⟨k, hk, γ, hγ, hbd⟩
    refine isHurwitz_of_tendsto_exp A (tendsto_exp_of_tendsto_exp_mulVec A fun x => ?_)
    have hlim : Tendsto (fun t : ℝ => k * Real.exp (-γ * t) * ‖x‖) atTop (𝓝 0) := by
      simpa using (tendsto_const_mul_exp_neg_atTop k hγ).mul_const ‖x‖
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simpa using hbd 0 le_rfl t ht x
  · intro heig
    obtain ⟨k, hk, γ, hγ, hbd⟩ := heig.exists_norm_exp_mulVec_le
    exact ⟨k, hk, γ, hγ, fun t₀ _ t ht x => hbd (t - t₀) (by linarith) x⟩

end LinearSystems

import LeanForControl.Analysis.SpectralRadius
import LeanForControl.LinearSystems.Stability.DefsStability
import LeanForControl.MatrixAlgebra.Complex
import LeanForControl.MatrixAlgebra.Eigenpair
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Architect

/-!
# `LinearSystems.Stability.Discrete.Schur`

The Schur condition (every eigenvalue in the open unit disc) as a condition on the powers of
`A`: it is equivalent to `Aᵏ → 0` and to a geometric envelope `‖Aᵏ‖ ≤ C ρᵏ` with `ρ < 1`.  The
discrete-time counterpart of `LinearSystems.Stability.Continuous.Hurwitz`, with `Aᵏ` in place of
`e^{At}`; no system semantics appear.

* `IsSchur.exists_norm_pow_le` — Schur gives a geometric envelope.  The spectral radius of `A`
  over `ℂ` is below `1`, so by Gelfand's formula some power `Aᵐ` contracts, and the contraction
  per block of `m` steps spreads to a geometric rate.
* `isSchur_of_tendsto_pow` — conversely, if `Aᵏ → 0` then `A` is Schur: an eigenvector with
  `|μ| ≥ 1` would have `‖Aᵏ v‖ = |μ|ᵏ ‖v‖ ≥ ‖v‖`.

Norms are the `L∞` operator norm, as on the continuous side.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.3.
-/

namespace LinearSystems

open Matrix Set Filter Topology
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Schur gives a geometric envelope -/

/-- **A Schur matrix has spectral radius below one** over `ℂ`. -/
lemma IsSchur.spectralRadius_lt_one [Nonempty X] {A : Matrix X X ℝ} (hA : IsSchur A) :
    spectralRadius ℂ A.complexify < 1 := by
  refine spectrum.spectralRadius_lt_of_forall_lt _ fun z hz => ?_
  obtain ⟨v, hv, hAv⟩ := (MatrixAlgebra.mem_spectrum_iff_exists_eigenpair _ _).1 hz
  simpa only [ENNReal.coe_lt_coe] using hA z v hv hAv

/-- Under the Schur condition some positive power of `A` is a strict contraction. -/
private lemma IsSchur.exists_pow_norm_lt_one {A : Matrix X X ℝ} (hA : IsSchur A) :
    ∃ m : ℕ, 0 < m ∧ ‖A ^ m‖ < 1 := by
  rcases isEmpty_or_nonempty X with _ | _
  · refine ⟨1, one_pos, ?_⟩
    rw [Subsingleton.elim (A ^ 1) 0]
    simp
  · obtain ⟨m, hm0, hm⟩ := exists_pow_norm_lt_one_of_spectralRadius_lt_one A.complexify
      hA.spectralRadius_lt_one
    refine ⟨m, hm0, ?_⟩
    calc ‖A ^ m‖ = ‖(A ^ m).complexify‖ := (Matrix.linfty_opNorm_complexify _).symm
      _ = ‖A.complexify ^ m‖ := by rw [Matrix.complexify_pow]
      _ < 1 := hm

/-- **Schur implies a geometric envelope.**  If every eigenvalue of `A` lies in the open unit
disc, then `‖Aᵏ‖ ≤ C ρᵏ` for some `C > 0` and `0 ≤ ρ < 1`.

Some power `Aᵐ` contracts, `‖Aᵐ‖ ≤ c < 1`.  Writing `k = r + m q` with `r < m`,
`‖Aᵏ‖ ≤ ‖Aʳ‖ ‖Aᵐ‖^q ≤ M c^q`, with `M` the largest `‖Aʳ‖`, `r < m`; and `c^q = ρ^{mq}` for
`ρ = c^{1/m}`, which costs one factor `c⁻¹` against `ρᵏ`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.3. -/
@[blueprint "thm:isSchur-exists-norm-pow-le"
  (title := "A Schur matrix has geometrically decaying powers")
  (statement := /-- If $A$ is Schur (\cref{def:stability-isSchur}) then there are $C > 0$ and
    $0 \le \rho < 1$ with
    \[
      \|A^{k}\| \le C\,\rho^{k}, \qquad \forall\, k \in \mathbb{N}.
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.3.
  -/)
  (proof := /-- The spectral radius of $A_{\mathbb C}$ is below $1$, so by Gelfand's formula
    (\cref{lem:exists-pow-norm-lt-one}) some power has $\|A^{m}\| < 1$; fix
    $\|A^{m}\| \le c < 1$ with $c > 0$, and let $M$ bound $\|A^{r}\|$ for $r < m$.  Writing
    $k = r + mq$ with $r < m$, submultiplicativity gives $\|A^{k}\| \le M c^{q}$, and with
    $\rho = c^{1/m}$, $c^{q} = \rho^{mq} \le \rho^{k}/c$. -/)]
theorem IsSchur.exists_norm_pow_le {A : Matrix X X ℝ} (hA : IsSchur A) :
    ∃ C > (0 : ℝ), ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k : ℕ, ‖A ^ k‖ ≤ C * ρ ^ k := by
  obtain ⟨m, hm0, hmc⟩ := hA.exists_pow_norm_lt_one
  -- The contraction factor `c`, kept away from `0`, and the per-step rate `ρ = c^{1/m}`.
  set c := max ‖A ^ m‖ (1 / 2) with hc_def
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hc1 : c < 1 := max_lt hmc (by norm_num)
  have hAm : ‖A ^ m‖ ≤ c := le_max_left _ _
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  set ρ := c ^ ((m : ℝ)⁻¹) with hρ_def
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hc0 _
  have hρ1 : ρ < 1 := Real.rpow_lt_one hc0.le hc1 (inv_pos.mpr hm0')
  have hρm : ρ ^ m = c := by
    rw [hρ_def, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le, inv_mul_cancel₀ hm0'.ne',
      Real.rpow_one]
  -- `M` bounds one block.
  set M := ∑ r ∈ Finset.range m, ‖A ^ r‖ with hM_def
  have hM : ∀ r < m, ‖A ^ r‖ ≤ M := fun r hr =>
    Finset.single_le_sum (f := fun r => ‖A ^ r‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr hr)
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨M / c + 1, by positivity, ρ, hρ0.le, hρ1, fun k => ?_⟩
  -- Split `k = r + m q` with `r < m`.
  set q := k / m with hq_def
  set r := k % m with hr_def
  have hk : k = r + m * q := (Nat.mod_add_div k m).symm
  have hr : r < m := Nat.mod_lt k hm0
  -- `‖Aᵏ‖ ≤ M c^q`.
  have hblock : ‖A ^ k‖ ≤ M * c ^ q := by
    rw [hk, pow_add, pow_mul]
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · rw [hq0, pow_zero, mul_one, pow_zero, mul_one]
      exact hM r hr
    · calc ‖A ^ r * (A ^ m) ^ q‖ ≤ ‖A ^ r‖ * ‖(A ^ m) ^ q‖ := norm_mul_le _ _
        _ ≤ M * c ^ q := by
          refine mul_le_mul (hM r hr) ((norm_pow_le' _ hqpos).trans ?_) (norm_nonneg _) hM0
          exact pow_le_pow_left₀ (norm_nonneg _) hAm q
  -- `c · c^q ≤ ρᵏ`, since `c^q = ρ^{mq}` and `ρ^m ≤ ρ^r`.
  have hcq : c * c ^ q ≤ ρ ^ k := by
    calc c * c ^ q = ρ ^ m * ρ ^ (m * q) := by rw [hρm, pow_mul, hρm]
      _ ≤ ρ ^ r * ρ ^ (m * q) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hρ0.le hρ1.le hr.le) (by positivity)
      _ = ρ ^ k := by rw [← pow_add, ← hk]
  have hMρ : M * c ^ q ≤ M / c * ρ ^ k := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
    nlinarith [mul_le_mul_of_nonneg_left hcq hM0]
  calc ‖A ^ k‖ ≤ M / c * ρ ^ k := hblock.trans hMρ
    _ ≤ (M / c + 1) * ρ ^ k := by nlinarith [pow_nonneg hρ0.le k]

/-- The geometric envelope applied to a state. -/
@[blueprint "thm:isSchur-exists-norm-pow-mulVec-le"
  (title := "Geometric decay of the state under a Schur matrix")
  (statement := /-- If $A$ is Schur (\cref{def:stability-isSchur}) then there are $C > 0$ and
    $0 \le \rho < 1$ with $\|A^{k}x\| \le C\,\rho^{k}\,\|x\|$ for every $k$ and $x$. -/)
  (proof := /-- \cref{thm:isSchur-exists-norm-pow-le} and
    $\|Ax\|_{\infty} \le \|A\|_{\infty}\|x\|_{\infty}$. -/)]
theorem IsSchur.exists_norm_pow_mulVec_le {A : Matrix X X ℝ} (hA : IsSchur A) :
    ∃ C > (0 : ℝ), ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (k : ℕ) (x : X → ℝ),
      ‖A ^ k *ᵥ x‖ ≤ C * ρ ^ k * ‖x‖ := by
  obtain ⟨C, hC, ρ, hρ0, hρ1, h⟩ := hA.exists_norm_pow_le
  exact ⟨C, hC, ρ, hρ0, hρ1, fun k x =>
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right (h k) (norm_nonneg x))⟩

/-! ## Decay forces the Schur condition -/

section Matrices

variable (A : Matrix X X ℝ)

/-- **Decay implies Schur.**  If `Aᵏ → 0` then every eigenvalue of `A` lies in the open unit
disc: an eigenvector `v` with `|μ| ≥ 1` has `‖Aᵏ v‖ = |μ|ᵏ ‖v‖ ≥ ‖v‖ > 0`. -/
@[blueprint "thm:isSchur-of-tendsto-pow"
  (title := "Decay of the matrix powers forces the Schur condition")
  (statement := /-- If $A^{k} \to 0$ as $k \to \infty$ then $A$ is Schur
    (\cref{def:stability-isSchur}).

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.3.
  -/)
  (proof := /-- Suppose $|\mu| \ge 1$ for an eigenpair $(\mu, v)$ of $A_{\mathbb C}$ with
    $v \ne 0$.  Complexification is continuous, so $A^{k}_{\mathbb C}v \to 0$; but
    $A^{k}_{\mathbb C}v = \mu^{k}v$ (\cref{lem:pow-mulVec-eigenpair}) has norm
    $|\mu|^{k}\|v\| \ge \|v\| > 0$. -/)]
theorem isSchur_of_tendsto_pow (hmat : Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0)) :
    IsSchur A := by
  intro μ v hv hAv
  by_contra hμ
  push Not at hμ
  -- Complexifying and applying to `v` is continuous, so the limit carries across to `ℂ`.
  have hcx : Tendsto (fun k : ℕ => ‖(A ^ k).complexify *ᵥ v‖) atTop (𝓝 0) := by
    have hcont : Continuous fun M : Matrix X X ℝ => M.complexify *ᵥ v :=
      Continuous.matrix_mulVec
        (continuous_id.matrix_map (by simpa using Complex.continuous_ofReal)) continuous_const
    simpa using ((hcont.tendsto 0).comp hmat).norm
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
  obtain ⟨k, hlt⟩ := (hcx.eventually_lt_const hv0).exists
  refine absurd hlt (not_lt.2 ?_)
  calc ‖v‖ = 1 * ‖v‖ := (one_mul _).symm
    _ ≤ ‖μ‖ ^ k * ‖v‖ := mul_le_mul_of_nonneg_right (one_le_pow₀ hμ) (norm_nonneg v)
    _ = ‖(A ^ k).complexify *ᵥ v‖ := by
        rw [Matrix.complexify_pow, MatrixAlgebra.pow_mulVec_of_mulVec_eq_smul hAv, norm_smul,
          norm_pow]

/-- Pointwise decay of `Aᵏ x` on real states upgrades to decay of `Aᵏ`: the standard basis
vectors return its columns. -/
private lemma tendsto_pow_of_tendsto_pow_mulVec
    (h : ∀ x : X → ℝ, Tendsto (fun k : ℕ => A ^ k *ᵥ x) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hcol := tendsto_pi_nhds.1 (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using hcol

/-- Pointwise decay of the state on real initial conditions forces the Schur condition. -/
@[blueprint "thm:isSchur-of-tendsto-pow-mulVec"
  (title := "Pointwise decay of the state forces the Schur condition")
  (statement := /-- If $A^{k}x \to 0$ as $k \to \infty$ for every real state $x$, then $A$ is
    Schur (\cref{def:stability-isSchur}). -/)
  (proof := /-- The standard basis vectors return the columns of $A^{k}$, so $A^{k} \to 0$;
    apply \cref{thm:isSchur-of-tendsto-pow}. -/)]
theorem isSchur_of_tendsto_pow_mulVec
    (h : ∀ x : X → ℝ, Tendsto (fun k : ℕ => A ^ k *ᵥ x) atTop (𝓝 0)) : IsSchur A :=
  isSchur_of_tendsto_pow A (tendsto_pow_of_tendsto_pow_mulVec A h)

/-! ## The equivalences -/

/-- A geometric envelope for `‖Aᵏ‖` makes `Aᵏ` vanish. -/
private lemma tendsto_pow_of_norm_pow_le {C ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hbd : ∀ k : ℕ, ‖A ^ k‖ ≤ C * ρ ^ k) : Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) :=
  squeeze_zero_norm hbd (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C)

/-- `A` is Schur exactly when `Aᵏ → 0`. -/
@[blueprint "thm:isSchur-iff-tendsto-pow"
  (title := "Schur is decay of the matrix powers")
  (statement := /-- A real square matrix $A$ is Schur (\cref{def:stability-isSchur}) if and only
    if $A^{k} \to 0$ as $k \to \infty$. -/)
  (proof := /-- Forwards, \cref{thm:isSchur-exists-norm-pow-le} supplies a geometric envelope;
    backwards is \cref{thm:isSchur-of-tendsto-pow}. -/)]
theorem isSchur_iff_tendsto_pow : IsSchur A ↔ Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) := by
  refine ⟨fun hA => ?_, isSchur_of_tendsto_pow A⟩
  obtain ⟨C, -, ρ, hρ0, hρ1, hbd⟩ := hA.exists_norm_pow_le
  exact tendsto_pow_of_norm_pow_le A hρ0 hρ1 hbd

/-- `A` is Schur exactly when `‖Aᵏ‖` admits a geometric envelope. -/
@[blueprint "thm:isSchur-iff-exists-norm-pow-le"
  (title := "Schur is a geometric envelope for the matrix powers")
  (statement := /-- A real square matrix $A$ is Schur (\cref{def:stability-isSchur}) if and only
    if there are $C > 0$ and $0 \le \rho < 1$ with $\|A^{k}\| \le C\rho^{k}$ for all $k$. -/)
  (proof := /-- Forwards is \cref{thm:isSchur-exists-norm-pow-le}; backwards, the envelope
    forces $A^{k} \to 0$ and \cref{thm:isSchur-iff-tendsto-pow} applies. -/)]
theorem isSchur_iff_exists_norm_pow_le :
    IsSchur A ↔ ∃ C > (0 : ℝ), ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k : ℕ, ‖A ^ k‖ ≤ C * ρ ^ k := by
  refine ⟨fun hA => hA.exists_norm_pow_le, ?_⟩
  rintro ⟨C, -, ρ, hρ0, hρ1, hbd⟩
  exact (isSchur_iff_tendsto_pow A).2 (tendsto_pow_of_norm_pow_le A hρ0 hρ1 hbd)

end Matrices

end LinearSystems

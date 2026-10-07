import LeanForControl.Analysis.SpectralRadius
import LeanForControl.LinearSystems.Stability.DefsStability
import LeanForControl.MatrixAlgebra.Complex
import LeanForControl.MatrixAlgebra.Exponential
import Mathlib.Analysis.Matrix.Normed
import Architect

/-!
# Hurwitz matrices

What the Hurwitz condition is equivalent to, and the rate-indexed refinement of it.

`IsHurwitz A` says every eigenvalue of `A` has strictly negative real part
(`Stability/DefsStability.lean`). This file proves it equivalent to two analytic conditions on
the matrix exponential — that `e^{At}` vanishes, and that `‖e^{At}‖` admits an exponentially
decaying envelope — and collects the API of `IsHurwitzWithRate`, which records a strict
spectral margin and is related to `IsHurwitz` by a spectral shift.

Nothing here mentions a system: these are facts about a matrix. Hespanha's Theorem 8.1 turns
them into statements about `ẋ = A x` in `LyapunovLTI.lean`.

## Note on two generic lemmas

`tendsto_const_mul_exp_neg` and `tendsto_zero_of_norm_le_envelope` are real analysis with no
matrices in them, and are candidates for `Analysis/`. They are public because
`LyapunovLTI.lean` needs them.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 8, Theorem 8.1.
-/

namespace LinearSystems

open Matrix Set Filter Topology NormedSpace
open scoped Matrix.Norms.Operator ComplexOrder

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## The rate-indexed predicate -/

omit [DecidableEq X] in
/-- Ordinary Hurwitz stability is exactly Hurwitz stability with rate zero.

`IsHurwitz` is stated primitively rather than as `IsHurwitzWithRate 0`, so that it unfolds
to `μ.re < 0` on the nose; `-0 = 0` is not definitional for the reals, which is why this is
no longer `Iff.rfl`.

Original: this is the compatibility lemma for the rate-indexed definition. -/
@[blueprint "lem:isHurwitz-iff-isHurwitzWithRate-zero"
  (title := "Hurwitz is rate zero")
  (latexEnv := "lemma")
  (statement := /-- A real square matrix $A$ is Hurwitz (\cref{def:stability-isHurwitz}) if and
    only if it is Hurwitz with decay rate $0$ (\cref{def:stability-isHurwitzWithRate}). -/)
  (proof := /-- Both unfold to a condition on $\operatorname{Re}\mu$, the first to
    $\operatorname{Re}\mu < 0$ and the second to $\operatorname{Re}\mu < -0$. -/)]
theorem isHurwitz_iff_isHurwitzWithRate_zero (A : Matrix X X ℝ) :
    IsHurwitz A ↔ IsHurwitzWithRate 0 A := by
  simp [IsHurwitz, IsHurwitzWithRate]

omit [DecidableEq X] in
/-- A certified Hurwitz decay rate may be weakened.

Original: monotonicity of the rate-indexed predicate. -/
@[blueprint "lem:isHurwitzWithRate-mono"
  (title := "A certified decay rate may be weakened")
  (latexEnv := "lemma")
  (statement := /-- If $A$ is Hurwitz with decay rate $\alpha$
    (\cref{def:stability-isHurwitzWithRate}) and $\beta \le \alpha$, then $A$ is Hurwitz with
    decay rate $\beta$. -/)
  (proof := /-- Each eigenvalue satisfies $\operatorname{Re}\mu < -\alpha \le -\beta$. -/)]
theorem IsHurwitzWithRate.mono {A : Matrix X X ℝ} {α β : ℝ}
    (hA : IsHurwitzWithRate α A) (hβα : β ≤ α) :
    IsHurwitzWithRate β A := by
  intro μ v hv hAv
  have hμ := hA μ v hv hAv
  linarith

omit [DecidableEq X] in
/-- Zero-dimensional matrices are Hurwitz with every rate, vacuously, because there is no
nonzero eigenvector.

Original: documents the chosen zero-dimensional convention. -/
@[blueprint "lem:isHurwitzWithRate-of-isEmpty"
  (title := "Zero-dimensional matrices are vacuously Hurwitz")
  (latexEnv := "lemma")
  (statement := /-- If the index type is empty then every $A$ is Hurwitz with every decay rate
    $\alpha$ (\cref{def:stability-isHurwitzWithRate}).

    This records the convention chosen for the degenerate case: the predicate quantifies over
    nonzero eigenvectors, and in dimension zero there are none. -/)
  (proof := /-- There is no nonzero vector, so the hypothesis of the predicate is never
    met. -/)]
theorem isHurwitzWithRate_of_isEmpty [IsEmpty X] (α : ℝ) (A : Matrix X X ℝ) :
    IsHurwitzWithRate α A := by
  intro μ v hv
  exfalso
  apply hv
  funext i
  exact isEmptyElim i

/-- A matrix has decay rate `α` exactly when shifting it by `α I` makes it Hurwitz.

The sign is positive: an eigenvalue `μ` of `A` becomes `μ + α` for `A + α I`, so
`Re μ < -α` is equivalent to `Re (μ + α) < 0`.

Reference: João P. Hespanha, *Linear Systems Theory* (2nd ed.), continuous-time
stability criterion. This spectral-shift corollary is proved directly from eigenpairs. -/
@[blueprint "thm:isHurwitzWithRate-iff-spectral-shift"
  (title := "Rate-Hurwitz via a spectral shift")
  (statement := /-- A real matrix $A$ is Hurwitz with decay rate $\alpha$ if and only if
    the spectrally shifted matrix $A + \alpha I$ is Hurwitz.

    Reference: João P. Hespanha, \emph{Linear Systems Theory} (2nd ed.), continuous-time stability
    criterion. This spectral-shift corollary is proved directly from eigenpairs.
  -/)
  (proof := /-- A complex eigenvalue $\mu$ of $A$ becomes $\mu + \alpha$ after the shift,
    and $\operatorname{Re}(\mu) < -\alpha$ is equivalent to
    $\operatorname{Re}(\mu + \alpha) < 0$. -/)]
theorem isHurwitzWithRate_iff_add_smul_one
    (α : ℝ) (A : Matrix X X ℝ) :
    IsHurwitzWithRate α A ↔ IsHurwitz (A + α • (1 : Matrix X X ℝ)) := by
  constructor
  · intro hA μ v hv hshift
    have hshift' : (A.complexify + (α : ℂ) • (1 : Matrix X X ℂ)) *ᵥ v
        = ((μ - (α : ℂ)) + (α : ℂ)) • v := by simpa using hshift
    have hμ := hA (μ - α) v hv
      ((MatrixAlgebra.mulVec_add_smul_one_eq_smul_iff _ _ _ _).1 hshift')
    simp only [Complex.sub_re, Complex.ofReal_re] at hμ
    linarith
  · intro hshift μ v hv hbase
    have heig : (A + α • (1 : Matrix X X ℝ)).complexify *ᵥ v = (μ + (α : ℂ)) • v := by
      simpa using (MatrixAlgebra.mulVec_add_smul_one_eq_smul_iff
        A.complexify (α : ℂ) μ v).2 hbase
    have hμ := hshift (μ + α) v hv heig
    simp only [Complex.add_re, Complex.ofReal_re] at hμ
    linarith

/-- The one-by-one matrix with entry `-γ` has every decay rate strictly below `γ`.
This is a concrete sanity check for the eigenpair definition and its sign convention.

Original: direct computation included as a sanity check for the definition. -/
@[blueprint "lem:isHurwitzWithRate-neg-one-by-one"
  (title := "The scalar example")
  (latexEnv := "lemma")
  (statement := /-- For $\alpha < \gamma$, the $1 \times 1$ matrix $(-\gamma)$ is Hurwitz with
    decay rate $\alpha$ (\cref{def:stability-isHurwitzWithRate}).

    Included as a concrete check on the sign convention of the definition. -/)
  (proof := /-- The only eigenvalue is $-\gamma$, and
    $\operatorname{Re}(-\gamma) = -\gamma < -\alpha$. -/)]
theorem isHurwitzWithRate_neg_one_by_one {α γ : ℝ} (hαγ : α < γ) :
    IsHurwitzWithRate α ((-γ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  intro μ v hv hAv
  have hv0 : v 0 ≠ 0 := by
    intro hv0
    apply hv
    funext i
    fin_cases i
    exact hv0
  have heig := congrFun hAv 0
  have hμ : μ = (-γ : ℝ) := by
    apply mul_right_cancel₀ hv0
    simpa [Matrix.mulVec, dotProduct] using heig.symm
  rw [hμ]
  simp only [Complex.ofReal_re]
  linarith

/-! ## From Hurwitz to a positive rate

`IsHurwitz` says each eigenvalue has negative real part, one at a time. Because the spectrum
is compact and nonempty, that upgrades to a *uniform* margin: some `c > 0` with every
eigenvalue to the left of `-c`.
-/

/-- Membership in the spectrum of a complex matrix is exactly having an eigenvector. -/
private lemma mem_spectrum_iff_exists_eigenpair (M : Matrix X X ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ M ↔ ∃ v : X → ℂ, v ≠ 0 ∧ M *ᵥ v = μ • v := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact ⟨v, hv.2, by simpa [Matrix.toLin'_apply'] using hv.apply_eq_smul⟩
  · rintro ⟨v, hv0, hv⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hv0⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa [Matrix.toLin'_apply'] using hv

-- `DecidableEq X` is used by the proof (the spectrum lives on `Matrix X X ℂ`, which needs the
-- ring structure) but not by the statement.
set_option linter.unusedDecidableInType false in
/-- **A Hurwitz matrix has a positive spectral margin.**
If every eigenvalue of `A` has strictly negative real part then they are all bounded away from
the imaginary axis: there is `c > 0` with `Re μ < -c` for every eigenvalue `μ`.

The spectrum is compact and nonempty, so `Re` attains a maximum on it, and that maximum is
itself the real part of an eigenvalue, hence negative.

This is what lets a qualitative Hurwitz hypothesis produce a quantitative rate. -/
@[blueprint "thm:isHurwitz-exists-pos-rate"
  (title := "A Hurwitz matrix has a positive spectral margin")
  (statement := /-- If $A$ is Hurwitz then there is $c > 0$ such that every eigenvalue $\mu$ of
    $A$ satisfies $\operatorname{Re}(\mu) < -c$. -/)
  (proof := /-- The spectrum is compact and nonempty, so $\operatorname{Re}$ attains a maximum
    on it at some $\mu_0$, which is an eigenvalue and hence has
    $\operatorname{Re}(\mu_0) < 0$.  Take $c = -\operatorname{Re}(\mu_0)/2$. -/)]
theorem IsHurwitz.exists_pos_isHurwitzWithRate {A : Matrix X X ℝ} (hA : IsHurwitz A) :
    ∃ c > (0 : ℝ), IsHurwitzWithRate c A := by
  rcases isEmpty_or_nonempty X with _ | _
  · exact ⟨1, one_pos, isHurwitzWithRate_of_isEmpty 1 A⟩
  obtain ⟨μ₀, hμ₀mem, hμ₀max⟩ :=
    (spectrum.isCompact (A.complexify)).exists_isMaxOn
      (spectrum.nonempty (A.complexify)) Complex.continuous_re.continuousOn
  obtain ⟨v₀, hv₀, hv₀eig⟩ := (mem_spectrum_iff_exists_eigenpair _ _).1 hμ₀mem
  have hneg : μ₀.re < 0 := hA μ₀ v₀ hv₀ hv₀eig
  refine ⟨-μ₀.re / 2, by linarith, fun μ v hv heig => ?_⟩
  have hmem : μ ∈ spectrum ℂ A.complexify :=
    (mem_spectrum_iff_exists_eigenpair _ _).2 ⟨v, hv, heig⟩
  have := hμ₀max hmem
  simp only [Set.mem_setOf_eq] at this
  linarith

/-! ## Equivalent analytic conditions

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
@[blueprint "lem:tendsto-const-mul-exp-neg"
  (title := "The decay envelope vanishes")
  (latexEnv := "lemma")
  (statement := /-- For $\gamma > 0$ and any constants $K, t_{0}$,
    \[
      \lim_{t \to \infty} K\,e^{-\gamma(t - t_{0})} = 0.
    \] -/)
  (proof := /-- The affine map $t \mapsto -\gamma(t - t_{0})$ tends to $-\infty$ because
    $-\gamma < 0$; compose with $\exp$ and scale by $K$. -/)]
lemma tendsto_const_mul_exp_neg (K t₀ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun t : ℝ => K * Real.exp (-γ * (t - t₀))) atTop (𝓝 0) := by
  have haff : Tendsto (fun t : ℝ => -γ * (t - t₀)) atTop atBot :=
    Tendsto.const_mul_atTop_of_neg (by linarith)
      (by simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-t₀) tendsto_id)
  simpa using (Real.tendsto_exp_atBot.comp haff).const_mul K

omit [Fintype X] [DecidableEq X] in
/-- **Squeeze against an exponentially decaying envelope.**
Anything whose norm sits under `k e^{-γ (t - t₀)} c` tends to zero.

This is `squeeze_zero_norm'`; what it saves is doing the envelope's limit and the
reassociation `k · E · c = (k · c) · E` once rather than at each call site. It is stated over
an arbitrary normed space because it is used for both matrix- and vector-valued quantities. -/
@[blueprint "lem:tendsto-zero-of-norm-le-envelope"
  (title := "Squeeze against an exponentially decaying envelope")
  (latexEnv := "lemma")
  (statement := /-- Let $E$ be a normed space, $f : \mathbb{R} \to E$, and $\gamma > 0$.  If
    eventually
    \[
      \|f(t)\| \le k\,e^{-\gamma(t - t_{0})}\,c,
    \]
    then $f(t) \to 0$ as $t \to \infty$.

    Stated over an arbitrary normed space because it is applied to both matrix- and
    vector-valued quantities. -/)
  (proof := /-- The squeeze theorem: $\|f\|$ is bounded below by $0$ and above by an envelope
    that tends to $0$ (\cref{lem:tendsto-const-mul-exp-neg}, after reassociating
    $k \cdot E \cdot c = (kc) \cdot E$). -/)]
lemma tendsto_zero_of_norm_le_envelope {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (k c t₀ : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (hbd : ∀ᶠ t in atTop, ‖f t‖ ≤ k * Real.exp (-γ * (t - t₀)) * c) :
    Tendsto f atTop (𝓝 0) := by
  refine squeeze_zero_norm' hbd ?_
  have heq : (fun t : ℝ => k * Real.exp (-γ * (t - t₀)) * c)
      = fun t : ℝ => k * c * Real.exp (-γ * (t - t₀)) := funext fun t => by ring
  rw [heq]
  exact tendsto_const_mul_exp_neg (k * c) t₀ hγ

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
      (exp (A.complexify))
      (MatrixAlgebra.spectralRadius_exp_complexify_lt_one A hA)
    refine ⟨m, hm0, ?_⟩
    calc ‖exp ((m : ℝ) • A)‖
        = ‖(exp ((m : ℝ) • A)).complexify‖ := (Matrix.linfty_opNorm_complexify _).symm
      _ = ‖exp (A.complexify) ^ m‖ := by
          rw [MatrixAlgebra.complexification_exp, ← Matrix.exp_nsmul]
          congr 2
          ext i j
          simp
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
@[blueprint "thm:isHurwitz-exists-norm-exp-le"
  (title := "A Hurwitz matrix has an exponentially decaying exponential")
  (statement := /-- If $A$ is Hurwitz (\cref{def:stability-isHurwitz}) then there are
    $k > 0$ and $\gamma > 0$ with
    \[
      \|e^{At}\| \le k\,e^{-\gamma t}, \qquad \forall\, t \ge 0.
    \] -/)
  (proof := /-- \emph{A contracting block.}  The spectral radius of $e^{A_{\mathbb C}}$ is
    below $1$ (\cref{lem:spectralRadius-exp-complexify-lt-one}), so by Gelfand's formula
    (\cref{lem:exists-pow-norm-lt-one}) some integer time $p > 0$ has
    $\|e^{Ap}\| < 1$.  Fix $c$ with $\|e^{Ap}\| \le c < 1$, kept away from $0$ so that
    $\log c$ exists.

    \emph{One block.}  $\|e^{Ar}\|$ is continuous, hence bounded by some $M \ge 1$ on the
    compact interval $[0, p]$.

    \emph{Spreading.}  Write $t = qp + r$ with $q \in \mathbb{N}$ and $r \in [0, p)$.  The
    exponents commute, so $e^{At} = e^{Ar}(e^{Ap})^{q}$, and submultiplicativity gives
    $\|e^{At}\| \le M c^{q}$ by induction on $q$.  Setting $\gamma = -\log c / p$ turns
    $c^{q}$ into $e^{-\gamma q p}$, and $qp \ge t - p$ costs one further factor $c^{-1}$.  The
    bound is $\|e^{At}\| \le (M/c)\,e^{-\gamma t}$.

    The contraction is taken in the $L^{\infty}$ operator norm, which is what makes it usable
    against $\|Ax\|_{\infty} \le \|A\|_{\infty}\|x\|_{\infty}$ in
    \cref{thm:isHurwitz-exists-norm-exp-mulVec-le}.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.1.
  -/)]
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
@[blueprint "thm:isHurwitz-exists-norm-exp-mulVec-le"
  (title := "Exponential decay of the state under a Hurwitz matrix")
  (statement := /-- If $A$ is Hurwitz (\cref{def:stability-isHurwitz}) then there are
    $k > 0$ and $\gamma > 0$ with
    \[
      \|e^{At}x\| \le k\,e^{-\gamma t}\,\|x\|, \qquad \forall\, t \ge 0,\ \forall\, x.
    \]

    This is the form the Lyapunov stability predicates consume. -/)
  (proof := /-- \cref{thm:isHurwitz-exists-norm-exp-le} bounds the matrix; one application of
    $\|Ax\|_{\infty} \le \|A\|_{\infty}\|x\|_{\infty}$ transfers it to the state.  This is the
    step at which the choice of the $L^{\infty}$ operator norm earns its keep. -/)]
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
@[blueprint "thm:isHurwitz-of-tendsto-exp"
  (title := "Decay of the matrix exponential forces the Hurwitz condition")
  (statement := /-- If $e^{At} \to 0$ as $t \to \infty$ then $A$ is Hurwitz
    (\cref{def:stability-isHurwitz}).

    Stated from mere convergence rather than from an exponential bound, so that it serves
    clause (2) and clause (3) of Theorem 8.1 alike.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 8, Theorem 8.1.
  -/)
  (proof := /-- Suppose $\operatorname{Re}\mu \ge 0$ for some eigenpair $(\mu, v)$ with
    $v \ne 0$.  Complexification is continuous, so $e^{At}_{\mathbb C}v \to 0$ as well.  But
    $v$ is an eigenvector of $tA_{\mathbb C}$ with eigenvalue $t\mu$, hence of its exponential
    (\cref{lem:exp-mulVec-eigenpair}), so
    \[
      \|e^{At}_{\mathbb C}v\| = |e^{t\mu}|\,\|v\| = e^{t\operatorname{Re}\mu}\|v\| \ge \|v\| > 0
    \]
    for every $t \ge 0$, contradicting convergence to $0$. -/)]
theorem isHurwitz_of_tendsto_exp
    (hmat : Tendsto (fun t : ℝ => exp (t • A)) atTop (𝓝 0)) :
    IsHurwitz A := by
  intro μ v hv hAv
  by_contra hre
  push Not at hre
  -- Complexifying and applying to `v` is continuous, so the limit carries across to `ℂ`.
  have hcx : Tendsto (fun t : ℝ =>
      ‖(exp (t • A)).complexify *ᵥ v‖) atTop (𝓝 0) := by
    have hcont : Continuous fun M : Matrix X X ℝ => M.complexify *ᵥ v :=
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
    _ = ‖exp ((t : ℂ) • A.complexify) *ᵥ v‖ := by
        -- `v` is an eigenvector of `tAℂ` with eigenvalue `tμ`, so of its exponential too.
        rw [MatrixAlgebra.exp_mulVec_of_mulVec_eq_smul _ _ _
            (MatrixAlgebra.smul_mulVec_of_mulVec_eq_smul hAv (t : ℂ)),
          norm_smul]
    _ = ‖(exp (t • A)).complexify *ᵥ v‖ := by
        have hmap : (exp (t • A)).complexify
            = exp ((t : ℂ) • A.complexify) := by
          rw [MatrixAlgebra.complexification_exp]
          congr 1
          ext i j
          simp
        rw [hmap]

/-- Pointwise decay of `e^{At}` on real states already forces `A` to be Hurwitz.

The composite both clauses of Theorem 8.1 reach for. -/
@[blueprint "thm:isHurwitz-of-tendsto-exp-mulVec"
  (title := "Pointwise decay of the state forces the Hurwitz condition")
  (statement := /-- If $e^{At}x \to 0$ as $t \to \infty$ for every real state $x$, then $A$ is
    Hurwitz (\cref{def:stability-isHurwitz}).

    This is the composite that both clauses of Theorem 8.1 reach for: the stability predicates
    speak about states, not about the matrix. -/)
  (proof := /-- Feeding the hypothesis the standard basis vectors returns the columns of
    $e^{At}$, and convergence in the matrix space is entrywise, so $e^{At} \to 0$; apply
    \cref{thm:isHurwitz-of-tendsto-exp}. -/)]
theorem isHurwitz_of_tendsto_exp_mulVec
    (h : ∀ x : X → ℝ, Tendsto (fun t : ℝ => exp (t • A) *ᵥ x) atTop (𝓝 0)) :
    IsHurwitz A :=
  isHurwitz_of_tendsto_exp A (tendsto_exp_of_tendsto_exp_mulVec A h)

/-! ### The equivalences

Hurwitz, decay of `e^{At}` to zero, and an explicit exponential envelope for it are the same
condition. Stated as two `Iff`s rather than a `List.TFAE` because each is used directly: the
first is what clause (2) of Theorem 8.1 needs, the second what clause (3) needs.
-/

/-- An exponentially decaying envelope for `‖e^{At}‖` makes `e^{At}` vanish.

Shared by both equivalences below, which otherwise repeat it verbatim. -/
private lemma tendsto_exp_of_norm_exp_le {k γ : ℝ} (hγ : 0 < γ)
    (hbd : ∀ t : ℝ, 0 ≤ t → ‖exp (t • A)‖ ≤ k * Real.exp (-γ * t)) :
    Tendsto (fun t : ℝ => exp (t • A)) atTop (𝓝 0) := by
  refine tendsto_zero_of_norm_le_envelope k 1 0 hγ ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simpa using hbd t ht

/-- `A` is Hurwitz exactly when `e^{At} → 0`. -/
@[blueprint "thm:isHurwitz-iff-tendsto-exp"
  (title := "Hurwitz is decay of the matrix exponential")
  (statement := /-- A real square matrix $A$ is Hurwitz (\cref{def:stability-isHurwitz}) if and
    only if $e^{At} \to 0$ as $t \to \infty$. -/)
  (proof := /-- Forwards, \cref{thm:isHurwitz-exists-norm-exp-le} supplies an exponentially
    decaying envelope and \cref{lem:tendsto-zero-of-norm-le-envelope} squeezes;
    backwards is \cref{thm:isHurwitz-of-tendsto-exp}. -/)]
theorem isHurwitz_iff_tendsto_exp :
    IsHurwitz A ↔ Tendsto (fun t : ℝ => exp (t • A)) atTop (𝓝 0) := by
  refine ⟨fun hA => ?_, isHurwitz_of_tendsto_exp A⟩
  obtain ⟨k, -, γ, hγ, hbd⟩ := hA.exists_norm_exp_le
  exact tendsto_exp_of_norm_exp_le A hγ hbd

/-- `A` is Hurwitz exactly when `‖e^{At}‖` admits an exponentially decaying envelope. -/
@[blueprint "thm:isHurwitz-iff-exists-norm-exp-le"
  (title := "Hurwitz is an exponential envelope for the matrix exponential")
  (statement := /-- A real square matrix $A$ is Hurwitz (\cref{def:stability-isHurwitz}) if and
    only if there are $k > 0$ and $\gamma > 0$ with
    $\|e^{At}\| \le k\,e^{-\gamma t}$ for all $t \ge 0$.

    Recorded separately from \cref{thm:isHurwitz-iff-tendsto-exp} because the two are what
    clauses (2) and (3) of Theorem 8.1 respectively need: bare convergence for asymptotic
    stability, an explicit rate for exponential stability. -/)
  (proof := /-- Forwards is \cref{thm:isHurwitz-exists-norm-exp-le}.  Backwards, the envelope
    forces $e^{At} \to 0$ (\cref{lem:tendsto-zero-of-norm-le-envelope}), so
    \cref{thm:isHurwitz-iff-tendsto-exp} applies. -/)]
theorem isHurwitz_iff_exists_norm_exp_le :
    IsHurwitz A ↔ ∃ k > (0 : ℝ), ∃ γ > (0 : ℝ), ∀ t : ℝ, 0 ≤ t →
      ‖exp (t • A)‖ ≤ k * Real.exp (-γ * t) := by
  refine ⟨fun hA => hA.exists_norm_exp_le, ?_⟩
  rintro ⟨k, -, γ, hγ, hbd⟩
  exact (isHurwitz_iff_tendsto_exp A).2 (tendsto_exp_of_norm_exp_le A hγ hbd)

end Matrices

end LinearSystems

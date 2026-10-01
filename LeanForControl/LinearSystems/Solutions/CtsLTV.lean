import LeanForControl.Analysis.Continuity
import LeanForControl.LinearSystems.DefsSystem
import LeanForControl.LinearSystems.Solutions.DefsCtsLTV
import LeanForControl.ODEs.ODE_properties
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Architect

/-!
# Continuous-time solutions: the Peano-Baker series

Theorems about `peanoBakerTerm` and `stateTransitionMatrix` (from `DefsCtsLTV.lean`),
building up to Theorem 5.1 (Peano-Baker series): the state transition matrix solves the
matrix ODE `Φ̇(t, t₀) = A(t) Φ(t, t₀)`, `Φ(t₀, t₀) = I`, and `x(t) := Φ(t, t₀) *ᵥ x₀` is the
unique solution of `ẋ = A(t) x`, `x(t₀) = x₀`.

The final section restates the solution for the `LinearSystem` object: the forced response is
a *trajectory* in the sense of `ContinuousLinearSystem.IsTrajectoryOn`, which is the predicate the
stability theory quantifies over. Everything before it works with the coefficient maps `A` and
`B` directly, which is where the analysis lives.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5.
-/

namespace LinearSystems

open scoped Matrix.Norms.Operator Nat
open Matrix MeasureTheory intervalIntegral

variable {X : Type*} [Fintype X] [DecidableEq X] {A : ℝ → Matrix X X ℝ}

/-- Each term of the Peano-Baker series is continuous in `t`, for `A` continuous.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "lem:continuous-peanoBakerTerm"
  (title := "Continuity of the Peano--Baker terms")
  (latexEnv := "lemma")
  (statement := /-- Each term $P_k(t,t_0)$ of the Peano--Baker series is continuous in $t$,
    for $A$ continuous.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5.
  -/)
  (proof := /-- Induction on $k$: $P_0$ is constant, and $P_{k+1}$ is the primitive of a
    continuous integrand (\cref{def:peanoBakerTerm}), hence continuous by the fundamental
    theorem of calculus. -/)]
theorem continuous_peanoBakerTerm (hA : Continuous A) (k : ℕ) (t₀ : ℝ) :
    Continuous (fun t => peanoBakerTerm A k t t₀) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih => exact continuous_primitive (hA.mul ih).intervalIntegrable t₀

/-- The factorial bound on the Peano-Baker series, for `t` on *either side* of `t₀`: if
`‖A s‖ ≤ M` on the segment between `t₀` and `t₁`, the `k`-th term is bounded by
`‖1‖ * (M|t - t₀|)^k / k!` for every `t` on that same segment. This is what makes
`∑' k, peanoBakerTerm A k t t₀` (absolutely) summable, by comparison with the exponential
series, for `t` before or after `t₀`.

Proof, by induction on `k`: the `k = 0` case is `‖1‖ ≤ ‖1‖`. For the inductive step, bound the
integrand `A s * peanoBakerTerm A k s t₀` pointwise on the segment between `t₀` and `t`
(submultiplicativity of the matrix norm, the bound on `A`, and the induction hypothesis), then
split on whether `t₀ ≤ t` or `t ≤ t₀`: in the forward case, integrate the majorant directly via
the power rule; in the backward case, flip the integral (`intervalIntegral.integral_symm`) to
land back in the forward orientation, where the same power rule applies with `t₀ - s` in place
of `s - t₀`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "lem:norm-peanoBakerTerm-le"
  (title := "Factorial bound on the Peano--Baker terms")
  (latexEnv := "lemma")
  (statement := /-- If $\|A(s)\| \le M$ for all $s$ between $t_0$ and $t_1$, then
    \[
      \|P_k(t,t_0)\| \;\le\; \|I\| \cdot \frac{(M|t-t_0|)^k}{k!}
      \qquad \text{for every } t \text{ between } t_0 \text{ and } t_1.
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5.
  -/)
  (proof := /-- Induction on $k$: bound the integrand $A(s) P_k(s,t_0)$ pointwise on the segment
    between $t_0$ and $t$, using submultiplicativity of the matrix norm and the induction
    hypothesis. Split on whether $t_0 \le t$ or $t \le t_0$ and integrate the majorant via the
    power rule, flipping the integral's orientation
    (\texttt{intervalIntegral.integral\_symm}) in the backward case. -/)]
theorem norm_peanoBakerTerm_le {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (k : ℕ) :
    ∀ t ∈ Set.uIcc t₀ t₁,
      ‖peanoBakerTerm A k t t₀‖ ≤ ‖(1 : Matrix X X ℝ)‖ * (M * |t - t₀|) ^ k / (k)! := by
  induction k with
  | zero => intro t _; simp [peanoBakerTerm]
  | succ k ih =>
    intro t ht
    set C1 : ℝ := ‖(1 : Matrix X X ℝ)‖
    -- `M` bounds a norm, hence is itself nonnegative.
    have hM_nonneg : 0 ≤ M := (norm_nonneg (A t₀)).trans (hA_le t₀ Set.left_mem_uIcc)
    have hsub : Set.uIcc t₀ t ⊆ Set.uIcc t₀ t₁ := Set.uIcc_subset_uIcc_left ht
    -- Pointwise bound on the integrand `A s * peanoBakerTerm A k s t₀`, for `s` between `t₀`
    -- and `t` (in either order).
    have hintegrand_le : ∀ s ∈ Set.uIcc t₀ t,
        ‖A s * peanoBakerTerm A k s t₀‖ ≤ M * (C1 * (M * |s - t₀|) ^ k / (k)!) := by
      intro s hs
      have hs_t₁ : s ∈ Set.uIcc t₀ t₁ := hsub hs
      calc ‖A s * peanoBakerTerm A k s t₀‖
          ≤ ‖A s‖ * ‖peanoBakerTerm A k s t₀‖ := norm_mul_le _ _
        _ ≤ M * (C1 * (M * |s - t₀|) ^ k / (k)!) :=
            mul_le_mul (hA_le s hs_t₁) (ih s hs_t₁) (norm_nonneg _) hM_nonneg
    rcases le_total t₀ t with hle | hle
    · -- Forward case: `t₀ ≤ t`.
      have hintegral_le :
          ‖∫ s in t₀..t, A s * peanoBakerTerm A k s t₀‖ ≤
            ∫ s in t₀..t, M * (C1 * (M * (s - t₀)) ^ k / (k)!) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hle
          (ae_of_all _ fun s hs => ?_) (Continuous.intervalIntegrable (by fun_prop) t₀ t)
        have hs' : s ∈ Set.uIcc t₀ t := by
          rw [Set.uIcc_of_le hle]; exact Set.Ioc_subset_Icc_self hs
        have hb' := hintegrand_le s hs'
        rwa [abs_of_nonneg (sub_nonneg.mpr hs.1.le)] at hb'
      -- Power rule: `∫ (s - t₀)^k ds = (t - t₀)^(k+1) / (k+1)`, via the shift `s ↦ s - t₀`.
      have hpow_integral : (∫ s in t₀..t, (s - t₀) ^ k) = (t - t₀) ^ (k + 1) / (k + 1) := by
        rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ k) t₀]
        simp [integral_pow]
      rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      calc ‖peanoBakerTerm A (k + 1) t t₀‖
          ≤ ∫ s in t₀..t, M * (C1 * (M * (s - t₀)) ^ k / (k)!) := hintegral_le
        _ = (M * C1 * M ^ k / (k)!) * ∫ s in t₀..t, (s - t₀) ^ k := by
            rw [← intervalIntegral.integral_const_mul]
            congr 1
            ext s
            rw [mul_pow]
            ring
        _ = (M * C1 * M ^ k / (k)!) * ((t - t₀) ^ (k + 1) / (k + 1)) := by rw [hpow_integral]
        _ = C1 * (M * (t - t₀)) ^ (k + 1) / (k + 1)! := by
            have hk_fac_ne : ((k)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
            rw [mul_pow, Nat.factorial_succ]
            push_cast
            field_simp
            ring
    · -- Backward case: `t ≤ t₀`. Flip the integral to land back in the forward orientation.
      have hpk : peanoBakerTerm A (k + 1) t t₀ = ∫ s in t₀..t, A s * peanoBakerTerm A k s t₀ :=
        rfl
      rw [hpk, intervalIntegral.integral_symm t t₀, norm_neg,
        abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
      have hintegral_le :
          ‖∫ s in t..t₀, A s * peanoBakerTerm A k s t₀‖ ≤
            ∫ s in t..t₀, M * (C1 * (M * (t₀ - s)) ^ k / (k)!) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hle
          (ae_of_all _ fun s hs => ?_) (Continuous.intervalIntegrable (by fun_prop) t t₀)
        have hs' : s ∈ Set.uIcc t₀ t := by
          rw [Set.uIcc_comm, Set.uIcc_of_le hle]; exact Set.Ioc_subset_Icc_self hs
        have hb' := hintegrand_le s hs'
        rwa [abs_of_nonpos (sub_nonpos.mpr hs.2), neg_sub] at hb'
      -- Power rule, mirrored: `∫ (t₀ - s)^k ds = (t₀ - t)^(k+1) / (k+1)`.
      have hpow_integral : (∫ s in t..t₀, (t₀ - s) ^ k) = (t₀ - t) ^ (k + 1) / (k + 1) := by
        rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ k) t₀]
        simp [integral_pow]
      calc ‖∫ s in t..t₀, A s * peanoBakerTerm A k s t₀‖
          ≤ ∫ s in t..t₀, M * (C1 * (M * (t₀ - s)) ^ k / (k)!) := hintegral_le
        _ = (M * C1 * M ^ k / (k)!) * ∫ s in t..t₀, (t₀ - s) ^ k := by
            rw [← intervalIntegral.integral_const_mul]
            congr 1
            ext s
            rw [mul_pow]
            ring
        _ = (M * C1 * M ^ k / (k)!) * ((t₀ - t) ^ (k + 1) / (k + 1)) := by rw [hpow_integral]
        _ = C1 * (M * (t₀ - t)) ^ (k + 1) / (k + 1)! := by
            have hk_fac_ne : ((k)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
            rw [mul_pow, Nat.factorial_succ]
            push_cast
            field_simp
            ring

/-- `norm_peanoBakerTerm_le`, uniformized to the *far endpoint* `t₁` rather than the point `t`
itself. Needed whenever a `t`-independent bound is required — the Weierstrass `M`-test, for
both continuity and differentiability of the series, needs one bound per term `k` valid across
the whole interval, not a different (tighter) bound at each point.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "lem:norm-peanoBakerTerm-le-of-mem"
  (title := "Factorial bound on a subinterval")
  (latexEnv := "lemma")
  (statement := /-- The bound in \cref{lem:norm-peanoBakerTerm-le}, uniformized to the worst
    case $t = t_1$:
    \[
      \|P_k(t,t_0)\| \;\le\; \|I\| \cdot \frac{(M|t_1-t_0|)^k}{k!}
      \qquad \text{for every } t \text{ between } t_0 \text{ and } t_1.
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5.
  -/)
  (proof := /-- Monotonicity of $t \mapsto (M|t-t_0|)^k$ on the segment between $t_0$ and $t_1$,
    combined with \cref{lem:norm-peanoBakerTerm-le}. -/)]
theorem norm_peanoBakerTerm_le_of_mem {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M)
    (k : ℕ) :
    ∀ t ∈ Set.uIcc t₀ t₁,
      ‖peanoBakerTerm A k t t₀‖ ≤
        ‖(1 : Matrix X X ℝ)‖ * (M * |t₁ - t₀|) ^ k / (k)! := by
  intro t ht
  have hM_nonneg : 0 ≤ M := (norm_nonneg (A t₀)).trans (hA_le t₀ Set.left_mem_uIcc)
  have hC1_nonneg : 0 ≤ ‖(1 : Matrix X X ℝ)‖ := norm_nonneg _
  -- `t` lies between `t₀` and `t₁`, so its distance to `t₀` is at most the full segment length.
  have habs_le : |t - t₀| ≤ |t₁ - t₀| := by
    rcases le_total t₀ t₁ with h | h
    · rw [Set.uIcc_of_le h] at ht
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1), abs_of_nonneg (sub_nonneg.mpr h)]
      linarith [ht.2]
    · rw [Set.uIcc_comm, Set.uIcc_of_le h] at ht
      rw [abs_of_nonpos (sub_nonpos.mpr ht.2), abs_of_nonpos (sub_nonpos.mpr h)]
      linarith [ht.1]
  have hpow_le : (M * |t - t₀|) ^ k ≤ (M * |t₁ - t₀|) ^ k := by gcongr
  exact (norm_peanoBakerTerm_le hA_le k t ht).trans (by gcongr)

/-- The Peano-Baker series `∑' k, peanoBakerTerm A k t t₀` converges absolutely, for `t₀ ≤ t`
and `A` bounded by `M` on `[t₀, t]`. This is what lets `stateTransitionMatrix` (defined as
`∑' k, peanoBakerTerm A k t t₀`) actually equal the Peano-Baker series (5.3), rather than a
sum of an eventually-meaningless (divergent) series.

Proof: compare against the exponential series `∑ (M(t-t₀))^k / k!` (summable, by
`Real.summable_pow_div_factorial`) via `norm_peanoBakerTerm_le` and the comparison test.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "lem:summable-peanoBakerTerm"
  (title := "Summability of the Peano--Baker series")
  (latexEnv := "lemma")
  (statement := /-- The Peano--Baker series $\sum_{k=0}^\infty P_k(t,t_0)$ converges absolutely,
    for $A$ bounded between $t_0$ and $t$ (in either order).

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5.
  -/)
  (proof := /-- Compare against the exponential series $\sum_k (M|t-t_0|)^k/k!$ via
    \cref{lem:norm-peanoBakerTerm-le} and the comparison test. -/)]
theorem summable_peanoBakerTerm {t t₀ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t, ‖A s‖ ≤ M) :
    Summable (fun k => peanoBakerTerm A k t t₀) :=
  Summable.of_norm_bounded
    (g := fun k => ‖(1 : Matrix X X ℝ)‖ * (M * |t - t₀|) ^ k / (k)!)
    (by
      have hexp : Summable (fun k => (M * |t - t₀|) ^ k / (k)!) :=
        Real.summable_pow_div_factorial (M * |t - t₀|)
      simpa [mul_div_assoc] using hexp.mul_left ‖(1 : Matrix X X ℝ)‖)
    (fun k => norm_peanoBakerTerm_le hA_le k t Set.right_mem_uIcc)

/-- The state transition matrix is continuous on the segment between `t₀` and `t₁` (including
both endpoints), for `A` continuous and bounded by `M` there. This is needed alongside
`hasDerivAt_stateTransitionMatrix` (valid only on the open interval strictly between `t₀` and
`t₁`) for arguments — like uniqueness of the solution — that need continuity *at* `t₀` itself.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "lem:continuousOn-stateTransitionMatrix"
  (title := "Continuity of the state transition matrix")
  (latexEnv := "lemma")
  (statement := /-- $\Phi(\cdot, t_0)$ is continuous on the segment between $t_0$ and $t_1$
    (including both endpoints), for $A$ continuous and bounded by $M$ there.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5.
  -/)
  (proof := /-- Each term $P_k(\cdot,t_0)$ is continuous (\cref{lem:continuous-peanoBakerTerm})
    with a summable, point-independent bound (\cref{lem:norm-peanoBakerTerm-le-of-mem}); apply
    the Weierstrass $M$-test for continuity of a series. -/)]
theorem continuousOn_stateTransitionMatrix (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) :
    ContinuousOn (fun t => stateTransitionMatrix A t t₀) (Set.uIcc t₀ t₁) := by
  have hu_summable :
      Summable (fun k => ‖(1 : Matrix X X ℝ)‖ * (M * |t₁ - t₀|) ^ k / (k)!) := by
    have hexp := Real.summable_pow_div_factorial (M * |t₁ - t₀|)
    simpa [mul_div_assoc] using hexp.mul_left ‖(1 : Matrix X X ℝ)‖
  exact continuousOn_tsum (fun k => (continuous_peanoBakerTerm hA k t₀).continuousOn)
    hu_summable (fun k t ht => norm_peanoBakerTerm_le_of_mem hA_le k t ht)

/-- The state transition matrix solves the matrix ODE `Φ̇(t, t₀) = A(t) Φ(t, t₀)`, for `t`
strictly between `t₀` and `t₁` (in either order), with `A` bounded by `M` on the segment
between `t₀` and `t₁`. This is the mathematical content of Theorem 5.1: everything before this
(`peanoBakerTerm`, its continuity, its factorial bound, and summability of the series) exists
only to make differentiating the series term-by-term legitimate.

Proof outline:
1. Differentiate the *shifted* series `∑' k, peanoBakerTerm A (k+1) z t₀` term-by-term, via
   `hasDerivAt_tsum_of_isPreconnected`. Each term is, by definition, an integral with variable
   upper limit, so its derivative is its integrand by the FTC. The factorial bound gives a
   *uniform* (point-independent) bound on these derivative terms across the open segment
   between `t₀` and `t₁`, which is what the term-by-term differentiation lemma needs.
2. `stateTransitionMatrix A z t₀ = 1 + ∑' k, peanoBakerTerm A (k+1) z t₀` (peeling the constant
   `k = 0` term off the series), so `Φ(·, t₀)` has the same derivative as the shifted series,
   near `t`.
3. `∑' k, A t * peanoBakerTerm A k t t₀ = A t * ∑' k, peanoBakerTerm A k t t₀ = A t * Φ(t, t₀)`,
   by linearity of `tsum` under left multiplication by the fixed matrix `A t`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "thm:hasDerivAt-stateTransitionMatrix"
  (title := "The state transition matrix solves the matrix ODE")
  (statement := /-- The state transition matrix solves the matrix ODE
    \[
      \dot\Phi(t,t_0) = A(t)\,\Phi(t,t_0)
    \]
    for $t$ strictly between $t_0$ and $t_1$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5.
  -/)
  (proof := /-- Differentiate the Peano--Baker series term by term, using
    \cref{lem:norm-peanoBakerTerm-le} as the uniform bound needed for term-by-term
    differentiation of a series. The $k=0$ term is constant, so peel it off and match the
    shifted series' derivative against $A(t)\Phi(t,t_0)$ using linearity of the sum under
    left multiplication by $A(t)$. -/)]
theorem hasDerivAt_stateTransitionMatrix (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) {t : ℝ} (ht : t ∈ Set.uIoo t₀ t₁) :
    HasDerivAt (fun z => stateTransitionMatrix A z t₀) (A t * stateTransitionMatrix A t t₀) t := by
  set C1 : ℝ := ‖(1 : Matrix X X ℝ)‖
  have hM_nonneg : 0 ≤ M := (norm_nonneg (A t₀)).trans (hA_le t₀ Set.left_mem_uIcc)
  -- Step 1a: the FTC gives the derivative of each *shifted* term, at every point.
  have hderiv : ∀ (k : ℕ) (z : ℝ),
      HasDerivAt (fun z => peanoBakerTerm A (k + 1) z t₀) (A z * peanoBakerTerm A k z t₀) z := by
    intro k z
    have hF : Continuous (fun s => A s * peanoBakerTerm A k s t₀) :=
      hA.mul (continuous_peanoBakerTerm hA k t₀)
    exact intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable t₀ z)
      hF.stronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  -- Step 1b: a uniform (`z`-independent) bound on the derivative terms over the open segment
  -- between `t₀` and `t₁`, from the factorial bound at the worst case `z = t₁`.
  have hu_summable : Summable (fun k => M * (C1 * (M * |t₁ - t₀|) ^ k / (k)!)) := by
    have hexp := Real.summable_pow_div_factorial (M * |t₁ - t₀|)
    simpa [mul_div_assoc] using (hexp.mul_left C1).mul_left M
  have hbound : ∀ (k : ℕ), ∀ z ∈ Set.uIoo t₀ t₁,
      ‖A z * peanoBakerTerm A k z t₀‖ ≤ M * (C1 * (M * |t₁ - t₀|) ^ k / (k)!) := by
    intro k z hz
    have hz' : z ∈ Set.uIcc t₀ t₁ := Set.uIoo_subset_uIcc_self hz
    calc ‖A z * peanoBakerTerm A k z t₀‖
        ≤ ‖A z‖ * ‖peanoBakerTerm A k z t₀‖ := norm_mul_le _ _
      _ ≤ M * (C1 * (M * |t₁ - t₀|) ^ k / (k)!) :=
          mul_le_mul (hA_le z hz') (norm_peanoBakerTerm_le_of_mem hA_le k z hz')
            (norm_nonneg _) hM_nonneg
  -- The bound `hA_le` on the segment between `t₀` and `t₁` restricts to the segment between
  -- `t₀` and `z`, for any `z` strictly between them — all `summable_peanoBakerTerm` needs to
  -- give summability of the *full* series at `z`.
  have hsummable_at : ∀ z ∈ Set.uIoo t₀ t₁, Summable (fun k => peanoBakerTerm A k z t₀) := by
    intro z hz
    have hz' : z ∈ Set.uIcc t₀ t₁ := Set.uIoo_subset_uIcc_self hz
    exact summable_peanoBakerTerm (fun s hs => hA_le s (Set.uIcc_subset_uIcc_left hz' hs))
  have hfull : Summable (fun k => peanoBakerTerm A k t t₀) := hsummable_at t ht
  -- The open segment between `t₀` and `t₁` is `Ioo (min t₀ t₁) (max t₀ t₁)` in disguise.
  have hopen : IsOpen (Set.uIoo t₀ t₁) := by rw [← Set.Ioo_min_max]; exact isOpen_Ioo
  have hconn : IsPreconnected (Set.uIoo t₀ t₁) := by
    rw [← Set.Ioo_min_max]; exact (convex_Ioo (min t₀ t₁) (max t₀ t₁)).isPreconnected
  -- Step 1: differentiate the shifted series on the open segment between `t₀` and `t₁`.
  have hshifted_deriv :
      HasDerivAt (fun z => ∑' k, peanoBakerTerm A (k + 1) z t₀)
        (∑' k, A t * peanoBakerTerm A k t t₀) t :=
    hasDerivAt_tsum_of_isPreconnected hu_summable hopen hconn
      (fun k z _ => hderiv k z) hbound ht ((summable_nat_add_iff 1).2 hfull) ht
  -- Step 3: the derivative value is `A t * Φ(t, t₀)`, by linearity of `tsum`.
  rw [hfull.tsum_mul_left (A t)] at hshifted_deriv
  -- Step 2: `Φ(·, t₀)` agrees with `1 + (shifted series)` on the open neighborhood between `t₀`
  -- and `t₁` of `t`, so it has the same derivative there.
  have hone_plus_deriv :
      HasDerivAt (fun z => (1 : Matrix X X ℝ) + ∑' k, peanoBakerTerm A (k + 1) z t₀)
        (A t * stateTransitionMatrix A t t₀) t := by
    have := (hasDerivAt_const t (1 : Matrix X X ℝ)).add hshifted_deriv
    rwa [zero_add] at this
  refine hone_plus_deriv.congr_of_eventuallyEq ?_
  filter_upwards [hopen.mem_nhds ht] with z hz
  rw [stateTransitionMatrix, (hsummable_at z hz).tsum_eq_zero_add]
  simp [peanoBakerTerm]

/-- `Φ(t₀, t₀) = I`: the state transition matrix is the identity when evaluated at equal times,
matching the initial condition in (5.2). Every term of the Peano-Baker series beyond `k = 0`
integrates a function over the degenerate interval `[t₀, t₀]`, hence vanishes.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "thm:stateTransitionMatrix-self"
  (title := "The state transition matrix at the initial time")
  (statement := /-- $\Phi(t_0,t_0) = I$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5.
  -/)
  (proof := /-- Every term of the Peano--Baker series beyond $k=0$ integrates over the
    degenerate interval $[t_0,t_0]$ and vanishes. -/)]
theorem stateTransitionMatrix_self (t₀ : ℝ) :
    stateTransitionMatrix A t₀ t₀ = 1 := by
  have hterm : ∀ k, peanoBakerTerm A k t₀ t₀ =
      if k = 0 then (1 : Matrix X X ℝ) else 0 := by
    intro k
    cases k with
    | zero => simp [peanoBakerTerm]
    | succ k => simp [peanoBakerTerm, intervalIntegral.integral_same]
  rw [stateTransitionMatrix, tsum_congr hterm,
    tsum_ite_eq 0 (fun _ => (1 : Matrix X X ℝ))]

/-- **Peano-Baker series: existence** (Hespanha, Theorem 5.1).
`x(t) := Φ(t, t₀) *ᵥ x₀` solves the
initial value problem `ẋ = A(t) x` — this is `hasDerivAt_stateTransitionMatrix` pushed through
the fixed linear map `M ↦ M *ᵥ x₀` (continuous, since the domain is finite-dimensional).

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Theorem 5.1. -/
@[blueprint "thm:hasDerivAt-stateTransitionMatrix-mulVec"
  (title := "Peano--Baker series: existence")
  (statement := /-- Hespanha, Theorem 5.1.  $x(t) := \Phi(t,t_0)\, x_0$ solves
    \[
      \dot x(t) = A(t)\, x(t).
    \] -/)
  (proof := /-- Push \cref{thm:hasDerivAt-stateTransitionMatrix} through the fixed linear map
    $M \mapsto M x_0$ (continuous, since the domain is finite-dimensional). -/)]
theorem hasDerivAt_stateTransitionMatrix_mulVec (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) {t : ℝ} (ht : t ∈ Set.uIoo t₀ t₁)
    (x₀ : X → ℝ) :
    HasDerivAt (fun z => stateTransitionMatrix A z t₀ *ᵥ x₀)
      (A t *ᵥ (stateTransitionMatrix A t t₀ *ᵥ x₀)) t := by
  -- The fixed linear map `M ↦ M *ᵥ x₀`, as a continuous linear map (automatic: the domain
  -- `Matrix X X ℝ` is finite-dimensional).
  set L : Matrix X X ℝ →L[ℝ] (X → ℝ) :=
    LinearMap.toContinuousLinearMap ((Matrix.mulVecBilin ℝ ℝ).flip x₀) with hL
  have hL_apply : ∀ M' : Matrix X X ℝ, L M' = M' *ᵥ x₀ := fun M' => rfl
  have hderiv := (L.hasFDerivAt (x := stateTransitionMatrix A t t₀)).comp_hasDerivAt t
    (hasDerivAt_stateTransitionMatrix hA hA_le ht)
  simpa [hL_apply, Matrix.mulVec_mulVec] using hderiv

/-- The matrix analogue of `hasDerivAt_stateTransitionMatrix_mulVec`: for a *constant* matrix
`C`, `Y(t) := Φ(t, t₀) * C` solves the matrix ODE `Ẏ = A(t) Y`. Needed for the semigroup
property (P5.3) and matrix-level uniqueness, where the "initial value" is a matrix rather than
a vector.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "thm:hasDerivAt-stateTransitionMatrix-mul"
  (title := "Matrix-valued solutions")
  (statement := /-- For a constant matrix $C$, $Y(t) := \Phi(t,t_0)\, C$ solves
    \[
      \dot Y(t) = A(t)\, Y(t).
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5.
  -/)
  (proof := /-- Right-multiply \cref{thm:hasDerivAt-stateTransitionMatrix} by the constant $C$
    (\texttt{HasDerivAt.mul\_const}), then reassociate. -/)]
theorem hasDerivAt_stateTransitionMatrix_mul (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) {t : ℝ} (ht : t ∈ Set.uIoo t₀ t₁)
    (C : Matrix X X ℝ) :
    HasDerivAt (fun z => stateTransitionMatrix A z t₀ * C)
      (A t * (stateTransitionMatrix A t t₀ * C)) t := by
  have hderiv := (hasDerivAt_stateTransitionMatrix hA hA_le ht).mul_const C
  rwa [mul_assoc] at hderiv

/-- The matrix analogue of `isIntegralSolution_stateTransitionMatrix_mulVec`: for a constant
matrix `C`, `Y(t) := Φ(t, t₀) * C` is an integral solution of `Ẏ = A(t) Y` on the segment
between `t₀` and `t₁` with initial value `C`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "lem:isIntegralSolution-stateTransitionMatrix-mul"
  (title := "Integral form, matrix-valued")
  (latexEnv := "lemma")
  (statement := /-- For a constant matrix $C$, $Y(t) := \Phi(t,t_0)\, C$ satisfies the integral
    equation
    \[
      Y(t) = C + \int_{t_0}^{t} A(s)\, Y(s)\,\mathrm{d}s
    \]
    for every $t$ between $t_0$ and $t_1$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5.
  -/)
  (proof := /-- The fundamental theorem of calculus applied to
    \cref{thm:hasDerivAt-stateTransitionMatrix-mul}, using $\Phi(t_0,t_0) = I$
    (\cref{thm:stateTransitionMatrix-self}) to fix the initial value. -/)]
theorem isIntegralSolution_stateTransitionMatrix_mul (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (C : Matrix X X ℝ) :
    IsIntegralSolution t₀ t₁ (fun t => stateTransitionMatrix A t t₀ * C) C
      (fun s Y => A s * Y) := by
  have hx_cont : ContinuousOn (fun t => stateTransitionMatrix A t t₀ * C) (Set.uIcc t₀ t₁) :=
    (continuous_fst.mul continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix hA hA_le).prodMk continuousOn_const)
  intro t ht
  have huIcc_sub : Set.uIcc t₀ t ⊆ Set.uIcc t₀ t₁ := Set.uIcc_subset_uIcc_left ht
  have huIoo_sub : Set.uIoo t₀ t ⊆ Set.uIoo t₀ t₁ := by
    rw [← Set.Ioo_min_max, ← Set.Ioo_min_max]
    exact Set.Ioo_subset_Ioo (le_min (min_le_left t₀ t₁) ht.1) (max_le (le_max_left t₀ t₁) ht.2)
  have hx_cont' : ContinuousOn (fun s => stateTransitionMatrix A s t₀ * C) (Set.uIcc t₀ t) :=
    hx_cont.mono huIcc_sub
  have hf'_cont : ContinuousOn (fun s => A s * (stateTransitionMatrix A s t₀ * C))
      (Set.uIcc t₀ t) :=
    (continuous_fst.mul continuous_snd).comp_continuousOn (hA.continuousOn.prodMk hx_cont')
  have hderiv : ∀ z ∈ Set.uIoo t₀ t,
      HasDerivWithinAt (fun z => stateTransitionMatrix A z t₀ * C)
        (A z * (stateTransitionMatrix A z t₀ * C)) (Set.Ioi z) z :=
    fun z hz => (hasDerivAt_stateTransitionMatrix_mul hA hA_le (huIoo_sub hz) C).hasDerivWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right hx_cont' hderiv
    hf'_cont.intervalIntegrable
  rw [stateTransitionMatrix_self, Matrix.one_mul] at hFTC
  rw [hFTC]
  abel

/-- `x(t) := Φ(t, t₀) *ᵥ x₀` is an *integral solution* (`IsIntegralSolution`, from
`ODEs/ODE_properties.lean`) of `ẋ = A(t) x` on the segment between `t₀` and `t₁` — the
integral-equation reformulation of `hasDerivAt_stateTransitionMatrix_mulVec`, via the
fundamental theorem of calculus. This is what lets uniqueness reuse `continuous_dependence_ODE`
(Theorem 3.4), which is stated in terms of `IsIntegralSolution` rather than `HasDerivAt`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "lem:isIntegralSolution-stateTransitionMatrix-mulVec"
  (title := "Integral form, vector-valued")
  (latexEnv := "lemma")
  (statement := /-- $x(t) := \Phi(t,t_0)\, x_0$ satisfies the integral equation
    \[
      x(t) = x_0 + \int_{t_0}^{t} A(s)\, x(s)\,\mathrm{d}s
    \]
    for every $t$ between $t_0$ and $t_1$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5.
  -/)
  (proof := /-- The fundamental theorem of calculus applied to
    \cref{thm:hasDerivAt-stateTransitionMatrix-mulVec}, using $\Phi(t_0,t_0) = I$
    (\cref{thm:stateTransitionMatrix-self}) to fix the initial value. -/)]
theorem isIntegralSolution_stateTransitionMatrix_mulVec (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (x₀ : X → ℝ) :
    IsIntegralSolution t₀ t₁ (fun t => stateTransitionMatrix A t t₀ *ᵥ x₀) x₀
      (fun s v => A s *ᵥ v) := by
  have hx_cont : ContinuousOn (fun t => stateTransitionMatrix A t t₀ *ᵥ x₀) (Set.uIcc t₀ t₁) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix hA hA_le).prodMk continuousOn_const)
  intro t ht
  have huIcc_sub : Set.uIcc t₀ t ⊆ Set.uIcc t₀ t₁ := Set.uIcc_subset_uIcc_left ht
  have huIoo_sub : Set.uIoo t₀ t ⊆ Set.uIoo t₀ t₁ := by
    rw [← Set.Ioo_min_max, ← Set.Ioo_min_max]
    exact Set.Ioo_subset_Ioo (le_min (min_le_left t₀ t₁) ht.1) (max_le (le_max_left t₀ t₁) ht.2)
  have hx_cont' : ContinuousOn (fun s => stateTransitionMatrix A s t₀ *ᵥ x₀) (Set.uIcc t₀ t) :=
    hx_cont.mono huIcc_sub
  have hf'_cont : ContinuousOn (fun s => A s *ᵥ (stateTransitionMatrix A s t₀ *ᵥ x₀))
      (Set.uIcc t₀ t) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (hA.continuousOn.prodMk hx_cont')
  have hderiv : ∀ z ∈ Set.uIoo t₀ t,
      HasDerivWithinAt (fun z => stateTransitionMatrix A z t₀ *ᵥ x₀)
        (A z *ᵥ (stateTransitionMatrix A z t₀ *ᵥ x₀)) (Set.Ioi z) z :=
    fun z hz =>
      (hasDerivAt_stateTransitionMatrix_mulVec hA hA_le (huIoo_sub hz) x₀).hasDerivWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right hx_cont' hderiv
    hf'_cont.intervalIntegrable
  rw [stateTransitionMatrix_self, Matrix.one_mulVec] at hFTC
  rw [hFTC]
  abel

/-- **Peano-Baker series: uniqueness** (Hespanha, Theorem 5.1).
Any integral solution `z` of
`ẋ = A(t) x`, `x(t₀) = x₀` on the segment between `t₀` and `t₁` coincides with
`x(t) := Φ(t, t₀) *ᵥ x₀`.

Proof: apply `continuous_dependence_ODE` (Theorem 3.4) with zero perturbation `g := 0`. Since
both solutions share the initial value `x₀` and the perturbation bound is `μ = 0`, the bound it
gives collapses to `‖x t - z t‖ ≤ 0`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Theorem 5.1. -/
@[blueprint "thm:stateTransitionMatrix-mulVec-unique"
  (title := "Peano--Baker series: uniqueness")
  (statement := /-- Hespanha, Theorem 5.1.  Any solution
    $z$ of $\dot x = A(t)\, x$, $x(t_0) = x_0$, for $t$ between $t_0$ and $t_1$, coincides with
    $x(t) := \Phi(t,t_0)\, x_0$. -/)
  (proof := /-- Apply the continuous-dependence bound of Theorem 3.4 with zero perturbation:
    since both solutions share the initial value $x_0$, the resulting bound on
    $\|x(t) - z(t)\|$ collapses to $0$. -/)]
theorem stateTransitionMatrix_mulVec_unique (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (x₀ : X → ℝ)
    {z : ℝ → X → ℝ} (hz : IsIntegralSolution t₀ t₁ z x₀ (fun s v => A s *ᵥ v))
    (hz_cont : ContinuousOn z (Set.uIcc t₀ t₁)) :
    ∀ t ∈ Set.uIcc t₀ t₁, z t = stateTransitionMatrix A t t₀ *ᵥ x₀ := by
  -- A fixed Lipschitz constant for `v ↦ A t *ᵥ v`, valid for every `t` on the segment.
  set L : ℝ := max M 1 with hL_def
  have hL_pos : (0 : ℝ) < L := lt_of_lt_of_le one_pos (le_max_right M 1)
  have hM_le_L : M ≤ L := le_max_left M 1
  have hLip : ∀ t ∈ Set.uIcc t₀ t₁,
      LipschitzWith ⟨L, hL_pos.le⟩ (fun v : X → ℝ => A t *ᵥ v) := by
    intro t ht
    refine LipschitzWith.of_dist_le_mul fun v₁ v₂ => ?_
    have hAt : ‖A t‖ ≤ L := (hA_le t ht).trans hM_le_L
    calc dist (A t *ᵥ v₁) (A t *ᵥ v₂) = ‖A t *ᵥ v₁ - A t *ᵥ v₂‖ := dist_eq_norm _ _
      _ = ‖A t *ᵥ (v₁ - v₂)‖ := by rw [Matrix.mulVec_sub]
      _ ≤ ‖A t‖ * ‖v₁ - v₂‖ := Matrix.linfty_opNorm_mulVec _ _
      _ ≤ L * dist v₁ v₂ := by rw [dist_eq_norm]; gcongr
  -- Feed `continuous_dependence_ODE` (Theorem 3.4) the zero perturbation `g := 0`.
  have hbound := continuous_dependence_ODE (g := fun _ _ => (0 : X → ℝ)) (μ := 0) hL_pos
    (isIntegralSolution_stateTransitionMatrix_mulVec hA hA_le x₀) (by simpa using hz)
    ((continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix hA hA_le).prodMk continuousOn_const))
    hz_cont ((hA.comp continuous_fst).matrix_mulVec continuous_snd) intervalIntegrable_const
    hLip (fun _ _ _ => by simp)
  intro t ht
  have h0 : ‖stateTransitionMatrix A t t₀ *ᵥ x₀ - z t‖ ≤ 0 := by simpa using hbound t ht
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp h0)).symm

/-- **Columns of the state transition matrix** (Hespanha, P5.2).
For a fixed standard basis vector `e_i`, `stateTransitionMatrix_mulVec_unique`
specializes to: any integral solution `z` of `ẋ = A(t) x`, `x(t₀) = e_i` on the segment between
`t₀` and `t₁` coincides with the `i`-th column of `Φ(t, t₀)` — via
`Φ(t, t₀) *ᵥ e_i = (Φ(t, t₀)).col i` (`Matrix.mulVec_single_one`).

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.2. -/
@[blueprint "thm:stateTransitionMatrix-col-unique"
  (title := "Columns of the state transition matrix")
  (statement := /-- Hespanha, P5.2.  For every fixed $i$, the $i$-th column of $\Phi(t,t_0)$ is
    the unique solution of $\dot x = A(t)\, x$, $x(t_0) = e_i$, where $e_i$ is the $i$-th
    standard basis vector. -/)
  (proof := /-- Restatement of \cref{thm:stateTransitionMatrix-mulVec-unique} at
    $x_0 := e_i$, using $\Phi(t,t_0)\, e_i = (\Phi(t,t_0))_{\cdot,i}$
    (\texttt{Matrix.mulVec\_single\_one}). -/)]
theorem stateTransitionMatrix_col_unique (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (i : X)
    {z : ℝ → X → ℝ} (hz : IsIntegralSolution t₀ t₁ z (Pi.single i 1) (fun s v => A s *ᵥ v))
    (hz_cont : ContinuousOn z (Set.uIcc t₀ t₁)) :
    ∀ t ∈ Set.uIcc t₀ t₁, z t = (stateTransitionMatrix A t t₀).col i := by
  intro t ht
  rw [← Matrix.mulVec_single_one]
  exact stateTransitionMatrix_mulVec_unique hA hA_le (Pi.single i 1) hz hz_cont t ht

/-- The matrix analogue of `stateTransitionMatrix_mulVec_unique`: any integral solution `Y` of
`Ẏ = A(t) Y`, `Y(t₀) = C` on the segment between `t₀` and `t₁` coincides with `Φ(t, t₀) * C`.
Unlike the vector case, the Lipschitz bound on `M ↦ A t * M` comes from submultiplicativity of
the operator norm (`norm_mul_le`) rather than `Matrix.linfty_opNorm_mulVec`, but the rest of the
argument — feeding `continuous_dependence_ODE` (Theorem 3.4) the zero perturbation `g := 0` —
is identical.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "thm:stateTransitionMatrix-mul-unique"
  (title := "Uniqueness of matrix-valued solutions")
  (statement := /-- Any solution $Y$ of $\dot Y = A(t)\, Y$, $Y(t_0) = C$, for $t$ between $t_0$
    and $t_1$, coincides with $\Phi(t,t_0)\, C$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5.
  -/)
  (proof := /-- Apply the continuous-dependence bound of Theorem 3.4 with zero perturbation:
    since both solutions share the initial value $C$, the resulting bound on
    $\|Y(t) - Z(t)\|$ collapses to $0$. -/)]
theorem stateTransitionMatrix_mul_unique (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (C : Matrix X X ℝ)
    {Y : ℝ → Matrix X X ℝ} (hY : IsIntegralSolution t₀ t₁ Y C (fun s M' => A s * M'))
    (hY_cont : ContinuousOn Y (Set.uIcc t₀ t₁)) :
    ∀ t ∈ Set.uIcc t₀ t₁, Y t = stateTransitionMatrix A t t₀ * C := by
  -- A fixed Lipschitz constant for `M' ↦ A t * M'`, valid for every `t` on the segment.
  set L : ℝ := max M 1 with hL_def
  have hL_pos : (0 : ℝ) < L := lt_of_lt_of_le one_pos (le_max_right M 1)
  have hM_le_L : M ≤ L := le_max_left M 1
  have hLip : ∀ t ∈ Set.uIcc t₀ t₁,
      LipschitzWith ⟨L, hL_pos.le⟩ (fun M' : Matrix X X ℝ => A t * M') := by
    intro t ht
    refine LipschitzWith.of_dist_le_mul fun M₁ M₂ => ?_
    have hAt : ‖A t‖ ≤ L := (hA_le t ht).trans hM_le_L
    calc dist (A t * M₁) (A t * M₂) = ‖A t * M₁ - A t * M₂‖ := dist_eq_norm _ _
      _ = ‖A t * (M₁ - M₂)‖ := by rw [mul_sub]
      _ ≤ ‖A t‖ * ‖M₁ - M₂‖ := norm_mul_le _ _
      _ ≤ L * dist M₁ M₂ := by rw [dist_eq_norm]; gcongr
  -- Feed `continuous_dependence_ODE` (Theorem 3.4) the zero perturbation `g := 0`.
  have hbound := continuous_dependence_ODE
    (g := fun _ _ => (0 : Matrix X X ℝ)) (μ := 0) hL_pos
    (isIntegralSolution_stateTransitionMatrix_mul hA hA_le C) (by simpa using hY)
    ((continuous_fst.mul continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix hA hA_le).prodMk continuousOn_const))
    hY_cont ((hA.comp continuous_fst).mul continuous_snd) intervalIntegrable_const
    hLip (fun _ _ _ => by simp)
  intro t ht
  have h0 : ‖stateTransitionMatrix A t t₀ * C - Y t‖ ≤ 0 := by simpa using hbound t ht
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp h0)).symm

/-- Auxiliary re-anchoring fact: `Y(z) := Φ(z, a) * C`, an integral solution of the matrix ODE
anchored at `a`, also satisfies the integral equation anchored at the *other* endpoint `b`, with
the whole segment between `a` and `b` still as the domain — what `stateTransitionMatrix_inv`
needs to compare `Φ(·, a)` against `Φ(·, b) * Φ(b, a)` using `stateTransitionMatrix_mul_unique`
anchored at `b`.

This is `IsIntegralSolution.reanchor` at the two endpoints, `s := b` and `r := a`. -/
private lemma isIntegralSolution_stateTransitionMatrix_mul_reanchor (hA : Continuous A) {a b M : ℝ}
    (hA_le : ∀ r ∈ Set.uIcc a b, ‖A r‖ ≤ M) (C : Matrix X X ℝ) :
    IsIntegralSolution b a (fun z => stateTransitionMatrix A z a * C)
      (stateTransitionMatrix A b a * C) (fun s Y => A s * Y) :=
  (isIntegralSolution_stateTransitionMatrix_mul hA hA_le C).reanchor
    ((hA.comp continuous_fst).mul continuous_snd)
    ((continuous_fst.mul continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix hA hA_le).prodMk continuousOn_const))
    Set.right_mem_uIcc Set.left_mem_uIcc

/-- **Semigroup property** (Hespanha, P5.3).
`Φ(t,s) * Φ(s,τ) = Φ(t,τ)` for `τ ≤ s < t`, with `A`
continuous and bounded by `M` on the segment between `τ` and `t`.

Proof: `Φ(·,τ)`, re-anchored at `s` (`IsIntegralSolution.reanchor`), is an integral solution of
the matrix ODE on the segment between `s` and `t` with initial value `Φ(s,τ)`, hence coincides
with `Φ(·,s) * Φ(s,τ)` there by `stateTransitionMatrix_mul_unique`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.3. -/
@[blueprint "thm:stateTransitionMatrix-semigroup"
  (title := "Semigroup property")
  (statement := /-- Hespanha, P5.3.  For $A$ continuous and bounded on
    $[\tau, t]$, and any $\tau \le s < t$,
    \[
      \Phi(t,s)\,\Phi(s,\tau) = \Phi(t,\tau).
    \] -/)
  (proof := /-- $\Phi(\cdot,\tau)$, re-anchored at $s$, is an integral solution of the matrix
    ODE on the segment between $s$ and $t$ with initial value $\Phi(s,\tau)$, hence coincides
    with $\Phi(\cdot,s)\,\Phi(s,\tau)$ there by \cref{thm:stateTransitionMatrix-mul-unique}. -/)]
theorem stateTransitionMatrix_semigroup (hA : Continuous A) {τ s t M : ℝ} (hτs : τ ≤ s)
    (hst : s < t) (hA_le : ∀ r ∈ Set.Icc τ t, ‖A r‖ ≤ M) :
    stateTransitionMatrix A t s * stateTransitionMatrix A s τ = stateTransitionMatrix A t τ := by
  have hτt : τ < t := hτs.trans_lt hst
  have hA_le_u : ∀ r ∈ Set.uIcc τ t, ‖A r‖ ≤ M := by rw [Set.uIcc_of_le hτt.le]; exact hA_le
  have hs_mem : s ∈ Set.uIcc τ t := by rw [Set.uIcc_of_le hτt.le]; exact ⟨hτs, hst.le⟩
  have hA_le'_u : ∀ r ∈ Set.uIcc s t, ‖A r‖ ≤ M := by
    rw [Set.uIcc_of_le hst.le]
    exact fun r hr => hA_le r (Set.Icc_subset_Icc hτs le_rfl hr)
  have hF_cont : Continuous (fun p : ℝ × Matrix X X ℝ => A p.1 * p.2) :=
    (hA.comp continuous_fst).mul continuous_snd
  have hbase : IsIntegralSolution τ t (fun z => stateTransitionMatrix A z τ)
      (1 : Matrix X X ℝ) (fun r Y => A r * Y) := by
    simpa using isIntegralSolution_stateTransitionMatrix_mul hA hA_le_u 1
  have hre := hbase.reanchor hF_cont (continuousOn_stateTransitionMatrix hA hA_le_u) hs_mem
    Set.right_mem_uIcc
  have hunique := stateTransitionMatrix_mul_unique hA hA_le'_u (stateTransitionMatrix A s τ) hre
    ((continuousOn_stateTransitionMatrix hA hA_le_u).mono (Set.uIcc_subset_uIcc_right hs_mem))
    t Set.right_mem_uIcc
  exact hunique.symm

/-- **Invertibility of the state transition matrix** (Hespanha, P5.4).
`Φ(t,τ)` is nonsingular, with `Φ(t,τ)⁻¹ = Φ(τ,t)`, for `A` continuous and bounded
by `M` on the segment between `τ` and `t`.

Proof: `Φ(·,τ)`, re-anchored at `t` (`isIntegralSolution_stateTransitionMatrix_mul_reanchor`), is
an integral solution of the matrix ODE on the segment between `t` and `τ` with initial value
`Φ(t,τ)`, hence coincides with `Φ(·,t) * Φ(t,τ)` there (`stateTransitionMatrix_mul_unique`).
Evaluating at `τ` gives `Φ(τ,t) * Φ(t,τ) = Φ(τ,τ) = I`, so `Φ(τ,t)` is a left inverse of
`Φ(t,τ)`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.4. -/
@[blueprint "thm:stateTransitionMatrix-inv"
  (title := "Invertibility of the state transition matrix")
  (statement := /-- Hespanha, P5.4.  For $A$ continuous and bounded on the segment between $\tau$
    and $t$, $\Phi(t,\tau)$ is nonsingular and
    \[
      \Phi(t,\tau)^{-1} = \Phi(\tau,t).
    \] -/)
  (proof := /-- From \cref{thm:stateTransitionMatrix-semigroup}, generalized to arbitrary order
    by re-anchoring $\Phi(\cdot,\tau)$ at $t$ and invoking uniqueness there,
    $\Phi(\tau,t)\Phi(t,\tau) = \Phi(\tau,\tau) = I$, so $\Phi(t,\tau)$ and $\Phi(\tau,t)$ are
    mutual inverses. -/)]
theorem stateTransitionMatrix_inv (hA : Continuous A) {t τ M : ℝ}
    (hA_le : ∀ r ∈ Set.uIcc τ t, ‖A r‖ ≤ M) :
    IsUnit (stateTransitionMatrix A t τ) ∧
      (stateTransitionMatrix A t τ)⁻¹ = stateTransitionMatrix A τ t := by
  -- `Φ(·,τ)`, re-anchored at `t`, coincides with `Φ(·,t) * Φ(t,τ)` on `[t,τ]` by uniqueness;
  -- evaluating at `τ` gives `Φ(τ,t) * Φ(t,τ) = Φ(τ,τ) = I`.
  have hmul : stateTransitionMatrix A τ t * stateTransitionMatrix A t τ = 1 := by
    have hY : IsIntegralSolution t τ (fun z => stateTransitionMatrix A z τ)
        (stateTransitionMatrix A t τ) (fun s Y => A s * Y) := by
      simpa using isIntegralSolution_stateTransitionMatrix_mul_reanchor hA hA_le
        (1 : Matrix X X ℝ)
    have huniq := stateTransitionMatrix_mul_unique hA
      (show ∀ r ∈ Set.uIcc t τ, ‖A r‖ ≤ M by rwa [Set.uIcc_comm])
      (stateTransitionMatrix A t τ) hY
      (show ContinuousOn (fun z => stateTransitionMatrix A z τ) (Set.uIcc t τ) by
        rw [Set.uIcc_comm]; exact continuousOn_stateTransitionMatrix hA hA_le)
      τ Set.right_mem_uIcc
    rwa [stateTransitionMatrix_self, eq_comm] at huniq
  exact ⟨IsUnit.of_mul_eq_one_right _ hmul, Matrix.inv_eq_left_inv hmul⟩

/-- Composition of the state transition matrix, varying the *first* argument: `Φ(z,a) =
Φ(z,b) * Φ(b,a)` for every `z` on the segment between `a` and `b`. This is the general form of
the fact used inside `stateTransitionMatrix_inv` (which only needed it at `z = τ`); kept general
here because `stateTransitionMatrix_comp` below needs it at an arbitrary point.

Proof: identical to `stateTransitionMatrix_inv`'s — `Φ(·,a)`, re-anchored at `b`
(`isIntegralSolution_stateTransitionMatrix_mul_reanchor`), coincides with `Φ(·,b) * Φ(b,a)` on
`[b,a]` by uniqueness (`stateTransitionMatrix_mul_unique`). -/
@[blueprint "lem:stateTransitionMatrix-comp-of-mem"
  (title := "Composition on a subinterval")
  (latexEnv := "lemma")
  (statement := /-- For every $z$ on the segment between $a$ and $b$,
    $\Phi(z, a) = \Phi(z, b)\,\Phi(b, a)$.  Composition with the \emph{first} argument free. -/)
  (proof := /-- $\Phi(\cdot, a)$, re-anchored at $b$, is an integral solution of
    $\dot Y = A(r)Y$ with value $\Phi(b,a)$ at $b$; so is $\Phi(\cdot, b)\Phi(b,a)$.  They agree
    by \cref{thm:stateTransitionMatrix-mul-unique}. -/)]
theorem stateTransitionMatrix_comp_of_mem (hA : Continuous A) {a b M : ℝ}
    (hA_le : ∀ r ∈ Set.uIcc a b, ‖A r‖ ≤ M) {z : ℝ} (hz : z ∈ Set.uIcc a b) :
    stateTransitionMatrix A z a = stateTransitionMatrix A z b * stateTransitionMatrix A b a := by
  have hY : IsIntegralSolution b a (fun z => stateTransitionMatrix A z a)
      (stateTransitionMatrix A b a) (fun r Y => A r * Y) := by
    simpa using isIntegralSolution_stateTransitionMatrix_mul_reanchor hA hA_le
      (1 : Matrix X X ℝ)
  exact stateTransitionMatrix_mul_unique hA (show ∀ r ∈ Set.uIcc b a, ‖A r‖ ≤ M by
      rwa [Set.uIcc_comm]) (stateTransitionMatrix A b a) hY
    (show ContinuousOn (fun z => stateTransitionMatrix A z a) (Set.uIcc b a) by
      rw [Set.uIcc_comm]; exact continuousOn_stateTransitionMatrix hA hA_le)
    z (by rwa [Set.uIcc_comm] at hz)

/-- **Semigroup property, order-free** (Hespanha, P5.3).
`Φ(t,s) * Φ(s,τ) = Φ(t,τ)` for *any* `s` on the segment between `τ`
and `t` — the order-free generalization of `stateTransitionMatrix_semigroup`, whose `τ ≤ s < t`
restriction was an artifact of matching the textbook's literal statement, not a genuine
requirement. Needed by the variation-of-constants existence proof, where `s = t₀` is fixed and
`τ` ranges over the *whole* segment `[t₀,t]`, not just points strictly after `t₀`.

Proof: `Φ(s,τ) = Φ(s,t) * Φ(t,τ)` by `stateTransitionMatrix_comp_of_mem`; left-multiply by
`Φ(t,s)` and simplify via `Φ(t,s) * Φ(s,t) = I` (P5.4, `stateTransitionMatrix_inv`).

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.3. -/
@[blueprint "thm:stateTransitionMatrix-comp"
  (title := "Semigroup property, order-free")
  (statement := /-- Hespanha, P5.3.  For \emph{any} $s$ on the segment between $\tau$
    and $t$,
    \[
      \Phi(t, s)\,\Phi(s, \tau) = \Phi(t, \tau).
    \]
    The $\tau \le s < t$ ordering in \cref{thm:stateTransitionMatrix-semigroup} matches the
    textbook's literal statement but is not a genuine requirement; the variation-of-constants
    proof needs the unordered form, where $s = t_0$ is fixed and $\tau$ ranges over the whole
    segment. -/)
  (proof := /-- \cref{lem:stateTransitionMatrix-comp-of-mem} gives
    $\Phi(s,\tau) = \Phi(s,t)\Phi(t,\tau)$; left-multiply by $\Phi(t,s)$ and cancel using
    $\Phi(t,s)\Phi(s,t) = I$ (\cref{thm:stateTransitionMatrix-inv}). -/)]
theorem stateTransitionMatrix_comp (hA : Continuous A) {τ t M : ℝ}
    (hA_le : ∀ r ∈ Set.uIcc τ t, ‖A r‖ ≤ M) {s : ℝ} (hs : s ∈ Set.uIcc τ t) :
    stateTransitionMatrix A t s * stateTransitionMatrix A s τ = stateTransitionMatrix A t τ := by
  have hcomp := stateTransitionMatrix_comp_of_mem hA hA_le hs
  have hA_le' : ∀ r ∈ Set.uIcc s t, ‖A r‖ ≤ M := fun r hr =>
    hA_le r (Set.uIcc_subset_uIcc_right hs hr)
  obtain ⟨hunit, hinv⟩ := stateTransitionMatrix_inv hA hA_le'
  rw [hcomp, ← mul_assoc, ← hinv, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
    hunit), Matrix.one_mul]

/-- Composition of the state transition matrix through a fixed *base* point: `Φ(t,t₀) *
Φ(t₀,τ) = Φ(t,τ)` for every `τ` on the segment between `t₀` and `t`. This is the shape needed by
variation-of-constants, where `t₀` and `t` are the fixed integration endpoints and `τ` is the
integration variable — unlike `stateTransitionMatrix_comp`, which needs the *middle* point of the
three (there, `τ` would have to lie between the two fixed points, not the reverse).

Proof: `stateTransitionMatrix_comp` (with `τ` itself as the middle point) gives
`Φ(t,τ) * Φ(τ,t₀) = Φ(t,t₀)`; solve for `Φ(t,τ)` by right-multiplying by `Φ(t₀,τ)` and
cancelling `Φ(τ,t₀) * Φ(t₀,τ) = I` (P5.4). -/
@[blueprint "lem:stateTransitionMatrix-comp-base"
  (title := "Change of base time")
  (latexEnv := "lemma")
  (statement := /-- For every $\tau$ on the segment between $t_0$ and $t$,
    $\Phi(t, t_0)\,\Phi(t_0, \tau) = \Phi(t, \tau)$: composition through a fixed \emph{base}
    point.  This differs from \cref{thm:stateTransitionMatrix-comp} in which of the three times
    is required to lie between the others — here the two fixed integration endpoints are the
    outer ones and $\tau$ is free, which is the shape variation of constants needs. -/)
  (proof := /-- \cref{thm:stateTransitionMatrix-comp} with $\tau$ itself as the middle point
    gives $\Phi(t,\tau)\Phi(\tau,t_0) = \Phi(t,t_0)$; right-multiply by $\Phi(t_0,\tau)$ and
    cancel $\Phi(\tau,t_0)\Phi(t_0,\tau) = I$. -/)]
theorem stateTransitionMatrix_comp_base (hA : Continuous A) {t₀ t M : ℝ}
    (hA_le : ∀ r ∈ Set.uIcc t₀ t, ‖A r‖ ≤ M) {τ : ℝ} (hτ : τ ∈ Set.uIcc t₀ t) :
    stateTransitionMatrix A t t₀ * stateTransitionMatrix A t₀ τ = stateTransitionMatrix A t τ := by
  have hcomp := stateTransitionMatrix_comp hA hA_le hτ
  obtain ⟨hunit, hinv⟩ := stateTransitionMatrix_inv hA
    (fun r hr => hA_le r (Set.uIcc_subset_uIcc_left hτ hr))
  rw [← hcomp, mul_assoc, ← hinv,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit), mul_one]

/-- Continuity of the state transition matrix in its *second* argument, with the first held
fixed — the mirror image of `continuousOn_stateTransitionMatrix` (which varies the first
argument, base fixed). Needed whenever `Φ(t, ·)` appears as an integrand, as in the
variation-of-constants formula.

Proof: `Φ(τ,t)⁻¹ = Φ(t,τ)` by P5.4 (`stateTransitionMatrix_inv`), so `τ ↦ Φ(t,τ)` is the
composition of `τ ↦ Φ(τ,t)` (continuous by `continuousOn_stateTransitionMatrix`) with matrix
inversion, continuous at every unit (`continuousAt_matrix_inv`). -/
@[blueprint "lem:continuousOn-stateTransitionMatrix-snd"
  (title := "Continuity in the initial time")
  (latexEnv := "lemma")
  (statement := /-- With the first argument held fixed, $\tau \mapsto \Phi(t, \tau)$ is
    continuous on the segment between $t$ and $t_1$ — the mirror of
    \cref{lem:continuousOn-stateTransitionMatrix}, which varies the first argument.  Needed
    wherever $\Phi(t, \cdot)$ is an integrand, as in variation of constants. -/)
  (proof := /-- By \cref{thm:stateTransitionMatrix-inv}, $\Phi(t,\tau) = \Phi(\tau,t)^{-1}$, so
    the map is $\tau \mapsto \Phi(\tau,t)$ — continuous in its first argument — followed by
    matrix inversion, which is continuous at every unit. -/)]
theorem continuousOn_stateTransitionMatrix_snd (hA : Continuous A) {t t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t t₁, ‖A s‖ ≤ M) :
    ContinuousOn (fun τ => stateTransitionMatrix A t τ) (Set.uIcc t t₁) := by
  intro τ hτ
  have hA_le' : ∀ r ∈ Set.uIcc t τ, ‖A r‖ ≤ M := fun r hr =>
    hA_le r (Set.uIcc_subset_uIcc_left hτ hr)
  obtain ⟨hunit, hinv⟩ := stateTransitionMatrix_inv hA hA_le'
  -- `hunit : IsUnit (Φ(τ,t))`, `hinv : (Φ(τ,t))⁻¹ = Φ(t,τ)`.
  have hdet_unit : IsUnit (stateTransitionMatrix A τ t).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hring_cont : ContinuousAt Ring.inverse (stateTransitionMatrix A τ t).det := by
    rw [← hdet_unit.unit_spec]
    exact NormedRing.inverse_continuousAt hdet_unit.unit
  have hcont_swap : ContinuousWithinAt (fun τ' => stateTransitionMatrix A τ' t)
      (Set.uIcc t t₁) τ :=
    continuousOn_stateTransitionMatrix hA hA_le τ hτ
  refine ((continuousAt_matrix_inv _ hring_cont).comp_continuousWithinAt
    (f := fun τ' => stateTransitionMatrix A τ' t) hcont_swap).congr
    (fun τ' hτ' => ?_) hinv.symm
  exact (stateTransitionMatrix_inv hA
    (fun r hr => hA_le r (Set.uIcc_subset_uIcc_left hτ' hr))).2.symm

variable {U Y : Type*} [Fintype U] [Fintype Y] {B : ℝ → Matrix X U ℝ} {u : ℝ → U → ℝ}
variable {C : ℝ → Matrix Y X ℝ} {D : ℝ → Matrix Y U ℝ}

/-- **Integrating-factor step 1.** `w(t) := x₀ + ∫ τ in t₀..t, Φ(t₀,τ) *ᵥ (B(τ) *ᵥ u(τ))` has
derivative `Φ(t₀,t) *ᵥ (B(t) *ᵥ u(t))` — an *ordinary* FTC fact, since `t₀` (unlike the outer `t`
in `hasDerivAt_variationOfConstants`) is fixed throughout the integrand: only the upper limit
depends on the differentiation variable. This avoids ever needing to differentiate `Φ` in its
second argument, only integrate it (`continuousOn_stateTransitionMatrix_snd`). -/
private lemma hasDerivAt_variationOfConstants_w (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M)
    {t : ℝ} (ht : t ∈ Set.uIoo t₀ t₁) (x₀ : X → ℝ) :
    HasDerivAt (fun z => x₀ + ∫ τ in t₀..z, stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))
      (stateTransitionMatrix A t₀ t *ᵥ (B t *ᵥ u t)) t := by
  have hF_cont : ContinuousOn (fun τ => stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))
      (Set.uIcc t₀ t₁) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix_snd hA hA_le).prodMk
        (hB.matrix_mulVec hu).continuousOn)
  have hopen : IsOpen (Set.uIoo t₀ t₁) := by rw [← Set.Ioo_min_max]; exact isOpen_Ioo
  have hF_cont_at : ContinuousAt (fun τ => stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ)) t :=
    (hF_cont.mono Set.uIoo_subset_uIcc_self).continuousAt (hopen.mem_nhds ht)
  have hint : IntervalIntegrable (fun τ => stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))
      volume t₀ t :=
    (hF_cont.mono (Set.uIcc_subset_uIcc_left (Set.uIoo_subset_uIcc_self ht))).intervalIntegrable
  have hderiv := intervalIntegral.integral_hasDerivAt_right hint
    (ContinuousOn.stronglyMeasurableAtFilter (μ := volume) hopen
      (hF_cont.mono Set.uIoo_subset_uIcc_self) t ht)
    hF_cont_at
  exact hderiv.const_add x₀

/-- **Integrating-factor step 2.** `x(z) = Φ(z,t₀) *ᵥ w(z)`, algebraically, for `w` as in
`hasDerivAt_variationOfConstants_w` — this is what lets differentiating `x` reduce to an ordinary
product rule on `Φ(·,t₀) *ᵥ w(·)` instead of a Leibniz rule.

Proof: push `Φ(z,t₀)` through the integral defining `w` (as a fixed continuous linear map), then
use `stateTransitionMatrix_comp_base` pointwise: `Φ(z,t₀) *ᵥ (Φ(t₀,τ) *ᵥ v) = Φ(z,τ) *ᵥ v`. -/
private lemma variationOfConstants_eq_mulVec (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (x₀ : X → ℝ)
    {z : ℝ} (hz : z ∈ Set.uIcc t₀ t₁) :
    stateTransitionMatrix A z t₀ *ᵥ x₀ +
        ∫ τ in t₀..z, stateTransitionMatrix A z τ *ᵥ (B τ *ᵥ u τ) =
      stateTransitionMatrix A z t₀ *ᵥ
        (x₀ + ∫ τ in t₀..z, stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ)) := by
  rw [Matrix.mulVec_add]
  congr 1
  set L : (X → ℝ) →L[ℝ] (X → ℝ) :=
    LinearMap.toContinuousLinearMap (stateTransitionMatrix A z t₀).mulVecLin with hL
  have hL_apply : ∀ v : X → ℝ, L v = stateTransitionMatrix A z t₀ *ᵥ v :=
    fun v => Matrix.mulVecLin_apply _ v
  have hA_le' : ∀ s ∈ Set.uIcc t₀ z, ‖A s‖ ≤ M := fun s hs =>
    hA_le s (Set.uIcc_subset_uIcc_left hz hs)
  have hcont : ContinuousOn (fun τ => stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))
      (Set.uIcc t₀ z) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix_snd hA hA_le').prodMk
        (hB.matrix_mulVec hu).continuousOn)
  have hL_comm := L.intervalIntegral_comp_comm (μ := volume) hcont.intervalIntegrable
  simp only [hL_apply] at hL_comm
  rw [← hL_comm]
  refine intervalIntegral.integral_congr fun τ hτ => ?_
  rw [Matrix.mulVec_mulVec (B τ *ᵥ u τ), stateTransitionMatrix_comp_base hA hA_le' hτ]

/-- **Integrating-factor step 3, matrix→CLM transport.** `M ↦ (v ↦ M *ᵥ v)`, as a continuous
linear map from matrices into `(X → ℝ) →L[ℝ] X → ℝ`. Needed to turn a *matrix*-valued
`HasDerivAt` (`hasDerivAt_stateTransitionMatrix`) into a `ContinuousLinearMap`-valued one, so
`HasDerivAt.clm_apply` can differentiate `z ↦ Φ(z,t₀) *ᵥ w(z)` as a product of two moving paths.

Built from `Matrix.mulVecBilin`, the curried linear (not yet continuous) version of `*ᵥ`, by
applying `LinearMap.toContinuousLinearMap` twice — once to continuify each value
`v ↦ M *ᵥ v` (inner map, domain `X → ℝ` is finite-dimensional), once to continuify the whole
assignment `M ↦ (that CLM)` (outer map, domain `Matrix X X ℝ` is finite-dimensional
too). -/
private noncomputable def matrixMulVecCLM :
    Matrix X X ℝ →L[ℝ] (X → ℝ) →L[ℝ] X → ℝ :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (Matrix.mulVecBilin ℝ ℝ))

omit [DecidableEq X] in
private lemma matrixMulVecCLM_apply (M : Matrix X X ℝ) (v : X → ℝ) :
    matrixMulVecCLM M v = M *ᵥ v := rfl

/-- **Integrating-factor step 3+4.** `z ↦ Φ(z,t₀) *ᵥ w(z)` solves `ẋ = A(t)x + B(t)u(t)` at
`t` — the ordinary product rule (`HasDerivAt.clm_apply`, via `matrixMulVecCLM`) applied to
`hasDerivAt_stateTransitionMatrix` and `hasDerivAt_variationOfConstants_w`, simplified using
`Φ(t,t₀) * Φ(t₀,t) = Φ(t,t) = I` (`stateTransitionMatrix_comp_base`,
`stateTransitionMatrix_self`) to cancel the forcing term down to `B(t) *ᵥ u(t)`. -/
private lemma hasDerivAt_variationOfConstants_mulVec (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M)
    {t : ℝ} (ht : t ∈ Set.uIoo t₀ t₁) (x₀ : X → ℝ) :
    HasDerivAt (fun z => stateTransitionMatrix A z t₀ *ᵥ
        (x₀ + ∫ τ in t₀..z, stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ)))
      (A t *ᵥ (stateTransitionMatrix A t t₀ *ᵥ
          (x₀ + ∫ τ in t₀..t, stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))) + B t *ᵥ u t) t := by
  have hΦ_deriv := (matrixMulVecCLM.hasFDerivAt
    (x := stateTransitionMatrix A t t₀)).comp_hasDerivAt t
    (hasDerivAt_stateTransitionMatrix hA hA_le ht)
  have hderiv := hΦ_deriv.clm_apply (hasDerivAt_variationOfConstants_w hA hB hu hA_le ht x₀)
  simp only [Function.comp_apply, matrixMulVecCLM_apply] at hderiv
  have hcancel : stateTransitionMatrix A t t₀ * stateTransitionMatrix A t₀ t = 1 := by
    rw [stateTransitionMatrix_comp_base hA
      (fun r hr => hA_le r (Set.uIcc_subset_uIcc_left (Set.uIoo_subset_uIcc_self ht) hr))
      Set.right_mem_uIcc, stateTransitionMatrix_self]
  rwa [Matrix.mulVec_mulVec (B t *ᵥ u t), hcancel, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec] at hderiv

/-- **Variation of constants: existence** (Hespanha, Theorem 5.2).
`x(t) := Φ(t,t₀) *ᵥ x₀ +
∫ τ in t₀..t, Φ(t,τ) *ᵥ (B(τ) *ᵥ u(τ))` solves the initial value problem
`ẋ = A(t) x + B(t) u(t)`, `x(t₀) = x₀`.

Proof: transfer `hasDerivAt_variationOfConstants_mulVec` (the derivative of `Φ(·,t₀) *ᵥ w(·)`)
across the pointwise equality `x(z) = Φ(z,t₀) *ᵥ w(z)` (`variationOfConstants_eq_mulVec`), valid
on the neighborhood `Set.uIcc t₀ t₁ ∈ 𝓝 t` since `t` is interior to it.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Theorem 5.2. -/
@[blueprint "thm:hasDerivAt-variationOfConstants"
  (title := "Variation of constants: existence")
  (statement := /-- Hespanha, Theorem 5.2.  For continuous $A$, $B$ and $u$, the
    function
    \[
      x(t) := \Phi(t, t_0)x_0 + \int_{t_0}^{t} \Phi(t, \tau)B(\tau)u(\tau)\,d\tau
    \]
    satisfies $\dot x(t) = A(t)x(t) + B(t)u(t)$ at every interior $t$. -/)
  (proof := /-- The obstacle is that $t$ appears in both the upper limit and the integrand.
    Factor it out: with
    $w(t) := x_0 + \int_{t_0}^{t}\Phi(t_0,\tau)B(\tau)u(\tau)\,d\tau$, whose integrand does not
    depend on $t$, the fundamental theorem of calculus gives $w$ directly, and
    \cref{lem:stateTransitionMatrix-comp-base} shows $x(t) = \Phi(t,t_0)w(t)$.  Differentiating
    that product and cancelling $\Phi(t,t_0)\Phi(t_0,t) = I$ leaves the claim.  $\Phi$ is thus
    only ever integrated in its second argument, never differentiated there. -/)]
theorem hasDerivAt_variationOfConstants (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M)
    {t : ℝ} (ht : t ∈ Set.uIoo t₀ t₁) (x₀ : X → ℝ) :
    HasDerivAt (fun z => stateTransitionMatrix A z t₀ *ᵥ x₀ +
        ∫ τ in t₀..z, stateTransitionMatrix A z τ *ᵥ (B τ *ᵥ u τ))
      (A t *ᵥ (stateTransitionMatrix A t t₀ *ᵥ x₀ +
          ∫ τ in t₀..t, stateTransitionMatrix A t τ *ᵥ (B τ *ᵥ u τ)) + B t *ᵥ u t) t := by
  have hopen : IsOpen (Set.uIoo t₀ t₁) := by rw [← Set.Ioo_min_max]; exact isOpen_Ioo
  have hderiv0 := hasDerivAt_variationOfConstants_mulVec hA hB hu hA_le ht x₀
  rw [← variationOfConstants_eq_mulVec hA hB hu hA_le x₀ (Set.uIoo_subset_uIcc_self ht)] at hderiv0
  refine hderiv0.congr_of_eventuallyEq ?_
  filter_upwards [Filter.mem_of_superset (hopen.mem_nhds ht) Set.uIoo_subset_uIcc_self] with z hz
  exact variationOfConstants_eq_mulVec hA hB hu hA_le x₀ hz

/-- The variation-of-constants formula matches the initial value `x₀` at `t = t₀`: the forcing
integral is over the degenerate interval `[t₀,t₀]`, and `Φ(t₀,t₀) = I`. -/
@[blueprint "lem:variationOfConstants-self"
  (title := "Variation of constants at the initial time")
  (latexEnv := "lemma")
  (statement := /-- The variation-of-constants formula takes the value $x_0$ at $t = t_0$: the
    forcing integral is over the degenerate interval and $\Phi(t_0,t_0) = I$.  Together with
    \cref{thm:hasDerivAt-variationOfConstants} this makes it a solution of the initial value
    problem, not merely of the differential equation. -/)]
theorem variationOfConstants_self (t₀ : ℝ) (x₀ : X → ℝ) :
    stateTransitionMatrix A t₀ t₀ *ᵥ x₀ +
        ∫ τ in t₀..t₀, stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ) = x₀ := by
  simp [stateTransitionMatrix_self]

/-- **Variation of constants: uniqueness** (Hespanha, Theorem 5.2).
Any two integral solutions of the
forced LTV system `ẋ = A(t) x + B(t) u(t)` sharing the same initial value `x₀` coincide on the
segment between `t₀` and `t₁`.

Unlike the existence half, this needs no new machinery: for fixed `t`, `v ↦ A(t) v + B(t) u(t)`
is affine, hence globally Lipschitz, in `v`, so `continuous_dependence_ODE` (Theorem 3.4) applies
directly with zero perturbation `g := 0`, exactly as in `stateTransitionMatrix_mulVec_unique`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Theorem 5.2. -/
@[blueprint "thm:variationOfConstants-unique"
  (title := "Variation of constants: uniqueness")
  (statement := /-- Hespanha, Theorem 5.2.  Any two continuous integral solutions of
    the forced system $\dot x = A(t)x + B(t)u(t)$ with the same initial value $x_0$ agree on the
    segment between $t_0$ and $t_1$. -/)
  (proof := /-- For fixed $t$ the right-hand side $v \mapsto A(t)v + B(t)u(t)$ is affine in $v$,
    hence Lipschitz with constant $\max(M, 1)$ where $\|A\| \le M$.  Continuous dependence on
    initial conditions with zero perturbation then bounds $\|z_1(t) - z_2(t)\|$ by $0$.  The
    forcing term $B(t)u(t)$ is common to both solutions and cancels in the difference, so it
    never enters the Lipschitz estimate. -/)]
theorem variationOfConstants_unique (hA : Continuous A) (hB : Continuous B) (hu : Continuous u)
    {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) {x₀ : X → ℝ}
    {z₁ z₂ : ℝ → X → ℝ}
    (hz₁ : IsIntegralSolution t₀ t₁ z₁ x₀ (fun s v => A s *ᵥ v + B s *ᵥ u s))
    (hz₂ : IsIntegralSolution t₀ t₁ z₂ x₀ (fun s v => A s *ᵥ v + B s *ᵥ u s))
    (hz₁_cont : ContinuousOn z₁ (Set.uIcc t₀ t₁)) (hz₂_cont : ContinuousOn z₂ (Set.uIcc t₀ t₁)) :
    ∀ t ∈ Set.uIcc t₀ t₁, z₁ t = z₂ t := by
  set L : ℝ := max M 1 with hL_def
  have hL_pos : (0 : ℝ) < L := lt_of_lt_of_le one_pos (le_max_right M 1)
  have hM_le_L : M ≤ L := le_max_left M 1
  have hLip : ∀ t ∈ Set.uIcc t₀ t₁,
      LipschitzWith ⟨L, hL_pos.le⟩ (fun v : X → ℝ => A t *ᵥ v + B t *ᵥ u t) := by
    intro t ht
    refine LipschitzWith.of_dist_le_mul fun v₁ v₂ => ?_
    have hAt : ‖A t‖ ≤ L := (hA_le t ht).trans hM_le_L
    calc dist (A t *ᵥ v₁ + B t *ᵥ u t) (A t *ᵥ v₂ + B t *ᵥ u t)
        = dist (A t *ᵥ v₁) (A t *ᵥ v₂) := dist_add_right _ _ _
      _ = ‖A t *ᵥ v₁ - A t *ᵥ v₂‖ := dist_eq_norm _ _
      _ = ‖A t *ᵥ (v₁ - v₂)‖ := by rw [Matrix.mulVec_sub]
      _ ≤ ‖A t‖ * ‖v₁ - v₂‖ := Matrix.linfty_opNorm_mulVec _ _
      _ ≤ L * dist v₁ v₂ := by rw [dist_eq_norm]; gcongr
  have hbound := continuous_dependence_ODE (g := fun _ _ => (0 : X → ℝ)) (μ := 0) hL_pos
    hz₁ (by simpa using hz₂) hz₁_cont hz₂_cont
    (((hA.comp continuous_fst).matrix_mulVec continuous_snd).add
      ((hB.comp continuous_fst).matrix_mulVec (hu.comp continuous_fst)))
    intervalIntegrable_const hLip (fun _ _ _ => by simp)
  intro t ht
  have h0 : ‖z₁ t - z₂ t‖ ≤ 0 := by simpa using hbound t ht
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

/-- **Variation of constants: output equation** (Hespanha, equation (5.8)).
`y(t) := C(t) x(t) + D(t)
u(t)`, for `x(t)` as in `hasDerivAt_variationOfConstants`, splits into the *homogeneous response*
`C(t) Φ(t,t₀) x₀` and the *forced response* `∫ τ in t₀..t, C(t) Φ(t,τ) B(τ) u(τ) + D(t) u(t)`. -/
@[blueprint "lem:variationOfConstants-output"
  (title := "Variation of constants: output equation")
  (latexEnv := "lemma")
  (statement := /-- (Hespanha, equation (5.8)).
    With $x$ as in
    \cref{thm:hasDerivAt-variationOfConstants}, the output $y(t) = C(t)x(t) + D(t)u(t)$ splits
    into the homogeneous response and the forced response:
    \[
      y(t) = C(t)\Phi(t,t_0)x_0
             + \int_{t_0}^{t} C(t)\Phi(t,\tau)B(\tau)u(\tau)\,d\tau
             + D(t)u(t).
    \] -/)
  (proof := /-- $v \mapsto C(t)v$ is a continuous linear map and so commutes with the interval
    integral; the integrand is continuous by
    \cref{lem:continuousOn-stateTransitionMatrix-snd}. -/)]
theorem variationOfConstants_output (hA : Continuous A) (hB : Continuous B) (hu : Continuous u)
    {t₀ t M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t, ‖A s‖ ≤ M) (x₀ : X → ℝ) :
    C t *ᵥ (stateTransitionMatrix A t t₀ *ᵥ x₀ +
        ∫ τ in t₀..t, stateTransitionMatrix A t τ *ᵥ (B τ *ᵥ u τ)) + D t *ᵥ u t =
      C t *ᵥ (stateTransitionMatrix A t t₀ *ᵥ x₀) +
        (∫ τ in t₀..t, C t *ᵥ (stateTransitionMatrix A t τ *ᵥ (B τ *ᵥ u τ))) + D t *ᵥ u t := by
  rw [Matrix.mulVec_add, add_assoc, add_assoc]
  congr 2
  -- `v ↦ C t *ᵥ v`, as a continuous linear map, commutes with the interval integral.
  set L : (X → ℝ) →L[ℝ] (Y → ℝ) := LinearMap.toContinuousLinearMap (C t).mulVecLin
    with hL
  have hΦ_cont : ContinuousOn (fun τ => stateTransitionMatrix A t τ) (Set.uIcc t₀ t) := by
    rw [Set.uIcc_comm]
    exact continuousOn_stateTransitionMatrix_snd hA (by rwa [Set.uIcc_comm])
  have hcont : ContinuousOn (fun τ => stateTransitionMatrix A t τ *ᵥ (B τ *ᵥ u τ))
      (Set.uIcc t₀ t) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (hΦ_cont.prodMk (hB.matrix_mulVec hu).continuousOn)
  have hL_apply : ∀ v : X → ℝ, L v = C t *ᵥ v := fun v => Matrix.mulVecLin_apply (C t) v
  simpa [hL_apply] using
    (L.intervalIntegral_comp_comm (μ := volume) hcont.intervalIntegrable).symm

/-- The forced response starts at `x₀`: at `t = t₀` the forcing integral is over a degenerate
interval and `Φ(t₀,t₀) = I`. Plumbing for the integral form; `variationOfConstants_self` is
the same fact stated on the formula itself. -/
private theorem forcedResponse_self (t₀ : ℝ) (x₀ : X → ℝ) :
    forcedResponse A B u t₀ x₀ t₀ = x₀ := variationOfConstants_self t₀ x₀

/-- The forced response is continuous on the closed segment between `t₀` and `t₁`, endpoints
included.

Proof: `variationOfConstants_eq_mulVec` rewrites the response as `Φ(z,t₀) *ᵥ w(z)` with
`w(z) = x₀ + ∫ τ in t₀..z, Φ(t₀,τ) *ᵥ (B τ *ᵥ u τ)`, whose integrand does not depend on `z` —
only the limit does. Continuity of `w` is then the ordinary continuity of a primitive. -/
@[blueprint "lem:continuousOn-forcedResponse"
  (title := "Continuity of the forced response")
  (latexEnv := "lemma")
  (statement := /-- For continuous $A$, $B$ and $u$, the forced response
    (\cref{def:forcedResponse}) is continuous on the closed segment between $t_0$ and $t_1$,
    endpoints included. -/)
  (proof := /-- The integrating-factor identity rewrites the response as
    $\Phi(z,t_0)\,w(z)$ with
    $w(z) = x_0 + \int_{t_0}^{z}\Phi(t_0,\tau)B(\tau)u(\tau)\,\mathrm{d}\tau$, whose
    integrand does not depend on $z$ --- only the limit does.  Continuity of $w$ is then the
    ordinary continuity of a primitive, and $\Phi(\cdot,t_0)$ is continuous by
    \cref{lem:continuousOn-stateTransitionMatrix}. -/)]
theorem continuousOn_forcedResponse (hA : Continuous A) (hB : Continuous B) (hu : Continuous u)
    {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (x₀ : X → ℝ) :
    ContinuousOn (forcedResponse A B u t₀ x₀) (Set.uIcc t₀ t₁) := by
  have hg : ContinuousOn (fun τ => stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))
      (Set.uIcc t₀ t₁) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix_snd hA hA_le).prodMk
        (hB.matrix_mulVec hu).continuousOn)
  have hw : ContinuousOn
      (fun z => x₀ + ∫ τ in t₀..z, stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))
      (Set.uIcc t₀ t₁) :=
    continuousOn_const.add
      (intervalIntegral.continuousOn_primitive_interval (hg.integrableOn_compact isCompact_uIcc))
  have hprod : ContinuousOn
      (fun z => stateTransitionMatrix A z t₀ *ᵥ
        (x₀ + ∫ τ in t₀..z, stateTransitionMatrix A t₀ τ *ᵥ (B τ *ᵥ u τ))) (Set.uIcc t₀ t₁) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix hA hA_le).prodMk hw)
  exact hprod.congr fun z hz => variationOfConstants_eq_mulVec hA hB hu hA_le x₀ hz

/-- **Variation of constants, integral form.** The forced response satisfies the integral
equation `x(t) = x₀ + ∫ s in t₀..t, (A(s) x(s) + B(s) u(s))` on the whole closed segment.

This is the differential statement `hasDerivAt_variationOfConstants` upgraded to include the
endpoints, which the differential form cannot reach: its window has `t₀` as an endpoint for
every choice of `t₁`, so `t₀` is never interior to it. The integral form has no such
restriction, and `IsIntegralSolution.isIntegralCurveOn` converts it back into a derivative
statement valid at `t₀` itself. -/
@[blueprint "thm:isIntegralSolution-forcedResponse"
  (title := "Variation of constants, integral form")
  (statement := /-- The forced response (\cref{def:forcedResponse}) satisfies
    \[
      x(t) = x_0 + \int_{t_0}^{t}\bigl(A(s)x(s) + B(s)u(s)\bigr)\,\mathrm{d}s
    \]
    for every $t$ on the closed segment between $t_0$ and $t_1$.

    This is \cref{thm:hasDerivAt-variationOfConstants} upgraded to include the endpoints, which
    the differential form cannot reach: its window has $t_0$ as an endpoint for every choice of
    $t_1$, so $t_0$ is never interior to it. -/)
  (proof := /-- The fundamental theorem of calculus, applied to the derivative on the open
    interval (\cref{thm:hasDerivAt-variationOfConstants}) together with continuity on the
    closed one (\cref{lem:continuousOn-forcedResponse}), with
    \cref{lem:variationOfConstants-self} fixing the initial value. -/)]
theorem isIntegralSolution_forcedResponse (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (x₀ : X → ℝ) :
    IsIntegralSolution t₀ t₁ (forcedResponse A B u t₀ x₀) x₀
      (fun s v => A s *ᵥ v + B s *ᵥ u s) := by
  have hx_cont := continuousOn_forcedResponse hA hB hu hA_le x₀
  intro t ht
  have huIcc_sub : Set.uIcc t₀ t ⊆ Set.uIcc t₀ t₁ := Set.uIcc_subset_uIcc_left ht
  have huIoo_sub : Set.uIoo t₀ t ⊆ Set.uIoo t₀ t₁ := by
    rw [← Set.Ioo_min_max, ← Set.Ioo_min_max]
    exact Set.Ioo_subset_Ioo (le_min (min_le_left t₀ t₁) ht.1) (max_le (le_max_left t₀ t₁) ht.2)
  have hx_cont' : ContinuousOn (forcedResponse A B u t₀ x₀) (Set.uIcc t₀ t) :=
    hx_cont.mono huIcc_sub
  have hf'_cont : ContinuousOn
      (fun s => A s *ᵥ forcedResponse A B u t₀ x₀ s + B s *ᵥ u s) (Set.uIcc t₀ t) :=
    ((continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (hA.continuousOn.prodMk hx_cont')).add (hB.matrix_mulVec hu).continuousOn
  have hderiv : ∀ z ∈ Set.uIoo t₀ t,
      HasDerivWithinAt (forcedResponse A B u t₀ x₀)
        (A z *ᵥ forcedResponse A B u t₀ x₀ z + B z *ᵥ u z) (Set.Ioi z) z :=
    fun z hz =>
      (hasDerivAt_variationOfConstants hA hB hu hA_le (huIoo_sub hz) x₀).hasDerivWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right hx_cont' hderiv
    hf'_cont.intervalIntegrable
  rw [forcedResponse_self] at hFTC
  rw [hFTC]
  abel

/-! ## The solution as a trajectory of the system

`ContinuousLinearSystem` (`LinearSystems/DefsSystem.lean`) bundles the coefficient maps and
says what equation they satisfy. The results above are stated on `A` and `B` directly; this
section is the thin skin that restates them for the bundled object. -/

namespace ContinuousLinearSystem

omit [Fintype Y] in
/-- The forced response of a system is a trajectory of that system — at every time, with a
two-sided derivative.

Nothing is assumed beyond continuity of `A`, `B` and `u`, and that is global, so the formula
solves the state equation on the whole line: for `t < t₀` the forcing integral simply runs
backwards. Restricting to an interval — `Set.Ici t₀`, the ray the stability predicates quantify
over — is `IsTrajectory.isTrajectoryOn`.

Away from `t₀` this is `hasDerivAt_variationOfConstants` on a window with `t` in its interior,
which `uIoo` being unordered already supplies on both sides. At `t₀` itself no such window
exists, since the formula is anchored there; the two one-sided derivatives are taken from the
integral form on `[t₀, t₀+1]` and `[t₀-1, t₀]` and glued. -/
@[blueprint "thm:isTrajectory-forcedResponse"
  (title := "The forced response is a trajectory")
  (statement := /-- Let $s$ be a continuous-time linear system with continuous coefficients
    $A$ and $B$, and let $u$ be a continuous input.  Then the forced response
    (\cref{def:forcedResponse}) from any state $x_0$ at any time $t_0$ is a trajectory of $s$
    (\cref{def:ctsLinearSystem-isTrajectory}) — it satisfies the state equation at every
    $t \in \mathbb{R}$, with a two-sided derivative.

    Restriction to an interval, in particular to the ray $[t_0,\infty)$ that the stability
    predicates quantify over, is \cref{lem:ctsLinearSystem-isTrajectory-isTrajectoryOn}.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, Theorem 5.2.
  -/)
  (proof := /-- For $t \ne t_0$, apply \cref{thm:hasDerivAt-variationOfConstants} on a window
    having $t$ in its interior; since the window is unordered this covers $t < t_0$ as well as
    $t > t_0$, and continuity of $A$ supplies the bound on the compact segment.

    At $t = t_0$ no such window exists, because the formula is anchored there and $t_0$ is an
    endpoint of every window.  Instead take the integral form
    (\cref{thm:isIntegralSolution-forcedResponse}) on $[t_0, t_0+1]$ and on $[t_0-1, t_0]$; each
    yields a one-sided derivative at $t_0$ (\cref{lem:isIntegralSolution-isIntegralCurveOn}),
    and the two glue to a two-sided one. -/)]
theorem isTrajectory_forcedResponse (s : ContinuousLinearSystem X U Y ℝ) (hA : Continuous s.A)
    (hB : Continuous s.B) (hu : Continuous u) (t₀ : ℝ) (x₀ : X → ℝ) :
    s.IsTrajectory u (forcedResponse s.A s.B u t₀ x₀) := by
  -- A one-sided derivative at every point of any compact window, from the integral form.
  have key : ∀ t₁ : ℝ, ∀ t ∈ Set.uIcc t₀ t₁,
      HasDerivWithinAt (forcedResponse s.A s.B u t₀ x₀)
        (s.vectorField u t (forcedResponse s.A s.B u t₀ x₀ t)) (Set.uIcc t₀ t₁) t := by
    intro t₁ t ht
    obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn (f := s.A)
      (s := Set.uIcc t₀ t₁) hA.continuousOn
    have hFx : ContinuousOn
        (fun r => s.A r *ᵥ forcedResponse s.A s.B u t₀ x₀ r + s.B r *ᵥ u r)
        (Set.uIcc t₀ t₁) :=
      ((continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
        (hA.continuousOn.prodMk (continuousOn_forcedResponse hA hB hu hM x₀))).add
        (hB.matrix_mulVec hu).continuousOn
    exact (isIntegralSolution_forcedResponse hA hB hu hM x₀).isIntegralCurveOn hFx t ht
  intro t
  rcases lt_trichotomy t t₀ with hlt | heq | hgt
  · obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn (f := s.A)
      (s := Set.uIcc t₀ (t - 1)) hA.continuousOn
    have hmem : t ∈ Set.uIoo t₀ (t - 1) := by
      rw [← Set.Ioo_min_max, min_eq_right (by linarith), max_eq_left (by linarith)]
      exact ⟨by linarith, hlt⟩
    exact hasDerivAt_variationOfConstants hA hB hu hM hmem x₀
  · subst heq
    have hR : HasDerivWithinAt (forcedResponse s.A s.B u t x₀)
        (s.vectorField u t (forcedResponse s.A s.B u t x₀ t)) (Set.Ici t) t := by
      refine (key (t + 1) t Set.left_mem_uIcc).mono_of_mem_nhdsWithin ?_
      rw [Set.uIcc_of_le (by linarith : t ≤ t + 1)]
      exact mem_nhdsWithin.2
        ⟨Set.Iio (t + 1), isOpen_Iio, Set.mem_Iio.2 (by linarith),
          fun r hr => ⟨hr.2, hr.1.le⟩⟩
    have hL : HasDerivWithinAt (forcedResponse s.A s.B u t x₀)
        (s.vectorField u t (forcedResponse s.A s.B u t x₀ t)) (Set.Iic t) t := by
      refine (key (t - 1) t Set.left_mem_uIcc).mono_of_mem_nhdsWithin ?_
      rw [Set.uIcc_comm, Set.uIcc_of_le (by linarith : t - 1 ≤ t)]
      exact mem_nhdsWithin.2
        ⟨Set.Ioi (t - 1), isOpen_Ioi, Set.mem_Ioi.2 (by linarith),
          fun r hr => ⟨hr.1.le, hr.2⟩⟩
    have hunion := hR.union hL
    rw [Set.Ici_union_Iic] at hunion
    exact hunion.hasDerivAt Filter.univ_mem
  · obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn (f := s.A)
      (s := Set.uIcc t₀ (t + 1)) hA.continuousOn
    have hmem : t ∈ Set.uIoo t₀ (t + 1) := by
      rw [← Set.Ioo_min_max, min_eq_left (by linarith), max_eq_right (by linarith)]
      exact ⟨hgt, by linarith⟩
    exact hasDerivAt_variationOfConstants hA hB hu hM hmem x₀

end ContinuousLinearSystem

end LinearSystems

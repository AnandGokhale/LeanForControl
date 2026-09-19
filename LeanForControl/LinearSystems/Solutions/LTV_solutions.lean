import LeanForControl.Analysis.Continuity
import LeanForControl.LinearSystems.Solutions.DefsLTV_solutions
import LeanForControl.ODEs.ODE_properties
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Architect

/-!
# Continuous-time solutions: the Peano-Baker series

Theorems about `peanoBakerTerm` and `stateTransitionMatrix` (from `DefsLTV_solutions.lean`),
building up to Theorem 5.1 (Peano-Baker series): the state transition matrix solves the
matrix ODE `Φ̇(t, t₀) = A(t) Φ(t, t₀)`, `Φ(t₀, t₀) = I`, and `x(t) := Φ(t, t₀) *ᵥ x₀` is the
unique solution of `ẋ = A(t) x`, `x(t₀) = x₀`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5.
-/

namespace LinearSystems

open scoped Matrix.Norms.Operator Nat
open Matrix MeasureTheory intervalIntegral

variable {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ}

/-- Each term of the Peano-Baker series is continuous in `t`, for `A` continuous.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "lem:continuous-peanoBakerTerm"
  (statement := /-- Each term $P_k(t,t_0)$ of the Peano--Baker series is continuous in $t$,
    for $A$ continuous. -/)
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
  (statement := /-- If $\|A(s)\| \le M$ for all $s$ between $t_0$ and $t_1$, then
    \[
      \|P_k(t,t_0)\| \;\le\; \|I\| \cdot \frac{(M|t-t_0|)^k}{k!}
      \qquad \text{for every } t \text{ between } t_0 \text{ and } t_1.
    \] -/)
  (proof := /-- Induction on $k$: bound the integrand $A(s) P_k(s,t_0)$ pointwise on the segment
    between $t_0$ and $t$, using submultiplicativity of the matrix norm and the induction
    hypothesis. Split on whether $t_0 \le t$ or $t \le t_0$ and integrate the majorant via the
    power rule, flipping the integral's orientation (`intervalIntegral.integral_symm`) in the
    backward case. -/)]
theorem norm_peanoBakerTerm_le {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) (k : ℕ) :
    ∀ t ∈ Set.uIcc t₀ t₁,
      ‖peanoBakerTerm A k t t₀‖ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ * (M * |t - t₀|) ^ k / (k)! := by
  induction k with
  | zero => intro t _; simp [peanoBakerTerm]
  | succ k ih =>
    intro t ht
    set C1 : ℝ := ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖
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

/-- `norm_peanoBakerTerm_le`, uniformized to the *right endpoint* `b` rather than the point `t`
itself. Needed whenever a `t`-independent bound is required — the Weierstrass `M`-test, for
both continuity and differentiability of the series, needs one bound per term `k` valid across
the whole interval, not a different (tighter) bound at each point.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "lem:norm-peanoBakerTerm-le-of-mem"
  (statement := /-- The bound in \cref{lem:norm-peanoBakerTerm-le}, uniformized to the worst
    case $t = t_1$:
    \[
      \|P_k(t,t_0)\| \;\le\; \|I\| \cdot \frac{(M|t_1-t_0|)^k}{k!}
      \qquad \text{for every } t \text{ between } t_0 \text{ and } t_1.
    \] -/)
  (proof := /-- Monotonicity of $t \mapsto (M|t-t_0|)^k$ on the segment between $t_0$ and $t_1$,
    combined with \cref{lem:norm-peanoBakerTerm-le}. -/)]
theorem norm_peanoBakerTerm_le_of_mem {t₀ t₁ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M)
    (k : ℕ) :
    ∀ t ∈ Set.uIcc t₀ t₁,
      ‖peanoBakerTerm A k t t₀‖ ≤
        ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ * (M * |t₁ - t₀|) ^ k / (k)! := by
  intro t ht
  have hM_nonneg : 0 ≤ M := (norm_nonneg (A t₀)).trans (hA_le t₀ Set.left_mem_uIcc)
  have hC1_nonneg : 0 ≤ ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ := norm_nonneg _
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
  (statement := /-- The Peano--Baker series $\sum_{k=0}^\infty P_k(t,t_0)$ converges absolutely,
    for $A$ bounded between $t_0$ and $t$ (in either order). -/)
  (proof := /-- Compare against the exponential series $\sum_k (M|t-t_0|)^k/k!$ via
    \cref{lem:norm-peanoBakerTerm-le} and the comparison test. -/)]
theorem summable_peanoBakerTerm {t t₀ M : ℝ} (hA_le : ∀ s ∈ Set.uIcc t₀ t, ‖A s‖ ≤ M) :
    Summable (fun k => peanoBakerTerm A k t t₀) :=
  Summable.of_norm_bounded
    (g := fun k => ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ * (M * |t - t₀|) ^ k / (k)!)
    (by
      have hexp : Summable (fun k => (M * |t - t₀|) ^ k / (k)!) :=
        Real.summable_pow_div_factorial (M * |t - t₀|)
      simpa [mul_div_assoc] using hexp.mul_left ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖)
    (fun k => norm_peanoBakerTerm_le hA_le k t Set.right_mem_uIcc)

/-- The state transition matrix is continuous on the segment between `t₀` and `t₁` (including
both endpoints), for `A` continuous and bounded by `M` there. This is needed alongside
`hasDerivAt_stateTransitionMatrix` (valid only on the open interval strictly between `t₀` and
`t₁`) for arguments — like uniqueness of the solution — that need continuity *at* `t₀` itself.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "lem:continuousOn-stateTransitionMatrix"
  (statement := /-- $\Phi(\cdot, t_0)$ is continuous on the segment between $t_0$ and $t_1$
    (including both endpoints), for $A$ continuous and bounded by $M$ there. -/)
  (proof := /-- Each term $P_k(\cdot,t_0)$ is continuous (\cref{lem:continuous-peanoBakerTerm})
    with a summable, point-independent bound (\cref{lem:norm-peanoBakerTerm-le-of-mem}); apply
    the Weierstrass $M$-test for continuity of a series. -/)]
theorem continuousOn_stateTransitionMatrix (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) :
    ContinuousOn (fun t => stateTransitionMatrix A t t₀) (Set.uIcc t₀ t₁) := by
  have hu_summable :
      Summable (fun k => ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ * (M * |t₁ - t₀|) ^ k / (k)!) := by
    have hexp := Real.summable_pow_div_factorial (M * |t₁ - t₀|)
    simpa [mul_div_assoc] using hexp.mul_left ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖
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
  (statement := /-- The state transition matrix solves the matrix ODE
    \[
      \dot\Phi(t,t_0) = A(t)\,\Phi(t,t_0)
    \]
    for $t$ strictly between $t_0$ and $t_1$. -/)
  (proof := /-- Differentiate the Peano--Baker series term by term, using
    \cref{lem:norm-peanoBakerTerm-le} as the uniform bound needed for term-by-term
    differentiation of a series. The $k=0$ term is constant, so peel it off and match the
    shifted series' derivative against $A(t)\Phi(t,t_0)$ using linearity of the sum under
    left multiplication by $A(t)$. -/)]
theorem hasDerivAt_stateTransitionMatrix (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) {t : ℝ} (ht : t ∈ Set.uIoo t₀ t₁) :
    HasDerivAt (fun z => stateTransitionMatrix A z t₀) (A t * stateTransitionMatrix A t t₀) t := by
  set C1 : ℝ := ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖
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
      HasDerivAt (fun z => (1 : Matrix (Fin n) (Fin n) ℝ) + ∑' k, peanoBakerTerm A (k + 1) z t₀)
        (A t * stateTransitionMatrix A t t₀) t := by
    have := (hasDerivAt_const t (1 : Matrix (Fin n) (Fin n) ℝ)).add hshifted_deriv
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
  (statement := /-- $\Phi(t_0,t_0) = I$. -/)
  (proof := /-- Every term of the Peano--Baker series beyond $k=0$ integrates over the
    degenerate interval $[t_0,t_0]$ and vanishes. -/)]
theorem stateTransitionMatrix_self (t₀ : ℝ) :
    stateTransitionMatrix A t₀ t₀ = 1 := by
  have hterm : ∀ k, peanoBakerTerm A k t₀ t₀ =
      if k = 0 then (1 : Matrix (Fin n) (Fin n) ℝ) else 0 := by
    intro k
    cases k with
    | zero => simp [peanoBakerTerm]
    | succ k => simp [peanoBakerTerm, intervalIntegral.integral_same]
  rw [stateTransitionMatrix, tsum_congr hterm,
    tsum_ite_eq 0 (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ))]

/-- **Theorem 5.1 (Peano-Baker series), existence half.** `x(t) := Φ(t, t₀) *ᵥ x₀` solves the
initial value problem `ẋ = A(t) x` — this is `hasDerivAt_stateTransitionMatrix` pushed through
the fixed linear map `M ↦ M *ᵥ x₀` (continuous, since the domain is finite-dimensional).

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Theorem 5.1. -/
@[blueprint "thm:hasDerivAt-stateTransitionMatrix-mulVec"
  (statement := /-- \textbf{Theorem 5.1} (Peano--Baker series, existence half).
    $x(t) := \Phi(t,t_0)\, x_0$ solves
    \[
      \dot x(t) = A(t)\, x(t).
    \] -/)
  (proof := /-- Push \cref{thm:hasDerivAt-stateTransitionMatrix} through the fixed linear map
    $M \mapsto M x_0$ (continuous, since the domain is finite-dimensional). -/)]
theorem hasDerivAt_stateTransitionMatrix_mulVec (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) {t : ℝ} (ht : t ∈ Set.uIoo t₀ t₁)
    (x₀ : Fin n → ℝ) :
    HasDerivAt (fun z => stateTransitionMatrix A z t₀ *ᵥ x₀)
      (A t *ᵥ (stateTransitionMatrix A t t₀ *ᵥ x₀)) t := by
  -- The fixed linear map `M ↦ M *ᵥ x₀`, as a continuous linear map (automatic: the domain
  -- `Matrix (Fin n) (Fin n) ℝ` is finite-dimensional).
  set L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ) :=
    LinearMap.toContinuousLinearMap ((Matrix.mulVecBilin ℝ ℝ).flip x₀) with hL
  have hL_apply : ∀ M' : Matrix (Fin n) (Fin n) ℝ, L M' = M' *ᵥ x₀ := fun M' => rfl
  have hderiv := (L.hasFDerivAt (x := stateTransitionMatrix A t t₀)).comp_hasDerivAt t
    (hasDerivAt_stateTransitionMatrix hA hA_le ht)
  simpa [hL_apply, Matrix.mulVec_mulVec] using hderiv

/-- The matrix analogue of `hasDerivAt_stateTransitionMatrix_mulVec`: for a *constant* matrix
`C`, `Y(t) := Φ(t, t₀) * C` solves the matrix ODE `Ẏ = A(t) Y`. Needed for the semigroup
property (P5.3) and matrix-level uniqueness, where the "initial value" is a matrix rather than
a vector.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "thm:hasDerivAt-stateTransitionMatrix-mul"
  (statement := /-- For a constant matrix $C$, $Y(t) := \Phi(t,t_0)\, C$ solves
    \[
      \dot Y(t) = A(t)\, Y(t).
    \] -/)
  (proof := /-- Right-multiply \cref{thm:hasDerivAt-stateTransitionMatrix} by the constant $C$
    (`HasDerivAt.mul_const`), then reassociate. -/)]
theorem hasDerivAt_stateTransitionMatrix_mul (hA : Continuous A) {t₀ t₁ M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t₁, ‖A s‖ ≤ M) {t : ℝ} (ht : t ∈ Set.uIoo t₀ t₁)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun z => stateTransitionMatrix A z t₀ * C)
      (A t * (stateTransitionMatrix A t t₀ * C)) t := by
  have hderiv := (hasDerivAt_stateTransitionMatrix hA hA_le ht).mul_const C
  rwa [mul_assoc] at hderiv

/-- The matrix analogue of `isIntegralSolution_stateTransitionMatrix_mulVec`: for a constant
matrix `C`, `Y(t) := Φ(t, t₀) * C` is an integral solution of `Ẏ = A(t) Y` on `[t₀, b]` with
initial value `C`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "lem:isIntegralSolution-stateTransitionMatrix-mul"
  (statement := /-- For a constant matrix $C$, $Y(t) := \Phi(t,t_0)\, C$ satisfies the integral
    equation
    \[
      Y(t) = C + \int_{t_0}^{t} A(s)\, Y(s)\,\mathrm{d}s \qquad \forall\, t \in [t_0, b].
    \] -/)
  (proof := /-- The fundamental theorem of calculus applied to
    \cref{thm:hasDerivAt-stateTransitionMatrix-mul}, using $\Phi(t_0,t_0) = I$
    (\cref{thm:stateTransitionMatrix-self}) to fix the initial value. -/)]
theorem isIntegralSolution_stateTransitionMatrix_mul (hA : Continuous A) {b t₀ M : ℝ}
    (hb : t₀ < b) (hA_le : ∀ s ∈ Set.Icc t₀ b, ‖A s‖ ≤ M) (C : Matrix (Fin n) (Fin n) ℝ) :
    IsIntegralSolution t₀ b (fun t => stateTransitionMatrix A t t₀ * C) C
      (fun s Y => A s * Y) := by
  have hx_cont : ContinuousOn (fun t => stateTransitionMatrix A t t₀ * C) (Set.Icc t₀ b) :=
    (continuous_fst.mul continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix hA hb.le hA_le).prodMk continuousOn_const)
  intro t ht
  have hx_cont' : ContinuousOn (fun s => stateTransitionMatrix A s t₀ * C) (Set.Icc t₀ t) :=
    hx_cont.mono (Set.Icc_subset_Icc_right ht.2)
  have hf'_cont : ContinuousOn (fun s => A s * (stateTransitionMatrix A s t₀ * C))
      (Set.Icc t₀ t) :=
    (continuous_fst.mul continuous_snd).comp_continuousOn (hA.continuousOn.prodMk hx_cont')
  have hderiv : ∀ z ∈ Set.Ioo t₀ t,
      HasDerivAt (fun z => stateTransitionMatrix A z t₀ * C)
        (A z * (stateTransitionMatrix A z t₀ * C)) z :=
    fun z hz => hasDerivAt_stateTransitionMatrix_mul hA hb hA_le ⟨hz.1, hz.2.trans_le ht.2⟩ C
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hx_cont' hderiv
    (hf'_cont.intervalIntegrable_of_Icc ht.1)
  rw [stateTransitionMatrix_self, Matrix.one_mul] at hFTC
  rw [hFTC]
  abel

/-- `x(t) := Φ(t, t₀) *ᵥ x₀` is an *integral solution* (`IsIntegralSolution`, from
`ODEs/ODE_properties.lean`) of `ẋ = A(t) x` on `[t₀, b]` — the integral-equation reformulation
of `hasDerivAt_stateTransitionMatrix_mulVec`, via the fundamental theorem of calculus. This is
what lets uniqueness reuse `continuous_dependence_ODE` (Theorem 3.4), which is stated in terms
of `IsIntegralSolution` rather than `HasDerivAt`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "lem:isIntegralSolution-stateTransitionMatrix-mulVec"
  (statement := /-- $x(t) := \Phi(t,t_0)\, x_0$ satisfies the integral equation
    \[
      x(t) = x_0 + \int_{t_0}^{t} A(s)\, x(s)\,\mathrm{d}s \qquad \forall\, t \in [t_0, b].
    \] -/)
  (proof := /-- The fundamental theorem of calculus applied to
    \cref{thm:hasDerivAt-stateTransitionMatrix-mulVec}, using $\Phi(t_0,t_0) = I$
    (\cref{thm:stateTransitionMatrix-self}) to fix the initial value. -/)]
theorem isIntegralSolution_stateTransitionMatrix_mulVec (hA : Continuous A) {b t₀ M : ℝ}
    (hb : t₀ < b) (hA_le : ∀ s ∈ Set.Icc t₀ b, ‖A s‖ ≤ M) (x₀ : Fin n → ℝ) :
    IsIntegralSolution t₀ b (fun t => stateTransitionMatrix A t t₀ *ᵥ x₀) x₀
      (fun s v => A s *ᵥ v) := by
  have hx_cont : ContinuousOn (fun t => stateTransitionMatrix A t t₀ *ᵥ x₀) (Set.Icc t₀ b) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix hA hb.le hA_le).prodMk continuousOn_const)
  intro t ht
  have hx_cont' : ContinuousOn (fun s => stateTransitionMatrix A s t₀ *ᵥ x₀) (Set.Icc t₀ t) :=
    hx_cont.mono (Set.Icc_subset_Icc_right ht.2)
  have hf'_cont : ContinuousOn (fun s => A s *ᵥ (stateTransitionMatrix A s t₀ *ᵥ x₀))
      (Set.Icc t₀ t) :=
    (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (hA.continuousOn.prodMk hx_cont')
  have hderiv : ∀ z ∈ Set.Ioo t₀ t,
      HasDerivAt (fun z => stateTransitionMatrix A z t₀ *ᵥ x₀)
        (A z *ᵥ (stateTransitionMatrix A z t₀ *ᵥ x₀)) z :=
    fun z hz => hasDerivAt_stateTransitionMatrix_mulVec hA hb hA_le ⟨hz.1, hz.2.trans_le ht.2⟩ x₀
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hx_cont' hderiv
    (hf'_cont.intervalIntegrable_of_Icc ht.1)
  rw [stateTransitionMatrix_self, Matrix.one_mulVec] at hFTC
  rw [hFTC]
  abel

/-- **Theorem 5.1 (Peano-Baker series), uniqueness half.** Any integral solution `z` of
`ẋ = A(t) x`, `x(t₀) = x₀` on `[t₀, b]` coincides with `x(t) := Φ(t, t₀) *ᵥ x₀`.

Proof: apply `continuous_dependence_ODE` (Theorem 3.4) with zero perturbation `g := 0`. Since
both solutions share the initial value `x₀` and the perturbation bound is `μ = 0`, the bound it
gives collapses to `‖x t - z t‖ ≤ 0`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Theorem 5.1. -/
@[blueprint "thm:stateTransitionMatrix-mulVec-unique"
  (statement := /-- \textbf{Theorem 5.1} (Peano--Baker series, uniqueness half). Any solution
    $z$ of $\dot x = A(t)\, x$, $x(t_0) = x_0$ on $[t_0,b]$ coincides with
    $x(t) := \Phi(t,t_0)\, x_0$. -/)
  (proof := /-- Apply the continuous-dependence bound of Theorem 3.4 with zero perturbation:
    since both solutions share the initial value $x_0$, the resulting bound on
    $\|x(t) - z(t)\|$ collapses to $0$. -/)]
theorem stateTransitionMatrix_mulVec_unique (hA : Continuous A) {b t₀ M : ℝ} (hb : t₀ < b)
    (hA_le : ∀ s ∈ Set.Icc t₀ b, ‖A s‖ ≤ M) (x₀ : Fin n → ℝ)
    {z : ℝ → Fin n → ℝ} (hz : IsIntegralSolution t₀ b z x₀ (fun s v => A s *ᵥ v))
    (hz_cont : ContinuousOn z (Set.Icc t₀ b)) :
    ∀ t ∈ Set.Icc t₀ b, z t = stateTransitionMatrix A t t₀ *ᵥ x₀ := by
  -- A fixed Lipschitz constant for `v ↦ A t *ᵥ v`, valid for every `t ∈ [t₀, b]`.
  set L : ℝ := max M 1 with hL_def
  have hL_pos : (0 : ℝ) < L := lt_of_lt_of_le one_pos (le_max_right M 1)
  have hM_le_L : M ≤ L := le_max_left M 1
  have hLip : ∀ t ∈ Set.Icc t₀ b,
      LipschitzWith ⟨L, hL_pos.le⟩ (fun v : Fin n → ℝ => A t *ᵥ v) := by
    intro t ht
    refine LipschitzWith.of_dist_le_mul fun v₁ v₂ => ?_
    have hAt : ‖A t‖ ≤ L := (hA_le t ht).trans hM_le_L
    calc dist (A t *ᵥ v₁) (A t *ᵥ v₂) = ‖A t *ᵥ v₁ - A t *ᵥ v₂‖ := dist_eq_norm _ _
      _ = ‖A t *ᵥ (v₁ - v₂)‖ := by rw [Matrix.mulVec_sub]
      _ ≤ ‖A t‖ * ‖v₁ - v₂‖ := Matrix.linfty_opNorm_mulVec _ _
      _ ≤ L * dist v₁ v₂ := by rw [dist_eq_norm]; gcongr
  -- Feed `continuous_dependence_ODE` (Theorem 3.4) the zero perturbation `g := 0`.
  have hbound := continuous_dependence_ODE (g := fun _ _ => (0 : Fin n → ℝ)) (μ := 0) hb.le hL_pos
    (isIntegralSolution_stateTransitionMatrix_mulVec hA hb hA_le x₀) (by simpa using hz)
    ((continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix hA hb.le hA_le).prodMk continuousOn_const))
    hz_cont ((hA.comp continuous_fst).matrix_mulVec continuous_snd) intervalIntegrable_const
    hLip (fun _ _ _ => by simp)
  intro t ht
  have h0 : ‖stateTransitionMatrix A t t₀ *ᵥ x₀ - z t‖ ≤ 0 := by simpa using hbound t ht
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp h0)).symm

/-- **P5.2.** For a fixed standard basis vector `e_i`, `stateTransitionMatrix_mulVec_unique`
specializes to: any integral solution `z` of `ẋ = A(t) x`, `x(t₀) = e_i` on `[t₀, b]` coincides
with the `i`-th column of `Φ(t, t₀)` — via `Φ(t, t₀) *ᵥ e_i = (Φ(t, t₀)).col i`
(`Matrix.mulVec_single_one`).

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.2. -/
@[blueprint "thm:stateTransitionMatrix-col-unique"
  (statement := /-- \textbf{P5.2.} For every fixed $i$, the $i$-th column of $\Phi(t,t_0)$ is
    the unique solution of $\dot x = A(t)\, x$, $x(t_0) = e_i$, where $e_i$ is the $i$-th
    standard basis vector. -/)
  (proof := /-- Restatement of \cref{thm:stateTransitionMatrix-mulVec-unique} at
    $x_0 := e_i$, using $\Phi(t,t_0)\, e_i = (\Phi(t,t_0))_{\cdot,i}$
    (`Matrix.mulVec_single_one`). -/)]
theorem stateTransitionMatrix_col_unique (hA : Continuous A) {b t₀ M : ℝ} (hb : t₀ < b)
    (hA_le : ∀ s ∈ Set.Icc t₀ b, ‖A s‖ ≤ M) (i : Fin n)
    {z : ℝ → Fin n → ℝ} (hz : IsIntegralSolution t₀ b z (Pi.single i 1) (fun s v => A s *ᵥ v))
    (hz_cont : ContinuousOn z (Set.Icc t₀ b)) :
    ∀ t ∈ Set.Icc t₀ b, z t = (stateTransitionMatrix A t t₀).col i := by
  intro t ht
  rw [← Matrix.mulVec_single_one]
  exact stateTransitionMatrix_mulVec_unique hA hb hA_le (Pi.single i 1) hz hz_cont t ht

/-- The matrix analogue of `stateTransitionMatrix_mulVec_unique`: any integral solution `Y` of
`Ẏ = A(t) Y`, `Y(t₀) = C` on `[t₀, b]` coincides with `Φ(t, t₀) * C`. Unlike the vector case,
the Lipschitz bound on `M ↦ A t * M` comes from submultiplicativity of the operator norm
(`norm_mul_le`) rather than `Matrix.linfty_opNorm_mulVec`, but the rest of the argument —
feeding `continuous_dependence_ODE` (Theorem 3.4) the zero perturbation `g := 0` — is identical.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "thm:stateTransitionMatrix-mul-unique"
  (statement := /-- Any solution $Y$ of $\dot Y = A(t)\, Y$, $Y(t_0) = C$ on $[t_0,b]$
    coincides with $\Phi(t,t_0)\, C$. -/)
  (proof := /-- Apply the continuous-dependence bound of Theorem 3.4 with zero perturbation:
    since both solutions share the initial value $C$, the resulting bound on
    $\|Y(t) - Z(t)\|$ collapses to $0$. -/)]
theorem stateTransitionMatrix_mul_unique (hA : Continuous A) {b t₀ M : ℝ} (hb : t₀ < b)
    (hA_le : ∀ s ∈ Set.Icc t₀ b, ‖A s‖ ≤ M) (C : Matrix (Fin n) (Fin n) ℝ)
    {Y : ℝ → Matrix (Fin n) (Fin n) ℝ} (hY : IsIntegralSolution t₀ b Y C (fun s M' => A s * M'))
    (hY_cont : ContinuousOn Y (Set.Icc t₀ b)) :
    ∀ t ∈ Set.Icc t₀ b, Y t = stateTransitionMatrix A t t₀ * C := by
  -- A fixed Lipschitz constant for `M' ↦ A t * M'`, valid for every `t ∈ [t₀, b]`.
  set L : ℝ := max M 1 with hL_def
  have hL_pos : (0 : ℝ) < L := lt_of_lt_of_le one_pos (le_max_right M 1)
  have hM_le_L : M ≤ L := le_max_left M 1
  have hLip : ∀ t ∈ Set.Icc t₀ b,
      LipschitzWith ⟨L, hL_pos.le⟩ (fun M' : Matrix (Fin n) (Fin n) ℝ => A t * M') := by
    intro t ht
    refine LipschitzWith.of_dist_le_mul fun M₁ M₂ => ?_
    have hAt : ‖A t‖ ≤ L := (hA_le t ht).trans hM_le_L
    calc dist (A t * M₁) (A t * M₂) = ‖A t * M₁ - A t * M₂‖ := dist_eq_norm _ _
      _ = ‖A t * (M₁ - M₂)‖ := by rw [mul_sub]
      _ ≤ ‖A t‖ * ‖M₁ - M₂‖ := norm_mul_le _ _
      _ ≤ L * dist M₁ M₂ := by rw [dist_eq_norm]; gcongr
  -- Feed `continuous_dependence_ODE` (Theorem 3.4) the zero perturbation `g := 0`.
  have hbound := continuous_dependence_ODE
    (g := fun _ _ => (0 : Matrix (Fin n) (Fin n) ℝ)) (μ := 0) hb.le hL_pos
    (isIntegralSolution_stateTransitionMatrix_mul hA hb hA_le C) (by simpa using hY)
    ((continuous_fst.mul continuous_snd).comp_continuousOn
      ((continuousOn_stateTransitionMatrix hA hb.le hA_le).prodMk continuousOn_const))
    hY_cont ((hA.comp continuous_fst).mul continuous_snd) intervalIntegrable_const
    hLip (fun _ _ _ => by simp)
  intro t ht
  have h0 : ‖stateTransitionMatrix A t t₀ * C - Y t‖ ≤ 0 := by simpa using hbound t ht
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp h0)).symm

/-- **P5.3 (semigroup property).** `Φ(t,s) * Φ(s,τ) = Φ(t,τ)` for `τ ≤ s < t ≤ b`, with `A`
continuous and bounded by `M` on `[τ, b]`.

Proof: `Φ(·,τ)`, re-anchored at `s` (`IsIntegralSolution.reanchor`), is an integral solution of
the matrix ODE on `[s, b]` with initial value `Φ(s,τ)`, hence coincides with `Φ(·,s) * Φ(s,τ)`
there by `stateTransitionMatrix_mul_unique`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.3. -/
@[blueprint "thm:stateTransitionMatrix-semigroup"
  (statement := /-- \textbf{P5.3} (semigroup property). For every $\tau \le s < t \le b$,
    \[
      \Phi(t,s)\,\Phi(s,\tau) = \Phi(t,\tau).
    \] -/)
  (proof := /-- $\Phi(\cdot,\tau)$, re-anchored at $s$, is an integral solution of the matrix
    ODE on $[s,b]$ with initial value $\Phi(s,\tau)$, hence coincides with
    $\Phi(\cdot,s)\,\Phi(s,\tau)$ there by \cref{thm:stateTransitionMatrix-mul-unique}. -/)]
theorem stateTransitionMatrix_semigroup (hA : Continuous A) {b τ s t M : ℝ} (hτs : τ ≤ s)
    (hst : s < t) (htb : t ≤ b) (hA_le : ∀ r ∈ Set.Icc τ b, ‖A r‖ ≤ M) :
    stateTransitionMatrix A t s * stateTransitionMatrix A s τ = stateTransitionMatrix A t τ := by
  have hτb : τ < b := (hτs.trans_lt hst).trans_le htb
  have hsb : s < b := hst.trans_le htb
  have hA_le' : ∀ r ∈ Set.Icc s b, ‖A r‖ ≤ M :=
    fun r hr => hA_le r (Set.Icc_subset_Icc hτs le_rfl hr)
  have hF_cont : Continuous (fun p : ℝ × Matrix (Fin n) (Fin n) ℝ => A p.1 * p.2) :=
    (hA.comp continuous_fst).mul continuous_snd
  have hbase : IsIntegralSolution τ b (fun t => stateTransitionMatrix A t τ)
      (1 : Matrix (Fin n) (Fin n) ℝ) (fun r Y => A r * Y) := by
    simpa using isIntegralSolution_stateTransitionMatrix_mul hA hτb hA_le 1
  have hre := hbase.reanchor hF_cont
    (continuousOn_stateTransitionMatrix hA hτb.le hA_le) ⟨hτs, hsb.le⟩
  have hunique := stateTransitionMatrix_mul_unique hA hsb hA_le' (stateTransitionMatrix A s τ) hre
    ((continuousOn_stateTransitionMatrix hA hτb.le hA_le).mono (Set.Icc_subset_Icc hτs le_rfl))
    t ⟨hst.le, htb⟩
  exact hunique.symm

end LinearSystems

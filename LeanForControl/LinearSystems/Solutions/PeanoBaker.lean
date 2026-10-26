import LeanForControl.LinearSystems.Solutions.DefsCtsLTV
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Architect

/-!
# The Peano-Baker series in a Banach algebra

Theorems about `peanoBakerTerm` and `stateTransitionMatrix` (from `DefsCtsLTV.lean`) for a
continuous coefficient `A : ℝ → 𝔸` in a real Banach algebra `𝔸`: the factorial bound on the
terms, summability, continuity, and the derivative `Φ̇(t, t₀) = A(t) Φ(t, t₀)` with
`Φ(t₀, t₀) = 1`.

The only structure used is the algebra's: products, sums and integrals, a submultiplicative
norm, and completeness. Matrices under any submultiplicative norm and the continuous linear
operators `E →L[ℝ] E` on a Banach space are both instances.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5.
-/

namespace LinearSystems

open scoped Nat
open MeasureTheory intervalIntegral

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] {A : ℝ → 𝔸}

omit [CompleteSpace 𝔸] in
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

/-- **Power rule, shifted to the base point.** `∫ s in a..b, (s - a)^k = (b - a)^(k+1) / (k+1)`,
via the shift `s ↦ s - a`. This is the integral behind the factorial `1 / k!` in every term of
the Peano-Baker series: here in `norm_peanoBakerTerm_le`, and in the closed form
`peanoBakerTerm_const` for constant `A` (`CtsLTI.lean`). -/
theorem integral_sub_pow (k : ℕ) (a b : ℝ) :
    ∫ s in a..b, (s - a) ^ k = (b - a) ^ (k + 1) / (k + 1) := by
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ k) a]
  simp [integral_pow]

/-- The integrated majorant of the induction step in `norm_peanoBakerTerm_le`: integrating the
`k`-th factorial bound `M * (C * (M * (s - a))^k / k!)` from `a` to `b` yields the `(k+1)`-st
bound `C * (M * (b - a))^(k+1) / (k+1)!`. -/
private lemma integral_peanoBakerMajorant (M C : ℝ) (k : ℕ) (a b : ℝ) :
    ∫ s in a..b, M * (C * (M * (s - a)) ^ k / (k)!) =
      C * (M * (b - a)) ^ (k + 1) / (k + 1)! := by
  -- Pull the constant `M * C * M^k / k!` out of the integral, then apply the power rule.
  have hfactor : ∀ s : ℝ,
      M * (C * (M * (s - a)) ^ k / (k)!) = (M * C * M ^ k / (k)!) * (s - a) ^ k := by
    intro s
    rw [mul_pow]
    ring
  have hk_fac_ne : ((k)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  simp_rw [hfactor, intervalIntegral.integral_const_mul, integral_sub_pow]
  rw [mul_pow, Nat.factorial_succ]
  push_cast
  field_simp
  ring

omit [CompleteSpace 𝔸] in
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
      ‖peanoBakerTerm A k t t₀‖ ≤ ‖(1 : 𝔸)‖ * (M * |t - t₀|) ^ k / (k)! := by
  induction k with
  | zero => intro t _; simp [peanoBakerTerm]
  | succ k ih =>
    intro t ht
    set C1 : ℝ := ‖(1 : 𝔸)‖
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
      rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      exact hintegral_le.trans_eq (integral_peanoBakerMajorant M C1 k t₀ t)
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
      -- Mirror `s ↦ t₀ - s` to land in the forward majorant integral, anchored at `0`.
      have hmajorant : ∫ s in t..t₀, M * (C1 * (M * (t₀ - s)) ^ k / (k)!) =
          C1 * (M * (t₀ - t)) ^ (k + 1) / (k + 1)! := by
        rw [intervalIntegral.integral_comp_sub_left
          (fun x : ℝ => M * (C1 * (M * x) ^ k / (k)!)) t₀, sub_self]
        simpa only [sub_zero] using integral_peanoBakerMajorant M C1 k 0 (t₀ - t)
      exact hintegral_le.trans_eq hmajorant

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
    (g := fun k => ‖(1 : 𝔸)‖ * (M * |t - t₀|) ^ k / (k)!)
    (by
      have hexp : Summable (fun k => (M * |t - t₀|) ^ k / (k)!) :=
        Real.summable_pow_div_factorial (M * |t - t₀|)
      simpa [mul_div_assoc] using hexp.mul_left ‖(1 : 𝔸)‖)
    (fun k => norm_peanoBakerTerm_le hA_le k t Set.right_mem_uIcc)

/-- The state transition matrix solves `Φ̇(t, t₀) = A(t) Φ(t, t₀)`, at every time `t`, for `A`
continuous. This is the mathematical content of Theorem 5.1: the factorial bound and
summability exist only to make differentiating the series term by term legitimate.

Proof outline:
1. On the ball of radius `r := |t - t₀| + 1` about `t₀`, `A` is bounded by some `M`
   (compactness of the closed ball), so the factorial bound gives one summable bound per term,
   valid across the whole ball.
2. Differentiate the *shifted* series `∑' k, peanoBakerTerm A (k+1) z t₀` term by term
   (`hasDerivAt_tsum_of_isPreconnected`); each term is an integral with variable upper limit,
   whose derivative is its integrand.
3. `Φ(z, t₀) = 1 + ∑' k, peanoBakerTerm A (k+1) z t₀` on the ball, and
   `∑' k, A t * peanoBakerTerm A k t t₀ = A t * Φ(t, t₀)` by linearity of `tsum`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "thm:hasDerivAt-stateTransitionMatrix"
  (title := "The state transition matrix solves the matrix ODE")
  (statement := /-- For $A$ continuous, the state transition matrix solves
    \[
      \dot\Phi(t,t_0) = A(t)\,\Phi(t,t_0)
    \]
    at every time $t$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5.
  -/)
  (proof := /-- On a ball about $t_0$ containing $t$, $A$ is bounded, so
    \cref{lem:norm-peanoBakerTerm-le} gives one summable bound per term across the ball.
    Differentiate the Peano--Baker series term by term there. The $k=0$ term is constant, so
    peel it off and match the shifted series' derivative against $A(t)\Phi(t,t_0)$ using
    linearity of the sum under left multiplication by $A(t)$. -/)]
theorem hasDerivAt_stateTransitionMatrix (hA : Continuous A) (t t₀ : ℝ) :
    HasDerivAt (fun z => stateTransitionMatrix A z t₀) (A t * stateTransitionMatrix A t t₀) t := by
  set r := |t - t₀| + 1
  obtain ⟨M, hM⟩ := (isCompact_closedBall t₀ r).exists_bound_of_continuousOn hA.continuousOn
  -- `A` is bounded by `M` between `t₀` and any point of the ball.
  have hA_le : ∀ z ∈ Metric.ball t₀ r, ∀ s ∈ Set.uIcc t₀ z, ‖A s‖ ≤ M := fun z hz s hs =>
    hM s ((Set.abs_sub_left_of_mem_uIcc hs).trans (Metric.mem_ball.1 hz).le)
  have hM_nonneg : 0 ≤ M :=
    (norm_nonneg _).trans (hM t₀ (Metric.mem_closedBall_self (by positivity)))
  have hderiv : ∀ (k : ℕ) (z : ℝ),
      HasDerivAt (fun z => peanoBakerTerm A (k + 1) z t₀) (A z * peanoBakerTerm A k z t₀) z := by
    intro k z
    have hF : Continuous (fun s => A s * peanoBakerTerm A k s t₀) :=
      hA.mul (continuous_peanoBakerTerm hA k t₀)
    exact intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable t₀ z)
      hF.stronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have hbound : ∀ (k : ℕ), ∀ z ∈ Metric.ball t₀ r,
      ‖A z * peanoBakerTerm A k z t₀‖ ≤ M * (‖(1 : 𝔸)‖ * (M * r) ^ k / (k)!) := by
    intro k z hz
    calc ‖A z * peanoBakerTerm A k z t₀‖
        ≤ ‖A z‖ * ‖peanoBakerTerm A k z t₀‖ := norm_mul_le _ _
      _ ≤ M * (‖(1 : 𝔸)‖ * (M * |z - t₀|) ^ k / (k)!) :=
          mul_le_mul (hA_le z hz z Set.right_mem_uIcc)
            (norm_peanoBakerTerm_le (hA_le z hz) k z Set.right_mem_uIcc) (norm_nonneg _)
            hM_nonneg
      _ ≤ M * (‖(1 : 𝔸)‖ * (M * r) ^ k / (k)!) := by
          gcongr; exact (Metric.mem_ball.1 hz).le
  have hsummable : ∀ z ∈ Metric.ball t₀ r, Summable (fun k => peanoBakerTerm A k z t₀) :=
    fun z hz => summable_peanoBakerTerm (hA_le z hz)
  have ht : t ∈ Metric.ball t₀ r := by
    rw [Metric.mem_ball, Real.dist_eq]; exact lt_add_one _
  have hshifted :
      HasDerivAt (fun z => ∑' k, peanoBakerTerm A (k + 1) z t₀)
        (∑' k, A t * peanoBakerTerm A k t t₀) t :=
    hasDerivAt_tsum_of_isPreconnected
      (by simpa [mul_div_assoc] using
        ((Real.summable_pow_div_factorial (M * r)).mul_left ‖(1 : 𝔸)‖).mul_left M)
      Metric.isOpen_ball (convex_ball t₀ r).isPreconnected (fun k z _ => hderiv k z) hbound ht
      ((summable_nat_add_iff 1 (f := fun k => peanoBakerTerm A k t t₀)).2 (hsummable t ht)) ht
  rw [(hsummable t ht).tsum_mul_left (A t)] at hshifted
  have hone_plus :
      HasDerivAt (fun z => (1 : 𝔸) + ∑' k, peanoBakerTerm A (k + 1) z t₀)
        (A t * stateTransitionMatrix A t t₀) t := by
    have := (hasDerivAt_const t (1 : 𝔸)).add hshifted
    rwa [zero_add] at this
  refine hone_plus.congr_of_eventuallyEq ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds ht] with z hz
  rw [stateTransitionMatrix, (hsummable z hz).tsum_eq_zero_add]
  simp [peanoBakerTerm]

omit [CompleteSpace 𝔸] in
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
      if k = 0 then (1 : 𝔸) else 0 := by
    intro k
    cases k with
    | zero => simp [peanoBakerTerm]
    | succ k => simp [peanoBakerTerm, intervalIntegral.integral_same]
  rw [stateTransitionMatrix, tsum_congr hterm,
    tsum_ite_eq 0 (fun _ => (1 : 𝔸))]

/-- **Uniqueness for linear equations.** Two solutions of `ż = L(t) z` on the whole line, with
`L` continuous, that agree at one time agree at every time.

Grönwall, through Mathlib's `ODE_solution_unique_of_mem_Ioo`: on a bounded window containing both
times, `L` is bounded (compactness), so the right-hand side is Lipschitz there. -/
@[blueprint "thm:ODE-solution-unique-linear"
  (title := "Uniqueness for linear equations")
  (statement := /-- Let $L : \mathbb{R} \to (F \to_L F)$ be continuous. If $z$ and $w$ both
    satisfy $\dot z(t) = L(t) z(t)$ for all $t$ and $z(t_0) = w(t_0)$, then $z = w$. -/)
  (proof := /-- On a bounded window containing $t_0$ and $t$, $\|L\|$ is bounded by compactness,
    so $z \mapsto L(s) z$ is Lipschitz there with one constant; apply Gr\"onwall uniqueness on
    that window. -/)]
theorem ODE_solution_unique_linear {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : ℝ → F →L[ℝ] F} (hL : Continuous L) {z w : ℝ → F} {t₀ : ℝ}
    (hz : ∀ t, HasDerivAt z (L t (z t)) t) (hw : ∀ t, HasDerivAt w (L t (w t)) t)
    (h : z t₀ = w t₀) : z = w := by
  funext t
  obtain ⟨K, hK⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc (a := min t t₀ - 1) (b := max t t₀ + 1)) hL.continuousOn
  exact ODE_solution_unique_of_mem_Ioo (K := K.toNNReal) (s := fun _ => Set.univ)
    (fun r hr => ((L r).lipschitz.weaken (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal']
      exact (hK r (Set.Ioo_subset_Icc_self hr)).trans (le_max_left _ _))).lipschitzOnWith)
    ⟨by linarith [min_le_right t t₀], by linarith [le_max_right t t₀]⟩
    (fun r _ => ⟨hz r, trivial⟩) (fun r _ => ⟨hw r, trivial⟩) h
    ⟨by linarith [min_le_left t t₀], by linarith [le_max_left t t₀]⟩

/-- **The semigroup property** (Hespanha, P5.3): `Φ(t, s) Φ(s, τ) = Φ(t, τ)` for all times, in
any order.

Both sides solve `Ż = A(t) Z` in `t` and agree at `t = s`, so they agree everywhere by
`ODE_solution_unique_linear`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.3. -/
@[blueprint "thm:stateTransitionMatrix-mul"
  (title := "Semigroup property")
  (statement := /-- For $A$ continuous, $\Phi(t, s)\,\Phi(s, \tau) = \Phi(t, \tau)$ for all
    $t, s, \tau$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, Property P5.3.
  -/)
  (proof := /-- Both sides solve $\dot Z = A(t) Z$ in $t$
    (\cref{thm:hasDerivAt-stateTransitionMatrix}) and agree at $t = s$
    (\cref{thm:stateTransitionMatrix-self}); apply \cref{thm:ODE-solution-unique-linear}. -/)]
theorem stateTransitionMatrix_mul (hA : Continuous A) (t s τ : ℝ) :
    stateTransitionMatrix A t s * stateTransitionMatrix A s τ = stateTransitionMatrix A t τ :=
  congrFun (ODE_solution_unique_linear (L := fun r => ContinuousLinearMap.mul ℝ 𝔸 (A r))
    ((ContinuousLinearMap.mul ℝ 𝔸).continuous.comp hA) (t₀ := s)
    (fun r => by
      simpa [mul_assoc] using
        (hasDerivAt_stateTransitionMatrix hA r s).mul_const (stateTransitionMatrix A s τ))
    (fun r => by simpa using hasDerivAt_stateTransitionMatrix hA r τ)
    (by simp [stateTransitionMatrix_self])) t

/-- **Invertibility** (Hespanha, P5.4): `Φ(t, τ) Φ(τ, t) = 1`, so `Φ(t, τ)` is invertible with
inverse `Φ(τ, t)`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.4. -/
@[blueprint "thm:stateTransitionMatrix-mul-swap"
  (title := "Invertibility of the state transition matrix")
  (statement := /-- For $A$ continuous, $\Phi(t, \tau)\,\Phi(\tau, t) = 1$.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 5, Property P5.4.
  -/)
  (proof := /-- \cref{thm:stateTransitionMatrix-mul} with $s = \tau$ and $\tau = t$, then
    \cref{thm:stateTransitionMatrix-self}. -/)]
theorem stateTransitionMatrix_mul_swap (hA : Continuous A) (t τ : ℝ) :
    stateTransitionMatrix A t τ * stateTransitionMatrix A τ t = 1 := by
  rw [stateTransitionMatrix_mul hA, stateTransitionMatrix_self]

/-- **The derivative in the initial time**: `∂Φ(t, τ)/∂τ = -Φ(t, τ) A(τ)`.

`Φ(t, ·)` is the pointwise inverse of `Φ(·, t)` (`stateTransitionMatrix_mul_swap`); differentiate
the inverse (`hasFDerivAt_ringInverse`).

Reference: Khalil, *Nonlinear Systems* (3rd ed.), proof of Theorem 4.12. -/
@[blueprint "thm:hasDerivAt-stateTransitionMatrix-snd"
  (title := "Derivative in the initial time")
  (statement := /-- For $A$ continuous,
    \[
      \frac{\partial}{\partial \tau}\Phi(t, \tau) = -\Phi(t, \tau)\,A(\tau)
    \]
    at every $\tau$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), proof of Theorem 4.12. -/)
  (proof := /-- $\Phi(t, \sigma) = \Phi(\sigma, t)^{-1}$
    (\cref{thm:stateTransitionMatrix-mul-swap}). Differentiate $\sigma \mapsto \Phi(\sigma, t)$
    by \cref{thm:hasDerivAt-stateTransitionMatrix} and the inverse by
    $d(M^{-1}) = -M^{-1}\,dM\,M^{-1}$:
    $-\Phi(t, \tau)\,A(\tau)\,\Phi(\tau, t)\,\Phi(t, \tau) = -\Phi(t, \tau)\,A(\tau)$. -/)]
theorem hasDerivAt_stateTransitionMatrix_snd (hA : Continuous A) (t τ : ℝ) :
    HasDerivAt (fun σ => stateTransitionMatrix A t σ) (-(stateTransitionMatrix A t τ * A τ)) τ := by
  let u : ℝ → 𝔸ˣ := fun σ => ⟨stateTransitionMatrix A σ t, stateTransitionMatrix A t σ,
    stateTransitionMatrix_mul_swap hA σ t, stateTransitionMatrix_mul_swap hA t σ⟩
  have h_inv : (fun σ => stateTransitionMatrix A t σ) =
      Ring.inverse ∘ fun σ => stateTransitionMatrix A σ t :=
    funext fun σ => (Ring.inverse_unit (u σ)).symm
  rw [h_inv]
  convert (hasFDerivAt_ringInverse (u τ)).comp_hasDerivAt τ
    (hasDerivAt_stateTransitionMatrix hA τ t) using 1
  simp [u, mul_assoc, stateTransitionMatrix_mul_swap hA]

omit [CompleteSpace 𝔸] in
/-- **Exponential growth of the state transition matrix**: if `‖A‖ ≤ M` between `t₀` and `t`,
then `‖Φ(t, t₀)‖ ≤ ‖1‖ e^{M |t - t₀|}`, by summing the term bounds of the Peano–Baker series.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5. -/
@[blueprint "lem:norm-stateTransitionMatrix-le"
  (title := "Exponential growth bound")
  (latexEnv := "lemma")
  (statement := /-- If $\|A(s)\| \le M$ on the segment between $t_0$ and $t$, then
    \[
      \|\Phi(t, t_0)\| \le \|1\|\, e^{M |t - t_0|}.
    \] -/)
  (proof := /-- Sum the term bounds of \cref{lem:norm-peanoBakerTerm-le}: they are $\|1\|$ times
    the terms of the exponential series. -/)]
theorem norm_stateTransitionMatrix_le {t₀ t M : ℝ}
    (hA_le : ∀ s ∈ Set.uIcc t₀ t, ‖A s‖ ≤ M) :
    ‖stateTransitionMatrix A t t₀‖ ≤ ‖(1 : 𝔸)‖ * Real.exp (M * |t - t₀|) := by
  have h_term : ∀ k, ‖peanoBakerTerm A k t t₀‖ ≤
      ‖(1 : 𝔸)‖ * ((M * |t - t₀|) ^ k / (k)!) := fun k => by
    rw [← mul_div_assoc]
    exact norm_peanoBakerTerm_le hA_le k t Set.right_mem_uIcc
  have h_exp : Summable fun k : ℕ => ‖(1 : 𝔸)‖ * ((M * |t - t₀|) ^ k / (k)!) :=
    (Real.summable_pow_div_factorial _).mul_left _
  have h_norm : Summable fun k => ‖peanoBakerTerm A k t t₀‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_term h_exp
  calc ‖stateTransitionMatrix A t t₀‖
      ≤ ∑' k, ‖peanoBakerTerm A k t t₀‖ := norm_tsum_le_tsum_norm h_norm
    _ ≤ ∑' k : ℕ, ‖(1 : 𝔸)‖ * ((M * |t - t₀|) ^ k / (k)!) :=
        Summable.tsum_le_tsum h_term h_norm h_exp
    _ = ‖(1 : 𝔸)‖ * Real.exp (M * |t - t₀|) := by
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- **Peano-Baker term for constant `A`** (Hespanha, equation (6.1)).
For a *constant* state matrix `A`, the `k`-th Peano-Baker term
collapses to the closed form `((t-t₀)^k / k!) • A^k`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, equation (6.1). -/
@[blueprint "lem:peanoBakerTerm-const"
  (title := "Peano--Baker terms for a constant matrix")
  (latexEnv := "lemma")
  (statement := /-- For a constant state matrix $A$, the $k$-th Peano--Baker term collapses to
    \[
      \Phi_k(t, t_0) = \frac{(t-t_0)^k}{k!}\,A^k .
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 6, equation (6.1).
  -/)
  (proof := /-- Induction on $k$.  The $k = 0$ term is the identity.  For the step,
    $\Phi_{k+1}(t,t_0) = \int_{t_0}^{t} A\,\Phi_k(s,t_0)\,ds$; substituting the inductive
    hypothesis pulls $A^{k+1}$ out of the integral and leaves
    $\int_{t_0}^{t}(s-t_0)^k ds = (t-t_0)^{k+1}/(k+1)$, which combines with $1/k!$ to give
    $1/(k+1)!$. -/)]
theorem peanoBakerTerm_const (A : 𝔸) (k : ℕ) (t t₀ : ℝ) :
    peanoBakerTerm (fun _ => A) k t t₀ = ((t - t₀) ^ k / (k)! : ℝ) • A ^ k := by
  induction k generalizing t with
  | zero =>
    change (1 : 𝔸) = _
    norm_num
  | succ k ih =>
    change (∫ s in t₀..t, A * peanoBakerTerm (fun _ => A) k s t₀) = _
    simp_rw [ih, Algebra.mul_smul_comm, ← pow_succ']
    rw [intervalIntegral.integral_smul_const]
    congr 1
    have hk_fac_ne : ((k)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    simp_rw [div_eq_inv_mul, intervalIntegral.integral_const_mul, integral_sub_pow,
      Nat.factorial_succ]
    push_cast
    field_simp

/-- **Peano-Baker series for constant `A`** (Hespanha, equation (6.1)).
For a *constant* state matrix `A`, the continuous-time state transition matrix
is given by the power series `Φ(t,t₀) = Σ_{k=0}^∞ ((t-t₀)^k / k!) A^k` — summing
`peanoBakerTerm_const` termwise.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, equation (6.1). -/
@[blueprint "lem:stateTransitionMatrix-const-eq-tsum"
  (title := "The LTI state transition matrix as a series")
  (latexEnv := "lemma")
  (statement := /-- For a constant state matrix $A$, the state transition matrix is the power
    series
    \[
      \Phi(t, t_0) = \sum_{k=0}^{\infty} \frac{(t-t_0)^k}{k!}\,A^k .
    \]

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 6, equation (6.1).
  -/)
  (proof := /-- Sum \cref{lem:peanoBakerTerm-const} termwise; the Peano--Baker series converges
    for any continuous state matrix, a constant one included. -/)]
theorem stateTransitionMatrix_const_eq_tsum (A : 𝔸) (t t₀ : ℝ) :
    stateTransitionMatrix (fun _ => A) t t₀ = ∑' k, ((t - t₀) ^ k / (k)! : ℝ) • A ^ k := by
  unfold stateTransitionMatrix
  exact tsum_congr fun k => peanoBakerTerm_const A k t t₀

/-- **The exponential as state transition matrix** (Hespanha, equation (6.2)).
For a *constant* state matrix `A`, the continuous-time state transition matrix
collapses to the exponential `Φ(t,t₀) = e^{A(t-t₀)}`. This is what lets every LTV
property already proved for `stateTransitionMatrix` (existence, uniqueness, semigroup,
invertibility, variation of constants) be reused directly for LTI by specialization.

Proof: sum `peanoBakerTerm_const` termwise and match against Mathlib's own series
characterization of `exp` (`NormedSpace.exp_eq_tsum`).

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 6, equation (6.2). -/
@[blueprint "thm:stateTransitionMatrix-const"
  (title := "The LTI state transition matrix is $e^{A(t-t_{0})}$")
  (statement := /-- For a constant state matrix $A$, the state transition matrix is the matrix
    exponential:
    \[
      \Phi(t, t_0) = e^{A(t-t_0)} .
    \]
    This is the bridge that lets every property already proved for $\Phi$ in the time-varying
    setting — existence, uniqueness, the semigroup law, invertibility, variation of constants —
    be reused for LTI systems by specialization rather than reproved.

    Reference: Hespanha, \emph{Linear Systems Theory} (2nd ed.), Chapter 6, equation (6.2).
  -/)
  (proof := /-- Both sides are power series in $A$: \cref{lem:stateTransitionMatrix-const-eq-tsum}
    for the left, the defining series of $\exp$ for the right.  Match them termwise. -/)]
theorem stateTransitionMatrix_const (A : 𝔸) (t t₀ : ℝ) :
    stateTransitionMatrix (fun _ => A) t t₀ = NormedSpace.exp ((t - t₀) • A) := by
  unfold stateTransitionMatrix
  simp only [NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
  refine tsum_congr fun k => ?_
  rw [peanoBakerTerm_const, smul_pow, smul_smul, div_eq_inv_mul]

end LinearSystems

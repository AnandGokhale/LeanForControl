import LeanForControl.Comparison.Axioms
import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKInfty
import LeanForControl.Comparison.ClassKL
import LeanForControl.Analysis.MonotoneFunctions

import Architect

/-- Any `ψ` with the stability properties — nonnegative, vanishing at `r = 0`, monotone in the
    radius, antitone and decaying to `0` in time, continuous in the radius at `0` — is dominated
    by a global class KL function. The usable form of
    `exists_classKLGlobal_of_stability_properties`. -/
@[blueprint "lem:exists-classKL-upper-bound"
  (statement := /-- Let $\psi : \mathbb{R} \to \mathbb{R} \to \mathbb{R}$ satisfy, for all
    $r, s \ge 0$:
    \begin{enumerate}
      \item $\psi(r, s) \ge 0$;
      \item $\psi(0, s) = 0$;
      \item $r \mapsto \psi(r, s)$ is monotone on $[0,\infty)$;
      \item $s \mapsto \psi(r, s)$ is antitone on $[0,\infty)$;
      \item $\psi(r, s) \to 0$ as $s \to \infty$;
      \item $r \mapsto \psi(r, 0)$ is continuous at $0$ within $[0,\infty)$.
    \end{enumerate}
    Then there is a global class $\mathcal{KL}$ function $\beta$ with
    $\psi(r,s) \le \beta(r,s)$ for all $r, s \ge 0$. -/)
  (proof := /-- The two hypotheses of
    \cref{lem:exists-classKLGlobal-of-stability-properties} are supplied in turn.  For uniform
    convergence, $\psi(r, \cdot) \to 0$ gives a time $T$ beyond which $\psi(r,t) < \varepsilon$,
    and monotonicity in the radius extends that bound to every $s \le r$.  For uniform
    stability, continuity of $\psi(\cdot, 0)$ at $0$ gives a $\delta$ with
    $\psi(s, 0) \le \varepsilon$ for $s \le \delta/2$, and antitonicity in time propagates it to
    all $t \ge 0$. -/)]
lemma exists_classKL_upper_bound (ψ : ℝ → ℝ → ℝ)
    (hψ_nonneg : ∀ r ≥ 0, ∀ s ≥ 0, 0 ≤ ψ r s)
    (hψ_zero : ∀ s ≥ 0, ψ 0 s = 0)
    (hψ_mono : ∀ s ≥ 0, MonotoneOn (fun r => ψ r s) (Set.Ici 0))
    (hψ_anti : ∀ r ≥ 0, AntitoneOn (fun s => ψ r s) (Set.Ici 0))
    (hψ_tendsto : ∀ r ≥ 0, Filter.Tendsto (fun s => ψ r s) Filter.atTop (nhds 0))
    (hψ_cont : ContinuousWithinAt (fun r => ψ r 0) (Set.Ici 0) 0) :
    ∃ β : ClassKLGlobal, ∀ r ≥ 0, ∀ s ≥ 0, ψ r s ≤ β.toFun r s := by
  apply exists_classKLGlobal_of_stability_properties
  · -- h_convergence: ψ(r,·) → 0 gives T; monotonicity in r bounds ψ(s,t) ≤ ψ(r,t)
    intro r hr ε hε
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hψ_tendsto r hr.le (Iio_mem_nhds hε))
    refine ⟨max T 0 + 1, by linarith [le_max_right T (0:ℝ)],
            fun s hs_nn hs_le t ht => ?_⟩
    have ht_nn : 0 ≤ t := by linarith [le_max_right T (0:ℝ)]
    exact (hψ_mono t ht_nn (Set.mem_Ici.mpr hs_nn) (Set.mem_Ici.mpr hr.le) hs_le).trans_lt
      (Set.mem_Iio.mp (hT t (by linarith [le_max_left T (0:ℝ)])))
  · -- h_uniform_stability: continuity of ψ(·,0) at 0 + antitone in s
    intro ε hε
    rw [Metric.continuousWithinAt_iff] at hψ_cont
    obtain ⟨δ, hδ_pos, hδ⟩ := hψ_cont ε hε
    refine ⟨δ / 2, half_pos hδ_pos, fun s hs_nn hs_le t ht => ?_⟩
    have hs_dist : dist s 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs_nn]
      exact hs_le.trans_lt (half_lt_self hδ_pos)
    have h_ψs0 := hδ (Set.mem_Ici.mpr hs_nn) hs_dist
    rw [hψ_zero 0 le_rfl, Real.dist_eq, sub_zero,
        abs_of_nonneg (hψ_nonneg s hs_nn 0 le_rfl)] at h_ψs0
    exact (hψ_anti s hs_nn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht).trans h_ψs0.le


/-- Given a class K∞ spatial bound `α` and a family `U` of singular class L time-decay
    functions that is monotone in the radius parameter, there exists a class KL-global
    function `β` satisfying:
    - `β(·, 0) → ∞` (K∞ propagation),
    - `α(r) ≤ β(r, 0)` for all `r ≥ 0`,
    - `min(α(r), √(α(r) · U(r+1)(s))) ≤ β(r, s)` for all `r ≥ 0`, `s > 0`.

    The candidate `ψ(r,s) = if s = 0 then α(r) else min(α(r), √(α(r)·U(r+1)(s)))` is
    constructed and smoothed internally; no details of `ψ` leak into the conclusion. -/
@[blueprint "lem:classKLGlobal-of-KInfty-LSingular-family"
  (statement := /-- Let $\alpha$ be class $\mathcal{K}_{\infty}$ and let $U$ be a family of
    functions such that
    \begin{enumerate}
      \item $U(r, s) > 0$ for all $r > 0$ and $s > 0$;
      \item $U(r, \cdot)$ is antitone on $(0,\infty)$ for each $r > 0$;
      \item $U(r, s) \to 0$ as $s \to \infty$, for each $r > 0$;
      \item $r \mapsto U(r+1, s)$ is monotone on $[0,\infty)$ for each $s > 0$.
    \end{enumerate}
    Then there is a global class $\mathcal{KL}$ function $\beta$ such that
    \begin{enumerate}
      \item $\beta(r, 0) \to \infty$ as $r \to \infty$;
      \item $\alpha(r) \le \beta(r, 0)$ for all $r \ge 0$;
      \item $\min\bigl(\alpha(r), \sqrt{\alpha(r)U(r+1, s)}\bigr) \le \beta(r, s)$ for all
        $r \ge 0$ and $s > 0$.
    \end{enumerate} -/)
  (proof := /-- Take $\psi(r, s) := \alpha(r)$ for $s = 0$ and
    $\min\bigl(\alpha(r), \sqrt{\alpha(r)U(r+1,s)}\bigr)$ for $s > 0$, the radius being shifted
    by $1$ so that $U$ is only ever evaluated at a strictly positive radius.  Each hypothesis of
    \cref{lem:exists-classKL-upper-bound} holds for $\psi$: monotonicity in $r$ from that of
    $\alpha$ and of $r \mapsto U(r+1,s)$, antitonicity in $s$ from that of $U(r+1,\cdot)$, decay
    from \cref{lem:tendstoMinSqrtMulZero}, and continuity at $r = 0$ because
    $\psi(\cdot, 0) = \alpha$.  The resulting $\beta$ dominates $\psi$, which gives the three
    conclusions; $\beta(r,0) \ge \alpha(r) \to \infty$ gives the first.  No property of $\psi$
    beyond these bounds appears in the statement. -/)]
lemma ClassKLGlobal.of_KInfty_LSingular_family
    (α : ClassKInfty) (U : ℝ → ℝ → ℝ)
    (hU_pos : ∀ r > 0, ∀ s > 0, 0 < U r s)
    (hU_anti : ∀ r > 0, AntitoneOn (U r) (Set.Ioi 0))
    (hU_tendsto : ∀ r > 0, Filter.Tendsto (U r) Filter.atTop (nhds 0))
    (hU_mono_r : ∀ s > 0, MonotoneOn (fun r => U (r + 1) s) (Set.Ici 0)) :
    ∃ β : ClassKLGlobal,
      Filter.Tendsto (fun r => β.toFun r 0) Filter.atTop Filter.atTop ∧
      (∀ r ≥ 0, α.toFun r ≤ β.toFun r 0) ∧
      (∀ r ≥ 0, ∀ s > 0,
        min (α.toFun r) (Real.sqrt (α.toFun r * U (r + 1) s)) ≤ β.toFun r s) := by
  let ψ : ℝ → ℝ → ℝ := fun r s =>
    if s = 0 then α.toFun r
    else min (α.toFun r) (Real.sqrt (α.toFun r * U (r + 1) s))
  have hψ_zero_val : ∀ r, ψ r 0 = α.toFun r := fun r => by simp [ψ]
  have hψ_pos_val : ∀ r s, 0 < s → ψ r s = min (α.toFun r) (Real.sqrt (α.toFun r * U (r + 1) s)) :=
    fun r s hs => by simp [ψ, hs.ne']
  have hψ_nonneg : ∀ r ≥ 0, ∀ s ≥ 0, 0 ≤ ψ r s := by
    intro r hr s _; simp only [ψ]; split_ifs
    · exact α.maps_to hr
    · exact le_min (α.maps_to hr) (Real.sqrt_nonneg _)
  have hψ_zero : ∀ s ≥ 0, ψ 0 s = 0 := by
    intro s _; simp only [ψ]; split_ifs with h
    · exact α.map_zero
    · rw [α.map_zero, zero_mul, Real.sqrt_zero, min_self]
  have hψ_mono : ∀ s ≥ 0, MonotoneOn (fun r => ψ r s) (Set.Ici 0) := by
    intro s hs r₁ hr₁ r₂ hr₂ h_le
    simp only [ψ]; rcases eq_or_lt_of_le h_le with rfl | h_lt
    · exact le_rfl
    · have h_α_le := le_of_lt (α.strict_mono hr₁ hr₂ h_lt)
      by_cases h_zero : s = 0
      · simp [if_pos h_zero, h_α_le]
      · simp only [if_neg h_zero]
        have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm h_zero)
        refine min_le_min h_α_le ?_
        rcases (Set.mem_Ici.mp hr₁).eq_or_lt with rfl | hr₁_pos
        · rw [α.map_zero, zero_mul, Real.sqrt_zero]; exact Real.sqrt_nonneg _
        · exact Real.sqrt_le_sqrt (mul_le_mul h_α_le (hU_mono_r s hs_pos hr₁ hr₂ h_le)
            (le_of_lt (hU_pos (r₁ + 1) (by positivity) s hs_pos)) (α.maps_to hr₂))
  have hψ_anti : ∀ r ≥ 0, AntitoneOn (fun s => ψ r s) (Set.Ici 0) := by
    intro r hr s₁ hs₁ s₂ hs₂ h_le
    simp only [ψ]; rcases eq_or_lt_of_le hr with rfl | _
    · simp [α.map_zero]
    · rcases (Set.mem_Ici.mp hs₁).eq_or_lt with rfl | hs₁_pos
      · rcases (Set.mem_Ici.mp hs₂).eq_or_lt with rfl | hs₂_pos
        · exact le_rfl
        · simp [if_neg (hs₂_pos.ne')]
      · rcases (Set.mem_Ici.mp hs₂).eq_or_lt with rfl | hs₂_pos
        · linarith
        · simp only [if_neg (hs₁_pos.ne'), if_neg (hs₂_pos.ne')]
          exact min_le_min_left _ (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
            (hU_anti (r + 1) (by positivity) hs₁_pos hs₂_pos h_le) (α.maps_to hr)))
  have hψ_tendsto : ∀ r ≥ 0, Filter.Tendsto (fun s => ψ r s) Filter.atTop (nhds 0) := by
    intro r hr; simp only [ψ]; rcases eq_or_lt_of_le hr with rfl | _
    · simp [α.map_zero]
    · apply (tendsto_min_sqrt_mul_zero (α.maps_to hr) (hU_tendsto (r + 1) (by positivity))).congr'
      filter_upwards [Filter.eventually_ne_atTop 0] with s hs; exact (if_neg hs).symm
  have hψ_cont : ContinuousWithinAt (fun r => ψ r 0) (Set.Ici 0) 0 := by
    have h : (fun r => ψ r 0) = α.toFun := funext fun r => by simp [ψ]
    rw [h]; exact α.continuous.continuousWithinAt (Set.mem_Ici.mpr le_rfl)
  obtain ⟨β, hβ_bound⟩ :=
    exists_classKL_upper_bound ψ hψ_nonneg hψ_zero hψ_mono hψ_anti hψ_tendsto hψ_cont
  refine ⟨β, ?_, fun r hr => ?_, fun r hr s hs => ?_⟩
  · rw [Filter.tendsto_atTop]; intro b
    filter_upwards [Filter.tendsto_atTop.mp α.tendsto_atTop b,
                    Filter.eventually_ge_atTop 0] with r hr h0r
    exact hr.trans (hψ_zero_val r ▸ hβ_bound r h0r 0 le_rfl)
  · exact hψ_zero_val r ▸ hβ_bound r hr 0 le_rfl
  · exact hψ_pos_val r s hs ▸ hβ_bound r hr s hs.le

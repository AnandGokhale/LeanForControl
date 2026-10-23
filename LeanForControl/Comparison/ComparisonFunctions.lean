import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKInfty
import LeanForControl.Comparison.ClassKL
import LeanForControl.Analysis.MonotoneFunctions

import Architect

open Set Filter Topology MeasureTheory in
/-- Any `ψ` with the stability properties — nonnegative, vanishing at `r = 0`, monotone in the
    radius, antitone and decaying to `0` in time, continuous in the radius at `0` — is dominated
    by a global class KL function.

    Compare Lemma 9 of Kellett, *A compendium of comparison function results* (2014), which
    builds such a majorant from uniform convergence and uniform stability hypotheses instead of
    monotonicity. -/
@[blueprint "lem:exists-classKL-upper-bound"
  (title := "Class $\\mathcal{KL}$ majorant")
  (latexEnv := "lemma")
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
  (proof := /-- Clamp both arguments of $\psi$ at $0$ and average it over a window in each
    variable: first $\psi_1(r, s) = \int_0^1 \psi(r, s - v)\,dv$, over $[s-1, s]$, then
    $\psi_2(r, s) = \int_1^2 \psi_1(ru, s)\,du$, over $[r, 2r]$.  Each window sits on the side
    that makes the average dominate, so $\psi \le \psi_1 \le \psi_2$, and $\psi_2$ is still
    nondecreasing in $r$ and nonincreasing in $s$.
    \begin{itemize}
      \item $\psi_1(r, \cdot)$ is a difference of primitives of $\psi(r, \cdot)$, so continuous;
        $\psi_2(r, \cdot)$ is then continuous by dominated convergence, the integrands being
        bounded by $\psi(2r, 0)$.
      \item For $r > 0$, $\psi_2(r, s) = r^{-1} \int_r^{2r} \psi_1(\cdot, s)$ is a quotient of
        primitives, so continuous; at $r \le 0$, $0 \le \psi_2(r, s) \le \psi(2\max(r,0), 0)
        \to \psi(0, 0) = 0$ by continuity of $\psi(\cdot, 0)$ at $0$.
    \end{itemize}
    By \cref{lem:continuous-uncurry-of-monotone-antitone}, $\psi_2$ is jointly continuous.
    Also $\psi_2(r, s) \le \psi(2r, s - 1) \to 0$.  Finally
    $\beta(r, s) = \psi_2(r, s) + r e^{-s}$ is class $\mathcal{KL}$, the second term making it
    strictly increasing in $r$. -/)]
lemma exists_classKL_upper_bound (ψ : ℝ → ℝ → ℝ)
    (hψ_nonneg : ∀ r ≥ 0, ∀ s ≥ 0, 0 ≤ ψ r s)
    (hψ_zero : ∀ s ≥ 0, ψ 0 s = 0)
    (hψ_mono : ∀ s ≥ 0, MonotoneOn (fun r => ψ r s) (Set.Ici 0))
    (hψ_anti : ∀ r ≥ 0, AntitoneOn (fun s => ψ r s) (Set.Ici 0))
    (hψ_tendsto : ∀ r ≥ 0, Filter.Tendsto (fun s => ψ r s) Filter.atTop (nhds 0))
    (hψ_cont : ContinuousWithinAt (fun r => ψ r 0) (Set.Ici 0) 0) :
    ∃ β : ClassKLGlobal, ∀ r ≥ 0, ∀ s ≥ 0, ψ r s ≤ β.toFun r s := by
  /- We take `β(r, s) = ψ₂(r, s) + r e⁻ˢ`, where `ψ₂` averages `ψ` over a window in each
     variable: first `[s - 1, s]` in time, then `[r, 2r]` in radius.  Both windows lie on the side
     that makes the average dominate `ψ`; averaging makes each section continuous, and
     monotonicity in each variable upgrades that to joint continuity.  The `r e⁻ˢ` term makes
     `β` strictly increasing in `r`. -/
  -- Step 1. Clamp both arguments at `0`, so that `Ψ` is monotone in `r` and antitone in `s` on
  -- all of `ℝ`.
  set Ψ : ℝ → ℝ → ℝ := fun r s => ψ (max r 0) (max s 0)
  have hΨ_mono : ∀ s, Monotone (Ψ · s) := fun s x y h =>
    hψ_mono _ (le_max_right s 0) (le_max_right x 0) (le_max_right y 0) (max_le_max h le_rfl)
  have hΨ_anti : ∀ r, Antitone (Ψ r) := fun r x y h =>
    hψ_anti _ (le_max_right r 0) (le_max_right x 0) (le_max_right y 0) (max_le_max h le_rfl)
  have hΨ_nonneg : ∀ r s, 0 ≤ Ψ r s := fun r s =>
    hψ_nonneg _ (le_max_right r 0) _ (le_max_right s 0)
  have hΨ_eq : ∀ r ≥ 0, ∀ s ≥ 0, Ψ r s = ψ r s := fun r hr s hs => by
    simp [Ψ, max_eq_left hr, max_eq_left hs]
  have hΨ_zero : ∀ s, Ψ 0 s = 0 := fun s => by simp [Ψ, hψ_zero _ (le_max_right s 0)]
  have hΨ_le : ∀ r s, Ψ r s ≤ ψ (max r 0) 0 := fun r s =>
    hψ_anti _ (le_max_right r 0) (le_refl (0 : ℝ)) (le_max_right s 0) (le_max_right s 0)
  -- Step 2. Average in time: `ψ₁(r, s) = ∫₀¹ Ψ(r, s - v) dv`, the average over `[s - 1, s]`.
  set ψ₁ : ℝ → ℝ → ℝ := fun r s => ∫ v in (0 : ℝ)..1, Ψ r (s - v)
  have hint₁ : ∀ r s, IntervalIntegrable (fun v => Ψ r (s - v)) volume 0 1 := fun r s =>
    (Antitone.comp (hΨ_anti r) fun _ _ h => sub_le_sub_left h s).intervalIntegrable
  have hψ₁_mono : ∀ s, Monotone (ψ₁ · s) := fun s x y h =>
    intervalIntegral.integral_mono_on zero_le_one (hint₁ x s) (hint₁ y s) fun _ _ =>
      hΨ_mono _ h
  have hψ₁_anti : ∀ r, Antitone (ψ₁ r) := fun r x y h =>
    intervalIntegral.integral_mono_on zero_le_one (hint₁ r y) (hint₁ r x) fun v _ =>
      hΨ_anti r (sub_le_sub_right h v)
  -- `Ψ(r, s) ≤ ψ₁(r, s) ≤ Ψ(r, s - 1)`, since `Ψ(r, ·)` is antitone.
  have hψ₁_ge : ∀ r s, Ψ r s ≤ ψ₁ r s := fun r s => by
    have h := intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const
      (hint₁ r s) fun v hv => hΨ_anti r (by linarith [hv.1] : s - v ≤ s)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at h
    exact h
  have hψ₁_le : ∀ r s, ψ₁ r s ≤ Ψ r (s - 1) := fun r s => by
    have h := intervalIntegral.integral_mono_on zero_le_one (hint₁ r s)
      intervalIntegrable_const fun v hv => hΨ_anti r (by linarith [hv.2] : s - 1 ≤ s - v)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at h
    exact h
  have hψ₁_zero : ∀ s, ψ₁ 0 s = 0 := fun s => by simp [ψ₁, hΨ_zero]
  have hψ₁_bdd : ∀ r s, ψ₁ r s ≤ ψ (max r 0) 0 := fun r s => (hψ₁_le r s).trans (hΨ_le r _)
  -- Each section `ψ₁(r, ·)` is continuous: it is a difference of primitives of `Ψ(r, ·)`.
  have hψ₁_cont : ∀ r, Continuous (ψ₁ r) := fun r => by
    have hint : ∀ a b, IntervalIntegrable (Ψ r) volume a b := fun _ _ =>
      (hΨ_anti r).intervalIntegrable
    have hΦ : Continuous fun b => ∫ x in (0 : ℝ)..b, Ψ r x :=
      intervalIntegral.continuous_primitive hint 0
    have h_eq : ψ₁ r = fun s => (∫ x in (0 : ℝ)..(s - 0), Ψ r x) - ∫ x in (0 : ℝ)..(s - 1), Ψ r x :=
      funext fun s => by
        simp only [ψ₁]
        rw [intervalIntegral.integral_comp_sub_left,
          intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
    rw [h_eq]
    exact (hΦ.comp (continuous_sub_right 0)).sub (hΦ.comp (continuous_sub_right 1))
  -- Step 3. Average in radius: `ψ₂(r, s) = ∫₁² ψ₁(r u, s) du`, the average over `[r, 2r]`
  -- (with `r` clamped at `0`).
  set ψ₂ : ℝ → ℝ → ℝ := fun r s => ∫ u in (1 : ℝ)..2, ψ₁ (max r 0 * u) s
  have hint₂ : ∀ r s, IntervalIntegrable (fun u => ψ₁ (max r 0 * u) s) volume 1 2 := fun r s =>
    (Monotone.comp (hψ₁_mono s)
      fun _ _ h => mul_le_mul_of_nonneg_left h (le_max_right r 0)).intervalIntegrable
  have hψ₂_mono : ∀ s, Monotone (ψ₂ · s) := fun s x y h =>
    intervalIntegral.integral_mono_on (by norm_num) (hint₂ x s) (hint₂ y s) fun u hu =>
      hψ₁_mono s (mul_le_mul_of_nonneg_right (max_le_max h le_rfl) (by linarith [hu.1]))
  have hψ₂_anti : ∀ r, Antitone (ψ₂ r) := fun r x y h =>
    intervalIntegral.integral_mono_on (by norm_num) (hint₂ r y) (hint₂ r x) fun _ _ =>
      hψ₁_anti _ h
  -- `ψ₁(r, s) ≤ ψ₂(r, s) ≤ ψ₁(2r, s)`, since `ψ₁(·, s)` is monotone.
  have hψ₂_ge : ∀ r ≥ 0, ∀ s, ψ₁ r s ≤ ψ₂ r s := fun r hr s => by
    have h := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 2)
      intervalIntegrable_const (hint₂ r s) fun u hu =>
        hψ₁_mono s (by rw [max_eq_left hr]; exact le_mul_of_one_le_right hr hu.1)
    norm_num at h
    exact h
  have hψ₂_le : ∀ r s, ψ₂ r s ≤ ψ₁ (2 * max r 0) s := fun r s => by
    have h := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 2)
      (hint₂ r s) intervalIntegrable_const fun u hu =>
        hψ₁_mono s (by nlinarith [hu.2, le_max_right r 0] : max r 0 * u ≤ 2 * max r 0)
    norm_num at h
    exact h
  have hψ₂_bdd : ∀ r s, ψ₂ r s ≤ ψ (2 * max r 0) 0 := fun r s => by
    have h := (hψ₂_le r s).trans (hψ₁_bdd _ s)
    rwa [max_eq_left (by linarith [le_max_right r 0] : (0 : ℝ) ≤ 2 * max r 0)] at h
  have hψ₂_nonneg : ∀ r s, 0 ≤ ψ₂ r s := fun r s =>
    (hΨ_nonneg _ _).trans ((hψ₁_ge _ _).trans (hψ₂_ge _ (le_max_right r 0) s |>.trans_eq
      (by simp [ψ₂])))
  have hψ₂_zero : ∀ r ≤ 0, ∀ s, ψ₂ r s = 0 := fun r hr s => by
    simp [ψ₂, max_eq_right hr, hψ₁_zero]
  -- Each section `ψ₂(r, ·)` is continuous, by dominated convergence: the integrands
  -- `ψ₁(r u, ·)` are continuous and bounded by `ψ(2r, 0)`.
  have hψ₂_cont_snd : ∀ r, Continuous (ψ₂ r) := fun r => by
    refine intervalIntegral.continuous_of_dominated_interval (bound := fun _ => ψ (2 * max r 0) 0)
      (fun s => (hint₂ r s).def'.aestronglyMeasurable) (fun s => ae_of_all _ fun u hu => ?_)
      intervalIntegrable_const (ae_of_all _ fun u _ => hψ₁_cont _)
    have hu : u ∈ Icc (1 : ℝ) 2 := by
      rw [uIoc_of_le (by norm_num)] at hu; exact ⟨hu.1.le, hu.2⟩
    -- `ψ₁(r u, s) ≤ ψ(r u, 0) ≤ ψ(2r, 0)`
    have h_le : ψ₁ (max r 0 * u) s ≤ ψ (2 * max r 0) 0 :=
      (hψ₁_bdd _ s).trans (hψ_mono 0 le_rfl (le_max_right (max r 0 * u) 0)
        (by linarith [le_max_right r 0] : (0 : ℝ) ≤ 2 * max r 0)
        (max_le (by nlinarith [hu.2, le_max_right r 0]) (by linarith [le_max_right r 0])))
    rw [Real.norm_of_nonneg ((hΨ_nonneg _ _).trans (hψ₁_ge _ _))]
    exact h_le
  -- Each section `ψ₂(·, s)` is continuous: for `r > 0` it is `r⁻¹ ∫ᵣ²ʳ ψ₁(·, s)`, a quotient of
  -- primitives; at `r ≤ 0` it is squeezed between `0` and `ψ(2 max r 0, 0) → ψ(0, 0) = 0`.
  have hψ₂_cont_fst : ∀ s, Continuous (ψ₂ · s) := fun s => by
    refine continuous_iff_continuousAt.mpr fun r₀ => ?_
    rcases le_or_gt r₀ 0 with hr₀ | hr₀
    · have h_upper : Tendsto (fun r => ψ (2 * max r 0) 0) (𝓝 r₀) (𝓝 0) := by
        have h := hψ_cont.comp_of_eq (x := r₀) (s := univ)
          (by fun_prop : Continuous fun r : ℝ => 2 * max r 0).continuousWithinAt
          (fun r _ => by simp only [mem_Ici]; linarith [le_max_right r 0])
          (by simp [max_eq_right hr₀])
        simpa [Function.comp_def, max_eq_right hr₀, hψ_zero 0 le_rfl] using h.tendsto
      rw [ContinuousAt, hψ₂_zero r₀ hr₀]
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper
        (fun r => hψ₂_nonneg r s) fun r => hψ₂_bdd r s
    · have hG : Continuous fun b => ∫ x in (0 : ℝ)..b, ψ₁ x s :=
        intervalIntegral.continuous_primitive (fun _ _ => (hψ₁_mono s).intervalIntegrable) 0
      have h_eq : ∀ r > 0, ψ₂ r s = r⁻¹ * ((∫ x in (0 : ℝ)..r * 2, ψ₁ x s) -
          ∫ x in (0 : ℝ)..r * 1, ψ₁ x s) := fun r hr => by
        simp only [ψ₂, max_eq_left hr.le]
        rw [intervalIntegral.integral_comp_mul_left (fun x => ψ₁ x s) hr.ne', smul_eq_mul,
          intervalIntegral.integral_interval_sub_left
            ((hψ₁_mono s).intervalIntegrable) ((hψ₁_mono s).intervalIntegrable)]
      have h : ContinuousAt (fun r => r⁻¹ * ((∫ x in (0 : ℝ)..r * 2, ψ₁ x s) -
          ∫ x in (0 : ℝ)..r * 1, ψ₁ x s)) r₀ :=
        (continuousAt_inv₀ hr₀.ne').mul (by fun_prop)
      exact h.congr ((eventually_gt_nhds hr₀).mono fun r hr => (h_eq r hr).symm)
  -- Step 4. Monotone in `r`, antitone in `s` and separately continuous, so jointly continuous.
  have hψ₂_cont : Continuous (Function.uncurry ψ₂) :=
    continuous_uncurry_of_monotone_antitone hψ₂_mono hψ₂_anti hψ₂_cont_fst hψ₂_cont_snd
  -- `ψ₂(r, ·) → 0`, since `ψ₂(r, s) ≤ ψ₁(2r, s) ≤ ψ(2r, s - 1)`.
  have hψ₂_tendsto : ∀ r ≥ 0, Tendsto (ψ₂ r) atTop (𝓝 0) := fun r hr => by
    have h_shift : Tendsto (fun s : ℝ => max (s - 1) 0) atTop atTop :=
      tendsto_atTop_mono (fun s => le_max_left _ _) (tendsto_atTop_add_const_right _ (-1)
        tendsto_id)
    have h_upper := (hψ_tendsto (2 * r) (by linarith)).comp h_shift
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper
      (hψ₂_nonneg r) fun s => (hψ₂_le r s).trans ((hψ₁_le _ s).trans_eq ?_)
    simp [Ψ, max_eq_left hr, max_eq_left (by linarith : (0 : ℝ) ≤ 2 * r)]
  -- Step 5. `β(r, s) = ψ₂(r, s) + r e⁻ˢ`.
  refine ⟨⟨fun r s => ψ₂ r s + r * Real.exp (-s), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- `β(0, s) = 0`
    intro s _
    simp [hψ₂_zero 0 le_rfl]
  · -- jointly continuous
    exact (hψ₂_cont.add (continuous_fst.mul (Real.continuous_exp.comp continuous_snd.neg)))
      |>.continuousOn
  · -- strictly increasing in `r`
    intro s _ r _ r' _ hrr'
    exact add_lt_add_of_le_of_lt (hψ₂_mono s hrr'.le)
      (mul_lt_mul_of_pos_right hrr' (Real.exp_pos _))
  · -- nonnegative
    intro r hr s _
    exact add_nonneg (hψ₂_nonneg r s) (mul_nonneg hr (Real.exp_pos _).le)
  · -- antitone in `s`
    intro r hr s _ s' _ hss'
    exact add_le_add (hψ₂_anti r hss')
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hss')) hr)
  · -- decays to `0` in `s`
    intro r hr
    simpa using (hψ₂_tendsto r hr).add (tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero)
  · -- dominates `ψ`: `ψ = Ψ ≤ ψ₁ ≤ ψ₂ ≤ β`
    intro r hr s hs
    have h := (hΨ_eq r hr s hs ▸ hψ₁_ge r s).trans (hψ₂_ge r hr s)
    exact h.trans (le_add_of_nonneg_right (mul_nonneg hr (Real.exp_pos _).le))

/-- Given a class K∞ spatial bound `α` and a family `U` of singular class L time-decay
    functions that is monotone in the radius parameter, there exists a class KL-global
    function `β` satisfying:
    - `β(·, 0) → ∞` (K∞ propagation),
    - `α(r) ≤ β(r, 0)` for all `r ≥ 0`,
    - `min(α(r), √(α(r) · U(r+1)(s))) ≤ β(r, s)` for all `r ≥ 0`, `s > 0`.

    The candidate `ψ(r,s) = if s = 0 then α(r) else min(α(r), √(α(r)·U(r+1)(s)))` is
    constructed and smoothed internally; no details of `ψ` leak into the conclusion. -/
@[blueprint "lem:classKLGlobal-of-KInfty-LSingular-family"
  (title := "Global class $\\mathcal{KL}$ from a decay family")
  (latexEnv := "lemma")
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

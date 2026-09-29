import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import LeanForControl.ODEs.ODE_properties
import Architect

/-!
# `ODEs.PicardLindelof`

Global-in-time existence for a globally Lipschitz vector field.

Mathlib's `IsPicardLindelof` carries the clause
`mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r`, where `L` bounds `‖f‖` on the ball of
radius `a` about the initial point. For a `K`-Lipschitz field the best available bound is
`L ≈ M + K·a`, so that clause reduces to `K · Δt < 1`: a single application never covers a long
interval, however nice `f` is. Continuation is therefore unavoidable, and is what this file adds.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Appendix C.1 (Theorem 3.2 in the text).

## Main results

* `exists_isIntegralCurveOn_Icc` — existence on an arbitrary compact interval.
* `eqOn_of_isIntegralCurveOn_Icc` — two solutions with the same initial value agree there.
-/

open Set Filter Topology Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ## One short step -/

/-- On a time interval short enough that `K · h ≤ 1/2`, the Picard–Lindelöf hypotheses hold with
an explicit ball radius and bound, so a solution exists on all of `[s, s + h]`.

The radius `a = 2Mh` and bound `L = 2M` are chosen so that `mul_max_le` holds with equality:
`L · h = 2Mh = a`. `M` bounds `‖f t x₀‖` over the (compact) time interval. -/
private lemma exists_isIntegralCurveOn_Icc_of_mul_le_half
    {f : ℝ → E → E} {K : NNReal}
    (hf_cont : Continuous (Function.uncurry f))
    (hf_lip : ∀ t, LipschitzWith K (f t))
    {s h : ℝ} (hh : 0 < h) (hKh : (K : ℝ) * h ≤ 1 / 2) (x₀ : E) :
    ∃ α : ℝ → E, α s = x₀ ∧ IsIntegralCurveOn α f (Icc s (s + h)) := by
  -- `M` bounds `‖f t x₀‖` on the compact time interval.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ t ∈ Icc s (s + h), ‖f t x₀‖ ≤ M :=
    (isCompact_Icc.image_of_continuousOn
      ((hf_cont.comp (continuous_id.prodMk continuous_const)).norm.continuousOn)).bddAbove.imp
      fun _ hb _ ht => hb ⟨_, ht, rfl⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM s ⟨le_rfl, by linarith⟩)
  set a : NNReal := ⟨2 * M * h, by positivity⟩ with ha_def
  set L : NNReal := ⟨2 * M, by positivity⟩ with hL_def
  have hac : (a : ℝ) = 2 * M * h := rfl
  have hLc : (L : ℝ) = 2 * M := rfl
  have hPL : IsPicardLindelof f (tmin := s) (tmax := s + h) ⟨s, ⟨le_rfl, by linarith⟩⟩
      x₀ a 0 L K := by
    refine ⟨fun t _ => (hf_lip t).lipschitzOnWith, fun x _ => ?_, fun t ht x hx => ?_, ?_⟩
    · exact (hf_cont.comp (continuous_id.prodMk continuous_const)).continuousOn
    · -- `‖f t x‖ ≤ ‖f t x₀‖ + K‖x - x₀‖ ≤ M + K·a ≤ 2M`, using `2Kh ≤ 1`.
      have hdist : ‖x - x₀‖ ≤ (a : ℝ) := by
        rw [← dist_eq_norm]; exact mem_closedBall.mp hx
      have hlip : ‖f t x - f t x₀‖ ≤ (K : ℝ) * ‖x - x₀‖ := by
        simpa [dist_eq_norm] using (hf_lip t).dist_le_mul x x₀
      have hKa : (K : ℝ) * (a : ℝ) ≤ M := by
        rw [hac, show (K : ℝ) * (2 * M * h) = 2 * ((K : ℝ) * h) * M by ring]
        nlinarith [K.coe_nonneg]
      calc ‖f t x‖ ≤ ‖f t x - f t x₀‖ + ‖f t x₀‖ := norm_le_norm_sub_add _ _
        _ ≤ (K : ℝ) * (a : ℝ) + M := by
            gcongr
            · exact hlip.trans (by gcongr)
            · exact hM t ht
        _ ≤ M + M := by linarith
        _ = (L : ℝ) := by rw [hLc]; ring
    · have hmax : max (s + h - s) (s - s) = h := by
        rw [show s + h - s = h by ring, show s - s = (0 : ℝ) by ring]
        exact max_eq_left hh.le
      simp only [NNReal.coe_zero, sub_zero, hac, hLc, hmax]
      exact le_of_eq (by ring)
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, hα⟩

/-! ## Gluing two consecutive solution segments -/

omit [CompleteSpace E] in
/-- Two solutions on abutting intervals, agreeing at the shared endpoint, splice into a solution
on the union.

The only delicate point is the junction `b`, where the derivative is two-sided: it is obtained by
`HasDerivWithinAt.union` from the left piece on `Icc a b` and the right piece on `Icc b c`. Away
from `b` the glued function agrees with one piece on a neighbourhood, so the derivative transfers
by congruence. -/
private lemma isIntegralCurveOn_glue
    {f : ℝ → E → E} {α β : ℝ → E} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hα : IsIntegralCurveOn α f (Icc a b))
    (hβ : IsIntegralCurveOn β f (Icc b c))
    (hjoin : β b = α b) :
    IsIntegralCurveOn (fun t => if t ≤ b then α t else β t) f (Icc a c) := by
  set γ : ℝ → E := fun t => if t ≤ b then α t else β t with hγ
  -- `γ` agrees with `α` on `Iic b` and with `β` on `Icc b c` (at `b` because of `hjoin`).
  have hγα : ∀ t ≤ b, γ t = α t := fun t ht => by simp [hγ, ht]
  have hγβ : ∀ t ∈ Icc b c, γ t = β t := by
    rintro t ⟨ht, -⟩
    rcases eq_or_lt_of_le ht with rfl | hlt
    · simp [hγ, hjoin]
    · simp [hγ, not_le.mpr hlt]
  intro t ht
  rcases lt_trichotomy t b with hlt | rfl | hgt
  · -- `t < b`: `Icc a b` is a neighbourhood of `t` within `Icc a c`, and `γ = α` near `t`.
    have hsub : Icc a b ∈ 𝓝[Icc a c] t :=
      mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds hlt))
        fun y hy => ⟨hy.1.1, hy.2.le⟩
    have hd : HasDerivWithinAt α (f t (α t)) (Icc a c) t :=
      (hα t ⟨ht.1, hlt.le⟩).mono_of_mem_nhdsWithin hsub
    refine (hd.congr_of_eventuallyEq ?_ (hγα t hlt.le)).congr_deriv (by rw [hγα t hlt.le])
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hlt)] with y hy using hγα y (le_of_lt hy)
  · -- `t = b`: two-sided, one side from each piece.
    have hleft : HasDerivWithinAt γ (f t (γ t)) (Icc a t) t := by
      refine (hα t ⟨hab, le_rfl⟩).congr (fun y hy => hγα y hy.2) (hγα t le_rfl) |>.congr_deriv ?_
      rw [hγα t le_rfl]
    have hright : HasDerivWithinAt γ (f t (γ t)) (Icc t c) t := by
      refine (hβ t ⟨le_rfl, hbc⟩).congr hγβ (hγβ t ⟨le_rfl, hbc⟩) |>.congr_deriv ?_
      rw [hγβ t ⟨le_rfl, hbc⟩]
    exact (Icc_union_Icc_eq_Icc hab hbc) ▸ hleft.union hright
  · -- `t > b`: symmetric to the first case.
    have hsub : Icc b c ∈ 𝓝[Icc a c] t :=
      mem_of_superset (inter_mem_nhdsWithin _ (Ioi_mem_nhds hgt))
        fun y hy => ⟨hy.2.le, hy.1.2⟩
    have hd : HasDerivWithinAt β (f t (β t)) (Icc a c) t :=
      (hβ t ⟨hgt.le, ht.2⟩).mono_of_mem_nhdsWithin hsub
    have hγt : γ t = β t := hγβ t ⟨hgt.le, ht.2⟩
    refine (hd.congr_of_eventuallyEq ?_ hγt).congr_deriv (by rw [hγt])
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hgt)] with y hy using by
      simp [hγ, not_le.mpr (mem_Ioi.mp hy)]

/-! ## Continuation: any number of short steps -/

/-- Chaining `n + 1` short steps. Indexing by `n + 1` rather than `n` avoids the degenerate
interval `Icc s s`, on which the statement is vacuously true but awkward to prove. -/
private lemma exists_isIntegralCurveOn_Icc_succ
    {f : ℝ → E → E} {K : NNReal}
    (hf_cont : Continuous (Function.uncurry f))
    (hf_lip : ∀ t, LipschitzWith K (f t))
    {h : ℝ} (hh : 0 < h) (hKh : (K : ℝ) * h ≤ 1 / 2) :
    ∀ (n : ℕ) (s : ℝ) (x₀ : E),
      ∃ α : ℝ → E, α s = x₀ ∧ IsIntegralCurveOn α f (Icc s (s + (n + 1) * h)) := by
  intro n
  induction n with
  | zero =>
      intro s x₀
      simpa using exists_isIntegralCurveOn_Icc_of_mul_le_half hf_cont hf_lip hh hKh (s := s) x₀
  | succ m ih =>
      intro s x₀
      obtain ⟨α, hα0, hα⟩ := ih s x₀
      set b : ℝ := s + ((m : ℝ) + 1) * h with hb
      have hsb : s ≤ b := by rw [hb]; nlinarith [hh.le, Nat.cast_nonneg (α := ℝ) m]
      have hbh : b + h = s + (((m : ℝ) + 1) + 1) * h := by rw [hb]; ring
      obtain ⟨β, hβ0, hβ⟩ :=
        exists_isIntegralCurveOn_Icc_of_mul_le_half hf_cont hf_lip hh hKh (s := b) (α b)
      refine ⟨fun t => if t ≤ b then α t else β t, by simp [hsb, hα0], ?_⟩
      have hglue := isIntegralCurveOn_glue hsb (by linarith : b ≤ b + h) hα (hbh ▸ hβ) hβ0
      have hcast : s + ((↑(m + 1) : ℝ) + 1) * h = b + h := by push_cast; rw [hb]; ring
      rw [hcast]
      exact hglue

/-! ## Existence on an arbitrary compact interval -/

/-- **Picard–Lindelöf, global on a compact interval.** A continuous, globally Lipschitz
time-dependent vector field admits an integral curve through any initial condition, defined on
all of `[t₀, t₁]`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 3.2. -/
@[blueprint "thm:exists-isIntegralCurveOn-Icc"
  (title := "Picard--Lindel\\\"of on a compact interval")
  (statement := /-- Let $f : \mathbb{R} \to E \to E$ be jointly continuous and $K$-Lipschitz in
    the state variable, uniformly in time, on a Banach space $E$.  Then for every $t_0 \le t_1$
    and every $x_0 \in E$ there is an $\alpha$ with $\alpha(t_0) = x_0$ solving
    $\dot\alpha = f(t, \alpha)$ on all of $[t_0, t_1]$.

    Global — rather than merely local — Lipschitz continuity is what makes the solution reach
    $t_1$: it forces linear growth in the state, ruling out finite-time blowup. -/)
  (proof := /-- Mathlib's Picard--Lindel\"of theorem supplies a solution on a time interval of
    length $\Delta t$ only when $\|f\| \le L$ on a ball of radius $a$ about $x_0$ with
    $L\,\Delta t \le a$.  For a $K$-Lipschitz field the sharpest available bound on that ball is
    $L = M + K a$, where $M$ bounds $\|f(t, x_0)\|$, so the condition becomes
    $M\Delta t \le a(1 - K \Delta t)$ --- solvable in $a$ exactly when $K \Delta t < 1$.  One
    application therefore never covers a long interval.

    Take instead a step $h$ with $Kh \le 1/2$; then $a = 2Mh$ and $L = 2M$ satisfy the
    hypotheses, since $\|f(t,x)\| \le M + Ka = M(1 + 2Kh) \le 2M$ and $Lh = 2Mh = a$.  This gives
    a solution on $[s, s+h]$ from any initial state.  Chain $n$ such steps, splicing consecutive
    segments at their shared endpoint: away from a junction the glued curve agrees with one piece
    on a neighbourhood, and at a junction the two one-sided derivatives combine.  Choosing $n$
    with $nh \ge t_1 - t_0$ covers $[t_0, t_1]$. -/)]
theorem exists_isIntegralCurveOn_Icc
    {f : ℝ → E → E} {K : NNReal}
    (hf_cont : Continuous (Function.uncurry f))
    (hf_lip : ∀ t, LipschitzWith K (f t))
    (t₀ t₁ : ℝ) (x₀ : E) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ IsIntegralCurveOn α f (Icc t₀ t₁) := by
  -- A step short enough for the one-step lemma, and enough steps to reach `t₁`.
  set h : ℝ := 1 / (2 * ((K : ℝ) + 1)) with hh_def
  have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hh : 0 < h := by rw [hh_def]; positivity
  have hKh : (K : ℝ) * h ≤ 1 / 2 := by
    rw [hh_def, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [K.coe_nonneg]
  obtain ⟨n, hn⟩ := exists_nat_gt ((t₁ - t₀) / h)
  obtain ⟨α, hα0, hα⟩ := exists_isIntegralCurveOn_Icc_succ hf_cont hf_lip hh hKh n t₀ x₀
  refine ⟨α, hα0, hα.mono (Icc_subset_Icc le_rfl ?_)⟩
  have : t₁ - t₀ < (n : ℝ) * h := by
    rw [div_lt_iff₀ hh] at hn; linarith
  nlinarith [hh.le]

/-! ## The right-ray derivative form, and uniqueness -/

omit [CompleteSpace E] in
/-- The derivative hypothesis Mathlib's Grönwall and uniqueness results want — `HasDerivWithinAt`
on the right ray `Ici s` — from the one an integral curve on a segment supplies. Inside the
segment the two agree, because `[s, t₁)` is a neighbourhood of `s` within `Ici s`. -/
@[blueprint "lem:hasDerivWithinAt-Ici-of-isIntegralCurveOn"
  (title := "Right derivatives of an integral curve")
  (latexEnv := "lemma")
  (statement := /-- If $\alpha$ is an integral curve of $f$ on $[t_0, t_1]$, then for every
    $s \in [t_0, t_1)$ it has right derivative $f(s, \alpha(s))$ at $s$, i.e.
    $\alpha$ has derivative $f(s,\alpha(s))$ within $[s,\infty)$ at $s$. -/)]
lemma hasDerivWithinAt_Ici_of_isIntegralCurveOn
    {f : ℝ → E → E} {α : ℝ → E} {t₀ t₁ : ℝ}
    (hα : IsIntegralCurveOn α f (Icc t₀ t₁)) :
    ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt α (f s (α s)) (Ici s) s := fun s hs =>
  (hα s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin <|
    Set.ordConnected_Icc.mem_nhdsGE ⟨hs.1, hs.2.le⟩ ⟨hs.1.trans hs.2.le, le_rfl⟩ hs.2

omit [CompleteSpace E] in
/-- **Grönwall separation.** Two integral curves of a Lipschitz field separate at most
exponentially in the elapsed time. -/
@[blueprint "lem:dist-le-of-isIntegralCurveOn-Icc"
  (title := "Gronwall separation of two solutions")
  (latexEnv := "lemma")
  (statement := /-- Let $f$ be $K$-Lipschitz in the state variable, uniformly in time, and let
    $\alpha, \beta$ be integral curves of $f$ on $[t_0, t_1]$.  Then
    \[
      d(\alpha(t), \beta(t)) \le d(\alpha(t_0), \beta(t_0))\, e^{K(t - t_0)}
      \qquad \forall\, t \in [t_0, t_1].
    \]
    Uniqueness (\cref{lem:eqOn-of-isIntegralCurveOn-Icc}) is the case where the initial
    distance is zero; continuous dependence on the initial state is the statement read as a
    bound on the whole interval. -/)]
lemma dist_le_of_isIntegralCurveOn_Icc
    {f : ℝ → E → E} {K : NNReal} (hf_lip : ∀ t, LipschitzWith K (f t))
    {α β : ℝ → E} {t₀ t₁ : ℝ}
    (hα : IsIntegralCurveOn α f (Icc t₀ t₁)) (hβ : IsIntegralCurveOn β f (Icc t₀ t₁)) :
    ∀ t ∈ Icc t₀ t₁, dist (α t) (β t) ≤ dist (α t₀) (β t₀) * Real.exp (K * (t - t₀)) :=
  dist_le_of_trajectories_ODE (fun t => hf_lip t) hα.continuousOn
    (hasDerivWithinAt_Ici_of_isIntegralCurveOn hα) hβ.continuousOn
    (hasDerivWithinAt_Ici_of_isIntegralCurveOn hβ) le_rfl

omit [CompleteSpace E] in
/-- **Uniqueness.** Two integral curves of a Lipschitz field agreeing at the left endpoint agree
throughout the interval. -/
@[blueprint "lem:eqOn-of-isIntegralCurveOn-Icc"
  (title := "Uniqueness of solutions")
  (latexEnv := "lemma")
  (statement := /-- Let $f$ be $K$-Lipschitz in the state variable, uniformly in time, and let
    $\alpha, \beta$ be integral curves of $f$ on $[t_0, t_1]$ with
    $\alpha(t_0) = \beta(t_0)$.  Then $\alpha = \beta$ on $[t_0, t_1]$. -/)
  (proof := /-- The initial distance in \cref{lem:dist-le-of-isIntegralCurveOn-Icc} is zero, so
    the bound forces the distance to vanish throughout. -/)]
lemma eqOn_of_isIntegralCurveOn_Icc
    {f : ℝ → E → E} {K : NNReal} (hf_lip : ∀ t, LipschitzWith K (f t))
    {α β : ℝ → E} {t₀ t₁ : ℝ}
    (hα : IsIntegralCurveOn α f (Icc t₀ t₁)) (hβ : IsIntegralCurveOn β f (Icc t₀ t₁))
    (h₀ : α t₀ = β t₀) :
    EqOn α β (Icc t₀ t₁) := fun t ht =>
  dist_le_zero.mp <| by
    simpa [h₀] using dist_le_of_isIntegralCurveOn_Icc hf_lip hα hβ t ht

/-! ## The scalar instance, in integral form -/

/-- **Picard–Lindelöf for scalar ODEs on compact intervals.**

The form the comparison lemma consumes: a solution in the integral sense, continuous on the
closed interval, with right derivatives matching `g` on the half-open one. -/
@[blueprint "thm:exists-isIntegralSolution-Icc-of-lipschitz"
  (title := "Picard--Lindel\\\"of, scalar integral form")
  (statement := /-- Let $g : \mathbb{R} \to \mathbb{R} \to \mathbb{R}$ be jointly continuous and
    $L$-Lipschitz in its state argument, uniformly in time, and let $t_0 \le t_1$.  Then for
    every $x_0$ there is a $z$, continuous on $[t_0, t_1]$, that is an integral solution of
    $\dot z = g(t, z)$ with $z(t_0) = x_0$ and has right derivative $g(s, z(s))$ at each
    $s \in [t_0, t_1)$.

    This is the scalar specialization of \cref{thm:exists-isIntegralCurveOn-Icc}; it is the
    existence hypothesis that \cref{thm:comparison-lemma} takes as an assumption rather than
    discharging. -/)
  (proof := /-- Apply \cref{thm:exists-isIntegralCurveOn-Icc} with $E = \mathbb{R}$.  Continuity
    on $[t_0,t_1]$ is automatic for an integral curve, which converts the differential form into
    the integral one (\cref{lem:isIntegralSolution-iff-isIntegralCurveOn-Icc}); the right
    derivatives are \cref{lem:hasDerivWithinAt-Ici-of-isIntegralCurveOn}. -/)]
theorem exists_isIntegralSolution_Icc_of_lipschitz
    {g : ℝ → ℝ → ℝ} {L : NNReal}
    (hg_cont : Continuous (Function.uncurry g))
    (hg_lip : ∀ t : ℝ, LipschitzWith L (g t))
    {t₀ t₁ x₀ : ℝ} (ht : t₀ ≤ t₁) :
    ∃ z : ℝ → ℝ,
      IsIntegralSolution t₀ t₁ z x₀ g ∧
      ContinuousOn z (Icc t₀ t₁) ∧
      ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt z (g s (z s)) (Ici s) s := by
  obtain ⟨α, hα0, hα⟩ := exists_isIntegralCurveOn_Icc hg_cont hg_lip t₀ t₁ x₀
  have hcont : ContinuousOn α (Icc t₀ t₁) := hα.continuousOn
  have hFx : ContinuousOn (fun s => g s (α s)) (Icc t₀ t₁) :=
    hg_cont.comp_continuousOn (continuousOn_id.prodMk hcont)
  refine ⟨α, ?_, hcont, hasDerivWithinAt_Ici_of_isIntegralCurveOn hα⟩
  have := (isIntegralSolution_iff_isIntegralCurveOn_Icc ht hFx).mpr hα
  rwa [hα0] at this

/-! ## Existence on the forward ray -/

/-- **Picard–Lindelöf on `[t₀, ∞)`.** A continuous, globally Lipschitz field admits a forward-
complete integral curve through any initial condition, unique on the ray.

Uniqueness is stated as agreement *on `Ici t₀`* rather than as `∃!`. That is not a weakening: a
predicate built from `HasDerivWithinAt _ _ (Ici t₀)` constrains a function only on `Ici t₀`, so
two solutions may differ freely below `t₀` and `∃!` over `ℝ → E` would be false. -/
@[blueprint "thm:exists-isIntegralCurveOn-Ici"
  (title := "Picard--Lindel\\\"of on the forward ray")
  (statement := /-- Let $f$ be jointly continuous and $K$-Lipschitz in the state variable,
    uniformly in time.  Then for every $t_0$ and $x_0$ there is an $\alpha$ with
    $\alpha(t_0) = x_0$ solving $\dot\alpha = f(t,\alpha)$ on all of $[t_0,\infty)$, and any
    other such solution agrees with it on $[t_0,\infty)$.

    Uniqueness is agreement on $[t_0,\infty)$, not equality of functions: the defining condition
    says nothing about $t < t_0$, so solutions may differ there. -/)
  (proof := /-- For each $n$ take a solution $\alpha_n$ on $[t_0, t_0+n]$
    (\cref{thm:exists-isIntegralCurveOn-Icc}).  By uniqueness
    (\cref{lem:eqOn-of-isIntegralCurveOn-Icc}) these agree wherever two of them are both defined,
    so $\Phi(t) := \alpha_{\lceil t - t_0\rceil}(t)$ is well defined and agrees with $\alpha_n$ on
    all of $[t_0, t_0+n]$.  Near any $t \ge t_0$ choose $n > t - t_0$; then $[t_0, t_0+n]$ is a
    neighbourhood of $t$ within $[t_0,\infty)$ on which $\Phi = \alpha_n$, so $\Phi$ inherits the
    derivative there.  Uniqueness on the ray follows by applying the compact-interval uniqueness
    at each $n$. -/)]
theorem exists_isIntegralCurveOn_Ici
    {f : ℝ → E → E} {K : NNReal}
    (hf_cont : Continuous (Function.uncurry f))
    (hf_lip : ∀ t, LipschitzWith K (f t))
    (t₀ : ℝ) (x₀ : E) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ IsIntegralCurveOn α f (Ici t₀) ∧
      ∀ β : ℝ → E, β t₀ = x₀ → IsIntegralCurveOn β f (Ici t₀) → EqOn β α (Ici t₀) := by
  choose α hα0 hα using fun n : ℕ =>
    exists_isIntegralCurveOn_Icc hf_cont hf_lip t₀ (t₀ + n) x₀
  -- Solutions for different horizons agree as far as both are defined.
  have hmono : ∀ m n : ℕ, m ≤ n → Icc t₀ (t₀ + (m : ℝ)) ⊆ Icc t₀ (t₀ + (n : ℝ)) := fun m n hmn =>
    Icc_subset_Icc le_rfl (by have : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn; linarith)
  have hagree : ∀ m n : ℕ, m ≤ n → EqOn (α m) (α n) (Icc t₀ (t₀ + (m : ℝ))) := fun m n hmn =>
    eqOn_of_isIntegralCurveOn_Icc hf_lip (hα m) ((hα n).mono (hmono m n hmn))
      ((hα0 m).trans (hα0 n).symm)
  set Φ : ℝ → E := fun t => α ⌈t - t₀⌉₊ t with hΦ
  -- `Φ` agrees with every horizon that reaches far enough.
  have hΦeq : ∀ (n : ℕ), ∀ t ∈ Icc t₀ (t₀ + (n : ℝ)), Φ t = α n t := by
    intro n t ht
    have hle : ⌈t - t₀⌉₊ ≤ n := Nat.ceil_le.mpr (by linarith [ht.2])
    exact hagree _ n hle ⟨ht.1, by
      have := Nat.le_ceil (t - t₀); linarith⟩
  have hΦ0 : Φ t₀ = x₀ := by simp [hΦ, hα0 0]
  refine ⟨Φ, hΦ0, fun t ht => ?_, fun β hβ0 hβ t ht => ?_⟩
  · -- derivative at `t`, read off the horizon `n = ⌈t - t₀⌉ + 1`
    set n : ℕ := ⌈t - t₀⌉₊ + 1 with hn
    have htn : t < t₀ + (n : ℝ) := by
      have := Nat.le_ceil (t - t₀); push_cast [hn]; linarith
    have hmem : Icc t₀ (t₀ + (n : ℝ)) ∈ 𝓝[Ici t₀] t :=
      mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds htn)) fun y hy => ⟨hy.1, hy.2.le⟩
    have hd : HasDerivWithinAt (α n) (f t (α n t)) (Ici t₀) t :=
      (hα n t ⟨ht, htn.le⟩).mono_of_mem_nhdsWithin hmem
    have hΦt : Φ t = α n t := hΦeq n t ⟨ht, htn.le⟩
    refine (hd.congr_of_eventuallyEq ?_ hΦt).congr_deriv (by rw [hΦt])
    filter_upwards [hmem] with y hy using hΦeq n y hy
  · -- uniqueness on the ray, horizon by horizon
    set n : ℕ := ⌈t - t₀⌉₊ with hn
    have htn : t ∈ Icc t₀ (t₀ + (n : ℝ)) := ⟨ht, by have := Nat.le_ceil (t - t₀); linarith⟩
    have hβn : IsIntegralCurveOn β f (Icc t₀ (t₀ + (n : ℝ))) :=
      hβ.mono fun y hy => hy.1
    have := eqOn_of_isIntegralCurveOn_Icc hf_lip hβn (hα n) (hβ0.trans (hα0 n).symm) htn
    rw [this, ← hΦeq n t htn]

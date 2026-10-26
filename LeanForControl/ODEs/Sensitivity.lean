import LeanForControl.ODEs.PicardLindelof
import LeanForControl.Analysis.Continuity
import Mathlib.Analysis.Calculus.MeanValue
import Architect

/-!
# `ODEs.Sensitivity` — differentiability of solutions in the initial state

For an autonomous system `ż = g(z)` with `g` continuously differentiable, the solution at time `s`
depends differentiably on its initial state, and the derivative is the solution `Φ(s)` of the
*variational equation* along the base solution `γ`:
`Φ̇ = Dg(γ(s)) Φ`, `Φ(0) = I`.

A time-varying system `ẋ = f(t, x)` is covered by appending time to the state,
`z = (t, x)`, `ż = (1, f(t, x))`: the result then gives differentiability of the solution in the
initial time and the initial state together.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Section 3.3.

## Main results

* `IsIntegralCurveOn.exists_dist_le_of_contDiff` — near a solution, solutions separate at most
  exponentially: a local Lipschitz bound in the initial state.
* `IsIntegralCurveOn.exists_variational` — the variational equation has a solution.
* `IsIntegralCurveOn.exists_norm_sub_sub_variational_le` — the linearization `Φ(s) h` predicts the
  displacement of the solution to within `ε ‖h‖`, uniformly in `s`.
* `hasFDerivAt_of_isIntegralCurveOn` — the solution at time `s` is differentiable in the initial
  state, with derivative `Φ(s)`.

## The argument

All estimates are confined to the unit tube around the base solution `γ` on `[0, T]`: a compact
set, on which `Dg` is bounded (so `g` is Lipschitz there) and uniformly continuous (so the Taylor
remainder of `g` is uniformly small).  A solution starting close enough to `γ` cannot leave the
tube, by Gronwall's inequality at the first time it would.  Inside the tube, the error
`e = β - γ - Φ h` satisfies `ė = Dg(γ) e + R` with `R` a Taylor remainder, and Gronwall's
inequality bounds `e` by a small multiple of `‖h‖`.
-/

open Set Filter Topology Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Local Lipschitz bound in the initial state.**  Near a solution `γ` of `ż = g(z)` on `[0, T]`,
with `g` of class `C¹`, two solutions separate at most exponentially:
`dist (β s) (β' s) ≤ dist (β 0) (β' 0) e^{K s}` whenever both start within `ρ` of `γ(0)`. -/
@[blueprint "lem:isIntegralCurveOn-exists-dist-le-of-contDiff"
  (title := "Local Lipschitz dependence on the initial state")
  (latexEnv := "lemma")
  (statement := /-- Let $g : E \to E$ be $C^1$ on a finite-dimensional space and $\gamma$ a
    solution of $\dot z = g(z)$ on $[0, T]$.  There are $K \ge 0$ and $\rho > 0$ such that any two
    solutions $\beta, \beta'$ on $[0, T]$ starting within $\rho$ of $\gamma(0)$ satisfy
    $\|\beta(s) - \beta'(s)\| \le \|\beta(0) - \beta'(0)\|\, e^{K s}$ for $s \in [0, T]$. -/)
  (proof := /-- Let $K$ bound $\|Dg\|$ on the compact unit tube around $\gamma$, so that $g$ is
    $K$-Lipschitz on each unit ball $\overline B(\gamma(t), 1)$.  With
    $\rho = e^{-KT}/2$, a solution starting within $\rho$ of $\gamma(0)$ stays in the tube: at the
    first time it reached distance $1$ from $\gamma$, Gronwall's inequality on the tube would
    put it within $\rho e^{KT} = 1/2$.  Inside the tube, Gronwall's inequality compares any two
    such solutions. -/)]
theorem IsIntegralCurveOn.exists_dist_le_of_contDiff {g : E → E} (hg : ContDiff ℝ 1 g)
    {γ : ℝ → E} {T : ℝ} (hγ : IsIntegralCurveOn γ (fun _ => g) (Icc 0 T)) :
    ∃ K : ℝ≥0, ∃ ρ > 0, ∀ β β' : ℝ → E, IsIntegralCurveOn β (fun _ => g) (Icc 0 T) →
      IsIntegralCurveOn β' (fun _ => g) (Icc 0 T) → dist (β 0) (γ 0) < ρ →
        dist (β' 0) (γ 0) < ρ →
          ∀ s ∈ Icc 0 T, dist (β s) (β' s) ≤ dist (β 0) (β' 0) * Real.exp (K * s) := by
  -- Step 1. `g` is `K`-Lipschitz on the unit balls around the base solution.
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hγ.continuousOn).cthickening
    (r := 1) |>.exists_bound_of_continuousOn (hg.continuous_fderiv one_ne_zero).continuousOn
  set K : ℝ≥0 := M.toNNReal
  have hlip : ∀ t ∈ Icc 0 T, LipschitzOnWith K g (closedBall (γ t) 1) := fun t ht =>
    (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun u _ => hg.differentiable one_ne_zero u) fun u hu => by
        rw [← NNReal.coe_le_coe, coe_nnnorm]
        exact (hM u (closedBall_subset_cthickening (mem_image_of_mem γ ht) 1 hu)).trans
          (Real.le_coe_toNNReal M)
  -- Step 2. Gronwall's inequality for two solutions that stay in those balls up to time `τ`.
  have h_gronwall : ∀ τ ∈ Icc 0 T, ∀ β β' : ℝ → E,
      IsIntegralCurveOn β (fun _ => g) (Icc 0 T) → IsIntegralCurveOn β' (fun _ => g) (Icc 0 T) →
      (∀ u ∈ Ico 0 τ, β u ∈ closedBall (γ u) 1) → (∀ u ∈ Ico 0 τ, β' u ∈ closedBall (γ u) 1) →
        ∀ s ∈ Icc 0 τ, dist (β s) (β' s) ≤ dist (β 0) (β' 0) * Real.exp (K * s) := by
    intro τ hτ β β' hβ hβ' hβ_in hβ'_in s hs
    have hβτ := hβ.mono (Icc_subset_Icc_right hτ.2)
    have hβ'τ := hβ'.mono (Icc_subset_Icc_right hτ.2)
    simpa using dist_le_of_trajectories_ODE_of_mem (v := fun _ => g)
      (s := fun u => closedBall (γ u) 1) (fun u hu => hlip u ⟨hu.1, hu.2.le.trans hτ.2⟩)
      hβτ.continuousOn (hasDerivWithinAt_Ici_of_isIntegralCurveOn hβτ) hβ_in
      hβ'τ.continuousOn (hasDerivWithinAt_Ici_of_isIntegralCurveOn hβ'τ) hβ'_in le_rfl s hs
  -- Step 3. Trapping: a solution starting within `ρ` of `γ(0)` stays within `1` of `γ`.
  set ρ := (Real.exp (K * T))⁻¹ / 2
  have hρ : 0 < ρ := by positivity
  have h_trap : ∀ β : ℝ → E, IsIntegralCurveOn β (fun _ => g) (Icc 0 T) → dist (β 0) (γ 0) < ρ →
      ∀ s ∈ Icc 0 T, dist (β s) (γ s) < 1 := by
    intro β hβ hβ0 s hs
    have hρ_half : ρ * Real.exp (K * T) = 1 / 2 := by
      have h_ne : Real.exp (K * T) ≠ 0 := (Real.exp_pos _).ne'
      simp only [ρ]
      field_simp
    by_contra h_out
    obtain ⟨τ, hτ, hτ_eq, h_before⟩ := exists_first_sphere_hit (x_eq := (0 : E))
      (φ := fun u => β u - γ u) (hβ.continuousOn.sub hγ.continuousOn)
      (by
        rw [sub_zero, ← dist_eq_norm]
        calc dist (β 0) (γ 0) < ρ := hβ0
          _ ≤ ρ * Real.exp (K * T) := le_mul_of_one_le_right hρ.le
              (Real.one_le_exp (mul_nonneg K.coe_nonneg (hs.1.trans hs.2)))
          _ < 1 := by rw [hρ_half]; norm_num)
      hs (by rw [sub_zero, ← dist_eq_norm]; exact not_lt.mp h_out)
    have h_dist := h_gronwall τ hτ β γ hβ hγ
      (fun u hu => by
        rw [mem_closedBall, dist_eq_norm]
        simpa using h_before u (Ico_subset_Icc_self hu))
      (fun u _ => mem_closedBall_self zero_le_one) τ ⟨hτ.1, le_rfl⟩
    have h_one : dist (β τ) (γ τ) = 1 := by simpa [dist_eq_norm] using hτ_eq
    have h_half : dist (β 0) (γ 0) * Real.exp (K * τ) < 1 :=
      calc dist (β 0) (γ 0) * Real.exp (K * τ)
          < ρ * Real.exp (K * τ) := mul_lt_mul_of_pos_right hβ0 (Real.exp_pos _)
        _ ≤ ρ * Real.exp (K * T) := by
            gcongr
            exact hτ.2
        _ = 1 / 2 := hρ_half
        _ < 1 := by norm_num
    linarith
  -- Step 4. Two solutions starting within `ρ` both stay in the tube, so Step 2 applies on `[0, T]`.
  refine ⟨K, ρ, hρ, fun β β' hβ hβ' hβ0 hβ'0 s hs => ?_⟩
  exact h_gronwall T ⟨hs.1.trans hs.2, le_rfl⟩ β β' hβ hβ'
    (fun u hu => mem_closedBall.mpr (h_trap β hβ hβ0 u (Ico_subset_Icc_self hu)).le)
    (fun u hu => mem_closedBall.mpr (h_trap β' hβ' hβ'0 u (Ico_subset_Icc_self hu)).le) s hs

/-- **The variational equation has a solution.**  Along a solution `γ` of `ż = g(z)` on `[0, T]`,
the linear equation `Φ̇ = Dg(γ(s)) Φ` for an operator `Φ(s) : E →L[ℝ] E` has a solution with
`Φ(0) = I`. -/
@[blueprint "lem:isIntegralCurveOn-exists-variational"
  (title := "Existence of the variational solution")
  (latexEnv := "lemma")
  (statement := /-- Let $g : E \to E$ be $C^1$ on a finite-dimensional space and $\gamma$ a
    solution of $\dot z = g(z)$ on $[0, T]$, $T \ge 0$.  The variational equation
    $\dot\Phi = Dg(\gamma(s))\,\Phi$, $\Phi(0) = I$, has a solution on $[0, T]$. -/)
  (proof := /-- Freeze the coefficient outside $[0, T]$:
    $A(s) = Dg(\gamma(\pi(s)))$ with $\pi$ the projection onto $[0, T]$.  It is continuous and
    bounded, so $\Phi \mapsto A(s)\Phi$ is globally Lipschitz, uniformly in $s$, and
    Picard--Lindel\"of (\cref{thm:exists-isIntegralCurveOn-Icc}) gives a solution; on $[0, T]$ the
    frozen coefficient is the original one. -/)]
theorem IsIntegralCurveOn.exists_variational {g : E → E} (hg : ContDiff ℝ 1 g) {γ : ℝ → E}
    {T : ℝ} (hT : 0 ≤ T) (hγ : IsIntegralCurveOn γ (fun _ => g) (Icc 0 T)) :
    ∃ Φ : ℝ → E →L[ℝ] E, Φ 0 = ContinuousLinearMap.id ℝ E ∧
      IsIntegralCurveOn Φ (fun s X => (fderiv ℝ g (γ s)).comp X) (Icc 0 T) := by
  -- The coefficient `Dg(γ(s))`, frozen outside `[0, T]`: continuous and bounded on `ℝ`.
  set A : ℝ → E →L[ℝ] E := fun s => fderiv ℝ g (γ (projIcc 0 T hT s))
  have hA : Continuous A := (hg.continuous_fderiv one_ne_zero).comp
    (hγ.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun s => (projIcc 0 T hT s).2)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hA.continuousOn
  have h_lip : ∀ s, LipschitzWith M.toNNReal (fun X : E →L[ℝ] E => (A s).comp X) := fun s =>
    LipschitzWith.of_dist_le_mul fun X Y => by
      rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
      calc ‖(A s).comp (X - Y)‖
          ≤ ‖A s‖ * ‖X - Y‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M.toNNReal * ‖X - Y‖ := by
            gcongr
            -- `‖A s‖ = ‖A(π s)‖ ≤ M`, `π` the projection onto `[0, T]`
            exact ((show A (projIcc 0 T hT s) = A s by simp only [A, projIcc_val]) ▸
              hM (projIcc 0 T hT s) (projIcc 0 T hT s).2).trans (Real.le_coe_toNNReal M)
  obtain ⟨Φ, hΦ0, hΦ⟩ := exists_isIntegralCurveOn_Icc
    (show Continuous (Function.uncurry fun s (X : E →L[ℝ] E) => (A s).comp X) from
      (hA.comp continuous_fst).clm_comp continuous_snd) h_lip 0 T (ContinuousLinearMap.id ℝ E)
  refine ⟨Φ, hΦ0, fun s hs => ?_⟩
  change HasDerivWithinAt Φ ((fderiv ℝ g (γ s)).comp (Φ s)) (Icc 0 T) s
  rw [show fderiv ℝ g (γ s) = A s by simp only [A, projIcc_of_mem hT hs]]
  exact hΦ s hs

/-- **The linearization predicts the displacement.**  With `Φ` the variational solution along `γ`,
every solution `β` starting close enough to `γ(0)` satisfies
`‖β(s) - γ(s) - Φ(s)(β(0) - γ(0))‖ ≤ ε ‖β(0) - γ(0)‖` for all `s ∈ [0, T]`. -/
@[blueprint "thm:isIntegralCurveOn-exists-norm-sub-sub-variational-le"
  (title := "First-order sensitivity estimate")
  (statement := /-- Let $g : E \to E$ be $C^1$ on a finite-dimensional space, $\gamma$ a solution
    of $\dot z = g(z)$ on $[0, T]$, and $\Phi$ a solution of the variational equation
    $\dot\Phi = Dg(\gamma(s))\Phi$, $\Phi(0) = I$.  For every $\varepsilon > 0$ there is $\rho > 0$
    such that every solution $\beta$ on $[0, T]$ with $\|\beta(0) - \gamma(0)\| < \rho$ satisfies
    \[
      \|\beta(s) - \gamma(s) - \Phi(s)(\beta(0) - \gamma(0))\| \le
        \varepsilon\,\|\beta(0) - \gamma(0)\| \qquad \forall\, s \in [0, T].
    \]

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Section 3.3. -/)
  (proof := /-- Let $h = \beta(0) - \gamma(0)$ and $e = \beta - \gamma - \Phi h$, so $e(0) = 0$
    and
    \[
      \dot e = Dg(\gamma)\,e + \bigl(g(\beta) - g(\gamma) - Dg(\gamma)(\beta - \gamma)\bigr).
    \]
    By \cref{lem:isIntegralCurveOn-exists-dist-le-of-contDiff}, $\|\beta - \gamma\| \le \|h\|
    e^{KT}$, which is below the radius of
    \cref{thm:contDiff-exists-uniform-linearization-error-bound} for a small $\eta$; so the
    bracket is at most $\eta e^{KT}\|h\|$, and $\|Dg(\gamma)\| \le K'$.
    Gronwall's inequality gives $\|e(s)\| \le \eta e^{KT}\|h\|\, G$ with $G$ depending only on
    $K'$ and $T$; choose $\eta$ with $\eta e^{KT} G \le \varepsilon$. -/)]
theorem IsIntegralCurveOn.exists_norm_sub_sub_variational_le {g : E → E} (hg : ContDiff ℝ 1 g)
    {γ : ℝ → E} {T : ℝ} (hγ : IsIntegralCurveOn γ (fun _ => g) (Icc 0 T))
    {Φ : ℝ → E →L[ℝ] E} (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ E)
    (hΦ : IsIntegralCurveOn Φ (fun s X => (fderiv ℝ g (γ s)).comp X) (Icc 0 T))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ β : ℝ → E, IsIntegralCurveOn β (fun _ => g) (Icc 0 T) → ‖β 0 - γ 0‖ < ρ →
      ∀ s ∈ Icc 0 T, ‖β s - γ s - Φ s (β 0 - γ 0)‖ ≤ ε * ‖β 0 - γ 0‖ := by
  -- Step 1. Constants: the separation rate `K`, a bound `K'` on `Dg` along `γ`, and the
  -- Gronwall factor `G`.
  obtain ⟨K, ρ₀, hρ₀, h_sep⟩ := hγ.exists_dist_le_of_contDiff hg
  have hγC : IsCompact (γ '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hγ.continuousOn
  obtain ⟨K', hK'⟩ := hγC.exists_bound_of_continuousOn
    (hg.continuous_fderiv one_ne_zero).continuousOn
  set K'' := max K' 0
  set G := max (gronwallBound 0 K'' 1 T) 0
  set E₀ := Real.exp (K * T)
  have hE₀ : 0 < E₀ := Real.exp_pos _
  -- Step 2. The Taylor tolerance `η`, with `η E₀ G < ε`, and its radius `r`.
  set η := ε / (E₀ * G + 1)
  obtain ⟨r, hr, h_taylor⟩ :=
    hg.exists_uniform_linearization_error_bound hγC (show 0 < η from div_pos hε (by positivity))
  refine ⟨min ρ₀ (r / E₀), lt_min hρ₀ (div_pos hr hE₀), fun β hβ hβ0 s hs => ?_⟩
  have hT : 0 ≤ T := hs.1.trans hs.2
  set h := β 0 - γ 0
  -- Step 3. `β` stays within `‖h‖ E₀ < r` of `γ`.
  have h_near : ∀ u ∈ Icc 0 T, ‖β u - γ u‖ ≤ ‖h‖ * E₀ := fun u hu => by
    have h_d := h_sep β γ hβ hγ (by rw [dist_eq_norm]; exact hβ0.trans_le (min_le_left _ _))
      (by simpa using hρ₀) u hu
    rw [dist_eq_norm, dist_eq_norm] at h_d
    calc ‖β u - γ u‖ ≤ ‖h‖ * Real.exp (K * u) := h_d
      _ ≤ ‖h‖ * E₀ := mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 K.coe_nonneg)) (norm_nonneg _)
  -- Step 4. The error `e = β - γ - Φ h` and its right derivative.
  set e : ℝ → E := fun u => β u - γ u - Φ u h
  have he' : ∀ u ∈ Ico 0 T, HasDerivWithinAt e
      (g (β u) - g (γ u) - fderiv ℝ g (γ u) (Φ u h)) (Ici u) u := by
    intro u hu
    have hN : Icc 0 T ∈ 𝓝[≥] u := Icc_mem_nhdsGE_of_mem hu
    have hu' : u ∈ Icc 0 T := Ico_subset_Icc_self hu
    simpa using (((hβ u hu').mono_of_mem_nhdsWithin hN).sub
      ((hγ u hu').mono_of_mem_nhdsWithin hN)).sub
        (((hΦ u hu').mono_of_mem_nhdsWithin hN).clm_apply (hasDerivWithinAt_const u _ h))
  -- Step 5. That derivative is `Dg(γ) e` plus a Taylor remainder.
  have h_bound : ∀ u ∈ Ico 0 T, ‖g (β u) - g (γ u) - fderiv ℝ g (γ u) (Φ u h)‖ ≤
      K'' * ‖e u‖ + η * (‖h‖ * E₀) := by
    intro u hu
    have hu' : u ∈ Icc 0 T := Ico_subset_Icc_self hu
    have hγu : γ u ∈ γ '' Icc 0 T := mem_image_of_mem γ hu'
    calc ‖g (β u) - g (γ u) - fderiv ℝ g (γ u) (Φ u h)‖
        = ‖fderiv ℝ g (γ u) (e u) +
            (g (β u) - g (γ u) - fderiv ℝ g (γ u) (β u - γ u))‖ := by
          congr 1
          simp only [e, map_sub]
          abel
      _ ≤ ‖fderiv ℝ g (γ u) (e u)‖ +
            ‖g (β u) - g (γ u) - fderiv ℝ g (γ u) (β u - γ u)‖ := norm_add_le _ _
      _ ≤ K'' * ‖e u‖ + η * ‖β u - γ u‖ := by
          gcongr
          · exact (ContinuousLinearMap.le_opNorm _ _).trans
              (by gcongr; exact (hK' _ hγu).trans (le_max_left _ _))
          · exact h_taylor (γ u) hγu (β u)
              ((h_near u hu').trans_lt ((lt_div_iff₀ hE₀).mp (hβ0.trans_le (min_le_right _ _))))
      _ ≤ K'' * ‖e u‖ + η * (‖h‖ * E₀) := by
          gcongr
          exact h_near u hu'
  -- Step 6. Gronwall's inequality, from `e(0) = 0`.
  calc ‖β s - γ s - Φ s h‖
      = ‖e s‖ := rfl
    _ ≤ gronwallBound 0 K'' (η * (‖h‖ * E₀)) (s - 0) :=
        norm_le_gronwallBound_of_norm_deriv_right_le
          ((hβ.continuousOn.sub hγ.continuousOn).sub (hΦ.continuousOn.clm_apply continuousOn_const))
          he' (by simp [h, hΦ0]) h_bound s hs
    _ = η * (‖h‖ * E₀) * gronwallBound 0 K'' 1 s := by
        -- from a zero initial value, the Gronwall bound is linear in the forcing term
        rw [sub_zero]; unfold gronwallBound; split_ifs <;> ring
    _ ≤ η * (‖h‖ * E₀) * G := by
        gcongr
        exact (gronwallBound_mono le_rfl zero_le_one (le_max_right _ _) hs.2).trans
          (le_max_left _ _)
    _ = ε * ‖h‖ * (E₀ * G / (E₀ * G + 1)) := by
        simp only [η]
        field_simp
    _ ≤ ε * ‖h‖ * 1 := by
        gcongr
        exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_right zero_le_one)
    _ = ε * ‖h‖ := mul_one _

/-- **Differentiability in the initial state.**  Let `Ψ z` be a solution of `ż = g(z)` on
`[0, T]` starting at `z`, for every `z`.  Then for `s ∈ [0, T]`, `z ↦ Ψ z s` is differentiable at
`z₀`, with derivative the variational solution `Φ(s)` along `Ψ z₀`. -/
@[blueprint "thm:hasFDerivAt-of-isIntegralCurveOn"
  (title := "Differentiability of solutions in the initial state")
  (statement := /-- Let $g : E \to E$ be $C^1$ on a finite-dimensional space, and for every
    $z \in E$ let $\Psi(\cdot, z)$ be a solution of $\dot z = g(z)$ on $[0, T]$ with
    $\Psi(0, z) = z$.  Let $\Phi$ solve the variational equation along $\Psi(\cdot, z_0)$.  Then
    for $s \in [0, T]$, $z \mapsto \Psi(s, z)$ is differentiable at $z_0$ with derivative
    $\Phi(s)$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Section 3.3. -/)
  (proof := /-- \cref{thm:isIntegralCurveOn-exists-norm-sub-sub-variational-le} is the
    little-$o$ estimate defining the derivative. -/)]
theorem hasFDerivAt_of_isIntegralCurveOn {g : E → E} (hg : ContDiff ℝ 1 g) {T : ℝ}
    {Ψ : E → ℝ → E} (hΨ : ∀ z, IsIntegralCurveOn (Ψ z) (fun _ => g) (Icc 0 T))
    (hΨ0 : ∀ z, Ψ z 0 = z) {z₀ : E} {Φ : ℝ → E →L[ℝ] E}
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ E)
    (hΦ : IsIntegralCurveOn Φ (fun s X => (fderiv ℝ g (Ψ z₀ s)).comp X) (Icc 0 T))
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    HasFDerivAt (fun z => Ψ z s) (Φ s) z₀ := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
  obtain ⟨ρ, hρ, h_rem⟩ := (hΨ z₀).exists_norm_sub_sub_variational_le hg hΦ0 hΦ hε
  filter_upwards [ball_mem_nhds (0 : E) hρ] with k hk
  have h := h_rem (Ψ (z₀ + k)) (hΨ _) (by simpa [hΨ0] using hk) s hs
  rwa [hΨ0, hΨ0, add_sub_cancel_left] at h

import LeanForControl.Dini.DiniDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import LeanForControl.ODEs.ODE_properties
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.ContinuousOn

/-!
# `ODEs.ComparisonLemma`

Comparison Lemma 3.4 for scalar ODEs: if `u` is an exact solution of `u̇ = f(t, u)` with
`u(t₀) = u₀`, and `v` is continuous with upper Dini derivative satisfying
`D⁺v(t) ≤ f(t, v(t))` and `v(t₀) ≤ u₀`, then `v(t) ≤ u(t)` for all `t ∈ [t₀, t₁]`.

## Proof strategy (Appendix C.2)

* **Claim 1** (`comparison_claim_1`): For any perturbed solution `z` of `ż = f(t, z) + λ`
  with `λ > 0`, we have `v(t) ≤ z(t)` on `[t₀, t₁]`. Proved by contradiction: assuming
  the set `S = {s | v(s) = z(s)}` has a supremum `a < t_bad` (where `v(t_bad) > z(t_bad)`),
  the Dini derivative inequality at `a` forces `f(a, z(a)) + λ ≤ f(a, v(a))`, contradicting
  `v(a) = z(a)` and `λ > 0`.

* **Claim 2** (`comparison_lemma`): `v(t) ≤ u(t)` follows by sending `λ → 0`. For each
  `λ > 0`, `v(t) ≤ z_λ(t)` by Claim 1, and `z_λ(t) ≤ u(t) + ε/2` by the
  continuous-dependence estimate (Theorem 3.5). Since `ε > 0` is arbitrary, `v(t) ≤ u(t)`.

## Main declarations

* `isIntegralSolution_of_hasDerivAt` — converts a pointwise derivative condition into an
  integral solution.
* `diniDerivRight_nonneg_of_eventually_pos` — shows `D⁺w(a) ≥ 0` when `w(a) = 0` and `w`
  is immediately positive to the right of `a`.
* `comparison_claim_1` — the perturbed comparison inequality `v ≤ z_λ` for `λ > 0`.
* `comparison_lemma` — the full comparison inequality `v ≤ u`.
-/

open Set Filter Topology

/-! ## Integral solution helper -/

/-- Converts a classical (pointwise) ODE solution into an integral solution.

If `u` has derivative `f(t, u(t))` at every interior point of `[t₀, t₁]`, is continuous on
`[t₀, t₁]`, and satisfies `u(t₀) = u₀`, then `u` is an integral solution in the sense of
`IsIntegralSolution`. -/
lemma isIntegralSolution_of_hasDerivAt {f : ℝ → ℝ → ℝ} {u : ℝ → ℝ} {t₀ t₁ u₀ : ℝ}
    (hu_deriv : ∀ t ∈ Ioo t₀ t₁, HasDerivAt u (f t (u t)) t)
    (hu_cont : ContinuousOn u (Icc t₀ t₁))
    (hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hu₀      : u t₀ = u₀) :
    IsIntegralSolution t₀ t₁ u u₀ f := by
      intro s hs
      have h := hu_cont.mono (Icc_subset_Icc_right hs.2)
      linarith [hu₀, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1 h
        (fun _ hτ ↦ hu_deriv _ ⟨hτ.1, hτ.2.trans_le hs.2⟩)
        (ContinuousOn.intervalIntegrable_of_Icc hs.1 (by fun_prop))]

/-- Constant perturbation vector field `(t, x) ↦ λ`, used to form the perturbed system
`ż = f(t, z) + λ` in the proof of `comparison_claim_1`. -/
def g_lambda (lam : ℝ) (_ _ : ℝ) : ℝ := lam

/-! ## Auxiliary lemmas -/

/-- If `w(a) = 0` and `w` is eventually positive immediately to the right of `a`, and the
difference quotients `(w(a + h) - w(a)) / h` are bounded above near `h = 0⁺`, then the
upper Dini derivative at `a` is nonneg: `D⁺w(a) ≥ 0`. -/
lemma diniDerivRight_nonneg_of_eventually_pos {w : ℝ → ℝ} {a : ℝ}
    (hw0 : w a = 0)
    (hpos : ∀ᶠ h in 𝓝[>] 0, 0 < w (a + h))
    (hbdd : IsBoundedUnder (· ≤ ·) (𝓝[>] 0)
                (fun h => (w (a + h) - w a) / h)) :
    0 ≤ D⁺ w a := by
  unfold diniDerivRight
  apply le_limsup_of_frequently_le _ hbdd
  exact (hpos.and self_mem_nhdsWithin).frequently.mono fun h ⟨hwh, hh⟩ => by
    simp only [hw0, sub_zero]
    exact le_of_lt (div_pos hwh hh)

/-! ## Comparison Lemma 3.4 -/

/-- **Claim 1** of the comparison lemma: the subsolution `v` lies below every perturbed
solution `z` of `ż = f(t, z) + λ` when `λ > 0`.

Proved by contradiction. If `v(t_bad) > z(t_bad)` for some `t_bad ∈ [t₀, t₁]`, then since
`v(t₀) ≤ z(t₀) = u₀`, the intermediate value theorem gives a last crossing time
`a = sup {s ∈ [t₀, t_bad] | v(s) = z(s)}`. At `a`, the difference quotients of `v - z`
are eventually nonneg (because `v > z` on `(a, t_bad]`), so `D⁺v(a) ≥ ż(a)`. Combined with
`D⁺v(a) ≤ f(a, v(a)) = f(a, z(a))`, this gives `f(a, z(a)) + λ ≤ f(a, z(a))`,
contradicting `λ > 0`. -/
lemma comparison_claim_1
    {f : ℝ → ℝ → ℝ} {v z : ℝ → ℝ} {t₀ t₁ u₀ lam : ℝ}
    (hlam : 0 < lam)
    (ht : t₀ < t₁)
    (hz_sol : IsIntegralSolution t₀ t₁ z u₀ (fun s x => f s x + lam))
    (hz_deriv : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt z (f t (z t) + lam) (Ici t) t)
    (hv_cont : Continuous v)
    (hz_cont : ContinuousOn z (Icc t₀ t₁))
    (hDv : ∀ t ∈ Ico t₀ t₁, D⁺ v t ≤ f t (v t))
    (hv₀ : v t₀ ≤ u₀)
    (hv_bdd : ∀ t ∈ Ico t₀ t₁, IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (v (t + h) - v t) / h)) :
    ∀ t ∈ Icc t₀ t₁, v t ≤ z t := by
  by_contra h_not
  push Not at h_not
  obtain ⟨t_bad, ht_bad_mem, h_bad_ineq⟩ := h_not
  have hz₀ : z t₀ = u₀ := by
    simpa [intervalIntegral.integral_same] using hz_sol t₀ (left_mem_Icc.mpr ht.le)
  let diff s := v s - z s
  have h_cont_diff : ContinuousOn diff (Icc t₀ t_bad) :=
    hv_cont.continuousOn.sub (hz_cont.mono <| Icc_subset_Icc_right ht_bad_mem.2)
  obtain ⟨s, hs_mem, hs_eq⟩ := intermediate_value_Icc ht_bad_mem.1 h_cont_diff
    ⟨by simpa [diff, hz₀] using hv₀, le_of_lt (sub_pos.mpr h_bad_ineq)⟩
  -- `S` is the set of crossing times before `t_bad`; it is nonempty and bounded above.
  let S := { s ∈ Icc t₀ t_bad | v s = z s }
  have hS_nonempty : S.Nonempty := ⟨s, hs_mem, sub_eq_zero.mp hs_eq⟩
  have hS_bdd : BddAbove S :=  ⟨t_bad, fun s hs => hs.1.2⟩
  -- `a` is the last crossing time.
  let a := sSup S
  have ha_lub : IsLUB S a := Real.isLUB_sSup hS_nonempty hS_bdd
  have ha_le_tbad : a ≤ t_bad := ha_lub.right (fun s hs => hs.1.2)
  have ht₀_le_a : t₀ ≤ a := by
    rcases hS_nonempty with ⟨s, hs_mem⟩
    exact le_trans hs_mem.1.1 (ha_lub.left hs_mem)
  have ha_Icc : a ∈ Icc t₀ t_bad := ⟨ht₀_le_a, ha_le_tbad⟩
  -- The supremum is actually attained: `v(a) = z(a)`.
  have h_eq_a : v a = z a := by
    have hS_compact : IsCompact S := by
      haveI : CompactSpace ↥(Icc t₀ t_bad) := isCompact_iff_compactSpace.mp isCompact_Icc
      have hcont' : Continuous (fun x : ↥(Icc t₀ t_bad) => diff x.val) :=
        h_cont_diff.restrict
      have hpre : IsClosed ((fun x : ↥(Icc t₀ t_bad) => diff x.val) ⁻¹' {0}) :=
        isClosed_singleton.preimage hcont'
      have hS_eq : S = Subtype.val '' ((fun x : ↥(Icc t₀ t_bad) => diff x.val) ⁻¹' {0}) := by
        ext x
        simp only [S, Set.mem_setOf_eq, Set.mem_image, Subtype.exists,
                  Set.mem_preimage, Set.mem_singleton_iff, diff, sub_eq_zero]
        exact ⟨fun ⟨hx, heq⟩ => ⟨x, hx, heq, rfl⟩,
              fun ⟨_, hy, heq, hval⟩ => hval ▸ ⟨hy, heq⟩⟩
      rw [hS_eq]
      exact hpre.isCompact.image continuous_subtype_val
    -- compact set in ℝ attains its maximum
    obtain ⟨m, hm_mem, hm_max⟩ :=
      hS_compact.exists_isMaxOn hS_nonempty continuousOn_id
    -- m is an upper bound of S, so a ≤ m; m ∈ S so m ≤ a
    have ha_eq : a = m := le_antisymm
      (ha_lub.right (fun x hx => hm_max hx))
      (ha_lub.left hm_mem)
    exact ha_eq ▸ hm_mem.2
  have ha_lt_tbad : a < t_bad := by
    by_contra h_eq
    have ha_eq_tbad : a = t_bad := le_antisymm ha_le_tbad (not_lt.mp h_eq)
    rw [← ha_eq_tbad] at h_bad_ineq
    linarith
  have ha_mem_Ico : a ∈ Ico t₀ t₁ := ⟨ht₀_le_a, lt_of_lt_of_le ha_lt_tbad ht_bad_mem.2⟩
  -- On `(a, t_bad]`, `v` is strictly above `z` (no further crossings by maximality of `a`).
  have h_strict : ∀ t ∈ Ioc a t_bad, z t < v t := by
    intro t ht
    by_contra h_not
    push Not at h_not
    let diff := fun s => v s - z s
    have h_cont_diff : ContinuousOn diff (Icc t t_bad) := by
      have h_subset : Icc t t_bad ⊆ Icc t₀ t₁ := by
        intro x hx
        exact ⟨le_trans ht₀_le_a (le_trans (le_of_lt ht.1) hx.1), le_trans hx.2 ht_bad_mem.2⟩
      exact hv_cont.continuousOn.sub (hz_cont.mono h_subset)
    have h_zero_mem : (0 : ℝ) ∈ Icc (diff t) (diff t_bad) :=
      ⟨(sub_nonpos.mpr h_not), (le_of_lt (sub_pos.mpr h_bad_ineq))⟩
    have h_ivt := intermediate_value_Icc ht.2 h_cont_diff h_zero_mem
    obtain ⟨s, hs_mem, hs_eq_zero⟩ := h_ivt
    have hs_in_S : s ∈ S := by
      simp only [S, mem_setOf_eq]
      refine ⟨⟨le_trans ht₀_le_a (le_trans (le_of_lt ht.1) hs_mem.1), hs_mem.2⟩,
        sub_eq_zero.mp hs_eq_zero⟩
    have hs_le_a : s ≤ a := ha_lub.left hs_in_S
    have ha_lt_s : a < s := lt_of_lt_of_le ht.1 hs_mem.1
    linarith
  -- Compare the Dini derivative of `v` at `a` with the derivative of `z` at `a`.
  let q_v := fun h => (v (a + h) - v a) / h
  let q_z := fun h => (z (a + h) - z a) / h
  have h_eventual_le : ∀ᶠ h in 𝓝[>] 0, q_z h ≤ q_v h := by
    have h_nhds : Iio (t_bad - a) ∈ 𝓝 0 := Iio_mem_nhds (sub_pos.mpr ha_lt_tbad)
    filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds h_nhds)] with h h_gt0 h_lt
    have : 0 < h := h_gt0
    have : h < t_bad - a := h_lt
    apply div_le_div_of_nonneg_right
      (by rw [h_eq_a]; linarith [h_strict (a + h) ⟨by linarith, by linarith⟩])
      h_gt0.le
  have hz_lim : Tendsto q_z (𝓝[>] 0) (𝓝 (f a (z a) + lam)) := by
    have h_deriv_a := hz_deriv a ha_mem_Ico
    rw [hasDerivWithinAt_iff_tendsto_slope] at h_deriv_a
    have h_shift : Tendsto (fun h => a + h) (𝓝[>] 0) (𝓝[Ici a \ {a}] a) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h_cont : Continuous (fun h => a + h) := continuous_const.add continuous_id
        have h_tendsto_0 := h_cont.tendsto 0
        rw [add_zero] at h_tendsto_0
        exact h_tendsto_0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        rw [mem_Ioi] at hh
        simp only [mem_diff, mem_Ici, mem_singleton_iff]
        exact ⟨by linarith, by linarith⟩
    have h_comp := h_deriv_a.comp h_shift
    apply Tendsto.congr' _ h_comp
    filter_upwards with h
    dsimp [q_z]
    have h_eq : a + h - a = h := by ring
    rw [slope_def_field, h_eq]
  -- The chain of inequalities yields the contradiction `λ ≤ 0`.
  have h_chain := calc f a (z a) + lam
      _ = limsup q_z (𝓝[>] 0) := hz_lim.limsup_eq.symm
      _ ≤ limsup q_v (𝓝[>] 0) := Filter.limsup_le_limsup
        h_eventual_le hz_lim.isCoboundedUnder_le (hv_bdd a ha_mem_Ico)
      _ = D⁺ v a              := rfl
      _ ≤ f a (v a)           := hDv a ha_mem_Ico
  rw [← h_eq_a] at h_chain
  linarith

/-- **Comparison Lemma 3.4.**  If `u` solves `u̇ = f(t, u)` with `u(t₀) = u₀`, and `v` is
continuous with `D⁺v(t) ≤ f(t, v(t))` and `v(t₀) ≤ u₀`, then `v(t) ≤ u(t)` on `[t₀, t₁]`.

Hypotheses:
* `f` is jointly continuous and globally Lipschitz in the state variable on `[t₀, t₁]`.
* `u` solves the ODE classically (pointwise derivative).
* `v` satisfies the Dini subsolution inequality and has bounded difference quotients.
* For each `λ > 0`, a perturbed solution `z_λ` of `ż = f(t, z) + λ` exists on `[t₀, t₁]`
  (the existence hypothesis `hz_exists`).

The proof uses `comparison_claim_1` to get `v ≤ z_λ`, then `continuous_dependence_parameters`
(Theorem 3.5) to bound `‖u - z_λ‖ ≤ ε/2`, and concludes `v(t) < u(t) + ε` for all `ε > 0`. -/
theorem comparison_lemma
    {f : ℝ → ℝ → ℝ} {u v : ℝ → ℝ} {t₀ t₁ u₀ : ℝ} {L : ℝ}
    (ht : t₀ < t₁)
    (hL : 0 < L)
    (hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hLip     : ∀ t ∈ Icc t₀ t₁, LipschitzWith ⟨L, hL.le⟩ (f t))
    (hu_deriv : ∀ t ∈ Ioo t₀ t₁, HasDerivAt u (f t (u t)) t)
    (hu_cont  : ContinuousOn u (Icc t₀ t₁))
    (hu₀      : u t₀ = u₀)
    (hv_cont  : Continuous v)
    (hDv      : ∀ t ∈ Ico t₀ t₁, D⁺ v t ≤ f t (v t))
    (hv_bdd   : ∀ t ∈ Ico t₀ t₁,
        IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (v (t+h) - v t) / h))
    (hv₀      : v t₀ ≤ u₀)
    (hz_exists : ∀ (lam : ℝ), 0 < lam →
        ∃ z : ℝ → ℝ, IsIntegralSolution t₀ t₁ z u₀ (fun s x => f s x + lam) ∧
                     ContinuousOn z (Icc t₀ t₁) ∧
                     ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt z (f s (z s) + lam) (Ici s) s) :
    ∀ t ∈ Icc t₀ t₁, v t ≤ u t := by
  intro t ht_mem
  apply le_of_forall_pos_lt_add
  intro ε hε
  set C := (1 + 1 / L) * Real.exp (L * (t₁ - t₀)) with hC_def
  have hC : 0 < C := by positivity
  set lam := ε / 2 / C with hlam_def
  have hlam_pos : 0 < lam := div_pos (half_pos hε) hC
  have hlam_cond : lam * (1 + 1 / L) * Real.exp (L * (t₁ - t₀)) ≤ ε / 2 := by
    have hcancel : lam * C = ε / 2 := div_mul_cancel₀ _ hC.ne'
    linarith [show lam * (1 + 1 / L) * Real.exp (L * (t₁ - t₀)) = lam * C by
      rw [hC_def]; ring]
  obtain ⟨z, hz_sol, hz_cont, hz_deriv⟩ := hz_exists lam hlam_pos
  have hv_le_z : v t ≤ z t :=
    comparison_claim_1 hlam_pos ht hz_sol hz_deriv hv_cont hz_cont
      hDv hv₀ hv_bdd t ht_mem
  have hz_close : ‖u t - z t‖ ≤ ε / 2 := by
    have hu_sol : IsIntegralSolution t₀ t₁ u u₀ f :=
      isIntegralSolution_of_hasDerivAt hu_deriv hu_cont hf_cont hu₀
    have hg_cont : Continuous (fun (_ : ℝ × ℝ) => lam) := continuous_const
    have hg_bound : ∀ τ ∈ Icc t₀ t₁, ∀ x : ℝ, ‖g_lambda lam τ x‖ ≤ lam := by
      intro τ _ x
      dsimp [g_lambda]
      rw [abs_of_pos hlam_pos]
    have hz₀_bound : ‖u₀ - u₀‖ ≤ lam := by simp [hlam_pos.le]
    exact continuous_dependence_parameters (le_of_lt ht) hL hlam_pos hlam_cond
      hu_sol hz_sol hu_cont hz_cont hf_cont hg_cont hLip hg_bound hz₀_bound t ht_mem
  have hzu : z t - u t ≤ ε / 2 := by
    have h : |u t - z t| ≤ ε / 2 := by rwa [← Real.norm_eq_abs]
    linarith [(abs_le.mp h).1]
  linarith [half_lt_self hε]

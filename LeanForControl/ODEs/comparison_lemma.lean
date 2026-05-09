import LeanForControl.Dini.DiniDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import LeanForControl.ODEs.ODE_properties
import Mathlib.Topology.Order.IntermediateValue

open Set Filter Topology



lemma isIntegralSolution_of_hasDerivAt {f : ℝ → ℝ → ℝ} {u : ℝ → ℝ} {t₀ t₁ u₀ : ℝ}
    (hu_deriv : ∀ t ∈ Ioo t₀ t₁, HasDerivAt u (f t (u t)) t)
    (hu_cont : ContinuousOn u (Icc t₀ t₁))
    (hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hu₀      : u t₀ = u₀) :
    IsIntegralSolution t₀ t₁ u u₀ f := by
      intro s hs
      have h_sub : Icc t₀ s ⊆ Icc t₀ t₁ := Icc_subset_Icc_right hs.2
      have hu_cont_s : ContinuousOn u (Icc t₀ s) := hu_cont.mono h_sub
      have hf_cont_s : ContinuousOn (fun τ => f τ (u τ)) (Icc t₀ s) := by
        have h_prod : ContinuousOn (fun τ : ℝ => (τ, u τ)) (Icc t₀ s) :=
          ContinuousOn.prodMk continuousOn_id hu_cont_s
        exact hf_cont.comp_continuousOn h_prod
      have h_int : ∫ τ in t₀..s, f τ (u τ) = u s - u t₀ := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
        · exact hu_cont_s
        · intro τ hτ
          exact hu_deriv τ ⟨hτ.1, lt_of_lt_of_le hτ.2 hs.2⟩
        · exact hf_cont_s.intervalIntegrable_of_Icc hs.1
      rw [hu₀] at h_int
      linarith


def g_lambda (lam : ℝ) : ℝ → ℝ → ℝ := fun _ _ => lam

/-! ### Auxiliary lemmas needed for the comparison proof -/

/-- If w(a) = 0 and w is immediately positive to the right, then D⁺w(a) ≥ 0 -/
lemma diniDerivRight_nonneg_of_eventually_pos {w : ℝ → ℝ} {a : ℝ}
    (hw0 : w a = 0)
    (hpos : ∀ᶠ h in 𝓝[>] 0, 0 < w (a + h))
    -- need bounded ABOVE (not cobounded) for le_limsup_of_frequently_le
    (hbdd : IsBoundedUnder (· ≤ ·) (𝓝[>] 0)
                (fun h => (w (a + h) - w a) / h)) :
    0 ≤ D⁺ w a := by
  unfold diniDerivRight
  apply le_limsup_of_frequently_le _ hbdd
  have hh_pos : ∀ᶠ h in 𝓝[>] 0, (0 : ℝ) < h := self_mem_nhdsWithin
  exact (hpos.and hh_pos).frequently.mono fun h ⟨hwh, hh⟩ => by
    simp only [hw0, sub_zero]
    exact le_of_lt (div_pos hwh hh)


/-! ### Comparison Lemma 3.4 -/

/-
  Lemma 3.4 (Comparison Lemma).
  If u solves u̇ = f(t,u) with u(t₀) = u₀,
  and v is continuous with D⁺v(t) ≤ f(t,v(t)) and v(t₀) ≤ u₀,
  then v(t) ≤ u(t) on [t₀,t₁].

  Proof strategy (following Appendix C.2):
    Step 1 (Claim 1): for any perturbed solution z of ż = f(t,z) + lam (lam > 0),
                      v(t) ≤ z(t) by contradiction via D⁺ at the last crossing.
    Step 2 (Claim 2): v(t) ≤ u(t) by taking lam → 0 via Theorem 3.5.
-/

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
  -- Proof by contradiction using le_diniDerivRight_iff
  by_contra h_not
  push Not at h_not
  obtain ⟨t_bad, ht_bad_mem, h_bad_ineq⟩ := h_not
  have hz₀ : z t₀ = u₀ := by
    have h_eq := hz_sol t₀ (left_mem_Icc.mpr (le_of_lt ht))
    simp [intervalIntegral.integral_same] at h_eq
    exact h_eq
  have hvz₀ : v t₀ ≤ z t₀ := by linarith
  -- Step 2: Define the set of points before t_bad where v(t) = z(t)
  -- Because v(t₀) ≤ z(t₀) and v(t_bad) > z(t_bad), they must cross.
  let S := { s ∈ Icc t₀ t_bad | v s = z s }
  have hS_nonempty : S.Nonempty := by
    -- Define our difference function
    let diff := fun s => v s - z s
    -- Prove diff is continuous on the sub-interval [t₀, t_bad]
    have h_cont_diff : ContinuousOn diff (Icc t₀ t_bad) := by
      have h_subset : Icc t₀ t_bad ⊆ Icc t₀ t₁ := Icc_subset_Icc_right ht_bad_mem.2
      exact hv_cont.continuousOn.sub (hz_cont.mono h_subset)
    -- Establish the bounds for IVT
    have h_diff_t₀ : diff t₀ ≤ 0 := sub_nonpos.mpr hvz₀
    have h_diff_tbad : 0 ≤ diff t_bad := le_of_lt (sub_pos.mpr h_bad_ineq)
    -- 0 is in the interval [diff t₀, diff t_bad]
    have h_zero_mem : (0 : ℝ) ∈ Icc (diff t₀) (diff t_bad) := ⟨h_diff_t₀, h_diff_tbad⟩
    -- Apply the theorem!
    have h_ivt := intermediate_value_Icc ht_bad_mem.1 h_cont_diff h_zero_mem
    -- Extract the crossing point 's' from the image set
    obtain ⟨s, hs_mem_Icc, hs_eq_zero⟩ := h_ivt
    -- Plug 's' into S to prove it's nonempty
    use s
    simp only [S, mem_setOf_eq]
    refine ⟨hs_mem_Icc, ?_⟩
    exact sub_eq_zero.mp hs_eq_zero
  -- Step 3: Extract the LAST time they cross before t_bad. Let's call it 'a'.
  -- Since S is closed and bounded, it has a maximum.
  have hS_bdd : BddAbove S := by
      use t_bad
      intro s hs
      exact hs.1.2
  let a := sSup S
  have ha_lub : IsLUB S a := Real.isLUB_sSup hS_nonempty hS_bdd
  have ha_le_tbad : a ≤ t_bad := ha_lub.right (fun s hs => hs.1.2)
  have ht₀_le_a : t₀ ≤ a := by
    rcases hS_nonempty with ⟨s, hs_mem⟩
    exact le_trans hs_mem.1.1 (ha_lub.left hs_mem)
  have ha_Icc : a ∈ Icc t₀ t_bad := ⟨ht₀_le_a, ha_le_tbad⟩
  -- (Assuming you extract 'a' as the supremum of S, and prove a ∈ S)
  have h_eq_a : v a = z a := by
    let diff := fun s => v s - z s
    have h_cont_diff : ContinuousOn diff (Icc t₀ t_bad) := by
      have h_subset : Icc t₀ t_bad ⊆ Icc t₀ t₁ := Icc_subset_Icc_right ht_bad_mem.2
      exact hv_cont.continuousOn.sub (hz_cont.mono h_subset)
    have h_cont_a : ContinuousWithinAt diff (Icc t₀ t_bad) a := h_cont_diff a ha_Icc
    by_contra h_neq
    have h_pos : 0 < |diff a| := abs_pos.mpr (sub_ne_zero.mpr h_neq)
    obtain ⟨δ, hδ_pos, hδ_bound⟩ := Metric.continuousWithinAt_iff.mp h_cont_a |diff a| h_pos
    have not_upper : ¬ (∀ x ∈ S, x ≤ a - δ/2) := by
      intro h_upper
      -- Lean knows this is definitionally the same as `a - δ/2 ∈ upperBounds S`!
      have h_least := ha_lub.right h_upper
      linarith
    push Not at not_upper
    obtain ⟨s, hs_mem, hs_gt⟩ := not_upper
    have h_diff_s : diff s = 0 := sub_eq_zero.mpr hs_mem.2
    have hs_Icc : s ∈ Icc t₀ t_bad := hs_mem.1
    have hs_le_a : s ≤ a := ha_lub.left hs_mem
    have hs_dist : dist s a < δ := by
      change |s - a| < δ
      have h1 : s - a ≤ 0 := by linarith
      rw [abs_of_nonpos h1]
      linarith
    have h_contra := hδ_bound hs_Icc hs_dist
    change |diff s - diff a| < |diff a| at h_contra
    rw [h_diff_s, zero_sub, abs_neg] at h_contra
    linarith
  have ha_lt_tbad : a < t_bad := by
    by_contra h_eq
    have ha_eq_tbad : a = t_bad := le_antisymm ha_le_tbad (not_lt.mp h_eq)
    rw [← ha_eq_tbad] at h_bad_ineq
    linarith
  have ha_mem_Ico : a ∈ Ico t₀ t₁ := ⟨ht₀_le_a, lt_of_lt_of_le ha_lt_tbad ht_bad_mem.2⟩
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
    have h_diff_t : diff t ≤ 0 := sub_nonpos.mpr h_not
    have h_diff_tbad : 0 ≤ diff t_bad := le_of_lt (sub_pos.mpr h_bad_ineq)
    have h_zero_mem : (0 : ℝ) ∈ Icc (diff t) (diff t_bad) := ⟨h_diff_t, h_diff_tbad⟩
    have h_ivt := intermediate_value_Icc ht.2 h_cont_diff h_zero_mem
    obtain ⟨s, hs_mem, hs_eq_zero⟩ := h_ivt
    have hs_in_S : s ∈ S := by
      simp only [S, mem_setOf_eq]
      refine ⟨⟨le_trans ht₀_le_a (le_trans (le_of_lt ht.1) hs_mem.1), hs_mem.2⟩,
        sub_eq_zero.mp hs_eq_zero⟩
    have hs_le_a : s ≤ a := ha_lub.left hs_in_S
    have ha_lt_s : a < s := lt_of_lt_of_le ht.1 hs_mem.1
    linarith
  let q_v := fun h => (v (a + h) - v a) / h
  let q_z := fun h => (z (a + h) - z a) / h
  have h_eventual_le : ∀ᶠ h in 𝓝[>] 0, q_z h ≤ q_v h := by
    -- The interval (0, t_bad - a) is a valid right-neighborhood of 0
    have h_pos : 0 < t_bad - a := sub_pos.mpr ha_lt_tbad
    have h_nhds : Iio (t_bad - a) ∈ 𝓝 0 := Iio_mem_nhds h_pos
    have h_nhdsWithin : Iio (t_bad - a) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds h_nhds
    filter_upwards [self_mem_nhdsWithin, h_nhdsWithin]
    intro h h_gt0 h_lt
    dsimp [q_v, q_z]
    have h1 : 0 < h := h_gt0
    have h2 : h < t_bad - a := h_lt
    have hah : a + h ∈ Ioc a t_bad := ⟨by linarith, by linarith⟩
    have h_val := h_strict (a + h) hah
    rw [h_eq_a]
    apply div_le_div_of_nonneg_right
    · linarith
    · linarith
  have hz_lim : Tendsto q_z (𝓝[>] 0) (𝓝 (f a (z a) + lam)) := by
    -- 1. Extract the right derivative specifically at 'a'
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
    -- 3. Compose the derivative slope with our shift map
    have h_comp := h_deriv_a.comp h_shift
    -- 4. Clean up the denominator to perfectly match our q_z definition
    apply Tendsto.congr' _ h_comp
    filter_upwards with h
    dsimp [q_z]
    have h_eq : a + h - a = h := by ring
    rw [slope_def_field, h_eq]
  have h_D_z_a : limsup q_z (𝓝[>] 0) = f a (z a) + lam := hz_lim.limsup_eq
  have h_limsup_le : limsup q_z (𝓝[>] 0) ≤ limsup q_v (𝓝[>] 0) := by
    exact Filter.limsup_le_limsup h_eventual_le hz_lim.isCoboundedUnder_le (hv_bdd a ha_mem_Ico)
  have h_D_v_a : limsup q_v (𝓝[>] 0) = D⁺ v a := rfl
  have h_chain : f a (z a) + lam ≤ f a (v a) := by
    calc f a (z a) + lam
      _ = limsup q_z (𝓝[>] 0) := h_D_z_a.symm
      _ ≤ limsup q_v (𝓝[>] 0) := h_limsup_le
      _ = D⁺ v a              := h_D_v_a
      _ ≤ f a (v a)           := hDv a ha_mem_Ico
  rw [← h_eq_a] at h_chain
  have h_lam_nonpos : lam ≤ 0 := by linarith
  linarith


theorem comparison_lemma
    {f : ℝ → ℝ → ℝ} {u v : ℝ → ℝ} {t₀ t₁ u₀ : ℝ} {L : ℝ}
    (ht : t₀ < t₁)
    (hL : 0 < L)
    -- f is continuous in t and Lipschitz in u (locally, here global on the interval)
    (hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hLip     : ∀ t ∈ Icc t₀ t₁, LipschitzWith ⟨L, hL.le⟩ (f t))
    -- u solves u̇ = f(t,u), u(t₀) = u₀
    (hu_deriv : ∀ t ∈ Ioo t₀ t₁, HasDerivAt u (f t (u t)) t)
    (hu_cont  : ContinuousOn u (Icc t₀ t₁))
    (hu₀      : u t₀ = u₀)
    -- v is continuous with D⁺v(t) ≤ f(t,v(t))
    (hv_cont  : Continuous v)
    (hDv      : ∀ t ∈ Ico t₀ t₁, D⁺ v t ≤ f t (v t))
    -- boundedness of v's difference quotients (needed for D⁺ machinery)
    (hv_bdd   : ∀ t ∈ Ico t₀ t₁,
        IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (v (t+h) - v t) / h))
    -- initial condition
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
    -- u is (no perturbation) solution, z is IsIntegralSolution t₀ t₁ z u₀ (fun s x => f s x + lam)
    -- Construct u from hu_deriv / hu_cont / hu₀:
    have hu_sol : IsIntegralSolution t₀ t₁ u u₀ f :=
      isIntegralSolution_of_hasDerivAt hu_deriv hu_cont hf_cont hu₀
    -- have hg_cont : Continuous (fun p : ℝ × ℝ => g_lambda lam p.1 p.2) :=
    --   continuous_const
    have hg_cont : Continuous (fun (_ : ℝ × ℝ) => lam) := continuous_const
    have hg_bound : ∀ τ ∈ Icc t₀ t₁, ∀ x : ℝ, ‖g_lambda lam τ x‖ ≤ lam := by
      intro τ _ x
      dsimp [g_lambda]
      -- Since lam > 0, its norm is just itself
      rw [abs_of_pos hlam_pos]
    have hz₀_bound : ‖u₀ - u₀‖ ≤ lam := by simp [hlam_pos.le]
    exact continuous_dependence_parameters (le_of_lt ht) hL hlam_pos hlam_cond
      hu_sol hz_sol hu_cont hz_cont hf_cont hg_cont hLip hg_bound hz₀_bound t ht_mem
  have hzu : z t - u t ≤ ε / 2 := by
    have h : |u t - z t| ≤ ε / 2 := by rwa [← Real.norm_eq_abs]
    linarith [(abs_le.mp h).1]
  linarith [half_lt_self hε]

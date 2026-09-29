import LeanForControl.Dini.DiniDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import LeanForControl.ODEs.ODE_properties
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.ContinuousOn
import LeanForControl.Analysis.Continuity
import Architect

/-!
# `ODEs.ComparisonLemma`

The comparison lemma for scalar ODEs: if `u` is an exact solution of `u̇ = f(t, u)` with
`u(t₀) = u₀`, and `v` is continuous with upper Dini derivative satisfying
`D⁺v(t) ≤ f(t, v(t))` and `v(t₀) ≤ u₀`, then `v(t) ≤ u(t)` for all `t ∈ [t₀, t₁]`.

## Proof strategy (Khalil, Appendix C.2)

* **Claim 1** (`comparison_claim_1`): For any perturbed solution `z` of `ż = f(t, z) + λ`
  with `λ > 0`, we have `v(t) ≤ z(t)` on `[t₀, t₁]`. Proved by contradiction: assuming
  the set `S = {s | v(s) = z(s)}` has a supremum `a < t_bad` (where `v(t_bad) > z(t_bad)`),
  the Dini derivative inequality at `a` forces `f(a, z(a)) + λ ≤ f(a, v(a))`, contradicting
  `v(a) = z(a)` and `λ > 0`.

* **Claim 2** (`comparison_lemma`): `v(t) ≤ u(t)` follows by sending `λ → 0`. For each
  `λ > 0`, `v(t) ≤ z_λ(t)` by Claim 1, and `z_λ(t) ≤ u(t) + ε/2` by the
  continuous-dependence estimate (Khalil, Theorem 3.5). Since `ε > 0` is arbitrary,
  `v(t) ≤ u(t)`.

## Main declarations

* `isIntegralSolution_of_hasDerivAt` — converts a pointwise derivative condition into an
  integral solution.
* `comparison_lemma` — the full comparison inequality `v ≤ u`.

`comparison_claim_1` is a private step of the latter's proof.
-/

open Set Filter Topology

/-! ## Integral solution helper -/

/-- Converts a classical (pointwise) ODE solution into an integral solution.

If `u` has derivative `f(t, u(t))` at every interior point of `[t₀, t₁]`, is continuous on
`[t₀, t₁]`, and satisfies `u(t₀) = u₀`, then `u` is an integral solution in the sense of
`IsIntegralSolution`. -/
@[blueprint "lem:isIntegralSolution-of-hasDerivAt"
  (title := "Integral form from a pointwise derivative")
  (latexEnv := "lemma")
  (statement := /-- Let $u$ be continuous on $[t_0, t_1]$ with $u(t_0) = u_0$ and
    $\dot u(t) = f(t, u(t))$ at every interior point, and let $f$ be jointly continuous.  Then
    $u$ is an integral solution:
    \[
      u(s) = u_0 + \int_{t_0}^{s} f(\tau, u(\tau))\,\mathrm{d}\tau .
    \]. -/)
  (proof := /-- The fundamental theorem of calculus on $[t_0, s]$; the integrand is continuous
    there, being a composition of continuous maps. -/)]
lemma isIntegralSolution_of_hasDerivAt {f : ℝ → ℝ → ℝ} {u : ℝ → ℝ} {t₀ t₁ u₀ : ℝ}
    (ht : t₀ ≤ t₁)
    (hu_deriv : ∀ t ∈ Ioo t₀ t₁, HasDerivAt u (f t (u t)) t)
    (hu_cont : ContinuousOn u (Icc t₀ t₁))
    (hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hu₀      : u t₀ = u₀) :
    IsIntegralSolution t₀ t₁ u u₀ f := by
  unfold IsIntegralSolution
  rw [uIcc_of_le ht]
  intro s hs
  have h := hu_cont.mono (Icc_subset_Icc_right hs.2)
  linarith [hu₀, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1 h
    (fun _ hτ ↦ hu_deriv _ ⟨hτ.1, hτ.2.trans_le hs.2⟩)
    (ContinuousOn.intervalIntegrable_of_Icc hs.1 (by fun_prop))]

/-! ## The comparison lemma -/

/-- **Claim 1** of the comparison lemma: the subsolution `v` lies below every perturbed
solution `z` of `ż = f(t, z) + λ` when `λ > 0`.

Proved by contradiction. If `v(t_bad) > z(t_bad)` for some `t_bad ∈ [t₀, t₁]`, then since
`v(t₀) ≤ z(t₀) = u₀`, the intermediate value theorem gives a last crossing time
`a = sup {s ∈ [t₀, t_bad] | v(s) = z(s)}`. At `a`, the difference quotients of `v - z`
are eventually nonneg (because `v > z` on `(a, t_bad]`), so `D⁺v(a) ≥ ż(a)`. Combined with
`D⁺v(a) ≤ f(a, v(a)) = f(a, z(a))`, this gives `f(a, z(a)) + λ ≤ f(a, z(a))`,
contradicting `λ > 0`. -/
private lemma comparison_claim_1
    {f : ℝ → ℝ → ℝ} {v z : ℝ → ℝ} {t₀ t₁ u₀ lam : ℝ}
    (hlam : 0 < lam)
    (hz_sol : IsIntegralSolution t₀ t₁ z u₀ (fun s x => f s x + lam))
    (hz_deriv : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt z (f t (z t) + lam) (Ici t) t)
    (hv_cont : ContinuousOn v (Icc t₀ t₁))
    (hz_cont : ContinuousOn z (Icc t₀ t₁))
    (hDv : ∀ t ∈ Ico t₀ t₁, D⁺ v t ≤ f t (v t))
    (hv₀ : v t₀ ≤ u₀)
    (hv_bdd : ∀ t ∈ Ico t₀ t₁, IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (v (t + h) - v t) / h)) :
    ∀ t ∈ Icc t₀ t₁, v t ≤ z t := by
  by_contra h_not
  push Not at h_not
  obtain ⟨t_bad, ht_bad_mem, h_bad_ineq⟩ := h_not
  have hz₀ : z t₀ = u₀ := by
    simpa [intervalIntegral.integral_same] using hz_sol t₀ left_mem_uIcc
  let diff s := v s - z s
  have h_cont_diff : ContinuousOn diff (Icc t₀ t_bad) :=
    (hv_cont.mono <| Icc_subset_Icc_right ht_bad_mem.2).sub
      (hz_cont.mono <| Icc_subset_Icc_right ht_bad_mem.2)
  have h_start : diff t₀ ≤ 0 := by simpa [diff, hz₀] using hv₀
  have h_end : 0 < diff t_bad := sub_pos.mpr h_bad_ineq
  have ht_lt : t₀ < t_bad := lt_of_le_of_ne ht_bad_mem.1 <| by
    rintro rfl; linarith
  obtain ⟨a, ha_mem, ha_eq_zero, h_strict⟩ :=
    h_cont_diff.exists_greatest_zero_of_nonpos_of_pos ht_lt h_start h_end
  have h_eq_a : z a = v a := sub_eq_zero.mp ha_eq_zero |>.symm
  have ha_strict_v : ∀ t ∈ Ioc a t_bad, z t < v t :=
    fun t ht_mem => sub_pos.mp (h_strict t ht_mem)
  have ha_Ico : a ∈ Ico t₀ t₁ := ⟨ha_mem.1, ha_mem.2.trans_le ht_bad_mem.2⟩
  have h_dini_le := (hz_deriv a ha_Ico).le_diniDerivRight_of_upper_bound
    ha_mem.2 h_eq_a ha_strict_v (hv_bdd a ha_Ico)
  have h_chain := calc f a (z a) + lam
      _ ≤ D⁺ v a    := h_dini_le
      _ ≤ f a (v a) := hDv a ha_Ico
  rw [h_eq_a] at h_chain
  linarith

/-- **Comparison lemma.**  If `u` solves `u̇ = f(t, u)` with `u(t₀) = u₀`, and `v` is
continuous with `D⁺v(t) ≤ f(t, v(t))` and `v(t₀) ≤ u₀`, then `v(t) ≤ u(t)` on `[t₀, t₁]`.

Hypotheses:
* `f` is jointly continuous and globally Lipschitz in the state variable on `[t₀, t₁]`.
* `u` solves the ODE classically (pointwise derivative).
* `v` satisfies the Dini subsolution inequality and has bounded difference quotients.
* For each `λ > 0`, a perturbed solution `z_λ` of `ż = f(t, z) + λ` exists on `[t₀, t₁]`
  (the existence hypothesis `hz_exists`).

The proof uses `comparison_claim_1` to get `v ≤ z_λ`, then `continuous_dependence_parameters`
(Khalil, Theorem 3.5) to bound `‖u - z_λ‖ ≤ ε/2`, and concludes `v(t) < u(t) + ε` for all
`ε > 0`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 3.4. Note this is Khalil's *Lemma* 3.4;
his *Theorem* 3.4 is the continuous-dependence result `continuous_dependence_ODE`. -/
@[blueprint "thm:comparison-lemma"
  (title := "Comparison lemma")
  (statement := /-- Khalil, Lemma 3.4.  Let $f$ be jointly
    continuous and $L$-Lipschitz in its state argument on $[t_0, t_1]$, and suppose
    \begin{enumerate}
      \item $u$ is continuous on $[t_0,t_1]$ and solves $\dot u = f(t,u)$ with $u(t_0) = u_0$;
      \item $v$ is continuous on $[t_0,t_1]$ with $v(t_0) \le u_0$, satisfies the Dini
        subsolution inequality $D^{+}v(t) \le f(t, v(t))$, and has forward difference quotients
        bounded above at each $t$;
      \item for every $\lambda > 0$ the perturbed equation
        $\dot z = f(t,z) + \lambda$, $z(t_0) = u_0$, has a solution on $[t_0,t_1]$.
    \end{enumerate}
    Then $v(t) \le u(t)$ for all $t \in [t_0, t_1]$.

    The perturbed solutions in (3) are not constructed here — the caller supplies them.  They do
    exist under the hypotheses already listed, since $f + \lambda$ is Lipschitz exactly when $f$
    is, so Picard--Lindel\"of applies on $[t_0,t_1]$; but that existence step is an axiom in this
    development, and leaving it as a hypothesis is what keeps this theorem, and everything
    downstream of it, free of any axiom beyond Lean's own. -/)
  (proof := /-- Fix $\lambda > 0$ and let $z_\lambda$ be as in hypothesis (3).

    \emph{Claim: $v \le z_\lambda$ on $[t_0,t_1]$.}  Otherwise $v(t_{\mathrm{bad}}) >
    z_\lambda(t_{\mathrm{bad}})$ for some $t_{\mathrm{bad}}$, and since $v(t_0) \le
    z_\lambda(t_0)$ the continuous difference $v - z_\lambda$ has a last zero $a <
    t_{\mathrm{bad}}$, with $v > z_\lambda$ on $(a, t_{\mathrm{bad}}]$.  Being below $v$
    immediately to the right of $a$ forces $\dot z_\lambda(a) \le D^{+}v(a)$, so
    \[
      f(a, z_\lambda(a)) + \lambda \;\le\; D^{+}v(a) \;\le\; f(a, v(a)) = f(a, z_\lambda(a)),
    \]
    contradicting $\lambda > 0$.

    Now let $\varepsilon > 0$ and choose $\lambda$ small enough that
    \cref{thm:continuous-dependence-parameters} — which applies because $f$ is Lipschitz in its
    state argument, and which treats $\lambda$ as a perturbation of size $\lambda$ — gives
    $\|u - z_\lambda\| \le \varepsilon/2$ on $[t_0,t_1]$.  Then $v \le z_\lambda \le u +
    \varepsilon$.  As $\varepsilon$ was arbitrary, $v \le u$. -/)]
theorem comparison_lemma
    {f : ℝ → ℝ → ℝ} {u v : ℝ → ℝ} {t₀ t₁ u₀ : ℝ} {L : ℝ}
    (ht : t₀ < t₁)
    (hL : 0 < L)
    (hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hLip     : ∀ t ∈ Icc t₀ t₁, LipschitzWith ⟨L, hL.le⟩ (f t))
    (hu_deriv : ∀ t ∈ Ioo t₀ t₁, HasDerivAt u (f t (u t)) t)
    (hu_cont  : ContinuousOn u (Icc t₀ t₁))
    (hu₀      : u t₀ = u₀)
    (hv_cont  : ContinuousOn v (Icc t₀ t₁))
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
    comparison_claim_1 hlam_pos hz_sol hz_deriv hv_cont hz_cont
      hDv hv₀ hv_bdd t ht_mem
  have hz_close : ‖u t - z t‖ ≤ ε / 2 := by
    have hu_sol : IsIntegralSolution t₀ t₁ u u₀ f :=
      isIntegralSolution_of_hasDerivAt ht.le hu_deriv hu_cont hf_cont hu₀
    have hg_cont : Continuous (fun (_ : ℝ × ℝ) => lam) := continuous_const
    have hg_bound : ∀ τ ∈ Icc t₀ t₁, ∀ x : ℝ, ‖lam‖ ≤ lam := by
      intro τ _ x
      rw [Real.norm_eq_abs, abs_of_pos hlam_pos]
    have hz₀_bound : ‖u₀ - u₀‖ ≤ lam := by simp [hlam_pos.le]
    exact continuous_dependence_parameters (le_of_lt ht) hL hlam_pos hlam_cond
      hu_sol hz_sol hu_cont hz_cont hf_cont hg_cont hLip hg_bound hz₀_bound t ht_mem
  linarith [half_lt_self hε,
    (abs_le.mp (by rwa [← Real.norm_eq_abs] : |u t - z t| ≤ ε/2)).1]

import LeanForControl.Analysis.DiniDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import LeanForControl.ODEs.ODE_properties
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.ContinuousOn
import LeanForControl.Analysis.Continuity
import LeanForControl.Analysis.AbsolutelyContinuous
import Architect

/-!
# `ODEs.ComparisonLemma`

The comparison lemma for scalar ODEs: if `u` is an exact solution of `u̇ = f(t, u)` with
`u(t₀) = u₀`, and `v` is continuous with upper Dini derivative satisfying
`D⁺v(t) ≤ f(t, v(t))` and `v(t₀) ≤ u₀`, then `v(t) ≤ u(t)` for all `t ∈ [t₀, t₁]`.

## Proof strategy (Khalil)

* **Claim 1** (`comparison_claim_1`): For any perturbed solution `z` of `ż = f(t, z) + λ`
  with `λ > 0`, we have `v(t) ≤ z(t)` on `[t₀, t₁]`. Proved by contradiction: assuming
  the set `S = {s | v(s) = z(s)}` has a supremum `a < t_bad` (where `v(t_bad) > z(t_bad)`),
  the Dini derivative inequality at `a` forces `f(a, z(a)) + λ ≤ f(a, v(a))`, contradicting
  `v(a) = z(a)` and `λ > 0`.

* **Claim 2** (`comparison_lemma`): `v(t) ≤ u(t)` follows by sending `λ → 0`. For each
  `λ > 0`, `v(t) ≤ z_λ(t)` by Claim 1, and `z_λ(t) ≤ u(t) + ε/2` by the
  continuous-dependence estimate (`continuous_dependence_parameters`). Since `ε > 0` is arbitrary,
  `v(t) ≤ u(t)`.

## Main declarations

* `isIntegralSolution_of_hasDerivAt` — converts a pointwise derivative condition into an
  integral solution.
* `comparison_lemma` — the full comparison inequality `v ≤ u`.
* `AbsolutelyContinuousOnInterval.comparison_lemma` — the comparison lemma for absolutely
  continuous functions, with the differential inequalities holding almost everywhere.  Neither
  form implies the other: this one asks more of `v` (absolute continuity) and less of the
  inequality (almost everywhere, classical derivative) and of `f` (a one-sided Lipschitz bound
  along the two curves, no continuity).

`comparison_claim_1` is a private step of the proof of `comparison_lemma`.
-/

open Set Filter Topology MeasureTheory

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
  have hint : IntervalIntegrable (fun τ => f τ (u τ)) MeasureTheory.volume t₀ s :=
    ContinuousOn.intervalIntegrable_of_Icc hs.1 (by fun_prop)
  refine ⟨hint, ?_⟩
  linarith [hu₀, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1 h
    (fun _ hτ ↦ hu_deriv _ ⟨hτ.1, hτ.2.trans_le hs.2⟩) hint]

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
    (hv₀ : v t₀ ≤ u₀) :
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
  -- `z` touches `v` at `a` and stays below it to the right, so `ż(a) = D⁺z(a) ≤ D⁺v(a)`.
  have h_chain : ((f a (z a) + lam : ℝ) : EReal) ≤ f a (v a) := calc
    ((f a (z a) + lam : ℝ) : EReal) = D⁺ z a :=
      (diniDerivRight_of_hasDerivWithinAt (hz_deriv a ha_Ico)).symm
    _ ≤ D⁺ v a := diniDerivRight_mono h_eq_a <| Filter.mem_of_superset
      (Ioc_mem_nhdsGT ha_mem.2) fun t ht => (ha_strict_v t ht).le
    _ ≤ f a (v a) := hDv a ha_Ico
  rw [h_eq_a] at h_chain
  linarith [EReal.coe_le_coe_iff.1 h_chain]

/-- **Comparison lemma.**  If `u` solves `u̇ = f(t, u)` with `u(t₀) = u₀`, and `v` is
continuous with `D⁺v(t) ≤ f(t, v(t))` and `v(t₀) ≤ u₀`, then `v(t) ≤ u(t)` on `[t₀, t₁]`.

Hypotheses:
* `f` is jointly continuous and globally Lipschitz in the state variable on `[t₀, t₁]`.
* `u` solves the ODE classically (pointwise derivative).
* `v` satisfies the Dini subsolution inequality.
* For each `λ > 0`, a perturbed solution `z_λ` of `ż = f(t, z) + λ` exists on `[t₀, t₁]`
  (the existence hypothesis `hz_exists`, kept for generality; it is always discharged by
  `exists_isIntegralSolution_Icc_of_lipschitz`).

The proof uses `comparison_claim_1` to get `v ≤ z_λ`, then `continuous_dependence_parameters`
to bound `‖u - z_λ‖ ≤ ε/2`, and concludes `v(t) < u(t) + ε` for all `ε > 0`.

For an absolutely continuous `v` satisfying the inequality only almost everywhere, as along a
Carathéodory trajectory, see `AbsolutelyContinuousOnInterval.comparison_lemma`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), the comparison lemma. -/
@[blueprint "thm:comparison-lemma"
  (title := "Comparison lemma")
  (statement := /-- The comparison lemma of Khalil, \emph{Nonlinear Systems} (3rd ed.).  Let
    $f$ be jointly continuous and $L$-Lipschitz in its state argument on $[t_0, t_1]$, and suppose
    \begin{enumerate}
      \item $u$ is continuous on $[t_0,t_1]$ and solves $\dot u = f(t,u)$ with $u(t_0) = u_0$;
      \item $v$ is continuous on $[t_0,t_1]$ with $v(t_0) \le u_0$, satisfies the Dini
        subsolution inequality $D^{+}v(t) \le f(t, v(t))$;
      \item for every $\lambda > 0$ the perturbed equation
        $\dot z = f(t,z) + \lambda$, $z(t_0) = u_0$, has a solution on $[t_0,t_1]$.
    \end{enumerate}
    Then $v(t) \le u(t)$ for all $t \in [t_0, t_1]$.

    The perturbed solutions in (3) are taken as a hypothesis for generality, so that callers with
    solutions already in hand need not re-derive them.  Under the hypotheses already listed they
    always exist: $f + \lambda$ is Lipschitz exactly when $f$ is, so
    \cref{thm:exists-isIntegralSolution-Icc-of-lipschitz} discharges (3). -/)
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
      hDv hv₀ t ht_mem
  have hz_close : ‖u t - z t‖ ≤ ε / 2 := by
    have hu_sol : IsIntegralSolution t₀ t₁ u u₀ f :=
      isIntegralSolution_of_hasDerivAt ht.le hu_deriv hu_cont hf_cont hu₀
    have hg_cont : Continuous (fun (_ : ℝ × ℝ) => lam) := continuous_const
    have hg_bound : ∀ τ ∈ Icc t₀ t₁, ∀ x : ℝ, ‖lam‖ ≤ lam := by
      intro τ _ x
      rw [Real.norm_eq_abs, abs_of_pos hlam_pos]
    have hz₀_bound : ‖u₀ - u₀‖ ≤ lam := by simp [hlam_pos.le]
    exact continuous_dependence_parameters (K := ⟨L, hL.le⟩) (le_of_lt ht) hL hlam_cond
      hu_sol hz_sol hLip hg_bound hz₀_bound t ht_mem
  linarith [half_lt_self hε,
    (abs_le.mp (by rwa [← Real.norm_eq_abs] : |u t - z t| ≤ ε/2)).1]

/-! ## The comparison lemma for absolutely continuous functions -/

/-- **Comparison lemma, absolutely continuous form.**  Let `v` and `u` be absolutely continuous on
`[a, b]` with `v̇ ≤ f(t, v)` and `f(t, u) ≤ u̇` almost everywhere, and `v(a) ≤ u(a)`.  If `f` is
one-sided Lipschitz along the two curves, `f(t, v(t)) - f(t, u(t)) ≤ L (v(t) - u(t))` for almost
every `t` with `u(t) < v(t)`, then `v ≤ u` on `[a, b]`.

The one-sided bound holds when `f t` is `L`-Lipschitz; `L` is any real, and `f` needs no
regularity in time.  In particular `u` may be a solution, `u̇ = f(t, u)`.

This is the form that applies along Carathéodory trajectories.  The textbook form,
`comparison_lemma`, asks `v` only continuous with the Dini inequality `D⁺v ≤ f(t, v)` at every
point, and `f` continuous and Lipschitz; neither form implies the other.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), the comparison lemma, there for a continuous
`v` and the upper right Dini derivative. -/
@[blueprint "thm:absolutelyContinuousOnInterval-comparison-lemma"
  (title := "Comparison lemma for absolutely continuous functions")
  (statement := /-- Let $v, u$ be real and absolutely continuous on $[a, b]$ with
    $v(a) \le u(a)$, and let $f : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ and
    $L \in \mathbb{R}$ be such that, for almost every $t \in (a, b)$,
    \[
      v'(t) \le f(t, v(t)), \qquad f(t, u(t)) \le u'(t), \qquad
      f(t, v(t)) - f(t, u(t)) \le L\,\bigl(v(t) - u(t)\bigr) \ \text{ if } u(t) < v(t).
    \]
    Then $v(t) \le u(t)$ for all $t \in [a, b]$.

    The last condition holds when $f(t, \cdot)$ is $L$-Lipschitz.  The textbook comparison lemma
    (\cref{thm:comparison-lemma}) asks $v$ only continuous, with the Dini inequality at every
    point; neither implies the other.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), the comparison lemma. -/)
  (proof := /-- The function $w(t) = e^{-L(t - a)}(v(t) - u(t))$ is absolutely continuous with
    $w(a) \le 0$, and for almost every $t$ with $w(t) > 0$, that is, $u(t) < v(t)$,
    \[
      w'(t) = e^{-L(t-a)}\bigl(v'(t) - u'(t) - L(v(t) - u(t))\bigr)
      \le e^{-L(t-a)}\bigl(f(t, v(t)) - f(t, u(t)) - L(v(t) - u(t))\bigr) \le 0.
    \]
    By \cref{lem:absolutelyContinuousOnInterval-le-max-of-deriv-nonpos}, $w \le 0$ on $[a, b]$,
    that is, $v \le u$. -/)]
theorem AbsolutelyContinuousOnInterval.comparison_lemma {f : ℝ → ℝ → ℝ} {u v : ℝ → ℝ}
    {a b L : ℝ} (hv : AbsolutelyContinuousOnInterval v a b)
    (hu : AbsolutelyContinuousOnInterval u a b)
    (hf : ∀ᵐ t, t ∈ Ioo a b → u t < v t → f t (v t) - f t (u t) ≤ L * (v t - u t))
    (hv' : ∀ᵐ t, t ∈ Ioo a b → deriv v t ≤ f t (v t))
    (hu' : ∀ᵐ t, t ∈ Ioo a b → f t (u t) ≤ deriv u t)
    (h₀ : v a ≤ u a) :
    ∀ t ∈ Icc a b, v t ≤ u t := by
  -- `w(t) = e^{-L(t - a)} (v(t) - u(t))` starts nonpositive and cannot rise above `0`.
  have hw : AbsolutelyContinuousOnInterval
      (fun t => Real.exp (-L * (t - a)) * (v t - u t)) a b :=
    (ContDiff.contDiffOn (by fun_prop)).absolutelyContinuousOnInterval.fun_mul (hv.sub hu)
  intro t ht
  have key := hw.le_max_of_deriv_nonpos (η := 0) ?_ t ht
  · rw [sub_self, mul_zero, Real.exp_zero, one_mul, max_eq_right (sub_nonpos.2 h₀)] at key
    exact sub_nonpos.mp (nonpos_of_mul_nonpos_right key (Real.exp_pos _))
  filter_upwards [hf, hv', hu', hv.ae_differentiableAt, hu.ae_differentiableAt]
    with s hfs hvs hus hdv hdu hmem hpos
  have hmem' : s ∈ uIcc a b := Icc_subset_uIcc (Ioo_subset_Icc_self hmem)
  have hd := ((((hasDerivAt_id s).sub_const a).const_mul (-L)).exp).mul
    ((hdv hmem').hasDerivAt.sub (hdu hmem').hasDerivAt)
  rw [show deriv (fun t => Real.exp (-L * (t - a)) * (v t - u t)) s = _ from hd.deriv]
  have hvu : 0 < v s - u s := pos_of_mul_pos_right hpos (Real.exp_pos _).le
  have h_rate : deriv v s - deriv u s - L * (v s - u s) ≤ 0 := by
    linarith [hfs hmem (sub_pos.1 hvu), hvs hmem, hus hmem]
  simp only [id, mul_one, Pi.sub_apply]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-L * (s - a))).le h_rate]

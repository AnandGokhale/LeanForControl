import LeanForControl.Analysis.OmegaLimit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import LeanForControl.Stability.DefsAutonomous
import LeanForControl.Stability.Continuous.Bridges
import LeanForControl.ODEs.PicardLindelof
import Architect

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-!
# `Stability.LaSalle`

LaSalle's invariance principle and its corollaries (Barbashin–Krasovskii theorems).

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.1 and Theorem 4.4.

## Main results

* `omegaLimitSet` and `mem_omegaLimitSet_iff` — the ω-limit set of a trajectory.
* `isPositivelyInvariant_omegaLimitTraj` — it is positively invariant (Khalil, Lemma 4.1).
* `lieDeriv_eq_zero_on_omegaLimitTraj` — `V̇` vanishes on it, i.e. `ω(φ) ⊆ E`.
* `lasalle_invariance_principle` — `φ(t) → M` for any `M` absorbing the positively invariant
  subsets of `E = LieDerivZeroSet f V Ω`.
* `lasalle_local_asymptotic_stable` (Barbashin's theorem) — local asymptotic stability
  via a compact sublevel set and LaSalle.
* `lasalle_global_asymptotic_stable` (Krasovskii's theorem) — global asymptotic stability
  when `V` is radially unbounded and `V̇ ≤ 0` everywhere.

## Proof strategy

1. `V ∘ φ` is antitone on `[0, ∞)`, since the Lie derivative is `≤ 0` on `Ω`.
2. `V(φ t) → L` by monotone convergence, `V` being bounded below on the compact `Ω`.
3. `V = L` on `ω(φ)`, by continuity and a cluster-point argument.
4. `ω(φ) ⊆ Ω`, since `Ω` is closed and `φ` stays in `Ω`.
5. `ω(φ)` is positively invariant — the one step that needs uniqueness of solutions, supplied
   here by a Grönwall comparison rather than by a globally defined flow. Steps 3 and 5 together
   force `V̇ = 0` on `ω(φ)`, so `ω(φ) ⊆ E`.
6. `φ t → ω(φ) ⊆ M` via the open-neighbourhood criterion for compact absorbing sets.

## Hypotheses that go beyond Khalil

`f` is assumed globally `LipschitzWith` (for uniqueness, via `dist_le_of_trajectories_ODE`) and
`ContDiff ℝ 1` (for existence of a solution through each ω-limit point). Khalil assumes only
that `f` is locally Lipschitz; trajectories here stay in the compact `Ω`, so a local hypothesis
should suffice, but the Grönwall tool in use takes a global one.

Invariance of `ω(φ)` is proved in the *forward* direction only. Khalil's `M` is the largest
invariant subset of `E`; `M` here must absorb every *positively* invariant subset, a larger
family, so the hypothesis on `M` is correspondingly stronger.
-/

open Filter Set Topology
open scoped Pointwise

/-! ## Invariance of the ω-limit set -/

/-- **The ω-limit set of a trajectory is positively invariant** (Khalil, Lemma 4.1).

This is the step that makes LaSalle's principle a theorem about Lyapunov functions rather than
a fact about compact sets: it is what turns `V ≡ a` on `ω(φ)` into `V̇ = 0` on `ω(φ)`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.1. -/
@[blueprint "lem:isPositivelyInvariant-omegaLimitSet"
  (title := "The $\\omega$-limit set is positively invariant")
  (latexEnv := "lemma")
  (statement := /-- Let $f$ be Lipschitz and let $\varphi$ be a solution of $\dot{x} = f(x)$ on
    $[0,\infty)$.  Then the $\omega$-limit set $\omega(\varphi)$ (\cref{def:omegaLimitSet}) is
    positively invariant (\cref{def:isPositivelyInvariant}): every solution segment starting in
    $\omega(\varphi)$ remains in $\omega(\varphi)$.

    Neither boundedness of $\varphi$ nor compactness of an enclosing set is needed; those
    hypotheses of Khalil's Lemma 4.1 are what make $\omega(\varphi)$ nonempty and compact, not
    what make it invariant. -/)
  (proof := /-- Let $\psi$ solve the equation on $[t_0, t_1]$ with $p = \psi(t_0) \in
    \omega(\varphi)$, and fix $t \in [t_0, t_1]$.  Given $\varepsilon > 0$, put
    $C = e^{K(t_1 - t_0)}$ and pick, by the definition of the $\omega$-limit set, arbitrarily
    large $r$ with $\|\varphi(r) - p\| < \varepsilon / C$.  The time-shifted curve
    $u(\cdot) = \varphi(\cdot + r - t_0)$ solves the same autonomous equation on $[t_0, t_1]$ and
    satisfies $u(t_0) = \varphi(r)$, so Grönwall gives
    \[
      \|\varphi(r + t - t_0) - \psi(t)\| = \|u(t) - \psi(t)\|
        \le \|\varphi(r) - p\|\, e^{K(t - t_0)} < \varepsilon .
    \]
    Since $r$ may be taken arbitrarily large, so may $r + t - t_0$; hence $\varphi$ is frequently
    within $\varepsilon$ of $\psi(t)$, i.e. $\psi(t) \in \omega(\varphi)$.

    Khalil argues instead with the flow map and the semigroup identity
    $\phi(t + t_i; x_0) = \phi(t; \phi(t_i; x_0))$, which presumes a globally defined flow.
    Comparing the two solutions directly needs only uniqueness, in its quantitative Grönwall
    form. -/)]
theorem isPositivelyInvariant_omegaLimitTraj
    {f : ℝⁿ → ℝⁿ} {K : NNReal} (hf : LipschitzWith K f)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici 0)) :
    IsPositivelyInvariant (omegaLimitSet φ) f := by
  intro t₀ t₁ ψ hψ hψ0 t ht
  rw [mem_omegaLimitSet_iff] at hψ0 ⊢
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  -- Shrink `ε` by the worst-case Grönwall amplification over the whole segment.
  set C : ℝ := Real.exp (K * (t₁ - t₀)) with hC_def
  have hC_pos : 0 < C := Real.exp_pos _
  have hfreq := hψ0 (Metric.ball (ψ t₀) (ε / C)) (Metric.ball_mem_nhds _ (div_pos hε hC_pos))
  rw [Filter.frequently_atTop] at hfreq ⊢
  intro a
  obtain ⟨r, hr_ge, hr⟩ := hfreq (max a 0)
  have hr0 : (0 : ℝ) ≤ r := (le_max_right a 0).trans hr_ge
  -- The trajectory restarted at time `r`, re-anchored to `t₀`.
  have hu : IsIntegralCurveOn (fun s => φ (s + (r - t₀))) (fun _ x => f x) (Set.Icc t₀ t₁) := by
    refine (hφ.comp_add_autonomous (r - t₀)).mono fun s hs => ?_
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg, Set.mem_Ici]
    linarith [hs.1]
  have hcmp := dist_le_of_isIntegralCurveOn_Icc (fun _ => hf) hu hψ t ht
  simp only [show t₀ + (r - t₀) = r by ring] at hcmp
  refine ⟨r + (t - t₀), by linarith [(le_max_left a 0).trans hr_ge, ht.1], hball ?_⟩
  have hexp : Real.exp (K * (t - t₀)) ≤ C := by
    rw [hC_def]
    exact Real.exp_le_exp.mpr (by nlinarith [K.coe_nonneg, ht.1, ht.2])
  have : dist (φ (r + (t - t₀))) (ψ t) < ε := by
    calc dist (φ (r + (t - t₀))) (ψ t)
        = dist (φ (t + (r - t₀))) (ψ t) := by rw [show r + (t - t₀) = t + (r - t₀) by ring]
      _ ≤ dist (φ r) (ψ t₀) * Real.exp (K * (t - t₀)) := hcmp
      _ ≤ dist (φ r) (ψ t₀) * C := mul_le_mul_of_nonneg_left hexp dist_nonneg
      _ < (ε / C) * C := mul_lt_mul_of_pos_right (Metric.mem_ball.mp hr) hC_pos
      _ = ε := div_mul_cancel₀ ε hC_pos.ne'
  exact Metric.mem_ball.mpr this

/-! ## Trajectories stay in a positively invariant set -/

/-- A solution on `[0, ∞)` that starts in a positively invariant `Ω` stays in `Ω` for all
    `t ≥ 0`: apply the invariance hypothesis to the segment `[0, t]`. -/
private lemma mem_of_isPositivelyInvariant_Ici
    {f : ℝⁿ → ℝⁿ} {Ω : Set ℝⁿ} (hΩ_inv : IsPositivelyInvariant Ω f)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici 0)) (hφ0 : φ 0 ∈ Ω) :
    ∀ t ≥ 0, φ t ∈ Ω := fun t ht =>
  hΩ_inv 0 t φ (hφ.mono (fun _ hr => hr.1)) hφ0 t ⟨ht, le_rfl⟩

/-! ## Lemma 1: V antitone on [0,∞) along trajectories -/

/-- `V(φ t)` is antitone on `[0, ∞)` when the Lie derivative `V̇ ≤ 0` on `Ω` and `φ` stays
    in `Ω`. -/
private lemma V_antitoneOn_lasalle
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω : Set ℝⁿ}
    (hV_c1 : ContDiff ℝ 1 V)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici 0))
    (hphi : ∀ t ≥ 0, φ t ∈ Ω) :
    AntitoneOn (V ∘ φ) (Set.Ici 0) :=
  antitoneOn_V_comp_traj (hV_c1.differentiable (by norm_num)) hV_c1.continuous
    (convex_Ici (0 : ℝ)) hφ fun t ht => by
      rw [interior_Ici] at ht
      exact hLie (φ t) (hphi t (le_of_lt ht))

/-! ## Lemma 2: V(φ t) converges to its infimum -/

/-- If `Ω` is compact and positively invariant and the Lie derivative `V̇ ≤ 0` on `Ω`,
    then `V(φ t)` converges to some limit `L` as `t → ∞`. -/
private lemma lasalle_V_tendsto
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω : Set ℝⁿ}
    (hV_c1 : ContDiff ℝ 1 V)
    (hΩ_compact : IsCompact Ω)
    (hΩ_inv : IsPositivelyInvariant Ω f)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici 0)) (hφ0 : φ 0 ∈ Ω) :
    ∃ L, Filter.Tendsto (V ∘ φ) Filter.atTop (nhds L) := by
  -- φ stays in Ω for all t ≥ 0
  have hphi : ∀ t ≥ 0, φ t ∈ Ω := mem_of_isPositivelyInvariant_Ici hΩ_inv hφ hφ0
  -- V(φ t) is antitone on [0, ∞)
  have hanti : AntitoneOn (V ∘ φ) (Set.Ici 0) := V_antitoneOn_lasalle hV_c1 hLie hφ hphi
  -- Ω is compact so V attains its minimum on Ω, giving a lower bound
  have hΩ_nonempty : Ω.Nonempty := ⟨φ 0, hφ0⟩
  have hV_cont : Continuous V := hV_c1.continuous
  obtain ⟨x_min, _, hx_min_le⟩ := hΩ_compact.exists_isMinOn hΩ_nonempty hV_cont.continuousOn
  -- Extend to globally antitone function via max trick
  set g : ℝ → ℝ := fun t => (V ∘ φ) (max t 0) with hg_def
  have hg_anti : Antitone g := fun s t hst =>
    hanti (Set.mem_Ici.mpr (le_max_right s 0)) (Set.mem_Ici.mpr (le_max_right t 0))
      (max_le_max_right 0 hst)
  -- V is bounded below on Ω, so V(φ t) ≥ V(x_min) for all t ≥ 0
  have hg_bdd : BddBelow (Set.range g) :=
    ⟨V x_min, fun _ ⟨t, ht⟩ => ht ▸ hx_min_le (hphi (max t 0) (le_max_right t 0))⟩
  set L := ⨅ t, g t
  have hg_tendsto : Filter.Tendsto g Filter.atTop (nhds L) :=
    tendsto_atTop_ciInf hg_anti hg_bdd
  -- The tendsto for g agrees with V ∘ φ for large t
  have hgL_eq : ∀ t ≥ (0 : ℝ), g t = (V ∘ φ) t := fun t ht => by
    simp [hg_def, max_eq_left ht]
  exact ⟨L, hg_tendsto.congr' ((Filter.eventually_ge_atTop 0).mono fun t ht => hgL_eq t ht)⟩

/-! ## Lemma 4: omegaLimitSet(φ) ⊆ Ω when Ω is compact and positively invariant -/

/-- If `Ω` is compact, positively invariant, and `φ 0 ∈ Ω`, then `ω(φ) ⊆ Ω`. -/
private lemma omegaLimit_subset_of_invariant
    {f : ℝⁿ → ℝⁿ} {Ω : Set ℝⁿ}
    (hΩ_compact : IsCompact Ω)
    (hΩ_inv : IsPositivelyInvariant Ω f)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici 0)) (hφ0 : φ 0 ∈ Ω) :
    omegaLimitSet φ ⊆ Ω :=
  omegaLimitSet_subset_of_eventually_mem hΩ_compact.isClosed
    ((Filter.eventually_ge_atTop 0).mono fun t ht =>
      mem_of_isPositivelyInvariant_Ici hΩ_inv hφ hφ0 t ht)

/-! ## Lemma 5: the Lie derivative vanishes on the ω-limit set -/

/-- **`V̇ = 0` on `ω(φ)`.** This is where the four preceding lemmas combine: `V(φ t)` converges
    to some `L`, so `V ≡ L` on `ω(φ)`; `ω(φ)` is positively invariant, so the solution through
    an ω-limit point stays in `ω(φ)`, where `V` is constant; hence its derivative — which is
    exactly the Lie derivative `DV(y)[f(y)]` — vanishes.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), proof of Theorem 4.4. -/
@[blueprint "lem:lieDeriv-eq-zero-on-omegaLimitSet"
  (title := "The Lie derivative vanishes on the $\\omega$-limit set")
  (latexEnv := "lemma")
  (statement := /-- Let $\Omega$ be compact and positively invariant for $\dot{x} = f(x)$ with
    $f$ of class $C^{1}$ and Lipschitz, let $V \in C^{1}$ satisfy $\dot{V} \le 0$ on $\Omega$,
    and let $\varphi$ be a solution on $[0,\infty)$ with $\varphi(0) \in \Omega$.  Then
    \[
      \dot{V}(y) = DV(y)\,[\,f(y)\,] = 0
      \qquad \text{for every } y \in \omega(\varphi).
    \]
    Equivalently $\omega(\varphi) \subseteq E = \{x : \dot{V}(x) = 0\}$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), proof of Theorem 4.4.
  -/)
  (proof := /-- Along the trajectory $V$ is nonincreasing and bounded below on the compact set
    $\Omega$, so $V(\varphi(t)) \to L$ for some $L$; by continuity of $V$ every
    $\omega$-limit point sees that same value, so $V \equiv L$ on $\omega(\varphi)$.  Fix
    $y \in \omega(\varphi)$ and let $\psi$ solve $\dot{x} = f(x)$ on $[0,T]$, $T > 0$, with
    $\psi(0) = y$; such a $\psi$ exists because $f$ is $C^{1}$.  By
    \cref{lem:isPositivelyInvariant-omegaLimitSet} the whole segment $\psi([0,T])$ lies in
    $\omega(\varphi)$, so $V \circ \psi \equiv L$ there.  A constant function has vanishing
    derivative, and the chain rule identifies that derivative at $0$ with
    $DV(\psi(0))[\dot\psi(0)] = DV(y)[f(y)]$.  Uniqueness of the derivative within $[0,T]$ at
    its left endpoint (valid because $T > 0$) gives $DV(y)[f(y)] = 0$. -/)]
theorem lieDeriv_eq_zero_on_omegaLimitTraj
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω : Set ℝⁿ} {K : NNReal}
    (hf_lip : LipschitzWith K f) (hf_c1 : ContDiff ℝ 1 f)
    (hV_c1 : ContDiff ℝ 1 V)
    (hΩ_compact : IsCompact Ω)
    (hΩ_inv : IsPositivelyInvariant Ω f)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici 0)) (hφ0 : φ 0 ∈ Ω) :
    ∀ y ∈ omegaLimitSet φ, fderiv ℝ V y (f y) = 0 := by
  obtain ⟨L, hVL⟩ := lasalle_V_tendsto hV_c1 hΩ_compact hΩ_inv hLie hφ hφ0
  have hVconst : ∀ y ∈ omegaLimitSet φ, V y = L := fun _ hy =>
    eq_of_tendsto_of_mem_omegaLimitSet hV_c1.continuous hVL hy
  have hinv := isPositivelyInvariant_omegaLimitTraj hf_lip hφ
  intro y hy
  -- A solution through `y`, which stays in `ω(φ)` by invariance.
  obtain ⟨T, ψ, hT, hψ0, hψ⟩ := (hf_c1.contDiffAt (x := y)).exists_isIntegralCurveOn_Icc
  have hψ_mem : ∀ s ∈ Set.Icc 0 T, ψ s ∈ omegaLimitSet φ :=
    hinv 0 T ψ hψ (hψ0 ▸ hy)
  -- `V ∘ ψ` is therefore constantly `L` on `[0, T]`, so its derivative at `0` is `0`.
  have hconst : ∀ s ∈ Set.Icc 0 T, (V ∘ ψ) s = L := fun s hs => hVconst _ (hψ_mem s hs)
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have hchain : HasDerivWithinAt (V ∘ ψ) (fderiv ℝ V (ψ 0) (f (ψ 0))) (Set.Icc 0 T) 0 :=
    (hV_c1.differentiable (by norm_num) (ψ 0)).hasFDerivAt.comp_hasDerivWithinAt 0 (hψ 0 hmem0)
  rw [hψ0] at hchain
  have hzero : HasDerivWithinAt (V ∘ ψ) 0 (Set.Icc 0 T) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) _ L).congr hconst (hconst 0 hmem0)
  exact (uniqueDiffOn_Icc hT 0 hmem0).eq_deriv _ hchain hzero

/-! ## Main theorem: LaSalle's invariance principle -/

/-- `E = {x ∈ Ω | V̇(x) = 0}`, the set where the Lie derivative of `V` along `f` vanishes.

LaSalle's principle localizes a trajectory's limiting behaviour inside this set: `V̇ ≤ 0` on `Ω`
says `V` never increases, and `E` is where it momentarily stops decreasing.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.4, where it is the set `E`. -/
@[blueprint "def:lieDerivZeroSet"
  (title := "The set where the Lie derivative vanishes")
  (statement := /-- For $\dot{x} = f(x)$, a function $V$ and a set $\Omega$, put
    \[
      E = \{x \in \Omega : \dot{V}(x) = DV(x)\,[\,f(x)\,] = 0\},
    \]
    the subset of $\Omega$ on which the Lie derivative of $V$ along $f$ vanishes.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.4, where it is the set $E$.
  -/)]
def LieDerivZeroSet (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (Ω : Set ℝⁿ) : Set ℝⁿ :=
  {x ∈ Ω | fderiv ℝ V x (f x) = 0}

/-- LaSalle's invariance principle.

Let Ω be compact and positively invariant for ẋ = f(x), V : ℝⁿ → ℝ a C¹ Lyapunov function
with V̇(x) = DV(x)[f(x)] ≤ 0 on Ω, and M any set large enough to contain every positively
invariant subset of `LieDerivZeroSet f V Ω`. Then φ(t) → M.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.4. -/
@[blueprint "thm:lasalle-invariance-principle"
  (title := "LaSalle's invariance principle")
  (statement := /-- Let $\Omega$ be compact and positively invariant for $\dot{x} = f(x)$ with $f$
    of class
    $C^{1}$ and Lipschitz, let $V \in C^{1}$ satisfy $\dot{V}(x) \le 0$ on $\Omega$, and put
    \[
      E = \{x \in \Omega : \dot{V}(x) = 0\}
    \]
    (\cref{def:lieDerivZeroSet}).  Let $M$ contain every positively invariant subset of $E$.
    Then every trajectory $\varphi$ on $[0,\infty)$ starting in $\Omega$ satisfies
    $\varphi(t) \to M$ as $t \to \infty$.

    Khalil takes $M$ to be the largest \emph{invariant} subset of $E$.  Here $M$ must absorb
    every \emph{positively} invariant subset, which is a larger family, so the hypothesis on
    $M$ is correspondingly stronger; what is proved about $\omega(\varphi)$ is forward
    invariance (\cref{lem:isPositivelyInvariant-omegaLimitSet}), and backward invariance would
    require solutions through every $\omega$-limit point to extend backwards in time.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.4.
  -/)
  (proof := /-- The $\omega$-limit set lies in $\Omega$, because $\Omega$ is closed and
    $\varphi$ stays in it, and $\dot{V}$ vanishes on it
    (\cref{lem:lieDeriv-eq-zero-on-omegaLimitSet}); hence
    $\omega(\varphi) \subseteq E$.  It is positively invariant by
    \cref{lem:isPositivelyInvariant-omegaLimitSet}, so the hypothesis on $M$ gives
    $\omega(\varphi) \subseteq M$.  Finally, a trajectory confined to a compact set converges
    to its own $\omega$-limit set: for any open $W \supseteq M \supseteq \omega(\varphi)$,
    $\varphi$ is eventually in $W$. -/)]
theorem lasalle_invariance_principle
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω M : Set ℝⁿ} {K : NNReal}
    (hΩ_compact : IsCompact Ω)
    (hΩ_inv : IsPositivelyInvariant Ω f)
    (hf_lip : LipschitzWith K f)
    (hf_c1 : ContDiff ℝ 1 f)
    (hV_c1 : ContDiff ℝ 1 V)
    -- V̇(x) = DV(x)[f(x)] ≤ 0 on Ω
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici 0)) (hφ0 : φ 0 ∈ Ω)
    -- `M` is any set absorbing the positively invariant subsets of `E = {x ∈ Ω | V̇ x = 0}`.
    (hM : ∀ N ⊆ LieDerivZeroSet f V Ω, IsPositivelyInvariant N f → N ⊆ M) :
    Filter.Tendsto φ Filter.atTop (𝓝ˢ M) := by
  -- ω(φ) ⊆ E: it lies in Ω, and V̇ vanishes on it.
  have hω_sub_E : omegaLimitSet φ ⊆ LieDerivZeroSet f V Ω := fun y hy =>
    ⟨omegaLimit_subset_of_invariant hΩ_compact hΩ_inv hφ hφ0 hy,
      lieDeriv_eq_zero_on_omegaLimitTraj hf_lip hf_c1 hV_c1 hΩ_compact hΩ_inv hLie hφ hφ0 y hy⟩
  -- ω(φ) is positively invariant, so `M` absorbs it.
  have hω_sub_M : omegaLimitSet φ ⊆ M :=
    hM _ hω_sub_E (isPositivelyInvariant_omegaLimitTraj hf_lip hφ)
  -- φ stays in Ω for t ≥ 0
  have hphi_in_Ω : ∀ t ≥ 0, φ t ∈ Ω := mem_of_isPositivelyInvariant_Ici hΩ_inv hφ hφ0
  exact tendsto_nhdsSet_of_omegaLimitSet_subset hΩ_compact
    ((Filter.eventually_ge_atTop 0).mono fun t ht => hphi_in_Ω t ht) hω_sub_M

/-! ## Barbashin–Krasovskii theorems -/

/-- **Re-anchoring at `0`.** A solution on `[t₀, ∞)`, shifted to `s ↦ φ (s + t₀)`, is a solution
    on `[0, ∞)` — where the LaSalle machinery above is stated. -/
private lemma isIntegralCurveOn_Ici_zero_of_shift
    {f : ℝⁿ → ℝⁿ} {φ : ℝ → ℝⁿ} {t₀ : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Set.Ici t₀)) :
    IsIntegralCurveOn (fun s => φ (s + t₀)) (fun _ x => f x) (Set.Ici 0) := by
  have hset : -t₀ +ᵥ Set.Ici t₀ = Set.Ici (0 : ℝ) := by
    ext x
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg, Set.mem_Ici]
    constructor <;> intro h <;> linarith
  have hshift := hφ.comp_add_autonomous t₀
  rwa [hset] at hshift

/-- **Undoing the re-anchoring.** If the shifted solution `s ↦ φ (s + t₀)` converges to `y`, so
    does `φ` itself. -/
private lemma tendsto_of_tendsto_shift
    {φ : ℝ → ℝⁿ} {t₀ : ℝ} {y : ℝⁿ}
    (hshift : Filter.Tendsto (fun s => φ (s + t₀)) Filter.atTop (𝓝 y)) :
    Filter.Tendsto φ Filter.atTop (𝓝 y) :=
  Filter.Tendsto.congr (fun s => by simp)
    (hshift.comp (Filter.tendsto_atTop_add_const_right Filter.atTop (-t₀) Filter.tendsto_id))

/-- Barbashin's theorem: local asymptotic stability via LaSalle.
    `V` C¹ and positive definite on `D`, `V̇ ≤ 0` on `D`, a compact positively invariant
    sublevel set `Ωc ⊆ D`, and `{x_eq}` the only positively invariant subset of
    `LieDerivZeroSet f V Ωc`.

    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Corollary 4.1. -/
@[blueprint "thm:lasalle-local-asymptotic-stable"
  (title := "Barbashin's theorem")
  (statement := /-- Let $V \in C^{1}$ be a local Lyapunov function for $\dot{x} = f(x)$ on a domain
    $D$
    (\cref{def:isLocalLyapunovFunction}).  Suppose for some $c > 0$ the sublevel set
    $\Omega_{c} = \{V \le c\}$ is contained in $D$, compact, and positively invariant, that
    $f$ is $C^{1}$ and Lipschitz, and that $\{x_{\mathrm{eq}}\}$ is the only positively
    invariant subset of $E = \{x \in \Omega_{c} : \dot{V}(x) = 0\}$
    (\cref{def:lieDerivZeroSet}).  Then $x_{\mathrm{eq}}$ is locally asymptotically stable
    (\cref{def:localAsymptoticStable}).

    The hypothesis on $E$ is the one a user of LaSalle actually discharges: solve
    $\dot{V} = 0$ and check that no solution can stay there but the equilibrium.  Positive
    invariance of $\Omega_{c}$ is a hypothesis rather than a consequence of $\dot{V} \le 0$:
    deducing it would need a solution through each point of $\Omega_{c}$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Corollary 4.1.
  -/)]
theorem lasalle_local_asymptotic_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV_c1 : ContDiff ℝ 1 V)
    (hV_local : IsLocalLyapunovFunction f V x_eq D)
    {c : ℝ} (hc_pos : 0 < c)
    (hΩ_sub_D : SublevelSet V c ⊆ D)
    (hΩ_compact : IsCompact (SublevelSet V c))
    (hΩ_inv : IsPositivelyInvariant (SublevelSet V c) f)
    {K : NNReal} (hf_lip : LipschitzWith K f) (hf_c1 : ContDiff ℝ 1 f)
    -- `{x_eq}` is the only positively invariant set on which `V̇` vanishes.
    (hLasalle : ∀ N ⊆ LieDerivZeroSet f V (SublevelSet V c),
                  IsPositivelyInvariant N f → N ⊆ {x_eq}) :
    LocalAsymptoticStable f x_eq := by
  refine ⟨lyapunov_stable hn hV_local, ?_⟩
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hV_local.hcont.continuousAt c hc_pos
  refine ⟨δ, hδ_pos, fun t₀ φ hφ hφ0 => ?_⟩
  -- re-anchor the solution at `0`, where the LaSalle machinery lives
  have hψ : IsIntegralCurveOn (fun s => φ (s + t₀)) (fun _ x => f x) (Set.Ici 0) :=
    isIntegralCurveOn_Ici_zero_of_shift hφ
  have hV0 : V (φ (0 + t₀)) < c := by
    have h := hδ (show dist (φ t₀) x_eq < δ by rw [dist_eq_norm]; exact hφ0)
    rw [Real.dist_eq, hV_local.hzero, sub_zero] at h
    simpa using (abs_lt.mp h).2
  have hψ0_in : (fun s => φ (s + t₀)) 0 ∈ SublevelSet V c := le_of_lt hV0
  have hconv := lasalle_invariance_principle hΩ_compact hΩ_inv hf_lip hf_c1 hV_c1
    (fun x hx => hV_local.hLie_nonpos x (hΩ_sub_D hx)) hψ hψ0_in hLasalle
  rw [nhdsSet_singleton] at hconv
  exact tendsto_of_tendsto_shift hconv

/-- Krasovskii's theorem: global asymptotic stability via LaSalle.
    `V` C¹, positive definite, radially unbounded, `V̇ ≤ 0` on `ℝⁿ`, and `{x_eq}` the only
    positively invariant subset of `LieDerivZeroSet f V Ωc` for every sublevel set `Ωc`.

    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Corollary 4.2. -/
@[blueprint "thm:lasalle-global-asymptotic-stable"
  (title := "Krasovskii's theorem")
  (statement := /-- If $V \in C^{1}$ is positive definite, $\dot{V} \le 0$ on $\mathbb{R}^{n}$ and
    radially
    unbounded, $f$ is $C^{1}$ and Lipschitz, and for every $c$ the only positively invariant
    subset of $E_{c} = \{x \in \Omega_{c} : \dot{V}(x) = 0\}$ (\cref{def:lieDerivZeroSet})
    is $\{x_{\mathrm{eq}}\}$, then $x_{\mathrm{eq}}$ is globally asymptotically stable
    (\cref{def:globalAsymptoticStable}).

    Unlike Barbashin's theorem (\cref{thm:lasalle-local-asymptotic-stable}) no positively
    invariant set is assumed: radial unboundedness makes every sublevel set compact, and
    $\dot{V} \le 0$ then keeps the trajectory inside the one through its initial state.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Corollary 4.2.
  -/)]
theorem lasalle_global_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV_c1 : ContDiff ℝ 1 V)
    (hzero : V x_eq = 0)
    (hpos : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x)
    (hLie : ∀ x : ℝⁿ, fderiv ℝ V x (f x) ≤ 0)
    (hradial : Filter.Tendsto V (Filter.comap norm Filter.atTop) Filter.atTop)
    {K : NNReal} (hf_lip : LipschitzWith K f) (hf_c1 : ContDiff ℝ 1 f)
    -- `{x_eq}` is the only positively invariant set on which `V̇` vanishes.
    (hLasalle : ∀ c : ℝ, ∀ N ⊆ LieDerivZeroSet f V (SublevelSet V c),
                  IsPositivelyInvariant N f → N ⊆ {x_eq}) :
    GlobalAsymptoticStable f x_eq := by
  have hV_local : IsLocalLyapunovFunction f V x_eq Set.univ :=
    { hD_open := isOpen_univ
      hD_mem := Set.mem_univ _
      hcont := hV_c1.continuous
      hV_diff := hV_c1.differentiable (by norm_num)
      hzero := hzero
      hpos := fun x _ hx => hpos x hx
      hLie_nonpos := fun x _ => hLie x }
  refine ⟨lyapunov_stable hn hV_local, fun t₀ φ hφ => ?_⟩
  -- re-anchor the solution at `0`, where the LaSalle machinery lives
  have hψ : IsIntegralCurveOn (fun s => φ (s + t₀)) (fun _ x => f x) (Set.Ici 0) :=
    isIntegralCurveOn_Ici_zero_of_shift hφ
  set c := V ((fun s => φ (s + t₀)) 0) with hc_def
  have hΩ_compact : IsCompact (SublevelSet V c) :=
    isCompact_sublevel_set V hV_c1.continuous hradial c
  have hΩ_inv : IsPositivelyInvariant (SublevelSet V c) f := by
    intro s₀ s₁ ξ hξ hξ0 t ht
    exact le_trans (V_nonincreasing_on hV_local
      (hξ.mono (Set.Icc_subset_Icc_right ht.2)) ht.1 (fun _ _ => Set.mem_univ _)) hξ0
  have hψ0_in : (fun s => φ (s + t₀)) 0 ∈ SublevelSet V c := by
    simp [SublevelSet, hc_def]
  have hconv := lasalle_invariance_principle hΩ_compact hΩ_inv hf_lip hf_c1 hV_c1
    (fun x _ => hLie x) hψ hψ0_in (hLasalle c)
  rw [nhdsSet_singleton] at hconv
  exact tendsto_of_tendsto_shift hconv

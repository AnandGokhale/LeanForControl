import LeanForControl.Analysis.OmegaLimit
import LeanForControl.Stability.Continuous.LyapunovTheorems
import Architect

/-!
# `Stability.Continuous.LaSalle` — LaSalle's invariance principle

LaSalle's invariance principle for a time-invariant system `ẋ = f(x)`, given as a
`ContinuousSystem E Unit Y` whose state equation is `s.F t x () = f x`, and its two stability
corollaries, the theorems of Barbashin and Krasovskii.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.1, Theorem 4.4 and Corollaries 4.1–4.2.

## Main results

* `isForwardInvariant_omegaLimitSet` — the ω-limit set of a trajectory is forward invariant
  (Khalil, Lemma 4.1).
* `fderiv_apply_eq_zero_of_mem_omegaLimitSet` — if `∇V · f ≤ 0` on a compact forward invariant
  `Ω` containing the trajectory, then `∇V · f = 0` on its ω-limit set.
* `lasalle_invariance_principle` — every trajectory starting in `Ω` converges to any set `M`
  containing the forward invariant subsets of `E = {x ∈ Ω | ∇V(x) · f(x) = 0}`.
* `locallyAsymptoticallyStable_of_lasalle` (Barbashin) and
  `globallyAsymptoticallyStable_of_lasalle` (Krasovskii).

## Hypotheses

`f` is globally Lipschitz.  It gives uniqueness of solutions in the quantitative Grönwall form
that the invariance of the ω-limit set needs, a solution through every ω-limit point, and forward
completeness, which the asymptotic stability notions require.  Khalil assumes only that `f` is
locally Lipschitz: trajectories stay in the compact `Ω`, so a local hypothesis would suffice,
at the price of a continuation theorem.

Invariance of `ω(φ)` is proved in the *forward* direction only.  Khalil's `M` is the largest
invariant subset of `E`; here `M` must absorb every *forward* invariant subset, a larger family,
so the hypothesis on `M` is correspondingly stronger.
-/

open Filter Set Topology Metric
open scoped Pointwise

namespace ContinuousSystem

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Monotonicity along trajectories -/

/-- `V` does not increase along a trajectory of a time-invariant system on an interval where
`∇V · f ≤ 0` along it. -/
private lemma antitoneOn_comp_of_fderiv_nonpos {s : ContinuousSystem E Unit Y} {f : E → E}
    (hF : ∀ t x, s.F t x () = f x) {V : E → ℝ} (hV : Differentiable ℝ V) {φ : ℝ → E}
    {I : Set ℝ} (hI : Convex ℝ I) (hφ : s.IsTrajectoryOn (fun _ => ()) φ I)
    (h_nonpos : ∀ t ∈ interior I, fderiv ℝ V (φ t) (f (φ t)) ≤ 0) :
    AntitoneOn (V ∘ φ) I :=
  IsIntegralCurveOn.antitoneOn_of_lieDerivative_nonpos (V := fun _ => V) hφ hI
    (fun t _ => (hV (φ t)).comp (t, φ t) differentiableAt_snd) fun t ht => by
      rw [lieDerivative_const (hV _)]
      simp only [vectorField_apply, hF]
      exact h_nonpos t ht

/-- A trajectory on `[t₀, ∞)` that starts in a forward invariant `Ω` stays in `Ω`: apply the
invariance to the segment `[t₀, t]`. -/
private lemma mem_of_isForwardInvariant {s : ContinuousSystem E Unit Y} {Ω : Set E}
    (hΩ : s.IsForwardInvariant (fun _ => ()) Ω) {t₀ : ℝ} {φ : ℝ → E}
    (hφ : s.IsTrajectoryOn (fun _ => ()) φ (Ici t₀)) (hφ₀ : φ t₀ ∈ Ω) : ∀ t ≥ t₀, φ t ∈ Ω :=
  fun t ht => hΩ t₀ t φ (IsIntegralCurveOn.mono hφ Icc_subset_Ici_self) hφ₀ t ⟨ht, le_rfl⟩

omit [NormedSpace ℝ E] in
/-- `V(φ(t))` converges when `V` is continuous and nonincreasing along a trajectory confined to a
compact set, where `V` is bounded below. -/
private lemma exists_tendsto_comp {φ : ℝ → E} {V : E → ℝ} {Ω : Set E} (hΩ : IsCompact Ω)
    (hV : Continuous V) {t₀ : ℝ} (h_in : ∀ t ≥ t₀, φ t ∈ Ω) (h_anti : AntitoneOn (V ∘ φ) (Ici t₀)) :
    ∃ L, Tendsto (V ∘ φ) atTop (𝓝 L) := by
  obtain ⟨x_min, -, h_min⟩ :=
    hΩ.exists_isMinOn ⟨φ t₀, h_in t₀ le_rfl⟩ hV.continuousOn
  -- Freeze the function before `t₀`, making it antitone on all of `ℝ`.
  set g : ℝ → ℝ := fun t => (V ∘ φ) (max t t₀) with hg
  have hg_anti : Antitone g := fun t t' htt' =>
    h_anti (mem_Ici.mpr (le_max_right t t₀)) (mem_Ici.mpr (le_max_right t' t₀))
      (max_le_max_right t₀ htt')
  have hg_bdd : BddBelow (range g) :=
    ⟨V x_min, fun _ ⟨t, ht⟩ => ht ▸ h_min (h_in (max t t₀) (le_max_right t t₀))⟩
  exact ⟨⨅ t, g t, (tendsto_atTop_ciInf hg_anti hg_bdd).congr'
    ((eventually_ge_atTop t₀).mono fun t ht => by simp [hg, max_eq_left ht])⟩

/-! ## The ω-limit set of a trajectory -/

/-- **The ω-limit set of a trajectory is forward invariant** (Khalil, Lemma 4.1), for a
time-invariant system with a Lipschitz field.

This is what makes LaSalle's principle a theorem about Lyapunov functions rather than about
compact sets: it turns `V ≡ L` on `ω(φ)` into `∇V · f = 0` on `ω(φ)`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.1. -/
@[blueprint "lem:continuousSystem-isForwardInvariant-omegaLimitSet"
  (title := "The $\\omega$-limit set is forward invariant")
  (latexEnv := "lemma")
  (statement := /-- Let $\dot x = f(x)$ with $f$ Lipschitz, and let $\varphi$ be a trajectory on
    $[t_0, \infty)$.  Then its $\omega$-limit set $\omega(\varphi)$ (\cref{def:omegaLimitSet}) is
    forward invariant (\cref{def:continuousSystem-isForwardInvariant}).

    Neither boundedness of $\varphi$ nor compactness of an enclosing set is needed; those
    hypotheses of Khalil's Lemma 4.1 are what make $\omega(\varphi)$ nonempty and compact, not
    what make it invariant.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.1. -/)
  (proof := /-- Let $\psi$ be a trajectory on $[a, b]$ with $p = \psi(a) \in \omega(\varphi)$,
    and fix $t \in [a, b]$.  Given $\varepsilon > 0$, put $C = e^{K(b - a)}$ and pick, by the
    definition of the $\omega$-limit set, arbitrarily large $r$ with
    $\|\varphi(r) - p\| < \varepsilon / C$.  The time-shifted curve
    $u(\cdot) = \varphi(\cdot + r - a)$ solves the same time-invariant equation on $[a, b]$ with
    $u(a) = \varphi(r)$, so Grönwall gives
    \[
      \|\varphi(r + t - a) - \psi(t)\| = \|u(t) - \psi(t)\|
        \le \|\varphi(r) - p\|\, e^{K(t - a)} < \varepsilon .
    \]
    Since $r$ may be taken arbitrarily large, so may $r + t - a$; hence $\varphi$ is frequently
    within $\varepsilon$ of $\psi(t)$, i.e. $\psi(t) \in \omega(\varphi)$.

    Khalil argues instead with the flow map and the semigroup identity, which presumes a
    globally defined flow; comparing the two solutions directly needs only uniqueness, in its
    quantitative Grönwall form. -/)]
theorem isForwardInvariant_omegaLimitSet {s : ContinuousSystem E Unit Y} {f : E → E}
    (hF : ∀ t x, s.F t x () = f x) {K : NNReal} (hf : LipschitzWith K f) {t₀ : ℝ} {φ : ℝ → E}
    (hφ : s.IsTrajectoryOn (fun _ => ()) φ (Ici t₀)) :
    s.IsForwardInvariant (fun _ => ()) (omegaLimitSet φ) := by
  have hv : s.vectorField (fun _ => ()) = fun _ x => f x := funext fun t => funext fun x => hF t x
  rw [IsTrajectoryOn, hv] at hφ
  intro a b ψ hψ hψa t ht
  rw [IsTrajectoryOn, hv] at hψ
  rw [mem_omegaLimitSet_iff] at hψa ⊢
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  -- Shrink `ε` by the worst-case Grönwall amplification over the whole segment.
  set C : ℝ := Real.exp (K * (b - a)) with hC_def
  have hC_pos : 0 < C := Real.exp_pos _
  have h_freq := hψa (ball (ψ a) (ε / C)) (ball_mem_nhds _ (div_pos hε hC_pos))
  rw [frequently_atTop] at h_freq ⊢
  intro T
  obtain ⟨r, hr_ge, hr⟩ := h_freq (max T t₀)
  have hr₀ : t₀ ≤ r := (le_max_right T t₀).trans hr_ge
  -- The trajectory restarted at time `r`, re-anchored to `a`.
  have hu : IsIntegralCurveOn (fun σ => φ (σ + (r - a))) (fun _ x => f x) (Icc a b) := by
    refine (hφ.comp_add_autonomous (r - a)).mono fun σ hσ => ?_
    simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg, mem_Ici]
    linarith [hσ.1]
  have h_cmp := dist_le_of_isIntegralCurveOn_Icc (fun _ => hf) hu hψ t ht
  simp only [show a + (r - a) = r by ring] at h_cmp
  refine ⟨r + (t - a), by linarith [(le_max_left T t₀).trans hr_ge, ht.1], hball ?_⟩
  have h_exp : Real.exp (K * (t - a)) ≤ C :=
    Real.exp_le_exp.mpr (by nlinarith [K.coe_nonneg, ht.1, ht.2])
  have h_close : dist (φ (r + (t - a))) (ψ t) < ε :=
    calc dist (φ (r + (t - a))) (ψ t)
        = dist (φ (t + (r - a))) (ψ t) := by rw [show r + (t - a) = t + (r - a) by ring]
      _ ≤ dist (φ r) (ψ a) * Real.exp (K * (t - a)) := h_cmp
      _ ≤ dist (φ r) (ψ a) * C := mul_le_mul_of_nonneg_left h_exp dist_nonneg
      _ < (ε / C) * C := mul_lt_mul_of_pos_right (mem_ball.mp hr) hC_pos
      _ = ε := div_mul_cancel₀ ε hC_pos.ne'
  exact mem_ball.mpr h_close

section Complete

variable [CompleteSpace E]

/-- **`∇V · f = 0` on the ω-limit set.**  Along the trajectory `V` is nonincreasing and bounded
below, so it converges to some `L`, and `V ≡ L` on `ω(φ)`.  The solution through an ω-limit
point stays in `ω(φ)` by invariance, so `V` is constant along it, and its derivative there,
`∇V · f`, vanishes.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), proof of Theorem 4.4. -/
@[blueprint "lem:continuousSystem-fderiv-apply-eq-zero-of-mem-omegaLimitSet"
  (title := "$\\dot V$ vanishes on the $\\omega$-limit set")
  (latexEnv := "lemma")
  (statement := /-- Let $\dot x = f(x)$ with $f$ Lipschitz, $\Omega$ compact and forward
    invariant, $V \in C^1$ with $\nabla V \cdot f \le 0$ on $\Omega$, and $\varphi$ a trajectory
    on $[t_0, \infty)$ with $\varphi(t_0) \in \Omega$.  Then $\nabla V(y) \cdot f(y) = 0$ for
    every $y \in \omega(\varphi)$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), proof of Theorem 4.4. -/)
  (proof := /-- $V(\varphi(t))$ is nonincreasing and bounded below on the compact $\Omega$, so it
    converges to some $L$, and $V \equiv L$ on $\omega(\varphi)$
    (\cref{lem:eq-of-tendsto-of-mem-omegaLimitSet}).  Through $y \in \omega(\varphi)$ take a
    solution $\psi$ on $[0, 1]$ (Picard--Lindel\"of, \cref{thm:exists-isIntegralCurveOn-Ici});
    it stays in $\omega(\varphi)$ by \cref{lem:continuousSystem-isForwardInvariant-omegaLimitSet},
    so $V \circ \psi \equiv L$ and its derivative at $0$, which is $\nabla V(y) \cdot f(y)$,
    vanishes. -/)]
theorem fderiv_apply_eq_zero_of_mem_omegaLimitSet {s : ContinuousSystem E Unit Y} {f : E → E}
    (hF : ∀ t x, s.F t x () = f x) {K : NNReal} (hf : LipschitzWith K f) {V : E → ℝ}
    (hV_c1 : ContDiff ℝ 1 V) {Ω : Set E} (hΩ : IsCompact Ω)
    (hΩ_inv : s.IsForwardInvariant (fun _ => ()) Ω) (h_nonpos : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {t₀ : ℝ} {φ : ℝ → E} (hφ : s.IsTrajectoryOn (fun _ => ()) φ (Ici t₀)) (hφ₀ : φ t₀ ∈ Ω) :
    ∀ y ∈ omegaLimitSet φ, fderiv ℝ V y (f y) = 0 := by
  have hv : s.vectorField (fun _ => ()) = fun _ x => f x := funext fun t => funext fun x => hF t x
  have hV : Differentiable ℝ V := hV_c1.differentiable one_ne_zero
  have h_in := mem_of_isForwardInvariant hΩ_inv hφ hφ₀
  -- `V(φ(t)) → L`, so `V ≡ L` on `ω(φ)`.
  obtain ⟨L, hL⟩ := exists_tendsto_comp hΩ hV.continuous h_in
    (antitoneOn_comp_of_fderiv_nonpos hF hV (convex_Ici t₀) hφ fun t ht =>
      h_nonpos _ (h_in t (interior_subset ht)))
  intro y hy
  -- A solution through `y`, which stays in `ω(φ)` by invariance.
  obtain ⟨ψ, hψ₀, hψ, -⟩ := exists_isIntegralCurveOn_Ici (f := fun _ x => f x)
    (hf.continuous.comp continuous_snd) (fun _ => hf) 0 y
  have hψ_seg : IsIntegralCurveOn ψ (fun _ x => f x) (Icc 0 1) := hψ.mono Icc_subset_Ici_self
  have hψ_traj : s.IsTrajectoryOn (fun _ => ()) ψ (Icc 0 1) := by
    rw [IsTrajectoryOn, hv]
    exact hψ_seg
  have h_const : ∀ σ ∈ Icc (0 : ℝ) 1, (V ∘ ψ) σ = L := fun σ hσ =>
    eq_of_tendsto_of_mem_omegaLimitSet hV.continuous hL
      (isForwardInvariant_omegaLimitSet hF hf hφ 0 1 ψ hψ_traj (hψ₀ ▸ hy) σ hσ)
  -- `V ∘ ψ` is constant on `[0, 1]`, so its derivative at `0`, which is `∇V(y) · f(y)`, is `0`.
  have h_mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h_chain : HasDerivWithinAt (V ∘ ψ) (fderiv ℝ V (ψ 0) (f (ψ 0))) (Icc 0 1) 0 :=
    (hV (ψ 0)).hasFDerivAt.comp_hasDerivWithinAt 0 (hψ_seg 0 h_mem)
  rw [hψ₀] at h_chain
  have h_zero : HasDerivWithinAt (V ∘ ψ) 0 (Icc 0 1) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) _ L).congr h_const (h_const 0 h_mem)
  exact (uniqueDiffOn_Icc zero_lt_one 0 h_mem).eq_deriv _ h_chain h_zero

/-! ## LaSalle's invariance principle -/

/-- **LaSalle's invariance principle.**  Let `Ω` be compact and forward invariant for the
time-invariant system `ẋ = f(x)`, `f` Lipschitz, and `V` a `C¹` function with `∇V · f ≤ 0` on
`Ω`.  Every trajectory starting in `Ω` converges to any set `M` containing the forward invariant
subsets of `E = {x ∈ Ω | ∇V(x) · f(x) = 0}`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.4. -/
@[blueprint "thm:continuousSystem-lasalle-invariance-principle"
  (title := "LaSalle's invariance principle")
  (statement := /-- Let $\dot x = f(x)$ with $f$ Lipschitz, $\Omega$ compact and forward
    invariant (\cref{def:continuousSystem-isForwardInvariant}), and $V \in C^1$ with
    $\nabla V \cdot f \le 0$ on $\Omega$.  Put
    \[
      E = \{x \in \Omega : \nabla V(x) \cdot f(x) = 0\},
    \]
    and let $M$ contain every forward invariant subset of $E$.  Then every trajectory $\varphi$ on
    $[t_0, \infty)$ with $\varphi(t_0) \in \Omega$ satisfies $\varphi(t) \to M$ as
    $t \to \infty$.

    Khalil takes $M$ to be the largest \emph{invariant} subset of $E$.  Here $M$ must absorb every
    \emph{forward} invariant subset, a larger family, so the hypothesis on $M$ is correspondingly
    stronger: backward invariance of $\omega(\varphi)$ would need solutions through its points to
    extend backwards in time.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.4. -/)
  (proof := /-- The $\omega$-limit set lies in $\Omega$, which is closed and contains the
    trajectory (\cref{lem:omegaLimitSet-subset-of-eventually-mem}), and $\nabla V \cdot f$
    vanishes on it (\cref{lem:continuousSystem-fderiv-apply-eq-zero-of-mem-omegaLimitSet}), so
    $\omega(\varphi) \subseteq E$.  It is forward invariant
    (\cref{lem:continuousSystem-isForwardInvariant-omegaLimitSet}), so
    $\omega(\varphi) \subseteq M$.  A trajectory confined to a compact set converges to every set
    containing its $\omega$-limit set (\cref{lem:tendsto-nhdsSet-of-omegaLimitSet-subset}). -/)]
theorem lasalle_invariance_principle {s : ContinuousSystem E Unit Y} {f : E → E}
    (hF : ∀ t x, s.F t x () = f x) {K : NNReal} (hf : LipschitzWith K f) {V : E → ℝ}
    (hV_c1 : ContDiff ℝ 1 V) {Ω M : Set E} (hΩ : IsCompact Ω)
    (hΩ_inv : s.IsForwardInvariant (fun _ => ()) Ω) (h_nonpos : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    (hM : ∀ N ⊆ {x ∈ Ω | fderiv ℝ V x (f x) = 0}, s.IsForwardInvariant (fun _ => ()) N → N ⊆ M)
    {t₀ : ℝ} {φ : ℝ → E} (hφ : s.IsTrajectoryOn (fun _ => ()) φ (Ici t₀)) (hφ₀ : φ t₀ ∈ Ω) :
    Tendsto φ atTop (𝓝ˢ M) := by
  have h_ev : ∀ᶠ t in atTop, φ t ∈ Ω :=
    (eventually_ge_atTop t₀).mono (mem_of_isForwardInvariant hΩ_inv hφ hφ₀)
  -- `ω(φ) ⊆ E`: it lies in `Ω`, and `∇V · f` vanishes on it; it is forward invariant, so `⊆ M`.
  have h_sub_E : omegaLimitSet φ ⊆ {x ∈ Ω | fderiv ℝ V x (f x) = 0} := fun y hy =>
    ⟨omegaLimitSet_subset_of_eventually_mem hΩ.isClosed h_ev hy,
      fderiv_apply_eq_zero_of_mem_omegaLimitSet hF hf hV_c1 hΩ hΩ_inv h_nonpos hφ hφ₀ y hy⟩
  exact tendsto_nhdsSet_of_omegaLimitSet_subset hΩ h_ev
    (hM _ h_sub_E (isForwardInvariant_omegaLimitSet hF hf hφ))

/-- A time-invariant system with a Lipschitz field is forward complete. -/
private lemma isForwardComplete_of_timeInvariant {s : ContinuousSystem E Unit Y} {f : E → E}
    (hF : ∀ t x, s.F t x () = f x) {K : NNReal} (hf : LipschitzWith K f) :
    s.IsForwardComplete (fun _ => ()) := by
  have hv : s.vectorField (fun _ => ()) = fun _ x => f x := funext fun t => funext fun x => hF t x
  exact isForwardComplete_of_lipschitz (K := K)
    (by rw [hv]; exact hf.continuous.comp continuous_snd) (by rw [hv]; exact fun _ => hf)

end Complete

/-! ## The theorems of Barbashin and Krasovskii -/

section Euclidean

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- **Barbashin's theorem**: local asymptotic stability by LaSalle.  `V` is `C¹` and positive
definite on a neighbourhood `D` of `x_eq` with `∇V · f ≤ 0` there; some sublevel set
`{V ≤ c}` is contained in `D`, compact and forward invariant; and `{x_eq}` contains every
forward invariant subset of `{V ≤ c}` on which `∇V · f` vanishes.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Corollary 4.1. -/
@[blueprint "thm:continuousSystem-locallyAsymptoticallyStable-of-lasalle"
  (title := "Barbashin's theorem")
  (statement := /-- Let $\dot x = f(x)$ on $\mathbb{R}^n$ with $f$ Lipschitz, and
    $V \in C^1$ positive definite on a neighbourhood $D$ of $x_{\mathrm{eq}}$
    (\cref{def:isPositiveDefiniteOn}) with $\nabla V \cdot f \le 0$ on $D$.  Suppose that for some
    $c > 0$ the sublevel set $\Omega_c = \{V \le c\}$ is contained in $D$, compact and forward
    invariant, and that $\{x_{\mathrm{eq}}\}$ contains every forward invariant subset of
    $\{x \in \Omega_c : \nabla V(x) \cdot f(x) = 0\}$.  Then $x_{\mathrm{eq}}$ is locally
    asymptotically stable (\cref{def:continuousSystem-locallyAsymptoticallyStable}).

    The hypothesis on $E$ is the one a user of LaSalle discharges: solve $\nabla V \cdot f = 0$
    and check that no solution can stay there but the equilibrium.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Corollary 4.1. -/)
  (proof := /-- Stability: $V$ is a uniform Lyapunov function
    (\cref{lem:continuousSystem-isUniformLyapunovFunction-of-timeInvariant},
    \cref{thm:continuousSystem-isUniformLyapunovFunction-uniformlyStable}).  Forward
    completeness: $f$ is Lipschitz (\cref{thm:continuousSystem-isForwardComplete-of-lipschitz}).
    Convergence: near $x_{\mathrm{eq}}$, $V < c$, so a trajectory starting there starts in
    $\Omega_c$, and \cref{thm:continuousSystem-lasalle-invariance-principle} with
    $M = \{x_{\mathrm{eq}}\}$ applies. -/)]
theorem locallyAsymptoticallyStable_of_lasalle [NeZero n] {s : ContinuousSystem ℝⁿ Unit Y}
    {f : ℝⁿ → ℝⁿ} (hF : ∀ t x, s.F t x () = f x) {K : NNReal} (hf : LipschitzWith K f)
    {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ} (hD : D ∈ 𝓝 x_eq) (hV_c1 : ContDiff ℝ 1 V)
    (hV_pos : IsPositiveDefiniteOn V x_eq D) (h_nonpos : ∀ x ∈ D, fderiv ℝ V x (f x) ≤ 0)
    {c : ℝ} (hc : 0 < c) (hΩ_sub : {x | V x ≤ c} ⊆ D) (hΩ : IsCompact {x | V x ≤ c})
    (hΩ_inv : s.IsForwardInvariant (fun _ => ()) {x | V x ≤ c})
    (hE : ∀ N ⊆ {x | V x ≤ c ∧ fderiv ℝ V x (f x) = 0}, s.IsForwardInvariant (fun _ => ()) N →
      N ⊆ {x_eq}) :
    s.LocallyAsymptoticallyStable x_eq := by
  have hV : Differentiable ℝ V := hV_c1.differentiable one_ne_zero
  have h_stable : s.Stable x_eq :=
    (IsUniformLyapunovFunction.of_timeInvariant hD (fun x _ => hV x) hV_pos fun t _ x hx => by
      rw [hF]
      exact h_nonpos x hx).uniformlyStable.stable
  have h_fc := isForwardComplete_of_timeInvariant hF hf
  refine ⟨h_stable, fun t₀ _ => ?_⟩
  -- Near `x_eq`, `V < c`: trajectories starting there start in `{V ≤ c}`.
  obtain ⟨δ, hδ, h_near⟩ := Metric.continuousAt_iff.mp hV.continuous.continuousAt c hc
  refine ⟨δ, hδ, fun t₁ x ht hx _ => h_fc t₀ t₁ x ht hx (mem_univ _), fun x hx h_init => ?_⟩
  have hV₀ : V (x t₀) ≤ c := by
    have h := h_near (show dist (x t₀) x_eq < δ by rwa [dist_eq_norm])
    rw [Real.dist_eq, hV_pos.2.1, sub_zero] at h
    exact (abs_lt.mp h).2.le
  have h_lim := lasalle_invariance_principle hF hf hV_c1 hΩ hΩ_inv
    (fun y hy => h_nonpos y (hΩ_sub hy)) hE hx hV₀
  rwa [nhdsSet_singleton] at h_lim

/-- **Krasovskii's theorem**: global asymptotic stability by LaSalle.  `V` is `C¹`, positive
definite on the whole space, with compact sublevel sets and `∇V · f ≤ 0` everywhere, and for
every `c`, `{x_eq}` contains every forward invariant subset of `{V ≤ c}` on which `∇V · f`
vanishes.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Corollary 4.2. -/
@[blueprint "thm:continuousSystem-globallyAsymptoticallyStable-of-lasalle"
  (title := "Krasovskii's theorem")
  (statement := /-- Let $\dot x = f(x)$ on $\mathbb{R}^n$ with $f$ Lipschitz, and $V \in C^1$
    positive definite on $\mathbb{R}^n$, with compact sublevel sets (equivalently, radially
    unbounded) and $\nabla V \cdot f \le 0$ everywhere.  Suppose that for every $c$,
    $\{x_{\mathrm{eq}}\}$ contains every forward invariant subset of
    $\{x : V(x) \le c,\ \nabla V(x) \cdot f(x) = 0\}$.  Then $x_{\mathrm{eq}}$ is globally
    asymptotically stable (\cref{def:continuousSystem-globallyAsymptoticallyStable}).

    Unlike Barbashin's theorem (\cref{thm:continuousSystem-locallyAsymptoticallyStable-of-lasalle})
    no forward invariant set is assumed: every sublevel set is compact, and
    $\nabla V \cdot f \le 0$ keeps a trajectory in the one through its initial state.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Corollary 4.2. -/)
  (proof := /-- Stability and forward completeness as in Barbashin's theorem.  The sublevel set
    $\{V \le V(x(t_0))\}$ is compact and, since $V$ does not increase along trajectories, forward
    invariant; apply \cref{thm:continuousSystem-lasalle-invariance-principle} with
    $M = \{x_{\mathrm{eq}}\}$. -/)]
theorem globallyAsymptoticallyStable_of_lasalle [NeZero n] {s : ContinuousSystem ℝⁿ Unit Y}
    {f : ℝⁿ → ℝⁿ} (hF : ∀ t x, s.F t x () = f x) {K : NNReal} (hf : LipschitzWith K f)
    {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hV_c1 : ContDiff ℝ 1 V) (hV_pos : IsPositiveDefiniteOn V x_eq univ)
    (hV_sub : ∀ c, IsCompact {x | V x ≤ c}) (h_nonpos : ∀ x, fderiv ℝ V x (f x) ≤ 0)
    (hE : ∀ c, ∀ N ⊆ {x | V x ≤ c ∧ fderiv ℝ V x (f x) = 0},
      s.IsForwardInvariant (fun _ => ()) N → N ⊆ {x_eq}) :
    s.GloballyAsymptoticallyStable x_eq := by
  have hV : Differentiable ℝ V := hV_c1.differentiable one_ne_zero
  have h_stable : s.Stable x_eq :=
    (IsUniformLyapunovFunction.of_timeInvariant univ_mem (fun x _ => hV x) hV_pos
      fun t _ x _ => by
      rw [hF]
      exact h_nonpos x).uniformlyStable.stable
  have h_fc := isForwardComplete_of_timeInvariant hF hf
  refine ⟨h_stable, fun t₀ _ => ⟨h_fc t₀, fun x hx => ?_⟩⟩
  -- The sublevel set through `x(t₀)` is forward invariant, since `V` does not increase.
  have hΩ_inv : s.IsForwardInvariant (fun _ => ()) {y | V y ≤ V (x t₀)} :=
    fun a b ξ hξ hξa t ht =>
      ((antitoneOn_comp_of_fderiv_nonpos hF hV (convex_Icc a b) hξ fun τ _ => h_nonpos _)
        ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1).trans hξa
  have h_lim := lasalle_invariance_principle hF hf hV_c1 (hV_sub _) hΩ_inv
    (fun y _ => h_nonpos y) (hE (V (x t₀))) hx (show V (x t₀) ≤ V (x t₀) from le_rfl)
  rwa [nhdsSet_singleton] at h_lim

end Euclidean

end ContinuousSystem

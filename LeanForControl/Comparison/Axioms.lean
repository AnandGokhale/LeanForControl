import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKInfty
import LeanForControl.Comparison.ClassKL

import Architect

/-!
The three statements below are `axiom`s: they are assumed, not proved, and every result that
depends on one inherits that assumption.  Their blueprint nodes therefore carry a statement and
no proof, so the rendered blueprint shows them as open.
-/

/-- Given `φ : ℝ≥0 × ℝ≥0 → ℝ` satisfying uniform convergence to zero in the first argument
    and uniform stability near zero, there exists a global class KL function `β` with
    `φ r s ≤ β r s` for all `r s ≥ 0`.

    This is the global analogue of Lemma 9 in Kellett, *A compendium of comparison function
    results* (2014), stated on `ℝ≥0 × ℝ≥0` with the paper's exact hypotheses. -/
@[blueprint "lem:exists-classKLGlobal-of-stability-properties" (latexEnv := "lemma")
  (statement := /-- \textbf{Assumed without proof.}  Let $\varphi : \mathbb{R} \to \mathbb{R}
    \to \mathbb{R}$ satisfy
    \begin{itemize}
      \item \emph{uniform convergence}: for every $r > 0$ and $\varepsilon > 0$ there is a
        $T > 0$ with $\varphi(s, t) < \varepsilon$ whenever $0 \le s \le r$ and $t \ge T$;
      \item \emph{uniform stability}: for every $\varepsilon > 0$ there is a $\delta > 0$ with
        $\varphi(s, t) \le \varepsilon$ whenever $0 \le s \le \delta$ and $t \ge 0$.
    \end{itemize}
    Then there is a global class $\mathcal{KL}$ function $\beta$ with
    $\varphi(r, s) \le \beta(r, s)$ for all $r, s \ge 0$.

    This is the global analogue of Lemma 9 of Kellett, \emph{A compendium of comparison function
    results} (2014). -/)]
axiom exists_classKLGlobal_of_stability_properties
    (φ : ℝ → ℝ → ℝ)
    (h_convergence : ∀ r > 0, ∀ ε > 0, ∃ T > 0,
        ∀ s, 0 ≤ s → s ≤ r → ∀ t ≥ T, φ s t < ε)
    (h_uniform_stability : ∀ ε > 0, ∃ δ > 0,
        ∀ s, 0 ≤ s → s ≤ δ → ∀ t ≥ 0, φ s t ≤ ε) :
    ∃ β : ClassKLGlobal, ∀ r ≥ 0, ∀ s ≥ 0, φ r s ≤ β.toFun r s


/-- Any class K function `α` on `[0, a)` has a class K minorant `β ≤ α` that is globally
Lipschitz on a neighbourhood of `0`. The Lipschitz extension `β_ext` agrees with `β` on `[0, a)`
and satisfies `β(x) ≤ L·x` near the base point. -/
@[blueprint "lem:exists-classK-minorant-lipschitz" (latexEnv := "lemma")
  (statement := /-- \textbf{Assumed without proof.}  Let $\alpha$ be a class $\mathcal{K}$
    function on $[0, a)$ and let $\mathrm{base} \in (0, a)$.  Then there are a class
    $\mathcal{K}$ function $\beta$ on $[0, a)$, a function $\beta_{\mathrm{ext}} :
    \mathbb{R} \to \mathbb{R}$ and a constant $L > 0$ such that
    $\beta(x) \le \alpha(x)$ and $\beta_{\mathrm{ext}}(x) = \beta(x)$ for $x \in [0, a)$,
    $\beta(x) \le L x$ for $x \in (0, \mathrm{base}]$, and $\beta_{\mathrm{ext}}$ is continuous
    and $L$-Lipschitz on all of $\mathbb{R}$. -/)]
axiom exists_classK_minorant_lipschitz {a b : ℝ} (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a) :
    ∃ (β : ClassK a b) (β_ext : ℝ → ℝ) (L : ℝ) (hL_pos : 0 < L),
      (∀ x ∈ Set.Ico 0 a, β.toFun x ≤ α.toFun x) ∧
      (∀ x ∈ Set.Ico 0 a, β_ext x = β.toFun x) ∧
      (∀ x ∈ Set.Ioc 0 base, β.toFun x ≤ L * x) ∧
      Continuous β_ext ∧
      LipschitzWith ⟨L, hL_pos.le⟩ β_ext

/-- Every class K function `α` on `[0, a)` extends to a continuous, monotone function on all
of `ℝ` that agrees with `α` on `[0, a)`. -/
@[blueprint "lem:classK-exists-global-extension" (latexEnv := "lemma")
  (statement := /-- \textbf{Assumed without proof.}  Every class $\mathcal{K}$ function $\alpha$
    on $[0, a)$ admits an $\alpha_{\mathrm{ext}} : \mathbb{R} \to \mathbb{R}$ that is continuous
    and monotone on all of $\mathbb{R}$ and agrees with $\alpha$ on $[0, a)$. -/)]
axiom ClassK.exists_global_extension {a b : ℝ} (α : ClassK a b) :
    ∃ (α_ext : ℝ → ℝ),
      Continuous α_ext ∧
      (∀ x ∈ Set.Ico 0 a, α_ext x = α.toFun x) ∧
      (∀ x y, x ≤ y → α_ext x ≤ α_ext y)

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Group.Bounded
import Architect
variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Class K and K∞ functions -/

/-- A function `α : [0, ∞) → ℝ` is of class `𝒦` when it is continuous, zero at
zero, and strictly increasing on `[0, ∞)`. -/
@[blueprint "def:isClassK"
  (statement := /-- A function $\alpha : [0, \infty) \to \mathbb{R}$ is of
    \emph{class $\mathcal{K}$} when it is continuous on $[0, \infty)$, vanishes
    at the origin ($\alpha(0) = 0$), and is strictly increasing on
    $[0, \infty)$. Class-$\mathcal{K}$ functions are the standard comparison
    functions used to bound a Lyapunov function from below. -/)]
def IsClassK (α : ℝ → ℝ) : Prop :=
  ContinuousOn α (Set.Ici 0) ∧ α 0 = 0 ∧ StrictMonoOn α (Set.Ici 0)

/-- Class `𝒦` and radially unbounded: `α(r) → ∞` as `r → ∞`. -/
@[blueprint "def:isClassKInfty"
  (statement := /-- A class-$\mathcal{K}$ function $\alpha$
    (see \cref{def:isClassK}) is of \emph{class $\mathcal{K}_{\infty}$} when it
    is moreover radially unbounded: $\alpha(r) \to \infty$ as $r \to \infty$.
    Class-$\mathcal{K}_{\infty}$ functions are used to sandwich a Lyapunov
    function in the global setting. -/)]
def IsClassKInfty (α : ℝ → ℝ) : Prop :=
  IsClassK α ∧ Filter.Tendsto α Filter.atTop Filter.atTop

/-! ## System primitives -/

/-- `φ` is a global solution of `ẋ = f(x)`, defined for all `t ∈ ℝ`. -/
@[blueprint "def:isTrajectory"
  (statement := /-- A curve $\varphi : \mathbb{R} \to \mathbb{R}^{n}$ is a
    \emph{trajectory} of the autonomous system $\dot{x} = f(x)$ when it is
    differentiable at every $t \in \mathbb{R}$ with
    $\dot{\varphi}(t) = f(\varphi(t))$. Trajectories are required to exist
    globally in time. -/)]
def IsTrajectory (φ : ℝ → ℝⁿ) (f : ℝⁿ → ℝⁿ) : Prop :=
  ∀ t : ℝ, HasDerivAt φ (f (φ t)) t

/-- `x_eq` is an equilibrium point: `f(x_eq) = 0`. -/
@[blueprint "def:isEquilibrium"
  (statement := /-- A point $x_{\mathrm{eq}} \in \mathbb{R}^{n}$ is an
    \emph{equilibrium} of $\dot{x} = f(x)$ when $f(x_{\mathrm{eq}}) = 0$.
    Equivalently, the constant curve $\varphi \equiv x_{\mathrm{eq}}$ is a
    trajectory (see \cref{def:isTrajectory}). -/)]
def IsEquilibrium (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  f x_eq = 0

/-! ## Stability predicates -/

/-- Standard ε–δ Lyapunov stability. -/
@[blueprint "def:lyapunovStable"
  (statement := /-- An equilibrium $x_{\mathrm{eq}}$ of $\dot{x} = f(x)$ is
    \emph{Lyapunov stable} when, for every $\varepsilon > 0$, there exists
    $\delta > 0$ such that every trajectory $\varphi$
    (see \cref{def:isTrajectory}) with
    $\|\varphi(0) - x_{\mathrm{eq}}\| < \delta$ satisfies
    $\|\varphi(t) - x_{\mathrm{eq}}\| < \varepsilon$ for all $t \ge 0$. -/)]
def LyapunovStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ φ : ℝ → ℝⁿ,
    IsTrajectory φ f → ‖φ 0 - x_eq‖ < δ → ∀ t ≥ 0, ‖φ t - x_eq‖ < ε

/-- Lyapunov stable and trajectories starting near `x_eq` converge to
`x_eq`. -/
@[blueprint "def:localAsymptoticStable"
  (statement := /-- An equilibrium $x_{\mathrm{eq}}$ of $\dot{x} = f(x)$ is
    \emph{locally asymptotically stable} when it is Lyapunov stable
    (see \cref{def:lyapunovStable}) and there exists $c > 0$ such that every
    trajectory $\varphi$ with $\|\varphi(0) - x_{\mathrm{eq}}\| < c$ satisfies
    $\varphi(t) \to x_{\mathrm{eq}}$ as $t \to \infty$. -/)]
def LocalAsymptoticStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  LyapunovStable f x_eq ∧
  ∃ c > 0, ∀ φ : ℝ → ℝⁿ,
    IsTrajectory φ f → ‖φ 0 - x_eq‖ < c → Filter.Tendsto φ Filter.atTop (nhds x_eq)

/-- Lyapunov stable and every trajectory converges to `x_eq`. -/
@[blueprint "def:globalAsymptoticStable"
  (statement := /-- An equilibrium $x_{\mathrm{eq}}$ of $\dot{x} = f(x)$ is
    \emph{globally asymptotically stable} when it is Lyapunov stable
    (see \cref{def:lyapunovStable}) and every trajectory $\varphi$ of the
    system satisfies $\varphi(t) \to x_{\mathrm{eq}}$ as $t \to \infty$. -/)]
def GlobalAsymptoticStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  LyapunovStable f x_eq ∧
  ∀ φ : ℝ → ℝⁿ, IsTrajectory φ f → Filter.Tendsto φ Filter.atTop (nhds x_eq)

/-! ## Sublevel sets -/

/-- The `c`-sublevel set of `V`. -/
@[blueprint "def:sublevelSet"
  (statement := /-- For $V : \mathbb{R}^{n} \to \mathbb{R}$ and $c \in
    \mathbb{R}$, the \emph{$c$-sublevel set} of $V$ is
    \[
      \Omega_{c}(V) = \{ x \in \mathbb{R}^{n} : V(x) \le c \}.
    \]
    Sublevel sets of Lyapunov functions are the canonical invariant
    neighborhoods used in stability proofs. -/)]
def SublevelSet (V : ℝⁿ → ℝ) (c : ℝ) : Set ℝⁿ := {x | V x ≤ c}

/-! ## Lyapunov function structures

Four structures forming a hierarchy:

  IsLocalLyapunovFunction (on domain D) → LyapunovStable
  IsStrictLocalLyapunovFunction (on domain D, compact sublevel set) → LocalAsymptoticStable
  IsStrictLyapunovFunction (global, compact sublevel sets) → GlobalAsymptoticStable
  IsAsymptoticLyapunovFunction (global, radially unbounded) → GlobalAsymptoticStable

For the local structures, V : ℝⁿ → ℝ is globally continuous and differentiable
(needed for chain rule and IVT arguments), but positivity and Lie-derivative
conditions hold only on the domain D. The bridge lemma `contDiffOn_extension`
justifies this: any C¹ function on open D extends to a globally C¹ function
agreeing with the original on a neighborhood of x_eq.

The Lie derivative DV(x)[f(x)] = fderiv ℝ V x (f x). -/

/-- Local Lyapunov function on an open domain `D ∋ x_eq`. `V` is globally
continuous and differentiable; positivity and Lie-derivative conditions hold
only on `D`. -/
@[blueprint "def:isLocalLyapunovFunction"
  (statement := /-- A function $V : \mathbb{R}^{n} \to \mathbb{R}$ is a
    \emph{local Lyapunov function} for $\dot{x} = f(x)$ at an equilibrium
    $x_{\mathrm{eq}}$ on an open set $D \ni x_{\mathrm{eq}}$ when
    \begin{enumerate}
      \item $V$ is continuous and (globally) differentiable on $\mathbb{R}^{n}$,
      \item $V(x_{\mathrm{eq}}) = 0$,
      \item $V(x) > 0$ for all $x \in D \setminus \{x_{\mathrm{eq}}\}$,
      \item the Lie derivative satisfies
        $\mathrm{D}V(x)\bigl[f(x)\bigr] \le 0$ for all $x \in D$.
    \end{enumerate}
    Global smoothness is for the chain rule; only on $D$ are positivity and
    monotonicity required. -/)]
structure IsLocalLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) (D : Set ℝⁿ) : Prop where
  hD_open     : IsOpen D
  hD_mem      : x_eq ∈ D
  hcont       : Continuous V
  hV_diff     : Differentiable ℝ V
  hzero       : V x_eq = 0
  hpos        : ∀ x ∈ D, x ≠ x_eq → 0 < V x
  hLie_nonpos : ∀ x ∈ D, fderiv ℝ V x (f x) ≤ 0

/-- Strict local Lyapunov function: strict Lie-derivative inequality on `D`
plus a compact sublevel set contained in `D`. -/
@[blueprint "def:isStrictLocalLyapunovFunction"
  (statement := /-- A function $V : \mathbb{R}^{n} \to \mathbb{R}$ is a
    \emph{strict local Lyapunov function} for $\dot{x} = f(x)$ at an
    equilibrium $x_{\mathrm{eq}}$ on an open set $D \ni x_{\mathrm{eq}}$ when
    \begin{enumerate}
      \item $V$ is continuous and $C^{1}$ on $\mathbb{R}^{n}$,
      \item $V(x_{\mathrm{eq}}) = 0$,
      \item $V(x) > 0$ for all $x \in D \setminus \{x_{\mathrm{eq}}\}$,
      \item $f(x_{\mathrm{eq}}) = 0$,
      \item the Lie derivative is strictly negative:
        $\mathrm{D}V(x)\bigl[f(x)\bigr] < 0$ for all $x \in D \setminus
        \{x_{\mathrm{eq}}\}$,
      \item there exists $c > 0$ such that the sublevel set
        $\Omega_{c}(V)$ (see \cref{def:sublevelSet}) is contained in $D$ and
        compact.
    \end{enumerate}
    The compact-sublevel hypothesis replaces radial unboundedness in the local
    setting. -/)]
structure IsStrictLocalLyapunovFunction
    (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) (D : Set ℝⁿ) : Prop where
  hD_open   : IsOpen D
  hD_mem    : x_eq ∈ D
  hcont     : Continuous V
  hV_c1     : ContDiff ℝ 1 V
  hzero     : V x_eq = 0
  hpos      : ∀ x ∈ D, x ≠ x_eq → 0 < V x
  hequil    : f x_eq = 0
  hLie_neg  : ∀ x ∈ D, x ≠ x_eq → fderiv ℝ V x (f x) < 0
  hcompact  : ∃ c > 0, SublevelSet V c ⊆ D ∧ IsCompact (SublevelSet V c)


-- structure IsLocalChetaevFunction
--     (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) (D : Set ℝⁿ) : Prop where
--   hD_open   : IsOpen D
--   hD_mem    : x_eq ∈ D
--   hcont     : Continuous V
--   hV_c1     : ContDiff ℝ 1 V
--   hzero     : V x_eq = 0




--   hpos      : ∀ x ∈ D, x ≠ x_eq → 0 < V x
--   hequil    : f x_eq = 0
--   hLie_neg  : ∀ x ∈ D, x ≠ x_eq → fderiv ℝ V x (f x) < 0
--   hcompact  : ∃ c > 0, SublevelSet V c ⊆ D ∧ IsCompact (SublevelSet V c)

/-- Global strict Lyapunov function: strict Lie derivative everywhere plus
coercivity (every sublevel set is compact). -/
@[blueprint "def:isStrictLyapunovFunction"
  (statement := /-- A function $V : \mathbb{R}^{n} \to \mathbb{R}$ is a
    \emph{strict (global) Lyapunov function} for $\dot{x} = f(x)$ at an
    equilibrium $x_{\mathrm{eq}}$ when
    \begin{enumerate}
      \item $V$ is continuous and $C^{1}$,
      \item $V(x_{\mathrm{eq}}) = 0$ and $V(x) > 0$ for all $x \neq
        x_{\mathrm{eq}}$,
      \item $f(x_{\mathrm{eq}}) = 0$,
      \item $\mathrm{D}V(x)\bigl[f(x)\bigr] < 0$ for all $x \neq
        x_{\mathrm{eq}}$,
      \item every sublevel set $\{V \le c\}$ is compact (coercivity).
    \end{enumerate}
    On $\mathbb{R}^{n}$ the coercivity condition is equivalent to radial
    unboundedness of $V$. -/)]
structure IsStrictLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont             : Continuous V
  hV_c1             : ContDiff ℝ 1 V
  hzero             : V x_eq = 0
  hpos              : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x
  hequil            : f x_eq = 0
  hLie_neg          : ∀ x : ℝⁿ, x ≠ x_eq → fderiv ℝ V x (f x) < 0
  hbounded_sublevel : ∀ c : ℝ, IsCompact {x : ℝⁿ | V x ≤ c}

/-- Global Lyapunov function with quantitative class-K-infinity sandwich
bounds. -/
@[blueprint "def:isGlobalLyapunovFunction"
  (statement := /-- A function $V : \mathbb{R}^{n} \to \mathbb{R}$ is a
    \emph{quantitative global Lyapunov function} for $\dot{x} = f(x)$ at an
    equilibrium $x_{\mathrm{eq}}$ when it is continuous, differentiable,
    sandwiched between two class-$\mathcal{K}_{\infty}$ functions
    (see \cref{def:isClassKInfty}) $\alpha_{1}, \alpha_{2}$ as
    $\alpha_{1}(\|x - x_{\mathrm{eq}}\|) \le V(x) \le
    \alpha_{2}(\|x - x_{\mathrm{eq}}\|)$,
    and has non-positive Lie derivative
    $\mathrm{D}V(x) \cdot f(x) \le 0$ for all $x$. -/)]
structure IsGlobalLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont       : Continuous V
  hV_diff     : Differentiable ℝ V
  halphas     : ∃ α₁ α₂ : ℝ → ℝ, IsClassKInfty α₁ ∧ IsClassKInfty α₂ ∧
                  ∀ x : ℝⁿ, α₁ ‖x - x_eq‖ ≤ V x ∧ V x ≤ α₂ ‖x - x_eq‖
  hLie_nonpos : ∀ x : ℝⁿ, fderiv ℝ V x (f x) ≤ 0


/-- Classical Lyapunov function for global asymptotic stability: `C¹`, positive
definite, strict Lie derivative, radially unbounded. -/
@[blueprint "def:isAsymptoticLyapunovFunction"
  (statement := /-- A function $V : \mathbb{R}^{n} \to \mathbb{R}$ is an
    \emph{asymptotic Lyapunov function} for $\dot{x} = f(x)$ at an
    equilibrium $x_{\mathrm{eq}}$ when
    \begin{enumerate}
      \item $V$ is continuous and $C^{1}$,
      \item $V(x_{\mathrm{eq}}) = 0$ and $V(x) > 0$ for all $x \neq
        x_{\mathrm{eq}}$,
      \item $f(x_{\mathrm{eq}}) = 0$,
      \item $\mathrm{D}V(x)\bigl[f(x)\bigr] < 0$ for all $x \neq
        x_{\mathrm{eq}}$,
      \item $V$ is radially unbounded: $V(x) \to \infty$ as $\|x\| \to
        \infty$.
    \end{enumerate}
    Together with $\cref{lem:isCompact-sublevel-set}$ this implies the
    coercivity hypothesis of \cref{def:isStrictLyapunovFunction}. -/)]
structure IsAsymptoticLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont    : Continuous V
  hV_c1    : ContDiff ℝ 1 V
  hzero    : V x_eq = 0
  hpos     : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x
  hequil   : f x_eq = 0
  hLie_neg : ∀ x : ℝⁿ, x ≠ x_eq → fderiv ℝ V x (f x) < 0
  hradial  : Filter.Tendsto V (Filter.comap norm Filter.atTop) Filter.atTop

/-- A set `S` is positively invariant: trajectories starting in `S` stay in
`S` for `t ≥ 0`. -/
@[blueprint "def:isPositivelyInvariant"
  (statement := /-- A set $S \subseteq \mathbb{R}^{n}$ is \emph{positively
    invariant} for $\dot{x} = f(x)$ when every trajectory $\varphi$
    (see \cref{def:isTrajectory}) with $\varphi(0) \in S$ satisfies
    $\varphi(t) \in S$ for all $t \ge 0$. Positively invariant sets are the
    natural confinement regions in Lyapunov arguments. -/)]
def IsPositivelyInvariant (S : Set ℝⁿ) (f : ℝⁿ → ℝⁿ) : Prop :=
  ∀ φ : ℝ → ℝⁿ, IsTrajectory φ f → φ 0 ∈ S → ∀ t ≥ 0, φ t ∈ S

/-- Sublevel sets of a radially unbounded continuous function are compact.

Proof:
1. Closed: `V ⁻¹' (Set.Iic c)`.
2. Bounded: coercivity gives `R` with `SublevelSet V c ⊆ closedBall 0 R`.
3. Heine-Borel in `ℝⁿ`: closed + bounded = compact. -/
@[blueprint "lem:isCompact-sublevel-set"
  (statement := /-- Let $V : \mathbb{R}^{n} \to \mathbb{R}$ be continuous and
    radially unbounded. Then for every $c \in \mathbb{R}$ the sublevel set
    $\Omega_{c}(V) = \{x : V(x) \le c\}$ (see \cref{def:sublevelSet}) is
    compact. -/)
  (proof := /-- $\Omega_{c}(V)$ is closed as the preimage of $(-\infty, c]$
    under the continuous map $V$. Radial unboundedness gives a compact
    $K \subseteq \mathbb{R}^{n}$ outside of which $V(x) > c$, so $\Omega_{c}(V)
    \subseteq K$ and $\Omega_{c}(V)$ is bounded. By Heine-Borel in
    $\mathbb{R}^{n}$, a closed and bounded set is compact. -/)]
lemma isCompact_sublevel_set
    (V : ℝⁿ → ℝ) (hcont : Continuous V)
    (hradial : Filter.Tendsto V (Filter.comap norm Filter.atTop) Filter.atTop)
    (c : ℝ) : IsCompact (SublevelSet V c) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_Iic.preimage hcont
  · rw [comap_norm_atTop, Metric.cobounded_eq_cocompact] at hradial
    have hev : {x : ℝⁿ | c < V x} ∈ Filter.cocompact ℝⁿ :=
      hradial (Filter.eventually_gt_atTop c)
    rw [Filter.mem_cocompact] at hev
    obtain ⟨K, hK_compact, hK⟩ := hev
    rw [Metric.isBounded_iff_subset_closedBall 0]
    obtain ⟨R, hR⟩ := hK_compact.isBounded.subset_closedBall 0
    refine ⟨R, fun x hx => hR ?_⟩
    by_contra hxK
    have hVx : c < V x := hK (Set.mem_compl hxK)
    exact absurd hVx (not_lt.mpr hx)

/-! ## Extension lemma

If V₀ is C¹ on an open set D containing x₀, it can be extended to a globally
C¹ function agreeing with V₀ on some neighborhood of x₀.

Proof sketch: V = ψ · V₀ where ψ : ℝⁿ → ℝ is a ContDiffBump function with
ψ = 1 near x₀ and supp ψ compactly contained in D. Since supp ψ ⊆ D and ψ
vanishes near ∂D, the product ψ · V₀ is globally C¹. -/

/-- A `C¹` function on an open neighborhood extends to a globally `C¹`
function agreeing with it on a neighborhood of the chosen point. -/
@[blueprint "lem:contDiffOn-extension"
  (statement := /-- Let $D \subseteq \mathbb{R}^{n}$ be open with
    $x_{0} \in D$, and let $V_{0} : \mathbb{R}^{n} \to \mathbb{R}$ be of class
    $C^{1}$ on $D$. There exist a globally $C^{1}$ function $V :
    \mathbb{R}^{n} \to \mathbb{R}$ and an open neighborhood $D' \subseteq D$
    of $x_{0}$ such that $V$ agrees with $V_{0}$ on $D'$. -/)
  (proof := /-- Multiply $V_{0}$ by a smooth bump $\psi : \mathbb{R}^{n} \to
    \mathbb{R}$ supported in $D$ and equal to $1$ on a neighborhood $D'$ of
    $x_{0}$. The product $\psi \cdot V_{0}$ extends by zero to a globally
    $C^{1}$ function on $\mathbb{R}^{n}$, and it agrees with $V_{0}$ on the
    set $\{\psi = 1\} \supseteq D'$. -/)]
lemma contDiffOn_extension
    {D : Set ℝⁿ} (hD : IsOpen D) {x₀ : ℝⁿ} (hx₀ : x₀ ∈ D)
    {V₀ : ℝⁿ → ℝ} (hV : ContDiffOn ℝ 1 V₀ D) :
    ∃ (V : ℝⁿ → ℝ) (D' : Set ℝⁿ), IsOpen D' ∧ x₀ ∈ D' ∧ D' ⊆ D ∧
      ContDiff ℝ 1 V ∧ Set.EqOn V V₀ D' := by
  sorry

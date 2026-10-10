import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Logic.Function.Iterate

import Architect

/-!
# `Stability.DefsDiscrete`

Core definitions for the stability theory of autonomous discrete-time systems
`x(k+1) = f(x(k))`, `k ∈ ℕ`.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems*, Encyclopedia of
Systems and Control Engineering, vol. 2 (2026), pp. 142–154, Definition 2.

## Conventions

* **State space.** An arbitrary normed additive group `E`, in practice a real normed space as
  in `Stability.DefsNonAutonomous`.  Unlike continuous time there are no derivatives, so
  nothing below uses more than the norm.  `E := EuclideanSpace ℝ (Fin n)` gives the concrete
  nonlinear case, and `E := X → ℝ` is where these predicates meet the linear track.
* **Trajectories.** The solution from `x₀` is the sequence of iterates `k ↦ f^[k] x₀`.  In
  discrete time it exists and is unique, so no trajectory predicate is needed, and every
  definition quantifies over initial states.
* **Equilibrium.** Jungers–van de Wouw place the equilibrium at the origin, with `f 0 = 0`.
  Here it is a general `x_eq`, as in the continuous-time files; it is a fixed point of `f`
  (`Function.IsFixedPt f x_eq`), which stability forces (`LyapunovStableDT.isFixedPt`).
* **Names.** Each predicate is its continuous-time counterpart in `Stability.DefsAutonomous`
  with the suffix `DT`.
* **Inequalities.** Non-strict (`≤ δ`, `≤ ε`), as in the reference.

## Contents

* **Stability predicates** (`LyapunovStableDT`, `UnstableDT`, `LocallyAttractiveDT`,
  `LocalAsymptoticStableDT`, `LocallyExponentiallyStableDT`), Definition 2.
* **Global versions** (`GlobalAsymptoticStableDT`, `GloballyExponentiallyStableDT`),
  Remark 2: the local definitions with `δ = +∞`.
* **Ultimate boundedness** (`LocallyUltimatelyBoundedDT`, `GloballyUltimatelyBoundedDT`),
  Definition 3.
* **Basic consequences**: a stable point is a fixed point; exponential stability implies
  asymptotic stability; each global notion implies its local one.
-/

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E]

/-! ## Stability predicates -/

/-- The equilibrium `x_eq` of `x(k+1) = f(x(k))` is **stable** (in the sense of Lyapunov):
every trajectory starting close enough stays within any prescribed distance.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems* (2026),
Definition 2 (*stability*), estimate (4).  They place the equilibrium at the origin. -/
@[blueprint "def:lyapunovStableDT"
  (title := "Stability of a discrete-time system")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ of $x_{k+1} = f(x_k)$ is \emph{stable}
    (in the sense of Lyapunov) when
    \[
      \forall \varepsilon > 0,\;\exists\,\delta > 0,\;
      \|x_0 - x_{\mathrm{eq}}\| \le \delta \;\Rightarrow\;
      \forall k \in \mathbb{N},\; \|x_k - x_{\mathrm{eq}}\| \le \varepsilon,
    \]
    where $x_k = f^{k}(x_0)$ is the trajectory from $x_0$.

    Reference: Jungers and van de Wouw, \emph{Discrete-time nonlinear control systems},
    Encyclopedia of Systems and Control Engineering (2026), Definition 2 (\emph{stability}),
    estimate (4).  They place the equilibrium at the origin. -/)]
def LyapunovStableDT (f : E → E) (x_eq : E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x₀ : E, ‖x₀ - x_eq‖ ≤ δ → ∀ k : ℕ, ‖f^[k] x₀ - x_eq‖ ≤ ε

/-- The equilibrium `x_eq` is **unstable** when it is not stable.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems* (2026),
Definition 2 (*instability*). -/
@[blueprint "def:unstableDT"
  (title := "Instability of a discrete-time system")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ of $x_{k+1} = f(x_k)$ is
    \emph{unstable} when it is not stable (\cref{def:lyapunovStableDT}).

    Reference: Jungers and van de Wouw, \emph{Discrete-time nonlinear control systems}
    (2026), Definition 2 (\emph{instability}). -/)]
def UnstableDT (f : E → E) (x_eq : E) : Prop :=
  ¬ LyapunovStableDT f x_eq

/-- The equilibrium `x_eq` is **locally attractive**: every trajectory starting close enough
converges to it.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems* (2026),
Definition 2 (*attractivity*), estimate (5). -/
@[blueprint "def:locallyAttractiveDT"
  (title := "Local attractivity of a discrete-time system")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ of $x_{k+1} = f(x_k)$ is
    \emph{locally attractive} when there is $\delta > 0$ with
    \[
      \|x_0 - x_{\mathrm{eq}}\| \le \delta \;\Rightarrow\;
      \lim_{k \to \infty} x_k = x_{\mathrm{eq}}.
    \]

    Reference: Jungers and van de Wouw, \emph{Discrete-time nonlinear control systems}
    (2026), Definition 2 (\emph{attractivity}), estimate (5). -/)]
def LocallyAttractiveDT (f : E → E) (x_eq : E) : Prop :=
  ∃ δ > 0, ∀ x₀ : E, ‖x₀ - x_eq‖ ≤ δ → Tendsto (fun k : ℕ => f^[k] x₀) atTop (𝓝 x_eq)

/-- The equilibrium `x_eq` is **locally asymptotically stable**: stable and locally
attractive.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems* (2026),
Definition 2 (*asymptotic stability*). -/
@[blueprint "def:localAsymptoticStableDT"
  (title := "Local asymptotic stability of a discrete-time system")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ of $x_{k+1} = f(x_k)$ is
    \emph{locally asymptotically stable} when it is stable (\cref{def:lyapunovStableDT}) and
    locally attractive (\cref{def:locallyAttractiveDT}).

    Reference: Jungers and van de Wouw, \emph{Discrete-time nonlinear control systems}
    (2026), Definition 2 (\emph{asymptotic stability}). -/)]
def LocalAsymptoticStableDT (f : E → E) (x_eq : E) : Prop :=
  LyapunovStableDT f x_eq ∧ LocallyAttractiveDT f x_eq

/-- The equilibrium `x_eq` is **locally exponentially stable** (geometrically stable):
trajectories starting close enough converge at a geometric rate `ρ < 1`, with overshoot
constant `C`.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems* (2026),
Definition 2 (*exponential stability or geometric stability*), estimate (6). -/
@[blueprint "def:locallyExponentiallyStableDT"
  (title := "Local exponential stability of a discrete-time system")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ of $x_{k+1} = f(x_k)$ is
    \emph{locally exponentially stable}, or \emph{geometrically stable}, when there are
    $\delta > 0$, $C > 0$ and $0 < \rho < 1$ with
    \[
      \|x_0 - x_{\mathrm{eq}}\| \le \delta \;\Rightarrow\;
      \forall k \in \mathbb{N},\;
      \|x_k - x_{\mathrm{eq}}\| \le C \rho^{k} \|x_0 - x_{\mathrm{eq}}\|.
    \]

    Reference: Jungers and van de Wouw, \emph{Discrete-time nonlinear control systems}
    (2026), Definition 2 (\emph{exponential stability or geometric stability}),
    estimate (6). -/)]
def LocallyExponentiallyStableDT (f : E → E) (x_eq : E) : Prop :=
  ∃ δ > 0, ∃ C > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
    ∀ x₀ : E, ‖x₀ - x_eq‖ ≤ δ → ∀ k : ℕ, ‖f^[k] x₀ - x_eq‖ ≤ C * ρ ^ k * ‖x₀ - x_eq‖

/-! ## Global versions -/

/-- The equilibrium `x_eq` is **globally asymptotically stable**: stable, and every trajectory
converges to it.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems* (2026), Remark 2:
`LocalAsymptoticStableDT` with `δ = +∞`. -/
@[blueprint "def:globalAsymptoticStableDT"
  (title := "Global asymptotic stability of a discrete-time system")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ of $x_{k+1} = f(x_k)$ is
    \emph{globally asymptotically stable} when it is stable (\cref{def:lyapunovStableDT}) and
    $\lim_{k \to \infty} x_k = x_{\mathrm{eq}}$ for every initial state $x_0$.

    Reference: Jungers and van de Wouw, \emph{Discrete-time nonlinear control systems}
    (2026), Remark 2: \cref{def:localAsymptoticStableDT} with $\delta = +\infty$. -/)]
def GlobalAsymptoticStableDT (f : E → E) (x_eq : E) : Prop :=
  LyapunovStableDT f x_eq ∧ ∀ x₀ : E, Tendsto (fun k : ℕ => f^[k] x₀) atTop (𝓝 x_eq)

/-- The equilibrium `x_eq` is **globally exponentially stable** (globally geometrically
stable): the geometric bound holds from every initial state.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems* (2026), Remark 2:
`LocallyExponentiallyStableDT` with `δ = +∞`. -/
@[blueprint "def:globallyExponentiallyStableDT"
  (title := "Global exponential stability of a discrete-time system")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ of $x_{k+1} = f(x_k)$ is
    \emph{globally exponentially stable}, or \emph{globally geometrically stable}, when there
    are $C > 0$ and $0 < \rho < 1$ with
    $\|x_k - x_{\mathrm{eq}}\| \le C \rho^{k} \|x_0 - x_{\mathrm{eq}}\|$ for every initial
    state $x_0$ and every $k \in \mathbb{N}$.

    Reference: Jungers and van de Wouw, \emph{Discrete-time nonlinear control systems}
    (2026), Remark 2: \cref{def:locallyExponentiallyStableDT} with $\delta = +\infty$. -/)]
def GloballyExponentiallyStableDT (f : E → E) (x_eq : E) : Prop :=
  ∃ C > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
    ∀ x₀ : E, ∀ k : ℕ, ‖f^[k] x₀ - x_eq‖ ≤ C * ρ ^ k * ‖x₀ - x_eq‖

/-! ## Ultimate boundedness -/

/-- The system is **locally ultimately bounded** with bound `ε` around the point `x_c`: there
is `γ > 0` such that trajectories starting within any `δ < γ` of `x_c` are within `ε` of it
from some finite time `K(δ, ε)` on.

This is a property of the system rather than of an equilibrium, so `x_c` need not be a fixed
point.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems* (2026),
Definition 3.  They measure from the origin. -/
@[blueprint "def:locallyUltimatelyBoundedDT"
  (title := "Local ultimate boundedness of a discrete-time system")
  (statement := /-- The system $x_{k+1} = f(x_k)$ is \emph{locally ultimately bounded} with
    bound $\varepsilon$ around $x_c$ when there is $\gamma > 0$ such that for every
    $0 < \delta < \gamma$ there is a finite $K = K(\delta, \varepsilon) \in \mathbb{N}$ with
    \[
      \|x_0 - x_c\| \le \delta \;\Rightarrow\; \forall k \ge K,\; \|x_k - x_c\| \le \varepsilon.
    \]

    Reference: Jungers and van de Wouw, \emph{Discrete-time nonlinear control systems}
    (2026), Definition 3.  They measure from the origin. -/)]
def LocallyUltimatelyBoundedDT (f : E → E) (x_c : E) (ε : ℝ) : Prop :=
  ∃ γ > 0, ∀ δ, 0 < δ → δ < γ → ∃ K : ℕ, ∀ x₀ : E, ‖x₀ - x_c‖ ≤ δ →
    ∀ k ≥ K, ‖f^[k] x₀ - x_c‖ ≤ ε

/-- The system is **globally ultimately bounded** with bound `ε` around `x_c`: every `δ > 0`
admits a finite time `K(δ, ε)` after which trajectories starting within `δ` of `x_c` are within
`ε` of it.

Reference: Jungers and van de Wouw, *Discrete-time nonlinear control systems* (2026),
Definition 3: `LocallyUltimatelyBoundedDT` with `γ = +∞`. -/
@[blueprint "def:globallyUltimatelyBoundedDT"
  (title := "Global ultimate boundedness of a discrete-time system")
  (statement := /-- The system $x_{k+1} = f(x_k)$ is \emph{globally ultimately bounded} with
    bound $\varepsilon$ around $x_c$ when \cref{def:locallyUltimatelyBoundedDT} holds with
    $\gamma = +\infty$: every $\delta > 0$ admits a finite $K(\delta, \varepsilon)$.

    Reference: Jungers and van de Wouw, \emph{Discrete-time nonlinear control systems}
    (2026), Definition 3. -/)]
def GloballyUltimatelyBoundedDT (f : E → E) (x_c : E) (ε : ℝ) : Prop :=
  ∀ δ > 0, ∃ K : ℕ, ∀ x₀ : E, ‖x₀ - x_c‖ ≤ δ → ∀ k ≥ K, ‖f^[k] x₀ - x_c‖ ≤ ε

/-! ## Basic consequences -/

/-- A stable equilibrium is a fixed point of `f`: the trajectory from `x_eq` itself must stay
within every `ε` of `x_eq`, so its first step `f x_eq` is at distance `0`. -/
@[blueprint "lem:lyapunovStableDT-isFixedPt"
  (title := "A stable equilibrium is a fixed point")
  (statement := /-- If $x_{\mathrm{eq}}$ is stable (\cref{def:lyapunovStableDT}), then
    $f(x_{\mathrm{eq}}) = x_{\mathrm{eq}}$. -/)
  (proof := /-- The trajectory from $x_0 = x_{\mathrm{eq}}$ satisfies
    $\|f(x_{\mathrm{eq}}) - x_{\mathrm{eq}}\| \le \varepsilon$ for every $\varepsilon > 0$. -/)]
lemma LyapunovStableDT.isFixedPt {f : E → E} {x_eq : E} (h : LyapunovStableDT f x_eq) :
    Function.IsFixedPt f x_eq := by
  -- `‖f x_eq - x_eq‖ ≤ ε` for every `ε > 0`, by stability applied at `x₀ = x_eq`, `k = 1`
  have h_small : ∀ ε > 0, ‖f x_eq - x_eq‖ ≤ ε := fun ε hε => by
    obtain ⟨δ, hδ, h_stay⟩ := h ε hε
    simpa using h_stay x_eq (by simpa using hδ.le) 1
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => by
    simpa using h_small ε hε))

/-- A geometric bound `C ρᵏ ‖x₀ - x_eq‖` on the trajectories from a ball of radius `δ₀` gives
stability: since `ρᵏ ≤ 1`, take `δ = min δ₀ (ε / C)`. -/
private lemma lyapunovStableDT_of_geometric_bound {f : E → E} {x_eq : E} {δ₀ C ρ : ℝ}
    (hδ₀ : 0 < δ₀) (hC : 0 < C) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1)
    (h_bound : ∀ x₀ : E, ‖x₀ - x_eq‖ ≤ δ₀ → ∀ k : ℕ,
      ‖f^[k] x₀ - x_eq‖ ≤ C * ρ ^ k * ‖x₀ - x_eq‖) :
    LyapunovStableDT f x_eq := by
  intro ε hε
  refine ⟨min δ₀ (ε / C), lt_min hδ₀ (div_pos hε hC), fun x₀ hx₀ k => ?_⟩
  -- `ρᵏ ≤ 1`, so the bound is at most `C ‖x₀ - x_eq‖ ≤ C (ε / C) = ε`
  have hρk : ρ ^ k ≤ 1 := pow_le_one₀ hρ_pos.le hρ_lt.le
  have hx₀_ε : C * ‖x₀ - x_eq‖ ≤ ε := by
    rw [← le_div_iff₀' hC]
    exact hx₀.trans (min_le_right _ _)
  calc ‖f^[k] x₀ - x_eq‖ ≤ C * ρ ^ k * ‖x₀ - x_eq‖ := h_bound x₀ (hx₀.trans (min_le_left _ _)) k
    _ ≤ C * 1 * ‖x₀ - x_eq‖ := by gcongr
    _ ≤ ε := by rwa [mul_one]

/-- A geometric bound `C ρᵏ ‖x₀ - x_eq‖` with `ρ < 1` forces the trajectory from `x₀` to
converge to `x_eq`. -/
private lemma tendsto_of_geometric_bound {f : E → E} {x_eq x₀ : E} {C ρ : ℝ}
    (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1)
    (h_bound : ∀ k : ℕ, ‖f^[k] x₀ - x_eq‖ ≤ C * ρ ^ k * ‖x₀ - x_eq‖) :
    Tendsto (fun k : ℕ => f^[k] x₀) atTop (𝓝 x_eq) := by
  have h_geom : Tendsto (fun k : ℕ => C * ρ ^ k * ‖x₀ - x_eq‖) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ_pos.le hρ_lt).const_mul C).mul_const
      ‖x₀ - x_eq‖
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun k => norm_nonneg _) h_bound h_geom

/-- Exponential stability implies asymptotic stability. -/
@[blueprint "lem:localAsymptoticStableDT-of-exponentiallyStable"
  (title := "Exponential stability implies asymptotic stability (discrete time)")
  (statement := /-- If $x_{\mathrm{eq}}$ is locally exponentially stable
    (\cref{def:locallyExponentiallyStableDT}), it is locally asymptotically stable
    (\cref{def:localAsymptoticStableDT}). -/)
  (proof := /-- Since $0 < \rho < 1$, the bound $C\rho^{k}\|x_0 - x_{\mathrm{eq}}\|$ is at
    most $C\|x_0 - x_{\mathrm{eq}}\|$, so $\delta = \min(\delta_0, \varepsilon / C)$ witnesses
    stability; and it tends to $0$ as $k \to \infty$, so the same $\delta_0$ witnesses
    attractivity. -/)]
lemma LocallyExponentiallyStableDT.localAsymptoticStableDT {f : E → E} {x_eq : E}
    (h : LocallyExponentiallyStableDT f x_eq) : LocalAsymptoticStableDT f x_eq := by
  obtain ⟨δ₀, hδ₀, C, hC, ρ, hρ_pos, hρ_lt, h_bound⟩ := h
  exact ⟨lyapunovStableDT_of_geometric_bound hδ₀ hC hρ_pos hρ_lt h_bound,
    δ₀, hδ₀, fun x₀ hx₀ => tendsto_of_geometric_bound hρ_pos hρ_lt (h_bound x₀ hx₀)⟩

/-- Global exponential stability implies global asymptotic stability. -/
@[blueprint "lem:globalAsymptoticStableDT-of-exponentiallyStable"
  (title := "Global exponential stability implies global asymptotic stability")
  (statement := /-- If $x_{\mathrm{eq}}$ is globally exponentially stable
    (\cref{def:globallyExponentiallyStableDT}), it is globally asymptotically stable
    (\cref{def:globalAsymptoticStableDT}). -/)
  (proof := /-- As in \cref{lem:localAsymptoticStableDT-of-exponentiallyStable}, with no
    restriction on the initial state. -/)]
lemma GloballyExponentiallyStableDT.globalAsymptoticStableDT {f : E → E} {x_eq : E}
    (h : GloballyExponentiallyStableDT f x_eq) : GlobalAsymptoticStableDT f x_eq := by
  obtain ⟨C, hC, ρ, hρ_pos, hρ_lt, h_bound⟩ := h
  exact ⟨lyapunovStableDT_of_geometric_bound one_pos hC hρ_pos hρ_lt fun x₀ _ => h_bound x₀,
    fun x₀ => tendsto_of_geometric_bound hρ_pos hρ_lt (h_bound x₀)⟩

/-- Global exponential stability implies local exponential stability, with any radius. -/
@[blueprint "lem:locallyExponentiallyStableDT-of-global"
  (title := "Global exponential stability implies local exponential stability")
  (statement := /-- If $x_{\mathrm{eq}}$ is globally exponentially stable
    (\cref{def:globallyExponentiallyStableDT}), it is locally exponentially stable
    (\cref{def:locallyExponentiallyStableDT}). -/)
  (proof := /-- Take $\delta = 1$; the global bound holds in particular on that ball. -/)]
lemma GloballyExponentiallyStableDT.locallyExponentiallyStableDT {f : E → E} {x_eq : E}
    (h : GloballyExponentiallyStableDT f x_eq) : LocallyExponentiallyStableDT f x_eq := by
  obtain ⟨C, hC, ρ, hρ_pos, hρ_lt, h_bound⟩ := h
  exact ⟨1, one_pos, C, hC, ρ, hρ_pos, hρ_lt, fun x₀ _ => h_bound x₀⟩

/-- Global asymptotic stability implies local asymptotic stability, with any radius. -/
@[blueprint "lem:localAsymptoticStableDT-of-global"
  (title := "Global asymptotic stability implies local asymptotic stability")
  (statement := /-- If $x_{\mathrm{eq}}$ is globally asymptotically stable
    (\cref{def:globalAsymptoticStableDT}), it is locally asymptotically stable
    (\cref{def:localAsymptoticStableDT}). -/)
  (proof := /-- Take $\delta = 1$ in the attractivity condition. -/)]
lemma GlobalAsymptoticStableDT.localAsymptoticStableDT {f : E → E} {x_eq : E}
    (h : GlobalAsymptoticStableDT f x_eq) : LocalAsymptoticStableDT f x_eq :=
  ⟨h.1, 1, one_pos, fun x₀ _ => h.2 x₀⟩

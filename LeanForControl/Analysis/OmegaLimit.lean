import Mathlib.Dynamics.OmegaLimit
import Mathlib.Topology.Order.Real
import Architect

/-!
# The ω-limit set of a curve or sequence

The ω-limit set `ω(φ)` of `φ : τ → X` is the set of points `φ` returns arbitrarily close to,
arbitrarily late: the cluster points of `φ` along `atTop`.  The index `τ` is any preorder, so the
same set serves a curve (`τ = ℝ`, continuous time) and a sequence (`τ = ℕ`, discrete time).  It is
Mathlib's `omegaLimit` for the one-element family (`omegaLimitSet_eq_omegaLimit`); stated as a set
of cluster points it reads as what it is.

Nothing here is about differential or difference equations; these are the topological facts
LaSalle's invariance principle uses.

## Main declarations

* `omegaLimitSet` and `mem_omegaLimitSet_iff` — the ω-limit set and its membership criterion.
* `omegaLimitSet_eq_omegaLimit` — it is Mathlib's `omegaLimit` of the one-element family.
* `eq_of_tendsto_of_mem_omegaLimitSet` — if `g(φ(t)) → L` for a continuous `g`, then `g ≡ L`
  on `ω(φ)`.
* `omegaLimitSet_subset_of_eventually_mem` — if `φ` is eventually in a closed set, so is its
  ω-limit set.
* `tendsto_nhdsSet_of_omegaLimitSet_subset` — `φ` eventually in a compact set converges to every
  set containing its ω-limit set.
-/

open Filter Set Topology

variable {τ X : Type*} [Preorder τ] [TopologicalSpace X]

/-- The ω-limit set of `φ : τ → X`: the cluster points of `φ` as `t → ∞`, the points `φ`
returns arbitrarily close to, arbitrarily late. -/
@[blueprint "def:omegaLimitSet"
  (title := "$\\omega$-limit set")
  (statement := /-- The \emph{$\omega$-limit set} of $\varphi : \tau \to X$, for $\tau$ a
    preordered index set such as $\mathbb{R}$ or $\mathbb{N}$, is the set of cluster points of
    $\varphi$ as $t \to \infty$:
    \[
      \omega(\varphi) = \bigcap_{T} \overline{\{\varphi(t) : t \ge T\}},
    \]
    the points $y$ such that $\varphi(t)$ is frequently in every neighbourhood of $y$ as
    $t \to \infty$. -/)]
def omegaLimitSet (φ : τ → X) : Set X :=
  {y | MapClusterPt y atTop φ}

/-- Membership unfolded: `y` is an ω-limit point of `φ` exactly when `φ` is frequently in every
neighbourhood of `y`. -/
@[blueprint "lem:mem-omegaLimitSet-iff"
  (title := "Membership in the $\\omega$-limit set")
  (latexEnv := "lemma")
  (statement := /-- $y \in \omega(\varphi)$ (\cref{def:omegaLimitSet}) if and only if for every
    neighbourhood $U$ of $y$ there are arbitrarily large $t$ with $\varphi(t) \in U$. -/)]
lemma mem_omegaLimitSet_iff {φ : τ → X} {y : X} :
    y ∈ omegaLimitSet φ ↔ ∀ U ∈ 𝓝 y, ∃ᶠ t in atTop, φ t ∈ U :=
  mapClusterPt_iff_frequently

/-- The ω-limit set of `φ` is Mathlib's `omegaLimit` of the family with one member, `φ`, indexed
by `Unit`. -/
@[blueprint "lem:omegaLimitSet-eq-omegaLimit"
  (title := "The $\\omega$-limit set as Mathlib's $\\omega$-limit")
  (latexEnv := "lemma")
  (statement := /-- \cref{def:omegaLimitSet} is the $\omega$-limit, in the sense of topological
    dynamics, of the one-member family $\{\varphi\}$. -/)]
lemma omegaLimitSet_eq_omegaLimit (φ : τ → X) :
    omegaLimitSet φ = omegaLimit atTop (fun (t : τ) (_ : Unit) => φ t) univ := by
  ext y
  rw [mem_omegaLimitSet_iff, mem_omegaLimit_iff_frequently]
  refine forall₂_congr fun U _ => ⟨fun h => h.mono fun t ht => ⟨(), by simpa using ht⟩,
    fun h => h.mono fun t ht => ?_⟩
  obtain ⟨_, -, ht⟩ := ht
  exact ht

/-- If `g(φ(t)) → L` for a continuous `g`, then `g` takes the value `L` on all of `ω(φ)`: `g(y)`
is a cluster point of `g ∘ φ`, which converges to `L`. -/
@[blueprint "lem:eq-of-tendsto-of-mem-omegaLimitSet"
  (title := "A limit of $g \\circ \\varphi$ is the value of $g$ on $\\omega(\\varphi)$")
  (latexEnv := "lemma")
  (statement := /-- Let $g : X \to Y$ be continuous, $Y$ Hausdorff, and
    $g(\varphi(t)) \to L$ as $t \to \infty$.  Then $g(y) = L$ for every
    $y \in \omega(\varphi)$ (\cref{def:omegaLimitSet}). -/)
  (proof := /-- $g(y)$ is a cluster point of $g \circ \varphi$, which converges to $L$; in a
    Hausdorff space the two coincide. -/)]
lemma eq_of_tendsto_of_mem_omegaLimitSet {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {φ : τ → X} {g : X → Y} {L : Y} (hg : Continuous g) (h_lim : Tendsto (g ∘ φ) atTop (𝓝 L))
    {y : X} (hy : y ∈ omegaLimitSet φ) : g y = L :=
  eq_of_nhds_neBot ((hy.continuousAt_comp hg.continuousAt).clusterPt.neBot.mono
    (inf_le_inf_left _ h_lim))

/-- If `φ` is eventually in a closed set `Ω`, so is its ω-limit set. -/
@[blueprint "lem:omegaLimitSet-subset-of-eventually-mem"
  (title := "The $\\omega$-limit set of a curve trapped in a closed set")
  (latexEnv := "lemma")
  (statement := /-- If $\Omega$ is closed and $\varphi(t) \in \Omega$ for all large $t$, then
    $\omega(\varphi) \subseteq \Omega$. -/)
  (proof := /-- A point outside $\Omega$ has the open neighbourhood $X \setminus \Omega$, which
    $\varphi$ eventually avoids. -/)]
lemma omegaLimitSet_subset_of_eventually_mem {φ : τ → X} {Ω : Set X} (hΩ : IsClosed Ω)
    (h_ev : ∀ᶠ t in atTop, φ t ∈ Ω) : omegaLimitSet φ ⊆ Ω := fun y hy => by
  by_contra hyΩ
  obtain ⟨t, h_out, h_in⟩ :=
    ((mem_omegaLimitSet_iff.mp hy _ (hΩ.isOpen_compl.mem_nhds hyΩ)).and_eventually h_ev).exists
  exact h_out h_in

/-- If `φ` is eventually in a compact set, it converges to every set `M` containing its ω-limit
set: it is eventually inside each open neighbourhood of `M`. -/
@[blueprint "lem:tendsto-nhdsSet-of-omegaLimitSet-subset"
  (title := "Convergence to a set containing the $\\omega$-limit set")
  (latexEnv := "lemma")
  (statement := /-- If $\varphi(t)$ lies in a compact set for all large $t$ and
    $\omega(\varphi) \subseteq M$, then $\varphi(t) \to M$: for every open $W \supseteq M$,
    $\varphi(t) \in W$ for all large $t$. -/)
  (proof := /-- Mathlib's
    \texttt{eventually\_mapsTo\_of\_isCompact\_absorbing\_of\_isOpen\_of\_omegaLimit\_subset}
    (\cref{lem:omegaLimitSet-eq-omegaLimit}): a family eventually absorbed by a compact set is
    eventually inside every open set containing its $\omega$-limit set. -/)]
lemma tendsto_nhdsSet_of_omegaLimitSet_subset [T2Space X] {φ : τ → X} {K M : Set X}
    (hK : IsCompact K) (h_ev : ∀ᶠ t in atTop, φ t ∈ K) (hM : omegaLimitSet φ ⊆ M) :
    Tendsto φ atTop (𝓝ˢ M) := by
  rw [tendsto_def]
  intro U hU
  obtain ⟨W, hW_open, hMW, hWU⟩ := mem_nhdsSet_iff_exists.mp hU
  have h_W : ∀ᶠ t in atTop, MapsTo (fun (_ : Unit) => φ t) univ W :=
    eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset atTop
      (fun (t : τ) (_ : Unit) => φ t) univ hK (h_ev.mono fun t ht _ _ => ht) hW_open
      (omegaLimitSet_eq_omegaLimit φ ▸ hM.trans hMW)
  exact h_W.mono fun t ht => hWU (ht (mem_univ ()))

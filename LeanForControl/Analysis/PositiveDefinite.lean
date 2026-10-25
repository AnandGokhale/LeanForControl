import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Group.Uniform
import Architect

/-!
# Positive definite functions

A real-valued function is *positive definite* on a set about a point when it is continuous there,
vanishes at the point, and is positive elsewhere in the set.  This is the function sense of the
term, used for Lyapunov functions and their comparison bounds; it is unrelated to the algebraic
notions of Mathlib (`Matrix.PosDef`, `QuadraticMap.PosDef`), which concern matrices and forms.
-/

/-- `W` is **positive definite on `S`** about `x₀`: continuous on `S`, zero at `x₀` and positive
at every other point of `S`. -/
@[blueprint "def:isPositiveDefiniteOn"
  (title := "Positive definite function")
  (statement := /-- A function $W$ is \emph{positive definite} on $S$ about $x_0$ when it is
    continuous on $S$, $W(x_0) = 0$, and $W(x) > 0$ for every $x \in S \setminus \{x_0\}$. -/)]
def IsPositiveDefiniteOn {E : Type*} [TopologicalSpace E] (W : E → ℝ) (x₀ : E) (S : Set E) :
    Prop :=
  ContinuousOn W S ∧ W x₀ = 0 ∧ ∀ x ∈ S, x ≠ x₀ → 0 < W x

namespace IsPositiveDefiniteOn

variable {E : Type*} [TopologicalSpace E] {W : E → ℝ} {x₀ : E} {S T : Set E}

/-- A positive definite function is nonnegative on its set. -/
lemma nonneg (hW : IsPositiveDefiniteOn W x₀ S) {x : E} (hx : x ∈ S) : 0 ≤ W x := by
  rcases eq_or_ne x x₀ with rfl | hne
  · exact hW.2.1.ge
  · exact (hW.2.2 x hx hne).le

/-- A positive definite function on `S` is positive definite on every subset of `S`. -/
lemma mono (hW : IsPositiveDefiniteOn W x₀ S) (hTS : T ⊆ S) : IsPositiveDefiniteOn W x₀ T :=
  ⟨hW.1.mono hTS, hW.2.1, fun x hx hne => hW.2.2 x (hTS hx) hne⟩

end IsPositiveDefiniteOn

/-- **A radial function is positive definite when its profile is**: if `g` is continuous on
`[0, ∞)`, vanishes at `0` and is positive on `(0, ∞)`, then `x ↦ g(‖x - x₀‖)` is positive
definite about `x₀` on every set. -/
@[blueprint "lem:isPositiveDefiniteOn-comp-norm-sub"
  (title := "Radial positive definite functions")
  (latexEnv := "lemma")
  (statement := /-- Let $g$ be continuous on $[0, \infty)$ with $g(0) = 0$ and $g(r) > 0$ for
    $r > 0$.  Then $x \mapsto g(\|x - x_0\|)$ is positive definite about $x_0$ on every set
    (\cref{def:isPositiveDefiniteOn}). -/)]
lemma isPositiveDefiniteOn_comp_norm_sub {E : Type*} [NormedAddCommGroup E] {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ici 0)) (hg0 : g 0 = 0) (hg_pos : ∀ r, 0 < r → 0 < g r)
    (x₀ : E) (S : Set E) : IsPositiveDefiniteOn (fun x => g ‖x - x₀‖) x₀ S :=
  ⟨(hg.comp_continuous (continuous_id.sub continuous_const).norm
      fun _ => Set.mem_Ici.2 (norm_nonneg _)).continuousOn,
    by simp [hg0], fun _ _ hx => hg_pos _ (norm_pos_iff.2 (sub_ne_zero.2 hx))⟩

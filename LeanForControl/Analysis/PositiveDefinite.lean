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

/-- **A composition of positive definite functions is positive definite**: if `g` is positive
definite about `0` on `[0, ∞)` and `W` is positive definite about `x₀` on `S`, so is `g ∘ W`.  `W`
is nonnegative, so it lands where `g` is positive definite, and it vanishes only at `x₀`. -/
@[blueprint "lem:isPositiveDefiniteOn-comp"
  (title := "Compositions of positive definite functions")
  (latexEnv := "lemma")
  (statement := /-- If $g$ is positive definite about $0$ on $[0, \infty)$ and $W$ is positive
    definite about $x_0$ on $S$ (\cref{def:isPositiveDefiniteOn}), then $g \circ W$ is positive
    definite about $x_0$ on $S$. -/)]
lemma IsPositiveDefiniteOn.comp {E : Type*} [TopologicalSpace E] {g : ℝ → ℝ} {W : E → ℝ}
    {x₀ : E} {S : Set E} (hg : IsPositiveDefiniteOn g 0 (Set.Ici 0))
    (hW : IsPositiveDefiniteOn W x₀ S) : IsPositiveDefiniteOn (g ∘ W) x₀ S :=
  ⟨hg.1.comp hW.1 fun _ hx => hW.nonneg hx, by simp [hW.2.1, hg.2.1],
    fun x hx hne => hg.2.2 _ (hW.nonneg hx) (hW.2.2 x hx hne).ne'⟩

/-- The distance to `x₀`, `x ↦ ‖x - x₀‖`, is positive definite about `x₀`. -/
@[blueprint "lem:isPositiveDefiniteOn-norm-sub"
  (title := "The distance is positive definite")
  (latexEnv := "lemma")
  (statement := /-- $x \mapsto \|x - x_0\|$ is positive definite about $x_0$ on every set
    (\cref{def:isPositiveDefiniteOn}). -/)]
lemma isPositiveDefiniteOn_norm_sub {E : Type*} [NormedAddCommGroup E] (x₀ : E) (S : Set E) :
    IsPositiveDefiniteOn (fun x => ‖x - x₀‖) x₀ S :=
  ⟨(continuous_id.sub continuous_const).norm.continuousOn, by simp,
    fun _ _ hx => norm_pos_iff.2 (sub_ne_zero.2 hx)⟩

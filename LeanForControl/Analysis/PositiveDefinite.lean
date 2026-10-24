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

/-- A positive multiple of the squared distance to `x₀` is positive definite about `x₀`. -/
lemma isPositiveDefiniteOn_mul_norm_sub_sq {E : Type*} [NormedAddCommGroup E] {c : ℝ}
    (hc : 0 < c) (x₀ : E) (S : Set E) :
    IsPositiveDefiniteOn (fun x => c * ‖x - x₀‖ ^ 2) x₀ S :=
  ⟨(continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2)).continuousOn,
    by simp, fun x _ hx => mul_pos hc (pow_pos (norm_pos_iff.2 (sub_ne_zero.2 hx)) 2)⟩

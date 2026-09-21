import LeanForControl.LinearSystems.Realization.Defs
import Mathlib.Data.Matrix.Basis
import Architect

/-!
# Markov parameters and realization equivalence

The strictly proper behavior of `(A,B,C,D)` is represented algebraically by
the sequence `C A^k B`; the feedthrough matrix `D` is recorded separately.
This is time-agnostic and is the common algebraic content of discrete impulse
responses and continuous-time transfer-function expansions.

References: Kailath, *Linear Systems*; Hespanha, *Linear Systems Theory*.
-/

namespace LinearSystems

open Matrix

namespace Realization

variable {𝕜 : Type*} [CommSemiring 𝕜]
variable {n n₁ n₂ n₃ m p : ℕ}

/-- The `k`-th Markov parameter `C A^k B` of a realization.

Reference: Kailath, *Linear Systems*. -/
def markovParameter (r : Realization 𝕜 n m p) (k : ℕ) :
    Matrix (Fin p) (Fin m) 𝕜 :=
  r.C * r.A ^ k * r.B

/-- Two realizations have the same external behavior when their feedthrough
matrices and all Markov parameters agree. Their state dimensions may differ.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "def:realization-behavioral-equivalence"
  (statement := /-- Two realizations are behaviorally equivalent when they
    have the same feedthrough matrix and the same Markov parameters
    $CA^kB$ for every $k\geq 0$. -/)]
def BehaviorallyEquivalent
    (r₁ : Realization 𝕜 n₁ m p) (r₂ : Realization 𝕜 n₂ m p) : Prop :=
  r₁.D = r₂.D ∧ ∀ k : ℕ, r₁.markovParameter k = r₂.markovParameter k

/-- Behavioral equivalence is reflexive.

Original: relation API for LeanForControl. -/
theorem behaviorallyEquivalent_refl (r : Realization 𝕜 n m p) :
    r.BehaviorallyEquivalent r :=
  ⟨rfl, fun _ => rfl⟩

/-- Behavioral equivalence is symmetric.

Original: relation API for LeanForControl. -/
theorem BehaviorallyEquivalent.symm {r₁ : Realization 𝕜 n₁ m p}
    {r₂ : Realization 𝕜 n₂ m p} (h : r₁.BehaviorallyEquivalent r₂) :
    r₂.BehaviorallyEquivalent r₁ :=
  ⟨h.1.symm, fun k => (h.2 k).symm⟩

/-- Behavioral equivalence is transitive.

Original: relation API for LeanForControl. -/
theorem BehaviorallyEquivalent.trans {r₁ : Realization 𝕜 n₁ m p}
    {r₂ : Realization 𝕜 n₂ m p} {r₃ : Realization 𝕜 n₃ m p}
    (h₁₂ : r₁.BehaviorallyEquivalent r₂)
    (h₂₃ : r₂.BehaviorallyEquivalent r₃) :
    r₁.BehaviorallyEquivalent r₃ :=
  ⟨h₁₂.1.trans h₂₃.1, fun k => (h₁₂.2 k).trans (h₂₃.2 k)⟩

/-- A matrix similarity witness between realizations of the same state
dimension. `Tinv` records invertibility, while the intertwining equations
state that `T` transports states, inputs, and outputs.

Reference: Kailath, *Linear Systems*. -/
structure Similar (r₁ r₂ : Realization 𝕜 n m p) where
  /-- Change-of-state-coordinates matrix. -/
  T : Matrix (Fin n) (Fin n) 𝕜
  /-- Inverse change-of-state-coordinates matrix. -/
  Tinv : Matrix (Fin n) (Fin n) 𝕜
  /-- `Tinv` is a left inverse of `T`. -/
  Tinv_mul_T : Tinv * T = 1
  /-- `Tinv` is a right inverse of `T`. -/
  T_mul_Tinv : T * Tinv = 1
  /-- The state matrices intertwine with `T`. -/
  state : r₂.A * T = T * r₁.A
  /-- The input matrices intertwine with `T`. -/
  input : r₂.B = T * r₁.B
  /-- The output matrices intertwine with `T`. -/
  output : r₂.C * T = r₁.C
  /-- Similar realizations have the same feedthrough matrix. -/
  feedthrough : r₂.D = r₁.D

/-- The state intertwining equation propagates to every matrix power.

Original: algebraic similarity infrastructure for LeanForControl. -/
lemma Similar.state_pow (r₁ r₂ : Realization 𝕜 n m p) (h : Similar r₁ r₂)
    (k : ℕ) : r₂.A ^ k * h.T = h.T * r₁.A ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ, Matrix.mul_assoc, ih]
      simp only [← Matrix.mul_assoc, h.state]

/-- Similar realizations have identical Markov parameters.

Reference: Kailath, *Linear Systems*. -/
theorem Similar.markovParameter_eq (r₁ r₂ : Realization 𝕜 n m p)
    (h : Similar r₁ r₂) (k : ℕ) :
    r₁.markovParameter k = r₂.markovParameter k := by
  rw [markovParameter, markovParameter, h.input]
  calc
    r₁.C * r₁.A ^ k * r₁.B =
        (r₂.C * h.T) * r₁.A ^ k * r₁.B := by rw [h.output]
    _ = r₂.C * (h.T * r₁.A ^ k) * r₁.B := by
      simp only [Matrix.mul_assoc]
    _ = r₂.C * (r₂.A ^ k * h.T) * r₁.B := by rw [h.state_pow]
    _ = r₂.C * r₂.A ^ k * (h.T * r₁.B) := by
      simp only [Matrix.mul_assoc]

/-- Similarity implies behavioral equivalence.

Reference: Kailath, *Linear Systems*. -/
@[blueprint "thm:similar-realizations-behaviorally-equivalent"
  (statement := /-- A change of state coordinates preserves the feedthrough
    matrix and every Markov parameter. -/)]
theorem Similar.behaviorallyEquivalent (r₁ r₂ : Realization 𝕜 n m p)
    (h : Similar r₁ r₂) : r₁.BehaviorallyEquivalent r₂ :=
  ⟨h.feedthrough.symm, h.markovParameter_eq r₁ r₂⟩

end Realization

end LinearSystems

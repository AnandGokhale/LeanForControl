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

/-- Realization similarity is reflexive.

Original: relation API for LeanForControl. -/
def similarRefl (r : Realization 𝕜 n m p) : Similar r r where
  T := 1
  Tinv := 1
  Tinv_mul_T := mul_one 1
  T_mul_Tinv := mul_one 1
  state := by simp
  input := by simp
  output := by simp
  feedthrough := rfl

/-- Realization similarity is symmetric.

Original: relation API for LeanForControl. -/
def Similar.symm {r₁ r₂ : Realization 𝕜 n m p}
    (h : Similar r₁ r₂) : Similar r₂ r₁ where
  T := h.Tinv
  Tinv := h.T
  Tinv_mul_T := h.T_mul_Tinv
  T_mul_Tinv := h.Tinv_mul_T
  state := by
    calc
      r₁.A * h.Tinv = (h.Tinv * h.T) * r₁.A * h.Tinv := by
        rw [h.Tinv_mul_T, one_mul]
      _ = h.Tinv * (h.T * r₁.A) * h.Tinv := by
        simp only [Matrix.mul_assoc]
      _ = h.Tinv * (r₂.A * h.T) * h.Tinv := by rw [h.state]
      _ = h.Tinv * r₂.A * (h.T * h.Tinv) := by
        simp only [Matrix.mul_assoc]
      _ = h.Tinv * r₂.A := by rw [h.T_mul_Tinv, mul_one]
  input := by
    calc
      r₁.B = (h.Tinv * h.T) * r₁.B := by
        rw [h.Tinv_mul_T]
        exact (Matrix.one_mul r₁.B).symm
      _ = h.Tinv * (h.T * r₁.B) := by rw [Matrix.mul_assoc]
      _ = h.Tinv * r₂.B := by rw [← h.input]
  output := by
    calc
      r₁.C * h.Tinv = (r₂.C * h.T) * h.Tinv := by rw [h.output]
      _ = r₂.C * (h.T * h.Tinv) := by rw [Matrix.mul_assoc]
      _ = r₂.C := by
        rw [h.T_mul_Tinv]
        exact Matrix.mul_one r₂.C
  feedthrough := h.feedthrough.symm

/-- Realization similarity is transitive.

Original: relation API for LeanForControl. -/
def Similar.trans {r₁ r₂ r₃ : Realization 𝕜 n m p}
    (h₁₂ : Similar r₁ r₂) (h₂₃ : Similar r₂ r₃) : Similar r₁ r₃ where
  T := h₂₃.T * h₁₂.T
  Tinv := h₁₂.Tinv * h₂₃.Tinv
  Tinv_mul_T := by
    calc
      (h₁₂.Tinv * h₂₃.Tinv) * (h₂₃.T * h₁₂.T) =
          h₁₂.Tinv * (h₂₃.Tinv * h₂₃.T) * h₁₂.T := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h₂₃.Tinv_mul_T, mul_one, h₁₂.Tinv_mul_T]
  T_mul_Tinv := by
    calc
      (h₂₃.T * h₁₂.T) * (h₁₂.Tinv * h₂₃.Tinv) =
          h₂₃.T * (h₁₂.T * h₁₂.Tinv) * h₂₃.Tinv := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h₁₂.T_mul_Tinv, mul_one, h₂₃.T_mul_Tinv]
  state := by
    calc
      r₃.A * (h₂₃.T * h₁₂.T) = (r₃.A * h₂₃.T) * h₁₂.T := by
        rw [Matrix.mul_assoc]
      _ = (h₂₃.T * r₂.A) * h₁₂.T := by rw [h₂₃.state]
      _ = h₂₃.T * (r₂.A * h₁₂.T) := by rw [Matrix.mul_assoc]
      _ = h₂₃.T * (h₁₂.T * r₁.A) := by rw [h₁₂.state]
      _ = (h₂₃.T * h₁₂.T) * r₁.A := by rw [Matrix.mul_assoc]
  input := by rw [h₂₃.input, h₁₂.input, Matrix.mul_assoc]
  output := by
    calc
      r₃.C * (h₂₃.T * h₁₂.T) = (r₃.C * h₂₃.T) * h₁₂.T := by
        rw [Matrix.mul_assoc]
      _ = r₂.C * h₁₂.T := by rw [h₂₃.output]
      _ = r₁.C := h₁₂.output
  feedthrough := h₂₃.feedthrough.trans h₁₂.feedthrough

/-- The state intertwining equation propagates to every matrix power.

Original: algebraic similarity infrastructure for LeanForControl. -/
lemma Similar.state_pow (r₁ r₂ : Realization 𝕜 n m p) (h : Similar r₁ r₂)
    (k : ℕ) : r₂.A ^ k * h.T = h.T * r₁.A ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        r₂.A ^ (k + 1) * h.T = r₂.A ^ k * (r₂.A * h.T) := by
          rw [pow_succ, Matrix.mul_assoc]
        _ = r₂.A ^ k * (h.T * r₁.A) := by rw [h.state]
        _ = (r₂.A ^ k * h.T) * r₁.A := by
          rw [Matrix.mul_assoc]
        _ = (h.T * r₁.A ^ k) * r₁.A := by rw [ih]
        _ = h.T * (r₁.A ^ k * r₁.A) := by
          rw [Matrix.mul_assoc]
        _ = h.T * r₁.A ^ (k + 1) := by rw [pow_succ]

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

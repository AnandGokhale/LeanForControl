import LeanForControl.LinearSystems.Solutions.DefsDiscLTV
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Abel
import Architect

/-!
# Discrete-time solutions

Theorems about `discStateTransitionMatrix` (from `DefsDiscLTV.lean`), building up to the
discrete-time analogue of Theorem 5.1: the state transition matrix solves the recursion
`Φ(t+1, t₀) = A(t) Φ(t, t₀)`, `Φ(t₀, t₀) = I`, and is the unique solution of
`x(t+1) = A(t) x(t)`, `x(t₀) = x₀`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Section 5.3.
-/

namespace LinearSystems

open Matrix

variable {n : ℕ}

/-- `Φ(t₀,t₀) = I`: the discrete-time state transition matrix is the identity when evaluated at
equal times, matching the initial condition of P5.5. The product defining `Φ(t₀,t₀)` is over the
empty range `[t₀,t₀)`, hence trivially `I`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.5. -/
theorem discStateTransitionMatrix_self (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (t₀ : ℕ) :
    discStateTransitionMatrix A t₀ t₀ = 1 := by
  simp [discStateTransitionMatrix]

/-- `Φ(t+1,t₀) = A(t) Φ(t,t₀)` for `t ≥ t₀`: the discrete-time state transition matrix satisfies
the recursion of P5.5. Combined with `discStateTransitionMatrix_self` (`Φ(t₀,t₀) = I`), this is
the existence half of P5.5.

Proof: unfold the definition and peel the leading factor `A(t)` off the product, via
`List.range_succ_eq_map` (`range (k+1) = 0 :: (range k).map succ`).

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.5. -/
theorem discStateTransitionMatrix_succ (A : ℕ → Matrix (Fin n) (Fin n) ℝ) {t t₀ : ℕ}
    (ht : t₀ ≤ t) :
    discStateTransitionMatrix A (t + 1) t₀ = A t * discStateTransitionMatrix A t t₀ := by
  unfold discStateTransitionMatrix
  rw [show t + 1 - t₀ = (t - t₀) + 1 from by omega, List.range_succ_eq_map, List.map_cons,
    List.prod_cons, List.map_map, show t + 1 - 1 - 0 = t from by omega]
  have hmap : (List.range (t - t₀)).map ((fun k => A (t + 1 - 1 - k)) ∘ Nat.succ) =
      (List.range (t - t₀)).map (fun k => A (t - 1 - k)) := by
    apply List.map_congr_left
    intro k _
    change A (t + 1 - 1 - (k + 1)) = A (t - 1 - k)
    congr 1
    omega
  rw [hmap]

/-- **P5.5, uniqueness half.** `Φ(t,t₀)` is the *unique* solution to the recursion
`Z(t+1) = A(t) Z(t)`, `Z(t₀) = I`, for `t ≥ t₀`.

Proof: induction on `t` starting at `t = t₀` (`Nat.le_induction`), exactly as the book's proof
sketch describes — the base case is `discStateTransitionMatrix_self`, the inductive step chains
`hZ` against `discStateTransitionMatrix_succ`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.5. -/
theorem discStateTransitionMatrix_unique (A : ℕ → Matrix (Fin n) (Fin n) ℝ) {t₀ : ℕ}
    {Z : ℕ → Matrix (Fin n) (Fin n) ℝ} (hZ₀ : Z t₀ = 1)
    (hZ : ∀ t ≥ t₀, Z (t + 1) = A t * Z t) :
    ∀ t ≥ t₀, Z t = discStateTransitionMatrix A t t₀ := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rw [hZ₀, discStateTransitionMatrix_self]
  | succ t ht ih => rw [hZ t ht, discStateTransitionMatrix_succ A ht, ih]

/-- The vector analogue of `discStateTransitionMatrix_unique`: `Φ(t,t₀) *ᵥ x₀` is the unique
solution to the recursion `z(t+1) = A(t) *ᵥ z(t)`, `z(t₀) = x₀`, for `t ≥ t₀`. Needed to specialize
to columns (`x₀ := e_i`) for P5.6.

Proof: the same induction as `discStateTransitionMatrix_unique`, pushed through `*ᵥ x₀` via
`discStateTransitionMatrix_succ` and `Matrix.mulVec_mulVec`. -/
theorem discStateTransitionMatrix_mulVec_unique (A : ℕ → Matrix (Fin n) (Fin n) ℝ) {t₀ : ℕ}
    (x₀ : Fin n → ℝ) {z : ℕ → Fin n → ℝ} (hz₀ : z t₀ = x₀)
    (hz : ∀ t ≥ t₀, z (t + 1) = A t *ᵥ z t) :
    ∀ t ≥ t₀, z t = discStateTransitionMatrix A t t₀ *ᵥ x₀ := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rw [hz₀, discStateTransitionMatrix_self, Matrix.one_mulVec]
  | succ t ht ih =>
    rw [hz t ht, discStateTransitionMatrix_succ A ht, ← Matrix.mulVec_mulVec, ih]

/-- **P5.6.** For every fixed `t₀`, the `i`-th column of `Φ(t,t₀)` is the unique solution to
`z(t+1) = A(t) z(t)`, `z(t₀) = e_i`, where `e_i` is the `i`-th standard basis vector, for
`t ≥ t₀`.

Proof: restatement of `discStateTransitionMatrix_mulVec_unique` at `x₀ := e_i`, using
`Φ(t,t₀) *ᵥ e_i = (Φ(t,t₀))_{·,i}` (`Matrix.mulVec_single_one`).

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.6. -/
theorem discStateTransitionMatrix_col_unique (A : ℕ → Matrix (Fin n) (Fin n) ℝ) {t₀ : ℕ}
    (i : Fin n) {z : ℕ → Fin n → ℝ} (hz₀ : z t₀ = Pi.single i 1)
    (hz : ∀ t ≥ t₀, z (t + 1) = A t *ᵥ z t) :
    ∀ t ≥ t₀, z t = (discStateTransitionMatrix A t t₀).col i := by
  intro t ht
  rw [← Matrix.mulVec_single_one]
  exact discStateTransitionMatrix_mulVec_unique A (Pi.single i 1) hz₀ hz t ht

/-- **P5.7 (semigroup property).** `Φ(t,s) Φ(s,τ) = Φ(t,τ)` for `t ≥ s ≥ τ ≥ 0`.

Proof: induction on `t` starting at `t = s` (`Nat.le_induction`) — the base case is
`discStateTransitionMatrix_self`, the inductive step chains `discStateTransitionMatrix_succ`
(applied at both `s` and `τ`) with associativity.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Property P5.7. -/
theorem discStateTransitionMatrix_semigroup (A : ℕ → Matrix (Fin n) (Fin n) ℝ) {s τ : ℕ}
    (hτs : τ ≤ s) :
    ∀ t ≥ s, discStateTransitionMatrix A t s * discStateTransitionMatrix A s τ =
      discStateTransitionMatrix A t τ := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rw [discStateTransitionMatrix_self, Matrix.one_mul]
  | succ t ht ih =>
    rw [discStateTransitionMatrix_succ A ht, mul_assoc, ih,
      discStateTransitionMatrix_succ A (hτs.trans ht)]

variable {m : ℕ} {B : ℕ → Matrix (Fin n) (Fin m) ℝ} {u : ℕ → Fin m → ℝ}

/-- **Discrete variation of constants, initial value.** The discrete-time variation-of-constants
formula `x(t) := Φ(t,t₀) *ᵥ x₀ + Σ_{τ=t₀}^{t-1} Φ(t,τ+1) *ᵥ (B(τ) *ᵥ u(τ))` matches the initial
value `x₀` at `t = t₀`: the forcing sum is over the empty range `[t₀,t₀)`, and `Φ(t₀,t₀) = I`.

Reference: Hespanha, *Linear Systems Theory* (2nd ed.), Chapter 5, Section 5.3 (discrete
variation of constants). -/
theorem discVariationOfConstants_self (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (t₀ : ℕ)
    (x₀ : Fin n → ℝ) :
    discStateTransitionMatrix A t₀ t₀ *ᵥ x₀ +
        ∑ τ ∈ Finset.Ico t₀ t₀, discStateTransitionMatrix A t₀ (τ + 1) *ᵥ (B τ *ᵥ u τ) = x₀ := by
  simp [discStateTransitionMatrix_self]

/-- **Discrete variation of constants, existence.** `x(t) := Φ(t,t₀) *ᵥ x₀ +
Σ_{τ=t₀}^{t-1} Φ(t,τ+1) *ᵥ (B(τ) *ᵥ u(τ))` satisfies the forced recursion
`x(t+1) = A(t) *ᵥ x(t) + B(t) *ᵥ u(t)`, for `t ≥ t₀`.

Proof: peel the top term off `x(t+1)`'s sum (`Finset.sum_Ico_succ_top`), and fold
`A(t) *ᵥ (Φ(t,τ+1) *ᵥ v)` into `Φ(t+1,τ+1) *ᵥ v` termwise via `discStateTransitionMatrix_succ`
(also applied once more to the leading `Φ(t,t₀)` term); the two sides then match up to
reassociating the sum. -/
theorem discVariationOfConstants_succ (A : ℕ → Matrix (Fin n) (Fin n) ℝ) {t₀ t : ℕ}
    (ht : t₀ ≤ t) (x₀ : Fin n → ℝ) :
    discStateTransitionMatrix A (t + 1) t₀ *ᵥ x₀ +
        ∑ τ ∈ Finset.Ico t₀ (t + 1), discStateTransitionMatrix A (t + 1) (τ + 1) *ᵥ (B τ *ᵥ u τ) =
      A t *ᵥ (discStateTransitionMatrix A t t₀ *ᵥ x₀ +
          ∑ τ ∈ Finset.Ico t₀ t, discStateTransitionMatrix A t (τ + 1) *ᵥ (B τ *ᵥ u τ)) +
        B t *ᵥ u t := by
  have hsum : ∑ τ ∈ Finset.Ico t₀ t,
      A t *ᵥ (discStateTransitionMatrix A t (τ + 1) *ᵥ (B τ *ᵥ u τ)) =
      ∑ τ ∈ Finset.Ico t₀ t, discStateTransitionMatrix A (t + 1) (τ + 1) *ᵥ (B τ *ᵥ u τ) := by
    refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [Matrix.mulVec_mulVec, ← discStateTransitionMatrix_succ A (Finset.mem_Ico.mp hτ).2]
  rw [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_mulVec,
    ← discStateTransitionMatrix_succ A ht, hsum, Finset.sum_Ico_succ_top ht,
    discStateTransitionMatrix_self, Matrix.one_mulVec]
  abel

/-- **Discrete variation of constants, uniqueness.** Any two solutions of the forced recursion
`z(t+1) = A(t) *ᵥ z(t) + B(t) *ᵥ u(t)` sharing the same initial value `x₀` coincide for all
`t ≥ t₀`.

Proof: induction on `t` starting at `t = t₀`. Unlike the continuous case
(`variationOfConstants_unique`), this needs no Lipschitz/Gronwall machinery — the recursion pins
each successive value directly. -/
theorem discVariationOfConstants_unique (A : ℕ → Matrix (Fin n) (Fin n) ℝ) {t₀ : ℕ}
    (x₀ : Fin n → ℝ) {z₁ z₂ : ℕ → Fin n → ℝ} (hz₁₀ : z₁ t₀ = x₀) (hz₂₀ : z₂ t₀ = x₀)
    (hz₁ : ∀ t ≥ t₀, z₁ (t + 1) = A t *ᵥ z₁ t + B t *ᵥ u t)
    (hz₂ : ∀ t ≥ t₀, z₂ (t + 1) = A t *ᵥ z₂ t + B t *ᵥ u t) :
    ∀ t ≥ t₀, z₁ t = z₂ t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rw [hz₁₀, hz₂₀]
  | succ t ht ih => rw [hz₁ t ht, hz₂ t ht, ih]

end LinearSystems

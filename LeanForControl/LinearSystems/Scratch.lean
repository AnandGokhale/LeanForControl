import LeanForControl.LinearSystems.Basic

/-!
# `LinearSystems.Scratch`

Sandbox for API exploration. Not imported from the project root.

The goal is to confirm, with `#check`, that the planned shapes for
`observabilityMatrix` and `controllabilityMatrix` elaborate, and that the
mathlib API we want to lean on (`Matrix.mulVec`, `Matrix.of`, `^` on square
matrices, `funext`) is reachable from `LinearSystems.Basic`.
-/

namespace LinearSystems.Scratch

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]
variable {n m p : ℕ}

-- Square-matrix powers come via the `Monoid (Matrix (Fin n) (Fin n) 𝕜)` instance,
-- which `Matrix.Mul` provides for `[Fintype n] [DecidableEq n] [Semiring α]`.
-- `Fin n` is automatically `Fintype` and `DecidableEq`, so `A ^ k` is available.

example (A : Matrix (Fin n) (Fin n) 𝕜) (k : ℕ) : Matrix (Fin n) (Fin n) 𝕜 :=
  A ^ k

-- Block-row index using `Fin n × Fin p`.
example
    (A : Matrix (Fin n) (Fin n) 𝕜) (C : Matrix (Fin p) (Fin n) 𝕜) :
    Matrix (Fin n × Fin p) (Fin n) 𝕜 :=
  Matrix.of fun ki j => (C * A ^ (ki.1 : ℕ)) ki.2 j

-- Block-column index using `Fin n × Fin m`.
example
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    Matrix (Fin n) (Fin n × Fin m) 𝕜 :=
  Matrix.of fun i kj => (A ^ (kj.1 : ℕ) * B) i kj.2

-- `mulVec` of the planned observability matrix at a coordinate `(k, i)` should
-- equal `((C * A ^ k) *ᵥ x) i`. Check this is `rfl` once we've unfolded.
example
    (A : Matrix (Fin n) (Fin n) 𝕜) (C : Matrix (Fin p) (Fin n) 𝕜)
    (x : Fin n → 𝕜) (k : Fin n) (i : Fin p) :
    ((Matrix.of fun ki j => (C * A ^ ((ki.1 : Fin n) : ℕ)) ki.2 j : Matrix (Fin n × Fin p) (Fin n) 𝕜)
        *ᵥ x) (k, i)
      = ((C * A ^ (k : ℕ)) *ᵥ x) i := by
  rfl

-- API sanity checks.
#check @Matrix.mulVec
#check @Matrix.of
#check @Matrix.mulVec_zero
#check @Matrix.zero_mulVec

-- Decision recorded for the milestone:
--   * Index the observability block-row as `Fin n × Fin p` and the controllability
--     block-column as `Fin n × Fin m`. This keeps `A ^ (k : ℕ)` available without
--     a `Fin.val` cast in every lemma.
--   * Phrase observability via the kernel of the assembled matrix:
--       `∀ x, observabilityMatrix A C *ᵥ x = 0 → x = 0`.
--   * The bridge `(observabilityMatrix A C *ᵥ x) (k, i) = ((C * A ^ k) *ᵥ x) i`
--     holds definitionally with the chosen index encoding.

end LinearSystems.Scratch

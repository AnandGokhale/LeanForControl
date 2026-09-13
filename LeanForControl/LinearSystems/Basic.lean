import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-!
# `LinearSystems.Basic`

Shared imports and conventions for the `LinearSystems` track.

Conventions used by every file in `LinearSystems`:

* scalars live in a generic field `𝕜` (often a `CommRing` is enough, in which case
  the per-file `variable` block uses `[CommRing 𝕜]` instead of `[Field 𝕜]`);
* state-space dimensions are natural numbers `n m p : ℕ`;
* state matrix `A : Matrix (Fin n) (Fin n) 𝕜`;
* input matrix `B : Matrix (Fin n) (Fin m) 𝕜`;
* output matrix `C : Matrix (Fin p) (Fin n) 𝕜`;
* state vectors are `Fin n → 𝕜`;
* matrix-vector multiplication is the mathlib `*ᵥ` from `Matrix.mulVec`.

Block matrices stacked over a `Fin n` index of powers of `A` use the product
index type `Fin n × Fin p` (or `Fin n × Fin m`) rather than `Fin (n * p)`.
This keeps `Aᵏ` available as `A ^ (k : ℕ)` for `k : Fin n` without going
through `Fin.val` extraction in every lemma.

This file holds *only* shared imports and documentation. Definitions and proofs
live in the sibling modules under `LeanForControl/LinearSystems`.
-/

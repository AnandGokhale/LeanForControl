# 1 — Hautus track follow-ups

Helpers needed before either Hautus direction or the rank-based reformulations
(observable ↔ `rank 𝒪 = n`):

- rank ↔ trivial-kernel bridge for `Matrix (Fin n × Fin p) (Fin n) 𝕜`,
  most naturally via `Matrix.toLin'` and `LinearMap.ker`
- block-matrix rank lemmas for stacked rows `[A₁; A₂; …; Aₖ]`
- transition from `(C * A^k) *ᵥ x = 0 ∀ k < n` to `A`-invariance of the
  unobservable subspace (Cayley–Hamilton style); needed to extract
  eigenvectors for the Hautus direction
- coercions between `(C * A^k) *ᵥ x` and `C *ᵥ (A^k *ᵥ x)`

Living source: tail comment of
`LeanForControl/LinearSystems/Observability.lean`.

These belong in a future `LeanForControl/LinearSystems/MatrixLemmas.lean`
(matrix-level facts) and `LeanForControl/LinearSystems/Hautus.lean`
(control-level facts).

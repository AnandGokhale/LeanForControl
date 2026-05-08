# 9 — Spectral decomposition + pseudoinverse for symmetric PSD

## Context

`dp-infhor` writes "SVD of `Σ`" but the matrices are real symmetric PSD, so
what we really need is the **spectral theorem for Hermitian matrices** plus
the **Moore–Penrose pseudoinverse restricted to PSD**. Both are narrower
than full SVD / general pseudoinverse, which are large undertakings.

mathlib has the spectral theorem for `IsHermitian` matrices in
`Mathlib/Analysis/InnerProductSpace/Spectrum.lean` and PSD machinery in
`Mathlib/LinearAlgebra/Matrix/PosDef.lean`. The pseudoinverse for PSD `Σ`
is definable directly via the spectral decomposition.

## Files to create or modify

Create:
- `LeanForControl/LinearSystems/PosDefAux.lean` — spectral decomposition
  wrappers + PSD pseudoinverse. Or extend `MatrixLemmas.lean` if it stays
  short (~3 lemmas).

## Sketch

1. `Σ.spectralDecomposition`: for PSD real-symmetric `Σ`, exhibit `U`
   orthogonal and `Λ` diagonal with `Σ = U * Λ * Uᵀ`. Wrap mathlib's
   `IsHermitian.eigenvectorMatrix` etc.
2. `def PosSemidef.pseudoinverse : Matrix n n ℝ → Matrix n n ℝ` using the
   spectral decomposition: replace each positive eigenvalue with its
   reciprocal, leave zero eigenvalues at zero.
3. Key identity: `Σ * Σ† * Σ = Σ` and `Σ† * Σ * Σ† = Σ†`.
4. The `M_1 Σ̃ M_1ᵀ` form from dp-infhor:eq:SigmaSVD — match mathlib's
   eigenvector basis to the `M_1, M_2` block structure.

## Risk

🟡 — mathlib has the heavy machinery (spectral theorem) but the
PSD-pseudoinverse wrapper is hand-built. Stay narrow.

## Open questions

- Real vs complex: dp-infhor is over `ℝ` for the estimator, but we've been
  doing Hautus over `ℂ`. The spectral theorem for PSD real symmetric is in
  mathlib via `IsHermitian` (since real symmetric is Hermitian over ℝ
  considered as a complex structure with no imaginary part). Pick the
  clean side.
- Avoid defining a generic Moore–Penrose pseudoinverse; only the PSD case
  is on the dp-infhor critical path.

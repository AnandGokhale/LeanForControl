# 11 — Block-diagonalize the initial covariance

## Context

dp-infhor's "Block-diagonalization of the initial covariance" applies the
canonical-form change of basis to `Σ_0`, then introduces a second
block-triangular transform `Θ = [[I, -Σ_{12} Σ_2⁻¹], [0, I]]` to kill the
off-diagonal block. The result: `Θ Σ_0 Θᵀ = diag(Σ̃_1, Σ_2)` where
`Σ̃_1 = Σ_1 − Σ_{12} Σ_2⁻¹ Σ_{12}ᵀ` is the Schur complement.

## Files to create or modify

Create:
- `LeanForControl/Estimation/Decomposition.lean` — the Θ transformation,
  the `Σ̃_1, Σ_2` block-diagonal form, and the support condition
  `Σ̃_1 ⊕ ℝ^{n_2}` for the unconstrained `e_2(0|T)`.

## Sketch

1. Assume the canonical-form decomposition (sprint 10) is in scope. Partition
   `Σ_0` conformally as `[[Σ_1, Σ_{12}], [Σ_{12}ᵀ, Σ_2]]`.
2. Prove dp-infhor's Lemma 1 (`lem:Sigma2-pd`): C2 ⇒ `Σ_2 ≻ 0`. Uses the
   characterization of unstable-uncontrollable subspace from sprint 8.
3. Define `Θ` as in dp-infhor:eq:Theta. Verify `Θ Θ⁻¹ = I`.
4. Prove `Θ Σ_0 Θᵀ = diag(Σ̃_1, Σ_2)` via direct block computation.
5. Express `range(Σ̃_0) = range(Σ̃_1) × ℝ^{n_2}` and the support condition.

## Risk

🟡 — block-matrix algebra is mostly mechanical (mathlib's `fromBlocks`
machinery covers it), and `Σ_2 ≻ 0` follows from C2 once detectability is
in place.

## Open questions

- Is C2 ("ker Σ_0 ∩ X_uu = 0") best phrased as a `Submodule` predicate
  or via a generator condition on rows of `Σ_0`? Pick when active.

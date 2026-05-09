# 10 — Stabilizability canonical form (Kalman decomposition)

## Context

dp-infhor's "Stabilizability canonical form" splits `(A, G)` into an upper
block-triangular structure `A = [[A_1, A_{12}], [0, A_2]]`, `G = [[G_1],
[0]]` with `(A_1, G_1)` stabilizable and `A_2` totally unstable (every
eigenvalue `|λ| ≥ 1`). This is a Kalman decomposition restricted to the
controllable-vs-uncontrollable axis (no observability split needed here).

## Files to create or modify

Create:
- `LeanForControl/LinearSystems/Decomposition.lean` —
  `stabilizabilityCanonicalForm` constructor (or existence theorem),
  showing the block-triangular form and naming the resulting blocks.

## Sketch

1. Identify the unstable-uncontrollable subspace `X_uu(A, G) ≤ Fin n → ℂ`:
   the largest `A`-invariant subspace contained in `(reachable subspace of
   (A, G))ᶜ` whose `A` restriction is totally unstable. (Equivalently: the
   reachable subspace's quotient where `A` acts unstably.)
2. Choose a complementary `A`-invariant subspace `X_s` such that
   `Fin n → ℂ = X_s ⊕ X_uu`. Mathlib's invariant-subspace machinery should
   give this once we have the Hautus characterization.
3. Use a basis `B = (B_s, B_u)` adapted to the split. Then in this basis,
   `A` becomes upper block-triangular and `G` becomes column-stacked with
   the `B_u` rows zero.
4. Bundle the resulting maps as a single `structure` carrying `A_1, A_2,
   A_{12}, G_1` plus the conjugating change-of-basis.
5. Phrase the result as: `∃ T : invertible matrix, T * A * T⁻¹` is in the
   canonical form, and `(A_1, G_1)` is stabilizable.

## Risk

🔴 from scratch. The hardest piece is constructing the complementary
`A`-invariant subspace; mathlib has invariant-subspace existence under
restrictive hypotheses but may not have exactly this. Possibly need to
hand-construct via the Schur decomposition (mathlib has it for complex
matrices) and group eigenvalues.

## Open questions

- Use Schur triangulation directly? Over `ℂ` every matrix has an upper
  triangular Schur form. Permuting eigenvalues to put unstable ones in the
  bottom-right block, then refining for the controllable-vs-uncontrollable
  split, may be simpler than the abstract subspace construction.
- Phrasing as a "data structure" (carrying `A_1, A_{12}, A_2, G_1, T`) vs
  as an existence theorem with these named in the statement: prefer the
  data structure for downstream sprints (15, 18).

# 5 — Controllability Hautus via duality

## Landed

Two new blueprint-tagged decls in
`LeanForControl/LinearSystems/Hautus.lean`:

- `def:hautusControllabilityMatrix` — `[μI - A | B]` via `Matrix.fromCols`,
  shape `Matrix (Fin n) (Fin n ⊕ Fin m) ℂ`.
- `thm:isControllable-iff-hautus` — `IsControllable A B ↔ ∀ μ ∈ ℂ,
  rank (hautusControllabilityMatrix A B μ) = n`.

Plus three supporting lemmas (untagged, plumbing):

- `controllabilityMatrix_transpose` — `𝒞(A, B)ᵀ = 𝒪(Aᵀ, Bᵀ)`. Pure
  matrix-algebra, holds entry-wise.
- `isControllable_iff_isObservable_transpose` — duality bridge over `ℂ`.
- `hautusControllabilityMatrix_transpose` — Hautus block matrices are
  transposes of each other under `(A, B) ↔ (Aᵀ, Bᵀ)`.

`lake build` green; no `sorry`/`admit`/`axiom`. Blueprint regenerated:
20 rendered nodes (18 prior + 2 new), 0 unresolved cross-references.

## Implementation note

Took the **duality-via-rank** route, not the direct-mirror route. The plan
flagged a fallback to mirroring observability's eigenvector argument; we
didn't need it. Path:

1. `(controllabilityMatrix A B)ᵀ = observabilityMatrix Aᵀ Bᵀ` by entry-wise
   `simp` over `Matrix.transpose_pow` + `Matrix.transpose_mul`.
2. `IsControllable A B ↔ IsObservable Aᵀ Bᵀ` by chaining sprint 3's
   rank-form characterizations through `Matrix.rank_transpose`.
3. `(hautusControllabilityMatrix A B μ)ᵀ = hautusObservabilityMatrix Aᵀ Bᵀ μ`
   by `Matrix.transpose_fromCols` + `transpose_sub`/`smul`/`one`.
4. `isControllable_iff_hautus` by chaining the duality bridge with sprint
   4's observability Hautus, then translating the kernel-form RHS to
   rank-form via `MatrixLemmas.mulVec_kernel_trivial_iff_rank_eq_card_cols`
   and the transpose bridge.

Build was green on first attempt — every rewrite pattern matched without
fixing.

## Mathlib pieces leaned on

- `Matrix.transpose_pow` (CommSemiring).
- `Matrix.transpose_mul` (CommMagma).
- `Matrix.transpose_fromCols`.
- `Matrix.rank_transpose` (Field).
- `Matrix.ker_mulVecLin_eq_bot_iff` (already used in sprint 4).

## Open follow-ups

- **Sprint 6 next**: Schur stability (`IsSchur A`, `A^k → 0` bridge,
  `fact:no-decay`). All Phase A foundations close after that + sprint 7
  (Schur complement / Gramian) + sprint 8 (detectability).
- Sprint 4's converse-direction proof and the new sprint 5 controllability
  Hautus together make the next planning revisit fairly cheap.

## Pointers

- Blueprint subsection: `Hautus controllability` in
  `blueprint/src/content.tex`.
- Lean: `LeanForControl/LinearSystems/Hautus.lean`, lines after the
  observability iff.
- Lemma names to remember for downstream Hautus uses:
  `isControllable_iff_isObservable_transpose`,
  `controllabilityMatrix_transpose`,
  `hautusControllabilityMatrix_transpose`.

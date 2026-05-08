# 4 — Observability Hautus lemma

## Landed

Full iff:

  `IsObservable A C ↔ ∀ μ : ℂ, ker (hautusObservabilityMatrix A C μ).mulVecLin = ⊥`

over `ℂ`, in `LeanForControl/LinearSystems/Hautus.lean`. Both directions
proved (failure direction was the main work; converse follows by induction
on `A^k *ᵥ v`).

Eight new blueprint-tagged decls:

- `def:unobservableSubspace` — the `A`-invariant kernel-of-`(C·A^k)`-for-all-`k:Fin n` submodule.
- `thm:unobservable-eq-bot-iff-observable` — bridge to `IsObservable`.
- `lem:unobservableSubspace-invariant` — `A *ᵥ ·` preserves it (Cayley–Hamilton at `k = n - 1`).
- `def:hautusObservabilityMatrix` — `[μ I - A; C]` via `Matrix.fromRows`.
- `lem:hautus-mulVec-eq-zero-iff` — kernel decomposes into `Av = μv ∧ Cv = 0`.
- `thm:not-isObservable-implies-hautus-failure` — failure direction.
- `thm:hautus-failure-implies-not-isObservable` — converse.
- `thm:isObservable-iff-hautus` — packaged iff.

`lake build` green; `grep sorry/admit/axiom`: zero hits. Blueprint regenerated:
18 rendered nodes (10 prior + 8 new), 0 unresolved cross-references.

## Implementation notes

Cayley–Hamilton enters once, in
`mulVec_aPowN_eq_zero_of_mem_unobservableSubspace`: expand
`Polynomial.aeval_eq_sum_range` against `Matrix.aeval_self_charpoly`,
isolate the leading `A^n` term via `charpoly_natDegree_eq_dim` + monicity
(`charpoly_monic`), and zero out the lower powers via the unobservable
membership.

`A`-invariance then case-splits on `k.val + 1 < n`: lower indices reduce to
membership directly, the boundary `k = n - 1` reuses the C–H helper.

Eigenvector extraction uses `Module.End.exists_eigenvalue` on
`A.mulVecLin.restrict` (with the obligation discharged by `A`-invariance).
The lifted eigenvector is in the unobservable subspace by construction, so
membership at `k = 0` reads off `C *ᵥ v = 0`. `0 < n` is recovered by
contradiction from `unobservableSubspace ≠ ⊥`.

The Hautus matrix uses `Matrix.fromRows`, indexed `Fin n ⊕ Fin p`. The
kernel decomposition lemma is proved directly by `Sum.elim` case analysis
plus `Matrix.sub_mulVec` / `Matrix.smul_mulVec` / `Matrix.one_mulVec`.

## Open follow-ups

- **Controllability Hautus** is now the next phase. Plan: rank `[μ I - A  B]`
  block-column matrix; mirror the dual structure (range-form instead of
  kernel-form).
- Optional rank-form corollary
  `IsObservable ↔ ∀ μ, rank (hautusObservabilityMatrix μ) = n`. Need a
  `MatrixLemmas` `fromRows` rank/kernel bridge over `[Field 𝕜]` (essentially
  the analogue of `mulVec_kernel_trivial_iff_rank_eq_card_cols` for stacked
  rows).

## Pointers

- Blueprint subsection: `Hautus observability` in
  `blueprint/src/content.tex`.
- Lean: `LeanForControl/LinearSystems/Hautus.lean` (whole file).
- Mathlib pieces leaned on: `Matrix.aeval_self_charpoly`,
  `Polynomial.aeval_eq_sum_range`, `Module.End.exists_eigenvalue`,
  `LinearMap.restrict`, `Matrix.fromRows_mulVec`,
  `Submodule.nontrivial_iff_ne_bot`.

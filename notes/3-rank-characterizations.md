# 3 — Rank characterizations of observability and controllability

## Landed

Three new blueprint-tagged decls, all in
`LeanForControl/LinearSystems/{Observability,Controllability}.lean`:

- `def:isControllable` — textbook controllability predicate (existential
  reachability in matrix-power language; no mention of the controllability
  matrix). Lives in the existing `[Semiring 𝕜]` section.
- `thm:isObservable-iff-rank` — observability iff full column rank of
  $\mathcal{O}(A, C)$.
- `thm:isControllable-iff-rank` — controllability iff full row rank of
  $\mathcal{C}(A, B)$.

Plumbing in `LeanForControl/LinearSystems/MatrixLemmas.lean` (no
`@[blueprint]`, intentional):

- `mulVec_kernel_trivial_iff_rank_eq_card_cols` — kernel-trivial bridges to
  rank = card of column type, over `[Field 𝕜]`.
- `mulVec_range_top_iff_rank_eq_card_rows` — range-top bridges to rank = card
  of row type, over `[Field 𝕜]`.

`lake build` green; no `sorry`/`admit`/`axiom`. Blueprint regenerated, all 10
nodes render with body content, 0 unresolved cross-references.

## Implementation note

Each Field-side theorem is in a re-opened `namespace LinearSystems` with
`[Field 𝕜]` as the only scalar typeclass. This breaks the typeclass diamond
that arises when `[Field 𝕜]` is added on top of the outer `[Semiring 𝕜]` —
without the close/reopen, the milestone iff and the matrix bridge instantiate
`*ᵥ` through different `NonUnitalNonAssocSemiring` paths and `rw` won't unify.

## Open follow-ups

Hautus is now structurally unblocked:

- The kernel/rank infrastructure is in place for the Hautus *failure direction*
  (need to extract an eigenvector witness from a non-trivial unobservable
  subspace).
- See `notes/1-hautus-followups.md` for the remaining helpers.

## Pointers

- Blueprint subsection: `Rank characterizations` (`blueprint/src/content.tex`).
- Lean: `LeanForControl/LinearSystems/Observability.lean`
  (rank theorem at the bottom, after the milestone),
  `LeanForControl/LinearSystems/Controllability.lean` (`IsControllable` and
  rank theorem),
  `LeanForControl/LinearSystems/MatrixLemmas.lean` (matrix bridges).

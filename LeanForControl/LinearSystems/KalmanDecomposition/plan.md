# Plan: Structural Kalman Decomposition

This roadmap covers the finite-dimensional structural theory that uses both
controllability and observability.  Transfer functions and minimal-realization
theory are deliberately deferred.

## Status

| Result | Public API | File | Status |
|---|---|---|---|
| Four-sector lattice decomposition | `exists_kalmanDecomposition` | `Decomposition.lean` | done |
| Adapted coordinates and forced block zeros | `kalman_block_matrix_zero_pattern` | `Decomposition.lean` | done |
| Reachable dimension/rank | `finrank_reachableSubspace_eq_rank_controllabilityMatrix` | `../Controllability/Reachability.lean` | done |
| Unobservable kernel and rank-nullity | `unobservableSubspace_eq_ker_observabilityMatrix`, `finrank_unobservableSubspace_add_rank_observabilityMatrix` | `../Observability/Observability.lean` | done |
| Four-sector finrank identities | `finrank_cuo_add_co_add_uuo_add_uo` | `Dimensions.lean` | done |
| Canonicality of sector dimensions | `finrank_*_eq_finrank_*` | `Dimensions.lean` | done |
| Standalone controllable decomposition | `reachableMatrices_isControllable` | `../Controllability/Decomposition.lean` | done |
| Standalone observable decomposition | `observableMatrices_isObservable` | `../Observability/Decomposition.lean` | done |
| Controllable Kalman portion | `KalmanDecomposition.controllablePart_isControllable` | `Semantic.lean` | done |
| Observable Kalman portion | `KalmanDecomposition.observablePart_isObservable` | `Semantic.lean` | done |
| Canonical controllable-observable core | `controllableObservableMatrices_isControllable_and_isObservable` | `Semantic.lean` | done |
| `co`-sector/core dimension identification | `KalmanDecomposition.finrank_co_eq_controllableObservableSpace` | `Semantic.lean` | done |
| Structural summary theorem | `exists_kalmanDecomposition_with_semantics` | `Semantic.lean` | done |

## Dependency graph

```text
controllability / observability matrices
  ├─ reachableSubspace + invariance
  │    └─ reachable restriction ── IsControllable
  └─ unobservableSubspace + invariance
       └─ observable quotient ──── IsObservable

reachable restriction + unobservable intersection
  └─ R / (R ∩ N)
       ├─ IsControllable
       ├─ IsObservable
       └─ finrank = finrank(co)

four-sector existence + adapted bases
  ├─ forced matrix zero pattern
  └─ structural summary theorem
```

## File ownership

- `Defs.lean`: four noncanonical sectors and adapted-coordinate definitions.
- `Decomposition.lean`: existence, coordinate characterizations, and matrix
  zero pattern.
- `Dimensions.lean`: sector finranks and dimension canonicality.
- `DefsSemantic.lean`: canonical quotient maps and their matrix
  representations.
- `Semantic.lean`: controllability, observability, core semantics, and the
  top-level structural theorem.
- `DecompositionExamples.lean`: public-API regression examples, including
  degenerate dimensions.

The standalone one-sided decompositions live in their respective subject
directories, not here.

## Deferred work

- Transfer functions and impulse responses.
- Minimal-realization definitions and the controllable-and-observable
  minimality theorem.
- Uniqueness of minimal realizations.
- Numerical decomposition algorithms and Gramian-based constructions.

These are realization-theory topics rather than gaps in the structural
decomposition proved here.

## Lessons learned

- The chosen `co`, `uuo`, and `uo` complements are coordinate sectors, not
  invariant subspaces.  Semantic systems must use restrictions and quotients.
- The observable part is naturally `X / N`, not an arbitrary complement of
  `N`.
- The canonical meaning of the `co` block is `R / (R ∩ N)`.  A chosen `co`
  sector has the same dimension, but is not claimed equal to this quotient.
- Universal properties of reachable and unobservable subspaces make the
  restriction and quotient proofs robust at dimension zero.

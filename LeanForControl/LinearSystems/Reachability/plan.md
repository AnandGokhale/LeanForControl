# Plan: Reachability and Kalman Decomposition

## Current status

| Result | Lean name | File | Status |
|---|---|---|---|
| Reachable subspace | `reachableSubspace` | `DefsReachability.lean` | done |
| Reachability membership | `mem_reachableSubspace_iff` | `Reachability.lean` | done |
| Range(B) contained in reachable space | `range_B_le_reachableSubspace` | `Reachability.lean` | done |
| Reachability iff controllability | `reachableSubspace_eq_top_iff_isControllable` | `Reachability.lean` | done |
| A-invariance | `reachableSubspace_invariant` | `Reachability.lean` | done |
| Kalman coordinate sectors | `KalmanDecomposition` | `DefsKalmanDecomposition.lean` | done |
| Existence | `exists_kalmanDecomposition` | `KalmanDecomposition.lean` | done |
| Adapted equivalence/basis | `KalmanDecomposition.linearEquiv` | `KalmanDecomposition.lean` | done |
| Forced block zero pattern | `KalmanDecomposition.kalman_block_matrix_zero_pattern` | `KalmanDecomposition.lean` | done |

## Files

- `DefsReachability.lean` — definition of the reachable subspace.
- `Reachability.lean` — finite-horizon characterizations, controllability
  equivalence, and reachable-subspace invariance.
- `DefsKalmanDecomposition.lean` — the four coordinate sectors and their
  lattice relationships.
- `KalmanDecomposition.lean` — existence, adapted coordinates and bases, and
  the forced block-zero pattern.
- `KalmanDecompositionExamples.lean` — standalone regression examples for
  degenerate dimensions and a concrete two-state system.

## Follow-up

- Extend the public API for working with the existing Kalman decomposition
  and its adapted coordinates.

## Lessons learned

- The four sectors are coordinate sectors adapted to the reachable and
  unobservable subspaces; arbitrary chosen complements are not individually
  asserted to be invariant under the state matrix.
- Cayley--Hamilton closes the `A ^ n B` boundary term while keeping the
  reachable-subspace definition at the finite horizon `0, ..., n - 1`.

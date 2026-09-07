# Finite-dimensional Kalman decomposition

This note describes the finite-dimensional Kalman decomposition formalized in
the linear-systems development.  The construction is dimension-generic in the
state, input, and output dimensions and includes zero-dimensional cases.  It
uses the project's existing convention of complex matrices indexed by
`Fin n`.

## Mathematical statement

For

```text
A : Matrix (Fin n) (Fin n) ℂ
B : Matrix (Fin n) (Fin m) ℂ
C : Matrix (Fin p) (Fin n) ℂ,
```

let `R(A,B)` be the range of the finite controllability matrix and let
`N(A,C)` be the finite-horizon unobservable subspace.  The construction
chooses four subspaces, in the order

```text
X_cūo, X_co, X_ūcūo, X_ūco,
```

such that

```text
X_cūo = R ∩ N,
X_cūo ⊕ X_co = R,
X_cūo ⊕ X_ūcūo = N,
R ⊕ X_ūcūo = R + N,
(R + N) ⊕ X_ūco = ℂⁿ.
```

Addition gives a linear equivalence from the nested product of the four
components to `Fin n → ℂ`.  After choosing bases of the components, the
transported state, input, and output maps have the forced-zero form

```text
     [ *  *  *  * ]        [ * ]
A' = [ 0  *  0  * ]   B' = [ * ]   C' = [ 0  *  0  * ].
     [ 0  0  *  * ]        [ 0 ]
     [ 0  0  0  * ]        [ 0 ]
```

Every displayed zero is proved entrywise.  The starred entries are
unconstrained.  The identities
`stateMatrix_eq_toMatrix_adapted`, `inputMatrix_eq_toMatrix_adapted`, and
`outputMatrix_eq_toMatrix_adapted` identify these matrices with the original
maps `A`, `B`, and `C` in the adapted basis.

## Reachability

`LeanForControl/LinearSystems/Reachability.lean` defines
`reachableSubspace A B` as the range of `controllabilityMatrix A B`.  It proves:

- the existential characterization of membership in the range;
- the finite-horizon block-column multiplication identity;
- membership of each response `(A ^ k * B) *ᵥ u`;
- equality with the supremum of the ranges of `A ^ k * B` for `k : Fin n`;
- inclusion of the range of `B`;
- equivalence between a top reachable subspace and controllability; and
- invariance under the state matrix `A`.

The invariance proof explicitly handles the only boundary term outside the
finite horizon.  The private lemma
`aPowN_mul_B_mulVec_mem_reachableSubspace` expands the characteristic
polynomial, applies Cayley--Hamilton, isolates its monic leading coefficient,
and expresses the remaining powers as reachable vectors.  Thus reachability
remains tied to the existing finite controllability matrix rather than being
defined as an invariant closure.

## Four-way decomposition and coordinates

`LeanForControl/LinearSystems/KalmanDecomposition.lean` defines
`KalmanDecomposition`, recording the four subspaces and the direct-sum
relationships used by the coordinate construction.  The theorem
`exists_kalmanDecomposition` obtains the components from relative complements
in the modular lattice of submodules.

The component semantics are exact:

- reachable states are precisely those whose `uuo` and `uo` coordinates
  vanish;
- unobservable states are precisely those whose `co` and `uo` coordinates
  vanish.

The definition `KalmanDecomposition.linearEquiv` composes three direct-sum
equivalences to obtain the change of coordinates.  The transported maps
`stateMap`, `inputMap`, and `outputMap` are then used to prove the component
zero patterns.  In particular, reachable-subspace invariance gives the
forced state and input zeros associated with uncontrollable coordinates, while
unobservable-subspace invariance gives the remaining state zeros.  The zeroth
observability condition gives the output zeros.

The definitions `coordinateBasis` and `adaptedBasis` transport arbitrary
bases of the four components to the original state space.  The entrywise
matrix theorems and `kalman_block_matrix_zero_pattern` package the component
results into the displayed block form.

## Design notes and limitations

- The complements are noncanonical vector-space complements.  No chosen
  complement is claimed to be individually `A`-invariant.
- Only zeros forced by invariance of the reachable and unobservable subspaces
  are asserted; the starred blocks remain unrestricted.
- The scalar field is `ℂ`, matching the existing Hautus and unobservable
  subspace development.  The reachable-subspace file itself is polymorphic
  over an arbitrary field.
- The result concerns LTI triples `(A, B, C)` and does not include a
  feedthrough matrix `D`.
- The adapted basis is an existence construction using classical choices; the
  theorem does not claim a numerical decomposition algorithm.

## Regression examples

`LeanForControl/LinearSystems/KalmanDecompositionExamples.lean` exercises the
public API on a two-state zero system.  It verifies that the reachable
subspace is bottom, the unobservable subspace is top, and the general
existence theorem specializes to the example.  A separate example checks the
state-dimension-zero case with arbitrary input and output dimensions.

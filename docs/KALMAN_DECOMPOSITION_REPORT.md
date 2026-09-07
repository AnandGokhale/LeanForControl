# Kalman Decomposition Formalization Report

## Scope and reproducibility baseline

This development extends
[`AnandGokhale/LeanForControl`](https://github.com/AnandGokhale/LeanForControl)
from upstream commit `c5cedca904fe7b8168643c428b5cf5fd8b6ebf6d`
(`fixed license and citation`, 2026-09-01).  Work was performed on branch
`feature/kalman-decomposition` in the fork
[`dongxuelian2/LeanForControl`](https://github.com/dongxuelian2/LeanForControl).
The pinned environment is Lean `v4.30.0-rc2` and mathlib `v4.30.0-rc2`.

The formalization is dimension-generic in the state, input, and output
dimensions `n`, `m`, and `p`.  It includes the zero-dimensional edge cases.
It follows the existing project convention of complex matrices indexed by
`Fin n`, rather than introducing a second, incompatible abstract system type.

## Mathematical statement

For

```text
A : Matrix (Fin n) (Fin n) ℂ
B : Matrix (Fin n) (Fin m) ℂ
C : Matrix (Fin p) (Fin n) ℂ,
```

let `R(A,B)` be the range of the finite controllability matrix and let
`N(A,C)` be the existing finite-horizon unobservable subspace.  The theorem
constructs four subspaces, in the order

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

Addition therefore induces an adapted linear equivalence from the nested
product of the four components to `Fin n → ℂ`.  After choosing arbitrary
bases of the components, the matrices of the transported state, input, and
output maps have the entrywise forced-zero form

```text
     [ *  *  *  * ]        [ * ]
A' = [ 0  *  0  * ]   B' = [ * ]   C' = [ 0  *  0  * ].
     [ 0  0  *  * ]        [ 0 ]
     [ 0  0  0  * ]        [ 0 ]
```

Every displayed zero is a proved equality for every row and column index.
The starred entries are deliberately unconstrained.  The identities
`stateMatrix_eq_toMatrix_adapted`, `inputMatrix_eq_toMatrix_adapted`, and
`outputMatrix_eq_toMatrix_adapted` show that these are exactly the original
maps `A`, `B`, and `C` in the adapted state basis, not merely analogous
coordinate maps.

## Definitions and theorem inventory

### Reachability

`LeanForControl/LinearSystems/Reachability.lean` adds:

- `reachableSubspace`: the range of `controllabilityMatrix A B` as a
  submodule;
- `mem_reachableSubspace_iff`: the expected existential matrix-vector
  characterization;
- `controllabilityMatrix_mulVec_eq_sum`: the public finite-horizon bridge;
- `pow_mul_B_mulVec_mem_reachableSubspace`;
- `reachableSubspace_eq_iSup_range`: equality with the supremum of the ranges
  of `A^k B` for `k : Fin n`;
- `range_B_le_reachableSubspace`;
- `reachableSubspace_eq_top_iff_isControllable`;
- `reachableSubspace_invariant`.

The difficult boundary in `reachableSubspace_invariant` is the `A^n B`
term.  It is not hidden under an unproved closure claim: the private lemma
`aPowN_mul_B_mulVec_mem_reachableSubspace` expands the characteristic
polynomial, uses Cayley--Hamilton, isolates the monic leading term, and
expresses the remaining lower powers as reachable vectors.  This also treats
`n = 0` without a nonempty-index assumption.

### Four-way decomposition and coordinates

`LeanForControl/LinearSystems/KalmanDecomposition.lean` adds:

- `KalmanDecomposition`, which records the four subspaces and the exact
  direct-sum lattice relationships;
- `exists_kalmanDecomposition`, using relative complements in the modular
  lattice of submodules;
- `KalmanDecomposition.linearEquiv`, the change of coordinates obtained by
  composing three direct-sum equivalences;
- `linearEquiv_mem_reachable_iff` and
  `linearEquiv_mem_unobservable_iff`, exact coordinate characterizations of
  `R` and `N`;
- `stateMap`, `inputMap`, and `outputMap`, the transported system maps;
- `stateMap_cuo_zero_pattern`, `stateMap_co_zero_pattern`,
  `stateMap_uuo_zero_pattern`, `inputMap_zero_pattern`,
  `outputMap_cuo_eq_zero`, and `outputMap_uuo_eq_zero`;
- `coordinateBasis` and `adaptedBasis`;
- `stateMatrix`, `inputMatrix`, and `outputMatrix`, plus their equality to
  the corresponding `LinearMap.toMatrix` expressions in the adapted basis;
- seven entrywise state-matrix zero theorems, two input-matrix zero theorems,
  and two output-matrix zero theorems;
- `kalman_block_matrix_zero_pattern`, which bundles all eleven zero-block
  families into the displayed classical form.

The component names have precise coordinate semantics.  Reachability is
equivalent to the vanishing of the last two coordinates; unobservability is
equivalent to the vanishing of the second and fourth coordinates.  Thus the
first/second components are exactly the reachable part, and the first/third
components are exactly the unobservable part.  The remaining components are
complementary in the recorded direct-sum sense.

## Dependency graph

```text
Controllability.controllabilityMatrix
                │
                ▼
       reachableSubspace ── finite-horizon range bridge
                │
                ├── Cayley–Hamilton ──► reachableSubspace_invariant
                │
                └────────────────────────────────────────┐
                                                         │
Hautus.unobservableSubspace ── Cayley–Hamilton invariance ┤
                                                         ▼
                              modular-lattice complements
                                                         │
                                                         ▼
                                      KalmanDecomposition
                                                         │
                              product direct-sum equivalences
                                                         │
                                                         ▼
                                  adapted coordinates/basis
                                                         │
                     reachable and unobservable membership iff lemmas
                                                         │
                                                         ▼
                              A/B/C component zero patterns
                                                         │
                                                         ▼
                             entrywise block-matrix theorem
```

## Design choices and difficult points

1. **Finite horizon versus invariant closure.**  Defining reachability as an
   arbitrary invariant span would make invariance easy but would weaken the
   connection to the project's controllability matrix.  The development
   instead uses the exact finite-horizon range and proves closure using
   Cayley--Hamilton.
2. **No invariant complements are assumed.**  Arbitrary vector-space
   complements need not be `A`-invariant.  The proof derives only the zeros
   forced by invariance of `R` and `N`.  This is why the starred blocks remain
   unconstrained, and why the theorem does not falsely advertise each chosen
   complement as a standalone invariant subsystem.
3. **Relative direct sums.**  Mathlib directly supplies a product equivalence
   for globally complementary submodules.  A small private helper packages
   addition as an equivalence onto a relative supremum, allowing the three
   complement choices to compose without quotient detours.
4. **Basis transport.**  The block result is first proved for transported
   linear maps because component projections are transparent there.  The
   three `*_eq_toMatrix_adapted` theorems then identify those matrices with
   `A`, `B`, and `C` in the mapped basis by definitional basis-transport
   identities.

## Regression coverage

`LeanForControl/LinearSystems/KalmanDecompositionExamples.lean` contains a
concrete two-state, one-input, one-output zero system.  It proves that its
reachable subspace is bottom, its unobservable subspace is top, and the
general four-way decomposition specializes to it.  A separate example checks
that the existential theorem elaborates uniformly for state dimension zero
and arbitrary input/output dimensions.

## Novelty and prior-art audit

This is a bounded, reproducible audit, not a claim of absolute global
priority.

- The named comparison library,
  [`mcdoll/DynamicalSystems`](https://github.com/mcdoll/DynamicalSystems), was
  inspected on 2026-09-07.  Its public umbrella imports autonomous and
  nonautonomous dynamics, input/output notions, stability, Lyapunov theory,
  and ODE support; its recursive source tree contained no paths matching
  `Kalman`, `Controll`, `Observ`, or `LinearSystem`.  No reusable Kalman
  decomposition was found there.
- Authenticated GitHub code searches on 2026-09-07 returned zero results for
  [`"Kalman decomposition" language:Lean`](https://github.com/search?q=%22Kalman+decomposition%22+language%3ALean&type=code),
  [`KalmanDecomposition language:Lean`](https://github.com/search?q=KalmanDecomposition+language%3ALean&type=code),
  and
  [`reachableSubspace language:Lean`](https://github.com/search?q=reachableSubspace+language%3ALean&type=code).
  Search indexing and private repositories limit what this establishes.
- Broader searches for Isabelle/HOL and Coq formalizations did not locate a
  machine-checked four-way finite-dimensional Kalman decomposition.  Related
  theorem-proving work such as
  [*Formal Verification of Control Systems Properties with Theorem Proving*](https://arxiv.org/abs/1405.7615)
  concerns deductive verification of modeled control-system properties in
  Why3, rather than the structural linear-algebra theorem proved here.

What is certainly new relative to the audited upstream commit is the complete
chain from finite-horizon reachable subspace, through its rigorous invariant
proof, to a four-way adapted basis and entrywise A/B/C block form.  Existing
upstream work on the unobservable subspace and its Cayley--Hamilton invariance
is reused directly.  Standard mathlib infrastructure for submodule ranges,
modular-lattice complements, product bases, linear equivalences, and matrix
conversion is also reused rather than reimplemented.

## Trust and limitations

- The new files contain no `sorry`, `admit`, `unsafe` declarations, or custom
  axioms.
- Noncomputability comes only from classical complement and basis choices.
- The scalar field is `ℂ`, matching the upstream Hautus development.  The
  reachability file itself is polymorphic over an arbitrary field.
- The theorem treats LTI triples `(A,B,C)` and does not add a feedthrough
  matrix `D`.
- Complements and the adapted basis are noncanonical.  The result proves
  existence and exact structure, not a numerically stable decomposition
  algorithm.
- The theorem states the block form as quantified entrywise zeros.  This is
  dimension-generic even when component dimensions are zero and avoids
  artificial casts between dependent block sizes.

## Validation protocol

The final validation is performed with the repository-pinned toolchain:

```text
lake clean
lake exe cache get
lake build
```

The proof audit additionally searches the changed source for forbidden proof
holes and runs `#print axioms` on the principal reachability, decomposition,
coordinate-equivalence, and matrix-block theorems.  Final command outcomes
and commit identifiers are recorded in the branch history and delivery
summary.

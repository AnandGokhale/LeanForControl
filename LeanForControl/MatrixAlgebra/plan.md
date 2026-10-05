# Plan: Jordan normal form

Roadmap for `MatrixAlgebra/Jordan.lean` and the modules it needs. The rest of
`MatrixAlgebra/` is covered by `LeanForControl/LinearSystems/plan.md` (`L`); this file exists
because Jordan normal form is a project in its own right rather than a file.

**Status: parked.** Nothing here is started. See *Why it is parked* below.

## Why do it at all

Hespanha's Theorem 8.1 has four clauses. Two of them — marginal stability (1) and instability
(4) — say "the Jordan blocks corresponding to eigenvalues with zero real part are `1 x 1`".
Mathlib has no Jordan normal form, so those clauses cannot be stated as the textbook states
them.

They *can* be worked around: "all blocks at `mu` are `1 x 1`" is equivalent to
`ker (A - mu)^2 = ker (A - mu)`, which is expressible with Mathlib's generalized eigenspaces.
That workaround is written up at the end of this file. It was rejected as the primary plan:
it is a lemma shaped to fit one theorem, and it leaves the library with no notion of a Jordan
block.

## What "done correctly" delivers

1. **Existence** — a basis in which the operator is block-diagonal with Jordan blocks.
2. **Uniqueness** — the multiset of blocks is an invariant of the operator.
3. **Computable invariants** — block counts as rank/nullity differences. This is the part that
   gets consumed downstream. "All blocks at `mu` are `1 x 1` iff `ker (f - mu)^2 = ker (f - mu)`"
   should be a *corollary*, not a definition.
4. **Analytic corollaries** — `exp (J t)` in closed form, hence the growth bound
   `‖exp (A t)‖ <= C (1 + t)^(d-1) exp (alpha t)` with `alpha = max Re mu` and `d` the largest
   block size.

With 4 in hand, all four clauses of Theorem 8.1 are corollaries — including 2 and 3, so the
existing `IsHurwitz.exists_norm_exp_le` development in
`LinearSystems/Stability/Continuous/LyapunovLTI.lean` becomes a special case rather than a
separate proof.

## State of Mathlib (checked 2026-10-02)

Available and load-bearing:

- `Module.End.iSup_maxGenEigenspace_eq_top` (`LinearAlgebra/Eigenspace/Triangularizable.lean`),
  for `[IsAlgClosed K] [FiniteDimensional K V]` — the primary decomposition. This is the engine
  for J2.
- `Module.End.IsFinitelySemisimple.genEigenspace_eq_eigenspace`
  (`LinearAlgebra/Eigenspace/Semisimple.lean`).
- `LinearMap.ker_pow_le_ker_pow_finrank` (`LinearAlgebra/FiniteDimensional/Lemmas.lean`) — the
  kernel filtration stabilises.
- `Module.equiv_free_prod_directSum` — the structure theorem for finitely generated modules
  over a PID. Only needed by Route A.
- `Matrix.blockDiagonal'`, indexed by a sigma type, so blocks may have different sizes.
  (`Matrix.blockDiagonal` is uniform-size and is *not* enough.)
- `LinearAlgebra/JordanChevalley.lean` — `exists_isNilpotent_isSemisimple` and
  `isNilpotent_isSemisimple_unique`. This is `A = S + N`, **not** Jordan form, and does not
  give block structure.

Not available: Jordan normal form itself, in any shape. It is a long-standing gap.

## Two routes

**Route A — structure theorem over a PID.** View `V` as a `K[X]`-module through `f`; `K[X]` is
a PID, so `V` decomposes as a direct sum of `K[X] / ((X - mu)^e)`, each of which is a Jordan
block. Uniqueness comes free from uniqueness of elementary divisors.

**Route B — nilpotent first.** Primary decomposition reduces to a single eigenvalue; shift so
the operator is nilpotent; prove Jordan form for a nilpotent operator by induction on the
kernel filtration; reassemble.

**Chosen: Route B.** Not because A is wrong. Route A's cost is all in translation — getting
from an abstract module isomorphism to a basis and then to a matrix — and the proof yields no
direct information about block sizes. In Route B the induction *is* the invariant computation,
so deliverable 3 falls out of the proof instead of being reconstructed afterwards.

## Modules

| | content | size |
|---|---|---|
| **J0** | `jordanBlock mu n`: `mu • 1 + shift`. Nilpotency of the shift, powers, `charpoly`, `minpoly`, `rank ((J - mu)^k)`. | small |
| **J1** | Jordan form of a **nilpotent** operator: the filtration `ker N <= ker N^2 <= ...` and a basis adapted to it. Block sizes read off from `d k = finrank (ker (N^k))`. | **hard — the core** |
| **J2** | Primary decomposition: `V = sum over mu of genEigenspace f mu`, each invariant, `(f - mu)` nilpotent on its summand. | medium, mostly Mathlib |
| **J3** | Existence: J1 + J2 give a basis in which `f` is `blockDiagonal'` of Jordan blocks. Matrix similarity as a corollary. | assembly |
| **J4** | Uniqueness and invariants: blocks of size `>= k` at `mu` number `finrank (ker (f-mu)^k) - finrank (ker (f-mu)^(k-1))`. Yields uniqueness of the block multiset, "all blocks `1 x 1` iff `ker (f-mu)^2 = ker (f-mu)`", and "largest block = multiplicity of `mu` in `minpoly`". | medium |
| **J5** | `exp (J t)` closed form; the growth bound; Hespanha 8.1 entire. | mechanical given J0, J3 |

Dependencies:

```
J0 ------------------> J5
J1 --\
      +-- J3 --> J4 --> J5
J2 --/
```

## Design decisions, to settle before J1

**Index type.** Jordan form needs a sized, ordered index. The library's abstract-`X` convention
cannot express block structure, and `Matrix.blockDiagonal` is uniform-size, so blocks live over
`Sigma i, Fin (n i)`.

Proposal: state the primary result about `Basis` and `LinearMap.toMatrix`, not about `Matrix`:

```lean
exists (iota : Type) (_ : Fintype iota) (mu : iota -> K) (n : iota -> Nat)
    (b : Basis (Sigma i, Fin (n i)) K V),
  LinearMap.toMatrix b b f = Matrix.blockDiagonal' (fun i => jordanBlock (mu i) (n i))
```

This keeps the sigma index off `X` entirely. Similarity for a concrete `A : Matrix X X K` is
then one `reindex` away, paid once rather than threaded through every statement.

**Scalars.** `[Field K] [IsAlgClosed K]` for the general theory. Real matrices enter by
complexification — which wants the `MatrixAlgebra/Complex.lean` tech-debt item done first,
since this development would otherwise spell `A.map (algebraMap R C)` hundreds of times.

**Location.** `MatrixAlgebra/Jordan.lean`, as `L` already anticipates. No control content, so
by the `Analysis/`-needs-no-citations convention it carries no textbook reference and is an
upstream candidate.

## Phasing, with real stopping points

1. **J0 alone.** Self-contained, immediately useful, and it forces the block-indexing decision
   early, where changing it is cheap.
2. **J1.** The real work. If it proves harder than expected, J0 still stands.
3. **J2 + J3.** Existence.
4. **J4.** Uniqueness and invariants — what makes this a development rather than a workaround.
5. **J5.** The control payoff; retires the specialized decay development.

## Why it is parked

Clauses 1 and 4 are the least useful clauses of Theorem 8.1 — marginal stability is the
boundary case, and the workhorses, clauses 2 and 3, are already proved. Theorem 8.2 (the
Lyapunov equation) needs no Jordan theory at all, and is also what structurally unblocks the
rewrite of `LinearSystems/Stability/Continuous/`, because `Stability/LyapunovIndirect/
Linearization.lean` on the nonlinear side depends on `LyapunovEquation.lean`.

So Jordan buys two boundary-case clauses; 8.2 buys the next textbook result and the demolition.
8.2 goes first.

Two things make parking cheap rather than lossy: **J0 is independent** and can be picked up at
any time, and **J2 is shared** with the workaround below, so it is not wasted in either
direction.

If this is ever done properly it is probably worth doing **as a Mathlib contribution** rather
than in-repo: same work, with review, and it stops being this project's maintenance burden.

## The rejected workaround, for the record

If clauses 1 and 4 are ever wanted before Jordan form exists, the specialized route is:

- Restate the block condition as semisimplicity on the imaginary-axis spectrum.
- Reduce clause 1 to `(exists C, forall t >= 0, ‖exp (A t)‖ <= C) iff (spectrum in closed left
  half-plane) and (imaginary-axis eigenvalues semisimple)`, using
  `stableNA_iff_boundedStateTransition` and `stateTransitionMatrix_const`.
- Clause 4 is then free: `UnstableNA` is `Not StableNA`, so it follows by `push Not`, exactly
  as `unstableNA_iff_unboundedHomogeneousResponse` did.
- The forward direction needs only instability certificates: `Re mu > 0` gives
  `exp (A t) v = exp (mu t) v`, and `Re mu = 0` with `(A - mu) w = v <> 0` gives
  `exp (A t) w = exp (mu t) (w + t v)`. Both are small, and reuse
  `MatrixAlgebra.exp_mulVec_of_mulVec_eq_smul`.
- The reverse direction needs J2 (shared), restriction of `exp` to an invariant subspace,
  boundedness on the semisimple imaginary part, and `IsHurwitz.exists_norm_exp_le` reused
  verbatim on the Hurwitz part.

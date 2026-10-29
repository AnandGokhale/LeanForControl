# Plan: Contraction theory

Index of the contraction-theory folders.  Each folder keeps its own `plan.md` with its remaining
work; this file only records what each folder is for and the order of work.

Spine: F. Bullo, *Contraction Theory for Dynamical Systems* (ed. 1.0, 2022), and A. V. Proskurnikov
and F. Bullo, *Regular Pairings for Nonquadratic Lyapunov Functions and Contraction Analysis*,
SIAM J. Control Optim. 64(1):496–521 (2026).

| Folder | Topic | Status |
|---|---|---|
| [`Norms/`](Norms/plan.md) | norms, induced and log norms, regular pairings, one-sided Lipschitz maps | norms core and one-sided Lipschitz maps done |
| [`Systems/`](Systems/plan.md) | solutions of one-sided Lipschitz systems, grades of contractivity, certificates | contraction bound stated |

Goal: make it easy to prove that a concrete system is contracting in a chosen norm, from a bound
`μ(DF(x)) ≤ -c` on its Jacobian.  Order of work:

1. the contraction bound in any norm, and the grades (`Systems/`);
2. the affine certificate, then the weighted ℓ∞ Hopfield certificate (`Systems/`);
3. retire `Analysis/OneSidedLipschitz.lean`.

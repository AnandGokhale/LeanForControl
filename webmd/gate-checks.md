# gate-checks.md

## Purpose

Do not enter the main `dp-infhor.tex` proof chain until these gates are checked.

Each gate must be either:

- already available, or
- assigned to a concrete local wrapper file

## Gate A — matrix order

Check or build:

- positive semidefinite / positive definite matrix notions over `ℝ`
- quadratic-form positivity lemmas
- monotonicity under congruence
- basic Schur-complement inequalities

## Gate B — block matrices

Check or build:

- block assembly / extraction identities
- multiplication rules
- transpose rules
- blockwise positivity consequences

Do not do large proofs with ad hoc block algebra inline.

## Gate C — quadratic optimization

Check or build:

- SPD Hessian implies unique minimizer
- quadratic completion lemmas
- block elimination / Schur reduction
- kernel-trivial implies invertible, when needed

## Gate D — semidefinite prior primitives

Check or build only what is needed:

- support/range constraint formulation
- block covariance decomposition
- the specific pseudoinverse identities used in the prior term
- range parameterization of the semidefinite block

Do not formalize full Moore–Penrose theory unless forced.

## Gate E — discrete-time recursion

Check or build:

- matrix-power trajectory lemmas
- one-step and multi-step recursion formulas
- Bellman recursion notation conventions
- stable finite-horizon indexing conventions

## Gate F — imported facts vs local wrappers

Decide explicitly what will be wrapped rather than reproved.

Expected examples:

- infinite-horizon LQR convergence fact
- Cayley–Hamilton
- Gramian / eigenvalue facts
- invariant-subspace facts

Do not discover this in the middle of a hard proof.

## Gate G — file split

Fix the target files before the main phase.

Likely split:

- semidefinite prior / covariance geometry
- finite-horizon forecasted-disturbance LQR
- matrix plumbing
- asymptotic / coercivity lemmas
- final infinite-horizon theorem

Do not dump everything into one file.

## Ready condition

The project is ready for the main proof chain only when:

- each gate is satisfied or assigned
- the file split is fixed
- `lake build` is green
- the next theorem is unambiguous
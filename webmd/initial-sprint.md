# LeanForControl plan: first linear-systems track

## Goal

Build a small, reliable linear-systems layer inside `LeanForControl` that is strong enough to support:

1. controllability / observability definitions
2. controllability and observability matrix lemmas
3. one or both Hautus lemmas
4. later: discrete-time estimator and LQR statements

We are **not** trying to formalize all of control theory at once.

We are also **not** trying to start with the hardest theorem.

The first target should be a theorem that teaches us:

- how matrices are represented in Lean/mathlib
- how rank, kernel, image, and linear independence are handled
- how to structure statements so they are actually provable in the existing ecosystem

---

## Current state of the repo

### Already present

The repo already has nontrivial Lean content in:

- `Dini/`
- `ODEs/`
- `Lyapunov/`

This material is mostly:

- continuous-time analysis
- Dini derivatives
- comparison lemmas
- Lyapunov stability notions

### Not present yet

We do **not** yet seem to have a reusable linear-systems library layer for:

- finite-dimensional matrices over `ℝ` or `ℂ`
- controllability / observability matrices
- rank and kernel reformulations
- block matrix lemmas
- eigenvalue / eigenspace helpers for PBH/Hautus
- discrete-time LQR / Riccati

### Important structural note

`LeanForControl.lean` currently only imports `Basic.lean`, so the project is not yet exporting the real theory modules from the root.

That is not fatal, but it means we should clean up library organization as we go.

---

## Big-picture strategy

We should proceed in four phases.

### Phase 0: stabilize the project workflow

Make sure a beginner can:

- open the repo in VS Code
- run `lake build`
- create a new `.lean` file
- import project modules and `Mathlib`
- use `#check`, `#print`, and `#find`

### Phase 1: create a linear-systems foundation

Add a new folder:

- `LeanForControl/LinearSystems/`

This phase should contain definitions and helper lemmas only.

### Phase 2: prove easier first wins

Before attacking Hautus, prove things like:

- controllability matrix formula
- observability matrix formula
- “observability matrix has trivial kernel” style lemmas
- finite-horizon reachability statements
- rank / kernel equivalences for controllability/observability matrices

These are much better first targets than LQR.

### Phase 3: attack Hautus

Once the matrix/control layer is usable, prove:

- one direction of Hautus controllability
- one direction of Hautus observability
- then the converses

Only after that should we decide whether to pursue:

- LQR convergence
- estimator-cost convergence
- asymptotic state-estimator convergence

---

## Recommended theorem order

This is the order I would use.

### Stage A: project and import hygiene

Do this first.

#### Tasks

1. Update `LeanForControl.lean` so it eventually re-exports useful modules.
2. Create a new directory `LeanForControl/LinearSystems/`.
3. Add one starter file `LeanForControl/LinearSystems/Basic.lean`.
4. Confirm that this file compiles via `lake build`.

#### First content in `Basic.lean`

Keep it tiny. Start with imports and notation experiments.

Use this file as a sandbox for:

- matrix type conventions
- index type conventions
- whether to use `Fin n`
- whether states are column vectors as functions `Fin n → 𝕂`

---

### Stage B: decide on conventions

This is crucial. The local agent should **not** improvise conventions per theorem.

#### Recommended conventions

Work over a field `𝕂`, usually `ℝ` first, later `ℂ` when Hautus needs eigenvalues.

Use:

- `Matrix (Fin n) (Fin n) 𝕂` for square matrices
- `Matrix (Fin n) (Fin m) 𝕂` for input matrices
- state vectors as `Fin n → 𝕂`

This is the standard mathlib style and will save pain later.

#### Decide early

- whether all first theorems are over `ℝ`
- whether Hautus is stated directly over `ℂ`
- whether to define controllability first over arbitrary fields

My recommendation:

- start controllability / observability matrix definitions over a general field
- delay the full Hautus lemma until you are willing to work over `ℂ`

---

### Stage C: build the first reusable linear-systems files

## File 1: `LinearSystems/Basic.lean`

### Purpose

Contain only basic definitions and shared imports.

### Likely contents

- aliases / abbreviations for state-space dimensions
- maybe a one-step discrete-time update
- helper notation if needed
- basic matrix-power facts if convenient

### Do not put here

- long proofs
- PBH/Hautus
- control-specific theorem clutter

Keep this file clean.

---

## File 2: `LinearSystems/Controllability.lean`

### First definitions

Define the finite controllability matrix

\[
\mathcal C(A,B)=\begin{bmatrix} B & AB & \cdots & A^{n-1}B \end{bmatrix}
\]

This is a perfect first major object.

### First target lemmas

Prove things like:

1. the columns of `A^k B` lie in the reachable subspace
2. the reachable subspace over `n` steps is the span / range of the controllability matrix
3. controllability means full column-span or rank `n`

The exact final formalization may vary depending on what is easy in mathlib, but the goal is to connect:

- reachability
- span of columns
- matrix rank / linear map range

### Why this should come first

Because Hautus will later need a bridge between:

- controllability defined by controllability matrix / reachable space
- controllability characterized by a rank test

So this file is foundational.

---

## File 3: `LinearSystems/Observability.lean`

### First definitions

Define the observability matrix

\[
\mathcal O(A,C)=\begin{bmatrix} C \\ CA \\ \vdots \\ CA^{n-1} \end{bmatrix}
\]

### First target lemmas

Prove:

1. if `𝒪(A,C) x = 0`, then `C A^k x = 0` for all `k = 0, …, n-1`
2. observability is equivalent to trivial kernel of the observability matrix
3. if the observability matrix has full column rank, then the system is observable

This file will be one of the easiest genuine wins and directly helps with your estimator proof later.

---

## File 4: `LinearSystems/MatrixLemmas.lean`

### Purpose

Collect all ugly facts that do not belong in theorem files.

Examples:

- block matrix lemmas
- rank lemmas
- kernel / range lemmas
- matrix-power helper lemmas
- identities for multiplication with block rows / columns
- coercions between matrices and linear maps if needed

This file will save enormous pain later.

Important rule:

If a proof in `Controllability.lean` or `Observability.lean` starts becoming “about matrices” rather than “about control,” move the matrix part here.

---

### Stage D: first theorem targets

These are the best realistic first theorems.

## First target theorem

A good first real theorem is **not** Hautus.

It is:

- observability iff the observability matrix has trivial kernel

or equivalently

- controllability iff the reachable subspace equals the full state space

Why these first:

- finite-dimensional
- constructive
- close to textbook definitions
- no eigenvalues yet
- no complex scalars yet
- no PBH/Hautus machinery yet

This is where the local agent should score its first success.

---

## Second target theorem

Then prove a rank formulation such as:

- observability iff `rank (observabilityMatrix A C) = n`
- controllability iff `rank (controllabilityMatrix A B) = n`

This will teach:

- how rank is used in Lean
- how to bridge rank and trivial kernel
- how finite-dimensional linear algebra is formalized in mathlib

---

## Third target theorem

Only then attack:

### Hautus for observability

\[
\rank \begin{bmatrix} \lambda I - A \\ C \end{bmatrix}=n \quad \forall \lambda \in \mathbb C
\]

### Hautus for controllability

\[
\rank \begin{bmatrix} \lambda I - A & B \end{bmatrix}=n \quad \forall \lambda \in \mathbb C
\]

Between the two, I would actually try **observability first**.

It often matches kernel / eigenvector reasoning more directly:

- if not observable, produce a nonzero state in the unobservable subspace
- use invariant-subspace / eigenvector reasoning
- derive a Hautus failure

Controllability can then be obtained by duality or proved separately.

---

## What not to do yet

Do **not** start with these:

- infinite-horizon LQR convergence
- DARE / Riccati existence
- estimator asymptotic convergence
- full Kalman decomposition
- detectability / stabilizability versions of Hautus

These are good later targets, but they require too much infrastructure too early.

---

## Concrete setup tasks for the local agent

The local agent should perform these in order.

### Task 1: inspect the current import graph

Find which imports are actually needed for:

- matrices
- rank
- linear maps
- eigenvalues / eigenspaces
- finite-dimensional vector spaces

It should test in a scratch file with commands like:

- `#check Matrix`
- `#check Matrix.rank`
- `#check LinearMap.ker`
- `#check FiniteDimensional.finrank`

and similar commands until it understands the API.

### Task 2: create a scratch file for theorem search

Make a file like `LeanForControl/LinearSystems/Scratch.lean`.

Use it to search:

- how to define block matrices
- how to state matrix rank
- how to express “full column rank”
- how to move between matrices and linear maps
- whether observability matrix definitions already exist in mathlib

This file is for experiments only.

### Task 3: decide whether to use matrix rank directly or linear-map kernel / range

A lot of the time, proofs are easier via linear maps than via raw matrix rank.

The local agent should test both worlds early.

### Task 4: define controllability and observability matrices

Even if mathlib has partial support, define project-local versions if needed.

The key is to get a clean API that you control.

### Task 5: prove small shape lemmas

For example:

- what is the `k`th block row of the observability matrix?
- what is the `k`th block column of the controllability matrix?
- what does multiplying by a state vector do?

These tiny lemmas are often the real work.

---

## Proposed file structure after the first pass

- `LeanForControl.lean`
- `LeanForControl/Basic.lean`
- `LeanForControl/LinearSystems/Basic.lean`
- `LeanForControl/LinearSystems/Scratch.lean`
- `LeanForControl/LinearSystems/MatrixLemmas.lean`
- `LeanForControl/LinearSystems/Controllability.lean`
- `LeanForControl/LinearSystems/Observability.lean`
- `LeanForControl/LinearSystems/Hautus.lean`

Later maybe:

- `LeanForControl/LinearSystems/Stabilizability.lean`
- `LeanForControl/LinearSystems/Detectability.lean`
- `LeanForControl/LinearSystems/LQR.lean`
- `LeanForControl/LinearSystems/Estimation.lean`

---

## How the beginner should run things

The local agent should assume the user is new, so it should explain setup in tiny steps.

### Basic workflow

From the project root:

- run `lake build`

To work in VS Code:

- open the inner Lean project root
- wait for Lean to finish checking files
- create a new `.lean` file under `LeanForControl/LinearSystems/`
- import the file in `LeanForControl.lean` only after it compiles

### Useful beginner commands in a Lean file

Use commands like:

- `#check Matrix`
- `#check Matrix.mul`
- `#check Matrix.rank`
- `#check Matrix.det`
- `#check LinearMap.ker`
- `#check Submodule`
- `#check FiniteDimensional.finrank`

Also useful:

- `#print Matrix.rank`
- `#find _ + _ = _ + _`

and hovering over names in VS Code.

---

## Suggested first milestone

The first milestone should be:

Create `Observability.lean` and prove a theorem equivalent to:

- if the observability matrix has trivial kernel, then the system is observable

That is modest, real, and directly useful later.

A slightly stronger milestone is:

- observable iff the observability matrix has full column rank

That is probably the best first serious theorem in this line.

---

## Suggested second milestone

Then do the controllability matrix side.

After both are in place, decide whether:

- to prove Hautus directly
- or to prove observability Hautus first and get controllability by duality

---

## Advice on Hautus specifically

Do not start with the exact textbook statement using

\[
\rank \begin{bmatrix} \lambda I - A \\ C \end{bmatrix}=n \quad \forall \lambda \in \mathbb C
\]

before you know how Lean wants you to express:

- `λ : ℂ`
- scalar extension from `ℝ` to `ℂ` if needed
- eigenvalues / eigenvectors
- stacked block matrices
- rank over `ℂ`

A better internal proof route may be:

1. formulate failure of observability as existence of a nonzero vector in the unobservable subspace
2. use finite-dimensional invariant-subspace arguments to produce an eigenvector
3. show this eigenvector violates the Hautus test

That is closer to textbook reasoning and likely cleaner than brute-force rank manipulations.

---

## What success looks like after the first serious pass

At the end of the first successful development sprint, we should have:

1. a new `LinearSystems` folder
2. a compiling scratch file for theorem search
3. clean project-local definitions of controllability and observability matrices
4. one nontrivial theorem proved about observability or controllability
5. a short list of missing matrix / rank lemmas needed for Hautus

That is a real, solid start.

---

## Bottom line

The immediate next move is:

1. create `LinearSystems/`
2. make a scratch file
3. define observability and controllability matrices
4. prove a matrix-based observability theorem first
5. only then attack Hautus
6. delay LQR and estimator asymptotics until this layer is stable

This keeps the target modest, teaches the local agent the right part of Lean/mathlib, and builds infrastructure you will actually reuse.
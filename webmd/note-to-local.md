# Next phase: Hautus for observability

## Goal

Prove the observability Hautus lemma before touching the controllability side.

Target shape:

\[
\rank \begin{bmatrix} \lambda I - A \\ C \end{bmatrix} = n
\qquad
\text{for all } \lambda \in \mathbb{C}
\]

Do observability first.

Do not start controllability Hautus yet.

---

## File plan

Create:

- `LeanForControl/LinearSystems/Hautus.lean`

If a proof needs reusable matrix-only facts, put those in:

- `LeanForControl/LinearSystems/MatrixLemmas.lean`

Keep control statements out of `MatrixLemmas.lean`.

---

## Scalar field

For Hautus, work over `ℂ`.

Do not fight this.

The theorem is about eigenvalues, so move to the field that naturally supports that machinery.

---

## Proof order

### Step 1

Define the Hautus observability test cleanly.

Do this in a way that does not commit too early to one exact rank API if the linear-map form is easier.

### Step 2

Prove the **failure direction** first:

- if `(A, C)` is not observable
- then there exists `λ : ℂ` such that the Hautus test fails

Recommended route:

1. define the unobservable subspace
2. prove it is `A`-invariant
3. show if observability fails, this subspace is nontrivial
4. extract an eigenvector from the nontrivial invariant subspace
5. use that eigenvector to violate the Hautus test

This is the main job of the phase.

### Step 3

Then prove the converse:

- if the Hautus test fails for some `λ`
- then `(A, C)` is not observable

This direction should be shorter.

Use the witness vector directly.

### Step 4

Only after both directions are stable, package the full iff theorem.

---

## Immediate helper lemmas to expect

Likely needed:

- unobservable subspace is a submodule
- unobservable subspace is `A`-invariant
- nontrivial finite-dimensional invariant subspace over `ℂ` contains an eigenvector
- witness vector from Hautus failure implies non-observability
- reassociation lemmas for matrix-vector products if needed

Do not prove all helpers up front.

Add them only when the proof demands them.

---

## Strategy rules

Prefer:

- invariant-subspace arguments
- kernel / linear-map reasoning
- short helper lemmas
- exact witness-based proofs

Avoid:

- brute-force rank manipulation
- giant block-matrix proofs
- starting from the final statement and thrashing on syntax
- touching controllability Hautus in this sprint

---

## Reporting

At the end of the phase:

1. `lake build` green
2. update `notes.md`
3. regenerate blueprint if new `@[blueprint]` declarations were added

---

## Definition of success

This phase is a success if:

- `Hautus.lean` exists and compiles
- the observability Hautus failure direction is proved
- ideally the full observability Hautus iff is proved
- no `sorry`, `admit`, or `axiom`
- build stays green
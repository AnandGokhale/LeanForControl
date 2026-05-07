# Next steps for the local agent

## Immediate target

Do **not** start Hautus yet.

The next goal is to bridge:

- observability as a kernel statement
- observability as a rank / full-column-rank statement

That infrastructure will be needed anyway.

---

## Step 1: add `MatrixLemmas.lean`

Create:

- `LeanForControl/LinearSystems/MatrixLemmas.lean`

Put only matrix-level facts here.

Do **not** put control-specific theorems here.

---

## Step 2: move to a stronger scalar assumption

Keep the current definitions over a weak scalar type.

For the next lemmas, work over a field.

Reason:

- rank and kernel tools are cleaner
- full-column-rank statements are cleaner
- this avoids fighting semiring generality too early

---

## Step 3: prove the matrix-to-linear-map bridge

Add lemmas connecting:

- `observabilityMatrix A C *ᵥ x = 0`
- kernel of the associated linear map
- rank / finrank / full-column-rank formulations

The agent should search mathlib first instead of inventing custom notions.

---

## Step 4: prove the rank version of observability

Target theorem:

- observability iff the observability matrix has full column rank

Equivalent rank form is also fine.

This should live in `Observability.lean`, using helper lemmas from `MatrixLemmas.lean`.

---

## Step 5: mirror the same pattern for controllability

In `Controllability.lean`:

- add the matching kernel / range / rank infrastructure
- prove the controllability-matrix characterization before Hautus

---

## Step 6: only then start Hautus

Start with observability-side Hautus first.

Do not begin from the final rank statement immediately.

Better route:

1. failure of observability
2. invariant unobservable subspace
3. eigenvector witness
4. conclude Hautus fails

Then prove the converse.

Only after that decide whether to get controllability by duality or prove it directly.

---

## File actions

Next files to touch:

- `LeanForControl/LinearSystems/MatrixLemmas.lean`
- `LeanForControl/LinearSystems/Observability.lean`

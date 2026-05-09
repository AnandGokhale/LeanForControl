# 6 — Schur stability

## Context

Define the discrete-time stability predicate for matrices and connect it to
mathlib's spectrum machinery. Most of the work wraps existing infrastructure
(`Mathlib/Analysis/Matrix/Spectrum.lean`, `Mathlib/LinearAlgebra/Eigenspace/`).
Needed by every later sprint that uses "Schur" or "stable" — including
detectability (sprint 8), the LQR closed-loop (sprint 15), and the
no-decay/`fact:no-decay` argument inside dp-infhor's zero-output lemma.

## Files to create or modify

Create:
- `LeanForControl/LinearSystems/Stability.lean` — `IsSchur`, `A^k → 0`
  bridge, no-decay lemma.

Modify:
- `LeanForControl.lean` — add the import once `Stability.lean` compiles.
- `blueprint/src/content.tex` — append "Stability" subsection.
- `notes/6-schur-stability.md`, `exports/6-schur-stability.zip` per the
  end-of-session recipe.

## Sketch

1. `def IsSchur (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=` "every eigenvalue
   of `A` has modulus `< 1`". Phrase via `spectrum ℂ A` (or `Matrix.spectrum`).
2. `IsSchur A ↔ ∀ k, ∀ v, A^k *ᵥ v → 0 as k → ∞` — the operational form.
3. `fact:no-decay`: for `A : Matrix (Fin n) (Fin n) ℂ` with all eigenvalues
   `|λ| ≥ 1`, `A^k *ᵥ v → 0` implies `v = 0`. The contrapositive of decay.
4. (Optional, if cheap) bridge to `LinearMap.spectralRadius` if mathlib has it.

## Risk

🟢 — most mathlib glue; the only awkward part is connecting the `n^∞ → 0`
limit to the algebraic eigenvalue bound. Schur form / triangulation might
help. Write the simplest direct proof first; refactor if it gets long.

## Open questions

- Does mathlib have `Matrix.IsSchur`? Explore says no — confirm and define
  ourselves.
- Phrasing of "eigenvalues `< 1`": via `spectrum`, via `charpoly` roots, or
  via `Module.End.HasEigenvalue`? Pick the one that makes downstream
  rewrites cleanest.

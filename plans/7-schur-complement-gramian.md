# 7 — Schur complement + Gramian divergence

## Context

Two matrix-level facts that downstream LQR/estimator proofs lean on. The
Schur complement bound is mostly mathlib glue
(`Mathlib/LinearAlgebra/Matrix/SchurComplement.lean` + `PosDef.lean`). The
Gramian divergence is `dp-infhor`'s `fact:gramian` and is a custom limit
argument over `[Field ℂ]`.

## Files to create or modify

Modify:
- `LeanForControl/LinearSystems/MatrixLemmas.lean` — append both lemmas (no
  `@[blueprint]` tags; this is plumbing).

Create:
- (none new)

## Sketch

### Step 1 — Schur complement bound

```
lemma schur_complement_bound
    {A : Matrix (Fin n) (Fin n) 𝕜} {B : Matrix (Fin n) (Fin m) 𝕜}
    {C : Matrix (Fin m) (Fin m) 𝕜}
    (hPSD : (Matrix.fromBlocks A B Bᵀ C).PosSemidef)
    (hC : C.PosDef) :
    (A - B * C⁻¹ * Bᵀ).PosSemidef
```

Likely a `Matrix.PosSemidef.fromBlocks₂₂` direct application or a tiny
wrapper. Verify lemma names when active.

### Step 2 — Spectral mapping for matrix powers

```
lemma spectrum_pow_subset_pow_spectrum
    (A : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    spectrum ℂ (A^m) ⊆ (· ^ m) '' spectrum ℂ A
```

(or equality, depending on what's needed by `fact:gramian`). Likely already
in mathlib's `Mathlib.Spectrum` machinery.

### Step 3 — Gramian divergence (`fact:gramian`)

```
theorem gramianSum_lambdaMin_atTop
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ μ : ℂ, μ ∈ spectrum ℂ A → 1 ≤ ‖μ‖)
    (m : ℕ) (hm : 0 < m) :
    Filter.Tendsto
      (fun q : ℕ => Matrix.lambdaMin (∑ j ∈ Finset.range q, (A^(j*m))ᵀ * A^(j*m)))
      Filter.atTop Filter.atTop
```

Proof follows dp-infhor's contradiction argument: assume
`λ_min(G_q) ↛ ∞`, extract a bounded subsequence of unit vectors, take a
limit, derive `A^{jm} v → 0` for the limit unit vector, then apply the
no-decay fact (sprint 6) to contradict `‖v‖ = 1`. The hard parts are
sequential compactness in `Fin n → ℂ` (which is finite-dim, so closed
bounded ⇒ compact) and chasing the matrix Gramian inequality.

## Risk

- 🟢 Schur complement bound (glue).
- 🟡 Spectral mapping (depends on mathlib lemma's exact form).
- 🔴 Gramian divergence (custom proof, likely the bulk of the sprint).

## Open questions

- Confirm mathlib lemma name for "PSD block matrix's Schur complement is
  PSD when bottom-right is PD".
- `Matrix.lambdaMin` — does mathlib expose this? If not, phrase the
  conclusion via "for every unit `v`, `v' G_q v → ∞`".
- Does the Gramian step need `[NormedAddCommGroup]` and/or `[CompleteSpace]`
  on `Fin n → ℂ`? Both auto-derive but call them out so the variable block
  stays clean.

# 8 — Detectability + Stabilizability

## Context

Define the textbook stability concepts that gate everything downstream.
**Critical-path sprint**: every later sprint outside Phase A's tail
depends on it.

`Detectability(A, C)` says "the unobservable subspace is `A`-stable":
states you can't observe must decay anyway. Equivalently (via Hautus),
"every eigenvalue of `A` corresponding to an unobservable mode has
`|λ| < 1`". Stabilizability is dual: every uncontrollable mode is stable.

This is mostly from-scratch (mathlib has nothing here), but reuses the
existing observability/Hautus + new Schur stability.

## Files to create or modify

Create:
- `LeanForControl/LinearSystems/Detectability.lean`
- `LeanForControl/LinearSystems/Stabilizability.lean`

Modify:
- `LeanForControl.lean` (add the two imports as each compiles).
- `blueprint/src/content.tex` (append two subsections).

## Sketch

### Step 1 — Detectability

```
def IsDetectable (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) : Prop :=
  ∀ v ∈ unobservableSubspace A C, Filter.Tendsto (fun k => A^k *ᵥ v) Filter.atTop (𝓝 0)
```

(or equivalently: the restriction of `A` to `unobservableSubspace` is Schur).

### Step 2 — Hautus characterization of detectability

```
theorem isDetectable_iff_hautus
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    IsDetectable A C
      ↔ ∀ μ : ℂ, 1 ≤ ‖μ‖ → LinearMap.ker (hautusObservabilityMatrix A C μ).mulVecLin = ⊥
```

i.e. the Hautus test only needs to hold for unstable `μ` (`|μ| ≥ 1`). This
is the working form for dp-infhor's `lem:zero-output`.

### Step 3 — Stabilizability (dually)

```
def IsStabilizable (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) : Prop :=
  IsDetectable Aᵀ Bᵀ
```

(or define directly via the unstable-uncontrollable subspace, then prove the
duality bridge).

### Step 4 — Connection to dp-infhor's `unstable-uncontrollable subspace`

dp-infhor's C2 condition reads "ker(Σ₀) ∩ unstable-uncontrollable subspace
of `(A, G)` is trivial". This is a finite-dim subspace condition. Define it
and bridge to stabilizability.

## Risk

🔴 from-scratch but the building blocks are now in place.

## Open questions

- Phrasing as `Filter.Tendsto` vs `IsSchur (A.restrict unobservable)`: the
  latter needs `LinearMap.restrict`'s well-definedness lemma over `ℂ`. Pick
  whichever is cleanest for downstream consumers in sprints 14, 19.
- Does mathlib expose "restriction of A to A-invariant subspace is the
  same as the natural endomorphism"? Used in the eigenvector argument
  (sprint 4) — that pattern works here too.

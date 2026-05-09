# 19 — Finite zero-output test + finite-window coercivity (dp-infhor Lemmas 5–6)

## Context

Three statements at a stretch:

- **Lemma 5 (`zero-output`)**: under detectability, `m ≥ n` zero outputs
  starting from `e(0)` force `e_2(0) = 0`. Uses Cayley–Hamilton + sprint
  6's `fact:no-decay` + sprint 8's detectability.
- **Corollary (`window-coercive`)**: for `m ≥ n`, the finite-window LQR cost
  `J̃_m(z)` is a coercive quadratic in the unstable initial state `z`,
  `J̃_m(z) = ½ zᵀ W_m z` with `W_m ≻ 0`.
- **Lemma 6 (`S-coercive`)**: `λ_min(S_T) → ∞` and
  `λ_min(Σ_2⁻¹ + S_T) → ∞`. Uses the corollary plus sprint 7's Gramian
  divergence (`fact:gramian`).

## Files to create or modify

Create:
- `LeanForControl/Estimation/Coercivity.lean` — all three statements.

## Sketch

1. **Lemma 5** unfolds: `Ce_0 = CAe_0 = ⋯ = CA^{n-1}e_0 = 0` ⇒ `e_0 ∈
   unobservableSubspace`. By detectability, `A^k e_0 → 0`. The bottom block
   `e_2(k) = A_2^k e_2(0)` therefore tends to zero. Since every eigenvalue
   of `A_2` has `|λ| ≥ 1`, sprint 6's no-decay forces `e_2(0) = 0`.
2. **Corollary**: `J̃_m` is a least-squares value, hence quadratic in `z`
   with PSD coefficient `W_m`. If `J̃_m(z) = 0`, the optimum has zero cost
   ⇒ `ω(k) = ν(k) = 0` for all `k` ⇒ apply Lemma 5 ⇒ `z = 0`. So `W_m ≻ 0`.
3. **Lemma 6**: split the horizon into windows of length `m`, lower-bound
   each window's cost by `J̃_m(A_2^{jm} z)`, sum to get
   `S_T ≽ α ∑_{j<q} (A_2^{jm})ᵀ A_2^{jm}`, apply sprint 7's Gramian
   divergence.

## Risk

🟡 — heavy reuse of Phase A. The hardest piece is the windowed-cost lower
bound (induction on horizon-window decomposition). Once Lemma 5 lands the
rest is mechanical.

# 13 — Finite-horizon LQR value function

## Context

With Riccati recursion and PSD invariants in hand (sprint 12), prove that
`V_T(x_0) = ½ x_0ᵀ P_T x_0` is the optimal finite-horizon LQR cost. The
proof is the standard Bellman-equation completion of squares.

## Files to create or modify

Create:
- `LeanForControl/LQR/FiniteHorizon.lean` — `V_T`, the value-function
  identity, and the optimal feedback `u^*_k = K_{k+1|T} x_k`.

## Sketch

1. Define `V_T : LQRData → ℕ → (Fin n → ℝ) → ℝ` via the inf over input
   sequences. (Or define inductively.)
2. Bellman recursion: `V_{T-k}(x) = ½ xᵀ Q x + min_u (½ uᵀ R u + V_{T-k-1}(Ax + Bu))`.
3. Inductive proof: assuming `V_{T-k-1}(y) = ½ yᵀ P_{k+1|T} y`, expand and
   complete the square in `u`. Optimal `u* = −K_{k+1|T} x` and the residual
   matches `½ xᵀ P_{k|T} x` by the Riccati recursion.

## Risk

🔴 from scratch but the structure is well-known.

## Open questions

- Phrasing the inf over input sequences in Lean: define `V_T` as the
  Bellman recursion directly (so the value-function identity is essentially
  the recursion definition), then separately prove that this matches the
  inf-over-sequences. This avoids upfront optimization machinery.

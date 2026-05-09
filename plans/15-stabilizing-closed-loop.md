# 15 — Stabilizing closed-loop (completing `fact:lqr`)

## Context

Sprint 14 produced `P_T → P` solving DARE. Now show:
- `K = (R + BᵀPB)⁻¹ BᵀPA` makes `A − BK` Schur (the closed-loop is stable).
- `P` is the *unique* stabilizing solution of DARE.

This completes dp-infhor's `fact:lqr` and unlocks sprint 16.

## Files to create or modify

Modify:
- `LeanForControl/LQR/InfiniteHorizon.lean` (extend with stabilizing K).

## Sketch

1. Closed-loop algebra: `A − BK = A − B(R + BᵀPB)⁻¹ BᵀPA`. Substitute into
   DARE to get a Lyapunov equation `(A − BK)ᵀ P (A − BK) − P = − Q − KᵀRK`.
2. The right side is `≼ 0`. By Lyapunov's theorem (`Q + KᵀRK ≽ 0` ⇒ `A −
   BK` Schur, given `P ≻ 0` on detectable modes), conclude `A − BK` Schur.
3. Uniqueness: another stabilizing solution `P'` would imply `P = P'` via
   Lyapunov stability comparison.

## Risk

🔴 from scratch, but the algebraic identities are standard.

## Open questions

- Need a Lyapunov-equation theorem: `(A − BK)ᵀ X (A − BK) − X = − Y` with
  `Y ≽ 0` and `(A − BK, Y^{1/2})` detectable ⇒ `A − BK` Schur. Likely needs
  Phase A's `IsSchur` + induction. Possibly extract as a `Stability.lean`
  lemma during this sprint.

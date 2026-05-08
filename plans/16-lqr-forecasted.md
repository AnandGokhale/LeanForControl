# 16 — LQR with forecasted disturbance (dp-infhor Lemma 2)

## Context

Generalize the LQR value function to handle a forecasted disturbance
`z(j) = A_2^{j-k} z_0` entering through `A_{12}` and `C_2`. The value
function gains two extra terms: a cross-term `Y_{k|T}` and a `z`-only term
`S_{k|T}`. Recursions for `(P, Y, S)` are dp-infhor:eq:P-rec / Y-rec / S-rec.

This is the cleanest "data-only" extension of finite-horizon LQR. No
new convergence theory.

## Files to create or modify

Create:
- `LeanForControl/LQR/Forecasted.lean` — forecast-augmented LQR, the
  `(P, Y, S)` recursions, and the `J_{k|T}` quadratic decomposition.

## Sketch

1. Augmented data: include `A_{12}, A_2, C_2`, output map `ν = C_1 e_1 +
   C_2 z`, and an autonomous `z⁺ = A_2 z` rolled in.
2. Bellman recursion: same shape as sprint 13 but with the cross-term
   `Y` and the `z`-only term `S`. Three coupled recursions.
3. Quadratic decomposition: `J_{k|T}(e_1(0), z_0) = ½ e_1ᵀ P e_1 + e_1ᵀ Y z_0
   + ½ z_0ᵀ S z_0` — sprint 12's PSD invariants generalize.
4. Convergence (only what dp-infhor's `lem:Pconv` cites): `P_T → P` from
   sprint 14; `Y_T, S_T` are *not* claimed to converge here — that's the
   job of sprint 17 / 19 / 20 / 21.

## Risk

🔴 from scratch but mostly mechanical extension of sprint 13.

## Open questions

- Whether to bundle `(P, Y, S)` as a single record or separately. Bundle
  is cleaner for sprint 18.

# 18 — Reduced quadratic form (dp-infhor Lemma 3)

## Context

After substitution from sprints 11 (block-diagonal covariance) and 16
(forecasted LQR), the estimator value function reduces to a quadratic in
`x_T = (η, e_2(0|T))`:

  `V̂_T(x_T) = ½ x_Tᵀ H_T x_T − h_Tᵀ x_T + κ_T`

with explicit `H_T`, `h_T`, `κ_T` (dp-infhor:eq:HT). The crucial property
is `H_T ≻ 0`, which gives a unique minimizer.

## Files to create or modify

Create:
- `LeanForControl/Estimation/ReducedForm.lean` — the reduced quadratic
  form, the explicit `H_T, h_T, κ_T` formulas, and `H_T ≻ 0`.

## Sketch

1. Substitute `e_1(0|T) = a_1 + Z_1 η` (using the spectral decomposition of
   `Σ̃_1` from sprint 9) into the cost from sprint 17.
2. Apply the forecasted-LQR value function (sprint 16) to eliminate
   `ω(0|T), …, ω(T-1|T)`.
3. Collect quadratic / linear / constant terms in `x_T = (η, e_2(0|T))`.
4. PD of `H_T`: dp-infhor's argument uses `Λ_1⁻¹ ≻ 0` and `Σ_2⁻¹ ≻ 0` plus
   PSD of the LQR-block matrix `[[P_T, Y_T], [Y_Tᵀ, S_T]]` (which we have
   from sprint 16).

## Risk

🟡 — collecting quadratic terms is mechanical with mathlib's `PosDef`
machinery, but careful index bookkeeping is needed.

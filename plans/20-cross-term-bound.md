# 20 — Cross-term bound (dp-infhor Lemma 7)

## Context

dp-infhor's bridge from "S coercive" to "Y bounded": the PSD block matrix
`[[P_T, Y_T], [Y_Tᵀ, S_T + Σ_2⁻¹]]` is `≽ 0`, so by Schur complement,
`P_T − Y_T M_T⁻¹ Y_Tᵀ ≽ 0` where `M_T = Σ_2⁻¹ + S_T`. Combined with
`λ_min(M_T) → ∞` (sprint 19), this gives `M_T⁻¹ Y_Tᵀ → 0` and similar
limits, plus `H_T`'s Schur complement is uniformly bounded below by
`Λ_1⁻¹ ≻ 0`.

## Files to create or modify

Modify:
- `LeanForControl/Estimation/Coercivity.lean` (or split into a separate
  `CrossTermBound.lean`).

## Sketch

1. Use sprint 7's Schur-complement bound on `[[P_T, Y_T], [Y_Tᵀ, M_T]]
   ≽ 0` with `M_T ≻ 0`.
2. Operator-norm chase: `‖M_T^{−1/2} Y_Tᵀ‖² = ‖Y_T M_T⁻¹ Y_Tᵀ‖ ≤ ‖P_T‖`.
   Sprint 14 gives `P_T → P` so `‖P_T‖` is uniformly bounded; sprint 19
   gives `λ_min(M_T) → ∞` so `‖M_T⁻¹‖ → 0`. Combine to get the limits in
   dp-infhor:eq:M-limits.
3. Schur complement of `H_T`: `Λ_1⁻¹ + Z_1ᵀ(P_T − Y_T M_T⁻¹ Y_Tᵀ)Z_1 ≽ Λ_1⁻¹
   ≻ 0`.

## Risk

🟢 — once Phase A's Schur complement is in place (sprint 7), this is
mostly mechanical.

# 21 — Infinite-horizon limit (dp-infhor Proposition `infhor-limit`)

## Context

The headfake's punch line. With everything from sprints 5–20 in place,
prove dp-infhor's main proposition:

  `η_T^* → η_∞ ≜ −(Λ_1⁻¹ + Z_1ᵀ P Z_1)⁻¹ Z_1ᵀ P a_1`,
  `e_2(0|T)^* → 0`,
  `V̂_T(η_T^*, e_2(0|T)^*) → V_∞^0`.

## Files to create or modify

Create:
- `LeanForControl/Estimation/InfiniteHorizon.lean` — the proposition and
  its proof.

## Sketch

dp-infhor's proof is direct given the prior infrastructure:

1. Minimize the reduced quadratic in `z = e_2(0|T)` to get `z_T(η)` (eq:zT-eta).
2. Substitute back to get `V̄_T(η)`, a quadratic in `η`.
3. Sprint 14: `P_T → P`. Sprint 20: `Y_T M_T⁻¹ Y_Tᵀ → 0` and
   `Y_T M_T⁻¹ Σ_2⁻¹ a_2 → 0`. Hence `V̄_T → V̄_∞` coefficientwise, where
   `V̄_∞(η) = ½ ηᵀ Λ_1⁻¹ η + ½ (a_1 + Z_1 η)ᵀ P (a_1 + Z_1 η)`.
4. Sprint 18's `H_T ≻ 0` plus convergence of the Hessian to `Λ_1⁻¹ + Z_1ᵀ P
   Z_1 ≻ 0` gives `η_T^* → η_∞`.
5. `e_2(0|T)^* = z_T(η_T^*) → 0` from the explicit formula and sprint 20's
   limits.
6. Value function: complete the square in `z` at `z = e_2(0|T)^*` (or just
   substitute and pass to the limit).

## Risk

🟡 — the algebra is mostly assembling prior results. The continuity
arguments need to be tight (matrix inversion is continuous on PD matrices,
which mathlib has).

## Open questions

- After sprint 21 lands, the master plan's Phase E begins. Revisit and
  pick the next Hespanha milestone.

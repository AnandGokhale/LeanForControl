# 17 — Estimation problem setup

## Context

Define the discrete-time estimator's optimization problem `P_T` (dp-infhor
§"Error system"), the error system `e⁺ = Ae − Gω, ν = Ce`, and the support
condition `M_2ᵀ(e(0) − a) = 0`. **Cite, don't re-prove**, the Kalman ↔
optimization equivalence (`lem:semiPT`); a full proof would derail.

## Files to create or modify

Create:
- `LeanForControl/Estimation/Basic.lean` — problem `P_T`, error system,
  support condition, and a `axiom`-style admit / `Lemma` placeholder for
  `lem:semiPT` if we want to keep `lake build` green without proving it
  yet. (Per CLAUDE.md, no `axiom`. Alternative: prove a one-direction
  bridge that's enough for downstream work without claiming full
  equivalence.)

Wait — CLAUDE.md is firm: no `sorry`/`admit`/`axiom`. So we either prove
`lem:semiPT` properly, or scope it out and downstream sprints work with
the optimization formulation directly without reference to a Kalman
filter. **Decision when active**: skip `lem:semiPT` entirely. Define
`P_T` as the optimization problem (it's well-defined on its own), do the
estimator analysis on it, and let "this is the Kalman filter" be a
side comment in the blueprint, not a Lean theorem.

## Sketch

1. `LQEstData (n p m : ℕ) := { A : ..., C : ..., G : ..., Σ_0 : ...,
   ox_0 : ..., x_0 : ... }` etc.
2. Cost `V_T : LQEstData → measurements → ((Fin n → ℝ) → ℝ)` defined as
   the optimization in dp-infhor:lem:semiPT.
3. Error system: derived dynamics + cost in error coordinates.
4. Support condition `M_2ᵀ(e(0) − a) = 0` as a `Submodule` predicate.

## Risk

🟡 — definitions are mechanical, but the support condition's interaction
with PSD and pseudoinverse needs Phase A sprint 9 in place.

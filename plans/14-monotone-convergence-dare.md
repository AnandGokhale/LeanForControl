# 14 — Riccati monotone convergence + DARE existence

## Context

The riskiest single sprint. Show `P_T → P` for some `P`, and `P` solves the
Discrete Algebraic Riccati Equation
`P = Q + AᵀPA − AᵀPB(R + BᵀPB)⁻¹BᵀPA` (dp-infhor:eq:are).

Proof outline (classical): under stabilizability + detectability,
- `P_T` is monotone non-decreasing in `T` (longer horizon ≥ shorter horizon
  cost).
- `P_T` is bounded above (use a stabilizing feedback as a feasible policy
  to get a uniform cost bound).
- Monotone bounded sequence in PSD matrices converges.
- The limit `P` solves the DARE by passing to the limit in the recursion.

## Files to create or modify

Create:
- `LeanForControl/LQR/InfiniteHorizon.lean` — DARE statement, monotone
  convergence, existence of `P`.

## Sketch

1. **Monotonicity**: `P_T ≼ P_{T+1}` for every `T` (with `P_T = P_{0|T}`).
   Proof: `V_T(x) ≤ V_{T+1}(x)` by feasibility (extend the optimal length-`T`
   plan with `u = 0` for one more step). Translate to PSD ordering on
   `P_T`.
2. **Upper bound**: `(A_1, B_1)` stabilizable ⇒ exists `K_0` with
   `A − BK_0` Schur. Use the static feedback `u_k = −K_0 x_k` as a
   feasible policy; its cost is bounded above (Lyapunov). So `V_T(x) ≤
   ½ xᵀ P_∞ x` for some PSD `P_∞`, uniformly in `T`. Hence `P_T ≼ P_∞`.
3. **Convergence**: monotone bounded PSD sequence converges (componentwise
   in the matrix entries; PSD ordering implies entrywise bounds).
4. **Limit solves DARE**: pass to the limit in the Riccati recursion.
   `Continuous` of the matrix operations does the work.

## Risk

🔴 highest-risk sprint of the roadmap. May need to split into two:

- 14a: monotonicity + upper bound (algebraic).
- 14b: convergence + DARE solution (analysis).

## Open questions

- mathlib's monotone convergence for matrix sequences: does
  `Mathlib/Analysis/Matrix/Order` have what we need? Explore flagged this
  as 30%-mathlib. Worst case, prove via componentwise convergence in `ℝ`.
- Can we postpone "P is the *unique stabilizing* solution" to sprint 15?
  Yes — sprint 14 just needs convergence.

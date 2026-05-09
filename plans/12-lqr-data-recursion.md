# 12 — LQR data + Riccati recursion shape

## Context

First sprint of the LQR phase. Set up the data: the LQR problem, the
Riccati recursion `P_{k|T}`, and the structural invariants (`P` symmetric,
PSD, recursion well-defined assuming `R ≻ 0`). No convergence yet — just
algebra.

mathlib has nothing here, so this is the foundation for sprints 13–16.

## Files to create or modify

Create:
- `LeanForControl/LQR/Basic.lean` — LQR data, Riccati recursion definition,
  basic invariants.

## Sketch

1. Bundle the LQR data into a `structure`:
   `LQRData (n m : ℕ) := { A : Matrix (Fin n) (Fin n) ℝ, B : Matrix (Fin n) (Fin m) ℝ,
     Q : Matrix (Fin n) (Fin n) ℝ, R : Matrix (Fin m) (Fin m) ℝ,
     hQ : Q.PosSemidef, hR : R.PosDef }`.
2. Recursion: `P_{k|T}` indexed `Fin (T+1)`, with `P_{T|T} = 0` and the
   backward recursion
     `P_{k|T} = Q + AᵀP_{k+1|T}A − AᵀP_{k+1|T}B(R + BᵀP_{k+1|T}B)⁻¹BᵀP_{k+1|T}A`.
   Define as a function `lqrRiccati : LQRData → ℕ → Matrix _ _`.
3. Invariant: `P_{k|T}` is symmetric and PSD for every `k`. Symmetry from
   transpose-friendly pieces, PSD by induction (each step's correction
   term is `−Bᵀ ... B`-shaped and the residual is the optimal cost).
4. Welldefinedness: `R + BᵀPB ≻ 0` (from `R ≻ 0` and `BᵀPB` PSD), so the
   inverse in the recursion is fine.

## Risk

🔴 from scratch. But the algebraic checks are local.

## Open questions

- Real vs complex scalars: dp-infhor is real (Q, R real). Stay over `ℝ` for
  LQR; the spectrum lives in `ℂ` only via `algebraMap ℝ ℂ`. For the
  closed-loop spectrum check, lift to `ℂ` lazily.
- Use `Matrix` over `Fin n` directly, or factor through `Module.End`? The
  former matches the rest of the project; stick with it.

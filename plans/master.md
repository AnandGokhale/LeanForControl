# Master plan: Lean formalization, headfaked through `dp-infhor.tex`

## Vision

Long-term: formalize the linear-systems / control core of **Hespanha's
textbook** in Lean 4 + mathlib.

Driving headfake: prove the results in `webmd/dp-infhor.tex` (Rawlings, Quah,
Müller — *Recursion proof of the infinite-horizon problem*). The paper proves
that the discrete-time Kalman filter, recast as an optimization, has a
well-defined infinite-horizon limit under detectability and a non-degeneracy
condition on the initial covariance. That proof requires linear algebra
plumbing, stability theory, decomposition theorems, and the full LQR
machinery — all of which are exactly the prerequisites we want for Hespanha
anyway. Nothing in the headfake is throwaway.

## Repo state at start of this roadmap

Already shipped (sprints 0–4):

- `LeanForControl/LinearSystems/{Basic,MatrixLemmas,Observability,Controllability,Hautus,Scratch}.lean`.
- Definitions: `observabilityMatrix`, `IsObservable`, `controllabilityMatrix`,
  `IsControllable`, `unobservableSubspace`, `hautusObservabilityMatrix`.
- Theorems: kernel-form observability milestone, rank-form characterizations
  (observability + controllability), full observability Hautus iff over `ℂ`.
- `MatrixLemmas`: kernel↔rank bridges over `[Field 𝕜]`.
- Reporting infra: `LeanArchitect` + `leanblueprint` wired, `notes/N-*.md`
  handoff, `exports/N-*.zip` per-sprint snapshots, end-of-session recipe in
  `CLAUDE.md`.

See `notes/0-…md` through `notes/4-…md` for what was learned in each sprint.

## Target code organization

```
LeanForControl/
├── Basic.lean, DiniCalculus.lean
├── Dini/, ODEs/, Lyapunov/                  ← untouched legacy
├── LinearSystems/
│   ├── Basic.lean                            ← existing conventions
│   ├── MatrixLemmas.lean                     ← extend (Schur cmplmnt, Gramian, spectral mapping)
│   ├── Observability.lean, Controllability.lean
│   ├── Hautus.lean                           ← extend with controllability side
│   ├── Stability.lean                        ← Schur matrices, A^k → 0, no-decay
│   ├── Detectability.lean                    ← Hautus characterization, ker-stability bridge
│   ├── Stabilizability.lean                  ← dual
│   ├── Decomposition.lean                    ← stabilizability canonical form (Kalman split)
│   └── Scratch.lean
├── LQR/
│   ├── Basic.lean                            ← Riccati recursion data + value-function shape
│   ├── FiniteHorizon.lean                    ← `P_{k|T}`, quadratic value function
│   ├── InfiniteHorizon.lean                  ← `P_T → P`, ARE, stabilizing solution
│   └── Forecasted.lean                       ← LQR with forecasted disturbance (dp-infhor Lemma 2)
└── Estimation/
    ├── Basic.lean                            ← problem `P_T`, error system, support condition
    ├── Decomposition.lean                    ← Θ transform, block-diagonalize covariance
    ├── ReducedForm.lean                      ← Lemma 3: H_T, h_T, κ_T
    ├── Coercivity.lean                       ← Lemma 5 + Cor + Lemma 6 + Lemma 7
    └── InfiniteHorizon.lean                  ← Prop `infhor-limit` (the headfake's payoff)
```

Each new top-level directory (`LQR/`, `Estimation/`) ships in the sprint that
introduces it. The split keeps `LinearSystems/` focused on the algebra; LQR
and the estimator are separable layers on top.

## mathlib gap analysis (refined sprint sizing)

Verified by exploration of mathlib v4.30.0-rc2:

**Mostly mathlib glue (≤ 1 sprint each):**

- Schur complement of PSD block matrices —
  `Mathlib/LinearAlgebra/Matrix/SchurComplement.lean` + `PosDef.lean`.
- Block-matrix manipulations and Cayley–Hamilton (already used in sprint 4).
- Quadratic forms / PSD ordering — `PosSemidef`, `PosDef`, addition, smul.
- Schur stability — wraps existing `Matrix` spectrum machinery.

**From-scratch / load-bearing (multi-sprint):**

- Detectability / stabilizability — nothing in mathlib.
- Discrete-time LQR / DARE — nothing in mathlib.
- SVD / Moore–Penrose generic — nothing for general matrices, but the
  *spectral decomposition for Hermitian / symmetric PSD* is in mathlib and
  is what `dp-infhor` actually needs (the "SVD"s in the paper are spectral
  decompositions of PSD covariances, not full SVDs).
- Gramian divergence (`fact:gramian`) — needs a custom limit argument.
- Monotone convergence of PSD matrices (`P_T → P`) — partial in mathlib;
  may need assembling.

This shifts sprint sizing: LQR (Phase C) is the biggest from-scratch chunk
and needs ~5 sprints. Spectral decomposition / pseudoinverse-on-PSD gets
its own sprint between Phase A and Phase B.

## Phases and sprint list

Status legend: ✓ shipped · ▶ active · · planned · ✗ blocked.
Risk legend: 🟢 mostly mathlib glue · 🟡 part glue, part new · 🔴 mostly from scratch.

### Phase A — Stability foundations (sprints 5–9)

| # | Title | Deliverable | Risk | Status |
|---|---|---|---|---|
| 5 | Controllability Hautus | Mirror sprint 4 via duality (`IsControllable A B ↔ IsObservable Aᵀ Bᵀ`). | 🟢 | · |
| 6 | Schur stability | `IsSchur A`; `A^k → 0` bridge; `fact:no-decay` (eigenvalues `\|λ\| ≥ 1` ⇒ no decay). | 🟢 | · |
| 7 | Schur complement + Gramian divergence | PSD-Schur bound (`fact:schur`), spectral mapping for matrix powers, Gramian sum divergence (`fact:gramian`). Schur is glue; Gramian is custom. | 🟡 | · |
| 8 | Detectability + Stabilizability | Definitions + Hautus characterizations. Bridges to `unobservableSubspace` / its dual. | 🔴 | · |
| 9 | Spectral decomposition for PSD + pseudoinverse | `Σ = U Λ Uᵀ`, `Σ†` for PSD `Σ`. Stay narrow — only what dp-infhor uses. | 🟡 | · |

### Phase B — Decomposition (sprints 10–11)

| # | Title | Deliverable | Risk | Status |
|---|---|---|---|---|
| 10 | Stabilizability canonical form | Kalman-style block split: `(A, G) → (A_1, A_{12}, 0, A_2; G_1, 0)` with `(A_1, G_1)` stabilizable and `A_2` totally unstable. | 🔴 | · |
| 11 | Block-diagonalize initial covariance | Θ transformation, structural decomposition (`tildeSigma` from dp-infhor §"Block-diagonalization"). | 🟡 | · |

### Phase C — LQR (sprints 12–16)

LQR is the biggest from-scratch chunk: 5 sprints, not 3.

| # | Title | Deliverable | Risk | Status |
|---|---|---|---|---|
| 12 | LQR data + Riccati recursion shape | `LQR/Basic.lean`: data structures + invariants (`P_{k\|T}` symmetric PSD, recursion well-defined). No convergence yet. | 🔴 | · |
| 13 | Finite-horizon value function | `LQR/FiniteHorizon.lean`: `V_T(x) = ½ x' P_T x` from the Bellman recursion. | 🔴 | · |
| 14 | Monotone convergence + DARE existence | `P_T` monotone, bounded above ⇒ `P_T → P`, `P` solves DARE. The riskiest single sprint. | 🔴 | · |
| 15 | Stabilizing closed-loop | `K = (R + B' P B)⁻¹ B' P A` makes `A − B K` Schur. Completes `fact:lqr` from dp-infhor. | 🔴 | · |
| 16 | LQR with forecasted disturbance | `LQR/Forecasted.lean`: dp-infhor Lemma 2 — `(P, Y, S)` recursion + quadratic value function. | 🔴 | · |

### Phase D — Estimator (sprints 17–21)

| # | Title | Deliverable | Risk | Status |
|---|---|---|---|---|
| 17 | Estimation setup | `Estimation/Basic.lean`: problem `P_T`, error system, support condition. Cite (don't re-prove) `lem:semiPT`. | 🟡 | · |
| 18 | Reduced quadratic form | dp-infhor Lemma 3 — `H_T`, `h_T`, `κ_T`, `H_T ≻ 0`. | 🟡 | · |
| 19 | Finite zero-output + coercivity | dp-infhor Lemma 5 + Corollary + Lemma 6 — `S_T` grows coercively. | 🟡 | · |
| 20 | Cross-term bound | dp-infhor Lemma 7 — `P_T − Y_T M_T⁻¹ Y_Tᵀ ≽ 0` and limit corollaries. | 🟢 | · |
| 21 | Infinite-horizon limit | dp-infhor Proposition `infhor-limit` — the headfake's punch line. | 🟡 | · |

### Phase E — Continuing toward Hespanha

After sprint 21 we revisit this master plan and pick up the remaining
Hespanha material: continuous-time analogues, more general
optimization-as-estimator results, separation principle, etc. Out of scope
for the headfake itself.

## Critical-path notes

- **Sprint 8 (detectability) is on the critical path**: every sprint after
  Phase A except sprint 9 depends on it.
- **Sprint 14 (Riccati monotone convergence) is the riskiest single sprint**.
  May need to split if monotone convergence of PSD matrices isn't available
  cleanly in mathlib's analysis layer.
- **Gramian divergence (sprint 7)** is a custom limit argument; budget for
  the whole sprint even though Schur complement is glue.
- **SVD/pseudoinverse (sprint 9)**: stay narrow — only what's needed for PSD
  covariance manipulation. Don't reformalize Moore–Penrose generically.

## Sprint sizing

A sprint = one session = roughly 5–10 atomic steps (the rhythm of sprints 3
and 4). When a sprint's mathlib-vs-from-scratch ratio looks unfavorable, split
it. When two sprints share an awkward proof boundary, merge them. Update this
master plan and the affected sprint plan files when that happens.

## Conventions (recap from `CLAUDE.md`)

- No `sorry`/`admit`/`axiom`. `lake build` green is the only "done".
- `notes/N-slug.md` for end-of-sprint handoff (backward-looking).
- `plans/N-slug.md` for the next sprint's design (forward-looking; this directory).
- `plans/master.md` (this file) is the index. Update whenever the roadmap
  changes — adding sprints, splitting them, swapping order.
- Field/scalar typeclasses: stay as weak as the proof allows. Use the
  close-and-reopen-namespace trick (sprint 3) when an outer `[Semiring 𝕜]`
  collides with an inner `[Field 𝕜]`.
- One commit per sprint, named-paths staging, gitignore updated before
  staging. Per-sprint zip dropped in `exports/N-slug.zip` (gitignored).

## Living-document rule

This file and `plans/N-*.md` are revised as we learn. Any sprint that turns
up a missing infrastructure piece must update both:

1. the master plan (insert a new sprint, reorder, or extend an existing one),
2. the sprint plan that's currently active (so the next session has the
   refined target).

Don't pretend the original plan was right if the sprint turned out
differently. Honest revision keeps the handoff to future agents reliable.

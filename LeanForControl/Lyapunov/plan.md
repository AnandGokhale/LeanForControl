# Plan: Khalil Chapter 4 — Lyapunov Stability

## Status

| Theorem | Lean name | File | Status |
|---|---|---|---|
| 4.1 Part 1 — Lyapunov stability | `lyapunov_stable` | `Autonomous.lean` | ✅ done |
| 4.1 Part 2/3 — GAS via strict Lyapunov | `lyapunov_asymptotic_stable` | `Autonomous.lean` | ✅ done |
| 4.2 — GAS via radially unbounded V | `lyapunov_global_asymptotic_stable` | `Autonomous.lean` | ✅ done |
| 4.3 — Chetaev instability | — | — | planned |
| 4.4 — LaSalle's invariance principle | — | — | planned |
| 4.5 — LaSalle corollary (GAS) | — | — | planned |
| 4.6 — Linearization (indirect method) | — | — | planned |

Files:
- `Lyapunov/Defs.lean` — definitions, fully populated
- `Lyapunov/Autonomous.lean` — Thm 4.1/4.2 fully proved

Infrastructure already in place:
- `hasDerivAt_V_comp_traj` (chain rule)
- `V_nonincreasing`, `V_le_initial`, `V_nonneg`
- `V_tendsto_limit` (via `tendsto_atTop_ciInf`)
- `V_limit_zero` (EVT on compact sublevel set + antitone bound)
- `isCompact_sublevel_set` (via `comap_norm_atTop`)
- `sphere_nonempty`, `trajectory_continuous`

---

## Next: Theorem 4.3 — Chetaev's Instability Theorem

### Statement

Let x_eq be an equilibrium. Suppose there exists a C¹ function V : D → ℝ and an open
set D₁ ⊂ D with x_eq ∈ ∂D₁ ∩ D such that:
- V(x) > 0 and V̇(x) > 0 for all x ∈ D₁
- V(x) = 0 for all x ∈ ∂D₁ ∩ D

Then x_eq is **unstable** (i.e., ¬ LyapunovStable f x_eq).

### Required definitions (new in `Defs.lean`)

```lean
-- IsChetaevFunction: all the hypotheses of Chetaev's theorem packaged together
structure IsChetaevFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) (D₁ : Set ℝⁿ) : Prop where
  hV_c1        : ContDiff ℝ 1 V
  hD₁_open     : IsOpen D₁
  hx_eq_bdry   : x_eq ∈ frontier D₁   -- x_eq ∈ ∂D₁ = closure D₁ \ interior D₁
  hV_pos       : ∀ x ∈ D₁, 0 < V x
  hLie_pos     : ∀ x ∈ D₁, 0 < fderiv ℝ V x (f x)
  hV_zero_bdry : ∀ x ∈ frontier D₁, V x = 0
```

### Target theorem

```lean
theorem chetaev_unstable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} {D₁ : Set ℝⁿ}
    (hV : IsChetaevFunction f V x_eq D₁) :
    ¬ LyapunovStable f x_eq
```

### Proof strategy

Unfold instability: find ε > 0 such that for every δ > 0 there exists a trajectory
starting in Bδ(x_eq) that eventually leaves Bε(x_eq).

Key argument:
1. Fix ε > 0 small enough that Bε(x_eq) ⊂ D (the domain).
2. Since x_eq ∈ ∂D₁, every ball Bδ(x_eq) intersects D₁. Pick x₀ ∈ Bδ(x_eq) ∩ D₁.
3. Let φ be the trajectory through x₀. Since V̇ > 0 in D₁, V(φ(t)) is strictly increasing
   while φ(t) ∈ D₁.
4. V(φ(t)) > V(φ(0)) > 0 for all t > 0 with φ(t) ∈ D₁, so φ cannot re-enter {V ≤ 0}
   which forces φ to stay in D₁ ∩ Bε(x_eq) or exit through ∂Bε(x_eq).
5. If φ stays in D₁ ∩ Bε(x_eq) forever, V(φ(t)) is strictly increasing and bounded above
   (by compactness), so V(φ(t)) → L > 0. But then φ is eventually in the compact set
   {x ∈ D₁ | V(x) ≥ V(x₀)/2} ∩ Bε(x_eq), so V̇ ≥ γ > 0 there (EVT), giving
   V(φ(t)) → ∞, contradiction.
6. So φ must exit Bε(x_eq). This shows instability.

Key Lean lemmas needed:
- `frontier_mem_nhds` or similar to find points of D₁ near x_eq
- `V_strictly_increasing` (mirror of `V_nonincreasing`): V̇ > 0 on D₁ → V ∘ φ strictly increasing
  while φ ∈ D₁. Lean path: `strictMono_of_deriv_pos` on D₁ time interval.
- EVT on compact subset of D₁: same `IsCompact.exists_isMaxOn` pattern as in `V_limit_zero`

---

## Next: Theorem 4.4 — LaSalle's Invariance Principle

### Statement

Let Ω be a compact set, positively invariant under ẋ = f(x). Let V : Ω → ℝ be C¹ with
V̇(x) ≤ 0 in Ω. Define:
- E = {x ∈ Ω | V̇(x) = 0}
- M = largest invariant subset of E

Then every trajectory starting in Ω satisfies φ(t) → M as t → ∞.

### What this adds over Theorem 4.1/4.2

Theorem 4.1 requires V̇ < 0 strictly. LaSalle only needs V̇ ≤ 0, and concludes
convergence to M (possibly larger than {x_eq}). In particular, if M = {x_eq} (the only
invariant subset of E is the equilibrium itself), then LAS follows even with V̇ only
semidefinite.

### Required definitions (new in `Defs.lean`)

```lean
-- A set S is positively invariant: trajectories starting in S stay in S for t ≥ 0.
def IsPositivelyInvariant (S : Set ℝⁿ) (f : ℝⁿ → ℝⁿ) : Prop :=
  ∀ φ : ℝ → ℝⁿ, IsTrajectory φ f → φ 0 ∈ S → ∀ t ≥ 0, φ t ∈ S

-- ω-limit set of a trajectory φ: accumulation points of {φ(t) : t → ∞}.
noncomputable def omegaLimit (φ : ℝ → ℝⁿ) : Set ℝⁿ :=
  ⋂ T : ℝ, closure {x | ∃ t ≥ T, φ t = x}
```

Note: Mathlib has `omegaLimit` in `Mathlib.Topology.OmegaLimit` for flows. Check whether
that definition can be reused for single trajectories before writing a new one.

### Target theorem

```lean
theorem lasalle_invariance_principle
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} {Ω : Set ℝⁿ}
    (hΩ_compact : IsCompact Ω)
    (hΩ_inv : IsPositivelyInvariant Ω f)
    (hV_c1 : ContDiff ℝ 1 V)
    (hLie_nonpos : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectory φ f) (hφ0 : φ 0 ∈ Ω)
    {M : Set ℝⁿ} (hM_inv : IsPositivelyInvariant M f)
    (hM_largest : M = ⋂ (S : Set ℝⁿ) (_ : IsPositivelyInvariant S f)
                            (_ : S ⊆ {x ∈ Ω | fderiv ℝ V x (f x) = 0}), S) :
    Filter.Tendsto φ Filter.atTop (nhds_set M)
```

(The statement of "largest invariant set in E" may need adjustment — see Open Questions.)

### Proof decomposition

**Lemma L1** `omegaLimit_nonempty`
```
hΩ_compact → hΩ_inv → φ 0 ∈ Ω → (omegaLimit φ).Nonempty
```
Proof: φ(t) ∈ Ω for all t ≥ 0 (positive invariance). The orbit {φ(t) : t ≥ 0} lies in the
compact set Ω. By sequential compactness, there exists a subsequence tₙ → ∞ with φ(tₙ)
convergent. Its limit lies in ω(φ).
Lean path: `IsCompact.isSeqCompact` + `Filter.Tendsto.congr'`.

**Lemma L2** `omegaLimit_subset_Omega`
```
omegaLimit φ ⊆ Ω
```
Proof: Ω is closed (compact ⟹ closed). For y ∈ ω(φ), there exist tₙ → ∞ with φ(tₙ) → y.
Since each φ(tₙ) ∈ Ω (positive invariance) and Ω is closed, y ∈ Ω.

**Lemma L3** `V_const_on_omegaLimit`
```
∀ y ∈ omegaLimit φ, V y = sInf (Set.range (V ∘ φ))
```
Proof: V(φ(t)) is antitone and bounded below (from Thm 4.1 infrastructure), so it converges
to L = sInf (range (V ∘ φ)). For y ∈ ω(φ), pick tₙ → ∞ with φ(tₙ) → y. By continuity of V,
V(y) = lim V(φ(tₙ)) = L.

**Lemma L4** `Lie_zero_on_omegaLimit` [requires ODE uniqueness]
```
∀ y ∈ omegaLimit φ, fderiv ℝ V y (f y) = 0
```
Proof: Let ψ be the trajectory through y (unique by Picard-Lindelöf, which requires a
Lipschitz hypothesis on f). Then V(ψ(t)) is antitone (Lie derivative ≤ 0) and equals L
for all t (since ω(φ) is invariant and V = L on ω(φ) by L3). A monotone constant function
has derivative 0, so Lie derivative = 0 at y.

**Lemma L5** `omegaLimit_subset_M`
```
omegaLimit φ ⊆ M
```
Proof: ω(φ) is a positively invariant set (requires ODE uniqueness) contained in E = {V̇ = 0}
by L4. M is the largest such set, so ω(φ) ⊆ M.

**Assembly**: φ(t) → M because ω(φ) ⊆ M and ω(φ) captures all limit points.

### Open questions / blockers for LaSalle

- **ODE uniqueness**: Lemma L4 requires the trajectory through y ∈ ω(φ) to be unique.
  This needs a Lipschitz hypothesis on f (or local Lipschitz + uniqueness theorem).
  Need to add `hf_lip : LocallyLipschitz f` as a hypothesis, or import from `ODEs/`.

- **"Largest invariant set" in Lean**: Defining M as the largest invariant subset of E
  requires either impredicative set comprehension or working with a specific M given as
  a hypothesis (user provides M and proves it's invariant + contained in E).
  Simpler approach: state the theorem with `M` given and `hM_inv` + `hM_in_E` as hypotheses,
  avoiding the need to construct M.

- **`nhds_set` vs pointwise convergence**: `Filter.Tendsto φ atTop (nhds_set M)` is the
  right notion of "φ(t) converges to M" (distance to M goes to 0). Verify this is in Mathlib.

---

## Next: Theorem 4.5 / Corollary — LaSalle gives GAS

### Statement

Corollary: Under the hypotheses of LaSalle's principle, if M = {x_eq} (the only invariant
subset of E is the equilibrium), then x_eq is globally asymptotically stable on Ω.

This follows immediately from the LaSalle theorem once we know M = {x_eq}, since
convergence to a singleton means convergence to x_eq.

No additional proof infrastructure needed beyond the LaSalle theorem.

---

## Next: Theorem 4.6 — Linearization (Indirect Lyapunov Method)

### Statement

Let f : ℝⁿ → ℝⁿ be C¹ with f(x_eq) = 0. Let A = fderiv ℝ f x_eq (the Jacobian at x_eq).

1. If A is Hurwitz (all eigenvalues have Re < 0), then x_eq is locally asymptotically stable.
2. If A has an eigenvalue with Re > 0, then x_eq is unstable.

### Required infrastructure

This theorem needs substantial external infrastructure:

- **Hurwitz matrices**: `IsHurwitz A ↔ ∀ λ ∈ A.eigenvalues ℂ, λ.re < 0`
  (partially developed in `Lyapunov_old/LinearSystems.lean`)

- **Lyapunov equation for Hurwitz matrices**: If A is Hurwitz, then for any Q ≻ 0 there exists
  a unique P ≻ 0 satisfying PA + AᵀP = -Q. Use Q = I for simplicity.
  (sketched in `Lyapunov_old/LinearSystems.lean`, all sorry)

- **Linearization error bound**: f(x) = Ax + g(x) where ‖g(x)‖/‖x‖ → 0 as x → x_eq.
  Lean path: Taylor's theorem / `HasFDerivAt` remainder bound.

### Proof strategy for Part 1

Given P satisfying PA + AᵀP = -I:
1. Define V(x) = ‖x - x_eq‖²_P = (x - x_eq)ᵀ P (x - x_eq) (quadratic Lyapunov function).
2. V is positive definite (P ≻ 0).
3. V̇ along ẋ = f(x):
   - V̇ = (x - x_eq)ᵀ(PA + AᵀP)(x - x_eq) + 2(x - x_eq)ᵀPg(x)
   - = -(x - x_eq)ᵀ(x - x_eq) + 2(x - x_eq)ᵀPg(x)   (using PA + AᵀP = -I)
   - = -‖x - x_eq‖² + 2(x - x_eq)ᵀPg(x)
4. Since ‖g(x)‖/‖x - x_eq‖ → 0, for small enough ‖x - x_eq‖, the second term is dominated,
   giving V̇ < 0 in a neighborhood of x_eq.
5. Apply `lyapunov_asymptotic_stable` with this V restricted to a sublevel set.

### Priority assessment

Theorem 4.6 is low priority for immediate Lean work because:
- It requires substantial eigenvalue/Hurwitz infrastructure not yet in the library.
- The LinearSystems files have this sketched but all sorry.
- Proving the Lyapunov equation existence (Sylvester-type) is a significant standalone project.

Suggested order: prove Thm 4.3 and Thm 4.4 first, then revisit 4.6.

---

## Recommended execution order

1. **Theorem 4.3 (Chetaev)** — new file `Lyapunov/Instability.lean`.
   Self-contained, mirrors the stability proof structure.
   Difficulty: medium. Estimated effort: 1–2 sessions.

2. **Theorem 4.4 (LaSalle)** — new file `Lyapunov/LaSalle.lean`.
   Requires ω-limit sets + ODE uniqueness hypothesis.
   Difficulty: hard. Add `hf_lip` or `hf_unique` hypothesis to avoid rebuilding Picard.
   Estimated effort: 3–4 sessions.

3. **LaSalle corollary (Theorem 4.5)** — append to `LaSalle.lean`.
   Trivial once LaSalle is done.

4. **Theorem 4.6 (Linearization)** — new file `Lyapunov/Linearization.lean`.
   Blocked on eigenvalue / Lyapunov equation infrastructure.
   Estimated effort: 4+ sessions after unblocking.

---

## Lessons from Theorem 4.1/4.2

- **Pointwise Lie derivative** (`∀ x, fderiv ℝ V x (f x) ≤ 0`) cleaner than trajectory-based
  (`∀ φ t, HasDerivAt (V ∘ φ) ... t`). The chain rule bridge lemma `hasDerivAt_V_comp_traj`
  handles the connection.

- **`hequil : f x_eq = 0`** must be in the Lyapunov function struct to handle the `x_eq`
  case in `strict_implies_semidefinite`. Remember this for future structures.

- **Mathlib lemma names that landed**:
  - `HasFDerivAt.comp_hasDerivAt` — chain rule
  - `antitone_of_deriv_nonpos` — monotone calculus
  - `tendsto_atTop_ciInf` — antitone + bddBelow → convergence
  - `Antitone.le_of_tendsto` — antitone limit lower-bounds values
  - `IsCompact.exists_isMaxOn` / `exists_isMinOn` — EVT
  - `isPreconnected_Icc.intermediate_value₂` — IVT
  - `comap_norm_atTop` + `Metric.cobounded_eq_cocompact` — compact sublevel sets

- **`hf_cont : Continuous f`** is needed as a theorem hypothesis (not in the Lyapunov struct)
  for `V_limit_zero`, because continuity of `x ↦ fderiv ℝ V x (f x)` requires it.
  Carry this pattern forward.

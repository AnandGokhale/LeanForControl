# 5 — Controllability Hautus

## Context

`webmd/note-to-local.md` flagged controllability Hautus as the natural next
sprint after observability Hautus (sprint 4). The whole observability
template is in place: `unobservableSubspace`, A-invariance via Cayley–Hamilton,
eigenvector extraction over `ℂ`, the block-row Hautus matrix, the kernel
decomposition lemma, and the iff.

The cleanest formalization of controllability Hautus is via **duality**:

  `IsControllable A B ↔ IsObservable Aᵀ Bᵀ`.

This bridge instantly yields controllability Hautus from the existing
observability Hautus, with one key new lemma (the duality bridge) and a
matrix-transpose identification of the two Hautus block matrices
(`[μI − A | B]` row-stacked vs `[μI − Aᵀ; Bᵀ]` column-stacked).

## Files to create or modify

Modify:

- `LeanForControl/LinearSystems/Hautus.lean` — append a controllability
  section over `ℂ`. Add the `IsControllable ↔ IsObservable Aᵀ Bᵀ` bridge,
  the controllability Hautus matrix, and the iff theorem. No new top-level
  file.
- `LeanForControl/LinearSystems/Controllability.lean` — *if* the duality
  bridge needs a small generic-field lemma (e.g. `IsControllable ↔
  IsObservable on transpose` over `[Semiring 𝕜]`), it lives here. Keep
  Hautus.lean control-over-`ℂ` only.
- `LeanForControl.lean` — no change (transitive imports already in place).
- `blueprint/src/content.tex` — append controllability Hautus subsection.
- `notes/5-controllability-hautus.md` — sprint mini-update at the end.
- `exports/5-controllability-hautus.zip` — `.lean` snapshot via the
  end-of-session recipe.

Do **not** modify:

- Existing observability proofs (sprint 4). Reuse, don't restate.
- `MatrixLemmas.lean` — should not need changes here unless a transpose
  bridge proves awkward.

## Mathlib pieces (verify when active)

- `Matrix.transpose` and its `mulVec` / `vecMul` interactions.
- `Matrix.fromCols` / `Matrix.fromRows` and how they relate under transpose
  (`(fromRows A B)ᵀ = fromCols Aᵀ Bᵀ`).
- `Matrix.transpose_pow` (`Aᵀ^k = (A^k)ᵀ`).
- `Matrix.mul_transpose` / `Matrix.transpose_mul` chain.

## Execution sketch

Each step ends with `lake build` green.

### Step 1 — Duality bridge (over `[Semiring 𝕜]`)

In `Controllability.lean`, prove:

```
theorem isControllable_iff_isObservable_transpose
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    IsControllable A B ↔ IsObservable Aᵀ Bᵀ
```

Math: `IsControllable A B` ↔ "image of `u ↦ ∑ k, (A^k * B) *ᵥ u_k` equals
`⊤`", which by orthogonality (or via cokernel-trivial form) is equivalent
to "every left-annihilator vanishes", i.e. `∀ w, (∀ k, w · A^k · B = 0) →
w = 0`. Transpose this: `∀ w, (∀ k, Bᵀ · (Aᵀ)^k *ᵥ w = 0) → w = 0`, which
is exactly `IsObservable Aᵀ Bᵀ`.

Lean implementation:
- Use `Matrix.transpose_pow` to convert `Aᵀ^k` ↔ `(A^k)ᵀ`.
- Use `Matrix.transpose_mul` for `Bᵀ * (A^k)ᵀ = (A^k * B)ᵀ`.
- Use `Matrix.mulVec_transpose` (or the equivalent) to convert
  `(A^k * B)ᵀ *ᵥ w = 0` into `w · (A^k * B) = 0`.
- The reachability ↔ left-cokernel-trivial bridge is then a standard
  surjective-iff-no-left-annihilator argument over a field.
  
**Risk**: this bridge may be more annoying than expected because
`IsControllable` is phrased existentially (every state reachable) and
`IsObservable Aᵀ Bᵀ` is universal. Connecting them may need a finite-dim
argument (range = ⊤ ↔ no nonzero functional annihilates the range), which
requires a field. May want to prove the bridge over `[Field 𝕜]` only and
move it to `Hautus.lean` if it doesn't survive at `[Semiring 𝕜]`.

### Step 2 — Hautus controllability matrix (over `ℂ`)

In `Hautus.lean`, in the existing `namespace LinearSystems`, define:

```
noncomputable def hautusControllabilityMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ) :
    Matrix (Fin n) (Fin n ⊕ Fin m) ℂ :=
  Matrix.fromCols (μ • 1 - A) B
```

Tag with `@[blueprint "def:hautusControllabilityMatrix"]`.

### Step 3 — Transpose bridge between the two Hautus matrices

Prove:

```
lemma hautusControllabilityMatrix_transpose_eq_hautusObservabilityMatrix_transpose
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ) :
    (hautusControllabilityMatrix A B μ)ᵀ = hautusObservabilityMatrix Aᵀ Bᵀ μ
```

Math: `[μI − A | B]ᵀ = [μI − Aᵀ; Bᵀ]`, modulo a `Matrix.transpose_sub /
transpose_smul / transpose_one` chain.

### Step 4 — Bridge for kernels via transpose

Prove (or pull from mathlib):

```
lemma rank_eq_rank_transpose_complex
    (M : Matrix m₁ n ℂ) :
    Matrix.rank M = Matrix.rank Mᵀ
```

over `[Field 𝕜]` (mathlib likely has this as `Matrix.rank_transpose`). Then:

```
lemma ker_hautusControllability_eq_bot_iff_ker_hautusObservability_transpose
    (A : ...) (B : ...) (μ : ℂ) :
    LinearMap.ker (hautusControllabilityMatrix A B μ).vecMulLin = ⊥
      ↔ LinearMap.ker (hautusObservabilityMatrix Aᵀ Bᵀ μ).mulVecLin = ⊥
```

— or, more pragmatically, phrase the controllability Hautus directly in
terms of the **transposed** Hautus kernel and skip stating the iff in two
ways. Decide when active.

### Step 5 — Controllability Hautus iff

```
theorem isControllable_iff_hautus
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    IsControllable A B
      ↔ ∀ μ : ℂ,
          LinearMap.ker (hautusObservabilityMatrix Aᵀ Bᵀ μ).mulVecLin = ⊥
```

Proof: combine `isControllable_iff_isObservable_transpose` with the
existing `isObservable_iff_hautus`. One line after the bridge lands.

Tag `@[blueprint "thm:isControllable-iff-hautus"]`.

### Step 6 — Wire blueprint, end-of-session recipe

Append to `blueprint/src/content.tex` under "Hautus" section:

```
\subsection{Hautus controllability}

\inputleannode{def:hautusControllabilityMatrix}
\inputleannode{thm:isControllable-iff-hautus}
```

Maybe also the duality bridge if blueprint-tagged. Then run the standard
end-of-session recipe (build, regen blueprint, write
`notes/5-controllability-hautus.md`, commit, zip).

## Verification

1. `lake build` exit 0.
2. No `sorry`/`admit`/`axiom` in `LinearSystems/`.
3. `leanblueprint checkdecls` exit 0.
4. Blueprint renders the new node(s) with body content.
5. Dep graph shows `thm:isControllable-iff-hautus` pointing at
   `thm:isObservable-iff-hautus` and the duality bridge.

## Open follow-ups for downstream sprints

- Schur complement and Gramian-divergence matrix lemmas (sprint 6).
- Detectability/stabilizability definitions (sprint 8) — these reuse the
  Hautus characterizations established here and in sprint 4.

## Risk register

- **Duality bridge complexity**: if `IsControllable ↔ IsObservable Aᵀ Bᵀ`
  is awkward at `[Semiring 𝕜]`, lift it to `[Field 𝕜]` and put both halves
  in `Hautus.lean`.
- **Direct mirror as fallback**: if duality proves harder than mirroring
  the observability proof step-by-step (define an "unreachable cokernel"
  submodule, show `Aᵀ`-invariance, extract eigenvector), fall back to
  that — same Cayley–Hamilton and `Module.End.exists_eigenvalue` machinery
  applies. Update this plan and `master.md` if we go that route.

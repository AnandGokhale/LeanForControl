# LeanForControl

A Lean 4 + mathlib formalization of linear-systems and control theory.
Long-term goal: Hespanha's textbook. Driving headfake: the discrete-time
infinite-horizon Kalman-filter result in `webmd/dp-infhor.tex`.

## Quick start

```bash
git clone https://github.com/AnandGokhale/LeanForControl.git
cd LeanForControl
lake exe cache get          # download mathlib's prebuilt artifacts
lake build                  # builds the project (~minutes the first time)
```

`lake build` green = source of truth. No `sorry`/`admit`/`axiom` allowed.

## Three artifacts, three ways to look at the project

### 1. Lean source — the proofs themselves

`LeanForControl/LinearSystems/` is the active development area. Open in
VS Code with the Lean 4 extension; you get inline proof states.

### 2. Blueprint — readable theorem statements + dependency graph

```bash
lake build :blueprint                       # extract LaTeX nodes from @[blueprint] decls
conda activate cortese                      # leanblueprint lives here
leanblueprint checkdecls                    # sanity-check labels
leanblueprint web                           # render → blueprint/web/
python3 -m http.server -d blueprint/web 8001
```

Then open `http://localhost:8001`. You see prose statements, `\leanok`
checkmarks, and a clickable dependency graph. **Caveat**: the prose
statements are *not* checked against the Lean signatures — they're
hand-written. See [`CLAUDE.md`](CLAUDE.md) ("Reporting workflow") for the
trust model.

### 3. doc-gen4 — the actual Lean source rendered like mathlib's docs

```bash
cd docbuild
lake build LeanForControl:docs              # ~tens of minutes the first time
python3 -m http.server -d .lake/build/doc 8000
```

Then open `http://localhost:8000`. Full source code, expandable proofs,
clickable cross-references — the same rendering you see at
[mathlib4_docs](https://leanprover-community.github.io/mathlib4_docs/).
The first build is slow; subsequent builds are incremental.

## Conventions you'll bump into

- **`plans/`** — forward-looking sprint plans. `plans/master.md` is the
  roadmap; `plans/N-slug.md` is the next/active sprint.
- **`notes/`** — backward-looking handoff. One mini-update per sprint.
  Web agents and future-you read these to catch up.
- **`exports/N-slug.zip`** — per-sprint `.lean` snapshots (gitignored).
- **`@[blueprint "label"]`** — annotation that exposes a Lean decl in the
  blueprint with hand-written prose. See `Observability.lean` for examples.

End-of-session recipe (compile → notes/ → blueprint → commit → zip) is
documented in [`CLAUDE.md`](CLAUDE.md).

## Repo layout

```
LeanForControl/                         ← Lean source
├── LinearSystems/                      ← active: matrices, Hautus, etc.
└── (Dini, ODEs, Lyapunov)              ← legacy
blueprint/src/content.tex               ← prose ↔ Lean glue
docbuild/                               ← nested project for doc-gen4
plans/                                  ← forward-looking
notes/                                  ← backward-looking
webmd/                                  ← long-form planning notes
.claude/agents/lean-prover.md           ← project-scoped Claude Code agent
```

## When something breaks

- `lake build` fails with `failed to fetch cache` after a `lake update`?
  Mathlib pinning shifted; re-run `lake exe cache get`.
- `leanblueprint checkdecls` reports a missing decl? You added an
  `@[blueprint "label"]` to a name that doesn't exist (typo or rename).
- doc-gen4 first build hangs at `genCore Lean`? Wait. It's compiling all
  of Lean core's documentation; ~10 min on its own.

For everything else, see `CLAUDE.md`.

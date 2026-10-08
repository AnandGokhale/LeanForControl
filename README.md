# LeanForControl

A Lean 4 + mathlib formalization of linear-systems and control theory.

## Quick start

```bash
git clone https://github.com/AnandGokhale/LeanForControl.git
cd LeanForControl
lake exe cache get          # download mathlib's prebuilt artifacts
lake build                  # builds the project (~minutes the first time)
```

`lake build` green is the source of truth. No `sorry` or `admit`. No custom `axiom`s
remain: `#print axioms` on any result shows only Lean's standard `propext`,
`Classical.choice` and `Quot.sound`. ODE existence and uniqueness are **proved**, not assumed — see
`LeanForControl/ODEs/PicardLindelof.lean`.

## Three ways to look at the project

### 1. Lean source — the proofs themselves

Open `LeanForControl/` in VS Code with the Lean 4 extension; you get inline proof states.
See "Repo layout" below for what lives where, and "What's next" for the current roadmap.

### 2. Blueprint — readable theorem statements + dependency graph

```bash
lake build :blueprint                       # extract LaTeX nodes from @[blueprint] decls
leanblueprint checkdecls                    # sanity-check labels match real Lean decls
leanblueprint web                           # render → blueprint/web/
python3 -m http.server -d blueprint/web 8001
```

`leanblueprint` is a Python tool from `leanprover-community`; install via
`pip install leanblueprint` (any active Python environment will do).

Then open `http://localhost:8001`. You see prose statements, `\leanok`
checkmarks, and a clickable dependency graph. **Caveat**: prose statements
are *not* checked against the Lean signatures — they're hand-written. Trust
the Lean source over the prose if they ever drift.

### 3. doc-gen4 — Lean source rendered like mathlib's docs

```bash
cd docbuild
lake build LeanForControl:docs              # ~tens of minutes the first time
python3 -m http.server -d .lake/build/doc 8000
```

Open `http://localhost:8000` for full source code, expandable proofs, and
clickable cross-references — the same rendering you see at
[mathlib4_docs](https://leanprover-community.github.io/mathlib4_docs/). The
first build is slow; subsequent builds are incremental.

## Annotating Lean for the blueprint

`@[blueprint "label" (statement := /-- LaTeX prose -/)]` exposes a Lean
declaration in the blueprint with the supplied statement. See
`LeanForControl/LinearSystems/Observability/Observability.lean` for examples covering
definitions, lemmas, and theorems (with `proof :=` fields). The `statement`
text is hand-written prose, not auto-extracted from the Lean signature —
keep it tight and faithful; trust the Lean source if they ever drift.

## Repo layout

```
LeanForControl/                          ← Lean source
├── Stability/                           ← Lyapunov, LaSalle, and indirect-method theory
├── Comparison/                          ← class K / K∞ / KL / L comparison-function library
├── ODEs/                                ← comparison lemma, Gronwall–Bellman, ODE existence
├── Analysis/                            ← supporting analysis: Dini derivatives, limsup, integrals, derivative remainders
├── MatrixAlgebra/                       ← matrix facts with no system semantics (rank, spectrum, exp, quadratic forms)
└── LinearSystems/                       ← solutions, controllability/observability, Hurwitz theory, Lyapunov equations
blueprint/src/                           ← .tex sources (run leanblueprint web to render)
docbuild/                                ← nested project for doc-gen4
home_page/                               ← Jekyll scaffold for the project's home page
.github/workflows/                       ← lean-action CI + blueprint deploy CI
```

## What's next

`LeanForControl/Stability/plan.md` is the maintained roadmap for the stability corner of
the library. It records the autonomous and non-autonomous Lyapunov theory, LaSalle, and both
branches of Lyapunov's indirect method (in `Stability/LyapunovIndirect/`). The quantitative
exponential Chetaev criterion used by the nonlinear instability proof is complete; the more
general boundary-form/geometric Chetaev theorem remains planned.
`LeanForControl/LinearSystems/plan.md` tracks the linear track — solutions, the structural
theory, and the Hurwitz foundation — along with its directory-placement rules. The other
directories don't have a written roadmap yet; check
`git log <dir>` for recent activity if you want a sense of what's currently being worked on.

## Contributing

See `CONTRIBUTING.md` for the CI-enforced rules (no `sorry`/`admit`, docstrings, axiom
policy) and the design conventions the library follows (file organization, naming,
citation style, blueprint annotations).

## Acknowledgments

Thanks to Titus Quah for useful discussions.

## When something breaks

- `lake build` fails with `failed to fetch cache` after `lake update`?
  Mathlib pinning shifted; re-run `lake exe cache get`.
- `leanblueprint checkdecls` reports a missing decl? You added an
  `@[blueprint "label"]` to a name that doesn't exist (typo or rename).
- doc-gen4 first build hangs at `genCore Lean`? Wait. It's compiling all
  of Lean core's documentation; ~10 min on its own.

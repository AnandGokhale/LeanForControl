# 0 — LinearSystems milestone + reporting infra stood up

## Landed

Milestone theorem `thm:isObservable-iff-ker-trivial`
(`LeanForControl/LinearSystems/Observability.lean`) plus the definitions and
shape lemmas it depends on:

- `def:observabilityMatrix`, `def:isObservable`,
  `lem:observabilityMatrix-apply`, `lem:observabilityMatrix-mulVec-apply`
- `def:controllabilityMatrix`, `lem:controllabilityMatrix-apply`

All seven `@[blueprint]`-tagged. `lake build` green; no `sorry`/`admit`/`axiom`.

## Reporting infrastructure

- `LeanArchitect` pinned at `f1c14e1c14290117ffcb017cf2d089a6a5e1523a` in
  `lakefile.toml`.
- `leanblueprint` scaffold under `blueprint/`; `blueprint/src/content.tex`
  wired to the seven labels via `\inputleannode{}`.
- `cleveref` added to `web.tex` and `print.tex` so `\cref{...}` resolves.

## Layout change

Repo flattened: lake project sits at the git root (was nested under
`LeanForControl/LeanForControl/`). Standard Lean+blueprint layout.

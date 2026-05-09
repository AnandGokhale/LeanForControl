# 2 — Blueprint CI deploy decision pending

Currently `lake build :blueprint` and `leanblueprint web` run **local-only**.
`.github/workflows/lean_action_ci.yml` builds the project and runs
`docgen-action` but does not extend to the blueprint.

Decision pending: extend the CI workflow to push `blueprint/web/` to GitHub
Pages on merges to `main`. Mirrors the manual end-of-session recipe in
`CLAUDE.md`.

Out of scope until the math layer is one Hautus direction deep — there's no
point publishing a blueprint that's just seven shape lemmas.

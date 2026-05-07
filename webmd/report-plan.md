# Reporting plan

We need a way to systematically report the progress and results of our work.
To do so, automate our progress tracking and keep notes.

## 1. Automated blueprint

Do not hand-edit the blueprint.

Use generated blueprint data from Lean source.

Preferred route:

- annotate Lean declarations
- run a generator
- commit generated output only if requested

Please use:
- `LeanArchitect` for extracting blueprint data from Lean source :contentReference[oaicite:0]{index=0}
- `leanblueprint` for rendering a blueprint site/document from structured blueprint content :contentReference[oaicite:1]{index=1}



## 2. `notes.md`

`notes.md` is hand-edited.

Keep it short. Edit it after each sprint. If items should be removed, remove them.

## 3. Default workflow

At the end of a work session:

1. make Lean compile
2. update `notes.md`
3.  regenerate blueprint

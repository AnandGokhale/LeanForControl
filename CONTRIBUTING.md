# Contributing to LeanForControl

This document covers two things: the rules CI actually enforces, and the design
conventions this library has settled on so far. If you're only fixing a typo or a single
proof, the "Non-negotiables" section is enough. If you're adding a new file or subject
area, read "Design conventions" too.

See `README.md` for how to build the project and the three ways to browse it
(Lean source, blueprint, doc-gen4).

## Non-negotiables (CI-enforced)

1. **`lake build` must be green**, including the linter (CI runs with `lint: true` and
   `mk_all-check: true`). Run it locally before opening a PR:
   ```bash
   lake exe cache get   # first time only
   lake build
   ```
2. **No `sorry`, no `admit`.** A proof that doesn't go through isn't done.
3. **Every public declaration needs a docstring** — the `docBlame` linter enforces this
   and will fail CI otherwise.
4. **Every new theorem or lemma must state where it came from.** Add a `Reference:` line
   to its doc comment (or the module docstring, if it covers the whole file) naming the
   textbook, paper, or standard result it formalizes — e.g. `Reference: Khalil,
   *Nonlinear Systems* (3rd ed.)` (see "Citing a textbook" below for the citation style
   itself: name only, no edition-specific numbers). If the result is original to this
   repo rather than taken from a source, say that explicitly (`Original.` or a one-line
   note on why it's needed) instead of leaving the provenance unstated. Repeat the source
   in the PR description too, so it's visible in review without opening every file.
5. **New custom axioms must be justified and registered, not scattered inline.**
   - Only add an axiom for a standard, well-established mathematical result that isn't
     (yet) in Mathlib — e.g. Picard–Lindelöf existence, or a real-analysis smoothing
     lemma. Don't axiomatize the thing you're actually trying to prove.
   - Write a doc comment on the axiom stating what standard result it captures and why
     it's reasonable to take as given (a citation is good; "obviously true" is not).
   - Put it in `LeanForControl/axioms.lean` or `LeanForControl/Comparison/Axioms.lean`
     (or an equally-named central file for a new subject area) — not inline in a proof
     file, so the full list of assumptions stays auditable in one place.
   - Say so explicitly in the PR description: which axiom, why it's needed, why it's
     standard.
6. **If you touch a file with `@[blueprint ...]` annotations, keep `leanblueprint
   checkdecls` passing** — it checks that blueprint labels still point at real Lean
   declarations.

## Design conventions

These aren't CI-enforced, but deviating from them without a reason makes review harder
and the codebase less consistent.

- **Definitions live apart from theorems.** Structures and predicates go in a dedicated
  `Defs*.lean` (e.g. `DefsAutonomous.lean`, `DefsNonAutonomous.lean`); theorems proved
  from them go in files grouped by result, not by definition (e.g. `Autonomous.lean`,
  `LaSalle.lean`, `NonAutonomous.lean`).
- **Generic infrastructure stays generic.** The comparison-function library (class K,
  K∞, KL, L) lives in `LeanForControl/Comparison/`, decoupled from any specific stability
  theory, so both the autonomous and non-autonomous stability work can reuse it. If
  you're building something reusable across subject areas, it belongs in its own
  directory, not buried inside the file that first needed it.
- **One lemma, one fact.** Each lemma should state and prove exactly one clean,
  reusable mathematical claim, rather than one monolithic proof term that inlines every
  sub-argument — the Lean equivalent of "a function should do one thing and do it well."
  `Autonomous.lean` is the model: `hasDerivAt_V_comp_traj` (just the chain rule),
  `trajectory_continuous`, `V_nonincreasing_on`, and `V_limit_zero_of_compact` are each
  one fact, and the top-level theorems (`lyapunov_stable`, `lyapunov_asymptotic_stable`)
  are just those pieces composed together. The payoff: a small lemma is independently
  reusable (`V_limit_zero_of_compact` is used by both the local and global stability
  proofs) and a change only breaks its direct callers instead of one giant proof. Don't
  over-split, either — if a "sub-lemma" only ever gets used once and needs its own name,
  hypotheses, and doc comment to say less than the `have` block it replaced would have,
  inline it instead.
- **Prefer pointwise hypotheses over trajectory-quantified ones** when formalizing a
  classical condition — e.g. `∀ x, fderiv ℝ V x (f x) ≤ 0` is easier to consume than
  `∀ φ t, HasDerivAt (V ∘ φ) ... t`. Write one chain-rule bridge lemma once
  (`hasDerivAt_V_comp_traj`-style) to connect the two forms, rather than threading the
  trajectory-quantified version through every downstream proof.
- **Bundle data that multiple proof branches need into the defining `structure`**, even
  if it looks redundant at the definition site — e.g. `hequil : f x_eq = 0` is stored on
  the Lyapunov-function structs because several proofs need it and re-deriving it ad hoc
  each time is worse than storing it once.
- **Naming**: predicates read as English (`IsLocalLyapunovFunction`, `LyapunovStable`,
  `UniformlyAsymptoticStableNA`); hypotheses are `h`-prefixed with a descriptive suffix
  (`hV_diff`, `hLie_nonpos`, `hΩ_compact`), matching Mathlib convention.
- **Citing a textbook**: attribute the source by title only — e.g. `Reference: Khalil,
  *Nonlinear Systems* (3rd ed.)` — without edition-specific theorem/lemma/definition
  numbers. Numbers drift across editions and mean nothing to a reader who doesn't own
  that exact edition. Refer to results by their descriptive or eponymous name instead
  (`Barbashin's theorem`, `class-K sandwich bounds`, `Osgood's construction`), the way
  the rest of the file names its own lemmas.
- **Blueprint annotations** (`@[blueprint "label" (statement := ...) (proof := ...)]`)
  go on definitions and named/main theorems worth exposing in the readable blueprint —
  not on every internal helper lemma (roughly a third of declarations carry one; that's
  the right ratio to aim for, not 100%). The `statement`/`proof` text is hand-written
  prose, not auto-extracted from the Lean signature — keep it tight and faithful, and
  treat the Lean source as ground truth if the two ever drift.
- **Keep a living `plan.md`** in any actively-developed subject-area directory (see
  `Stability/plan.md` for the template: a status table of what's proved vs. planned,
  file-by-file notes, and a "lessons learned" section). Update it as part of the PR that
  changes that area's status — a roadmap that isn't updated with the code it describes
  is worse than no roadmap.

## Opening a PR

- Keep it focused: one subject area per PR.
- `lake build` green locally first (the Mathlib cache from `lake exe cache get` makes
  this fast after the first run).
- State the source of any new theorem in the PR description (textbook/paper/original) —
  see item 4 above.
- If you're introducing a new subject-area directory meant for ongoing work, add a
  `plan.md` alongside it.

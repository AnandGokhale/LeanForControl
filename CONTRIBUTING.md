# Contributing to LeanForControl

This document covers two things: the rules CI actually enforces, and the design
conventions this library has settled on so far. If you're only fixing a typo or a single
proof, the "Non-negotiables" section is enough. If you're adding a new file or subject
area, read "Design conventions" too.

See `README.md` for how to build the project and the three ways to browse it
(Lean source, blueprint, doc-gen4).

## Non-negotiables (CI-enforced)

1. **`lake build` must be green.** `blueprint.yml` (push to `main`) explicitly runs with
   `lint: true` and `mk_all-check: true`. `lean_action_ci.yml` (every push/PR) doesn't set
   either input, and `mk_all-check` defaults to `false` in `lean-action` when unset — so
   `mk_all-check` is only actually checked on pushes to `main`, not on every PR. Run the
   full thing locally before opening a PR either way:
   ```bash
   lake exe cache get   # first time only
   lake build
   lake exe mk_all      # green `lake build` ≠ green CI: Lean tolerates duplicate
                        # imports and a stale `LeanForControl.lean`; `mk_all` does not
   ```
2. **No `sorry`, no `admit`.** A proof that doesn't go through isn't done.
3. **Every public declaration needs a docstring** — the `docBlame` linter enforces this
   and will fail CI otherwise. (It only checks that a docstring exists, not what's in it —
   see the `Reference:` convention below, which is not currently linted.)
4. **New custom axioms must be justified and registered, not scattered inline.**
   - Only add an axiom for a standard, well-established mathematical result that isn't
     (yet) in Mathlib — e.g. Picard–Lindelöf existence, or a real-analysis smoothing
     lemma. Don't axiomatize the thing you're actually trying to prove.
   - Write a doc comment on the axiom stating what standard result it captures and why
     it's reasonable to take as given (a citation is good; "obviously true" is not).
   - Put it in a central `Axioms.lean` file for its subject area (e.g.
     `LeanForControl/Comparison/Axioms.lean`) — not inline in a proof
     file, so the full list of assumptions stays auditable in one place.
   - Say so explicitly in the PR description: which axiom, why it's needed, why it's
     standard.
5. **If you touch a file with `@[blueprint ...]` annotations, keep `leanblueprint
   checkdecls` passing** — it checks that blueprint labels still point at real Lean
   declarations — and run the label-integrity check:
   ```bash
   python3 scripts/check_blueprint_labels.py
   ```
   Lean checks none of this, and the three failure modes look nothing alike: a dangling
   `\inputleannode` hard-errors the blueprint build; a dangling `\cref` degrades silently
   to `??`; a declared-but-never-inputted node produces **no diagnostic at all** — its
   LaTeX is written and compiled, and simply never rendered. The script catches all three
   and runs in `blueprint.yml`. Note that `\cref`s live inside other declarations'
   blueprint statements, not only in `content.tex`, so deleting a node can break a
   reference buried in a neighbouring Lean docstring.

   Passing these checks does **not** mean a blueprint statement is *true* of the
   declaration it is attached to — `statement`/`proof` are hand-written prose and nothing
   mechanical compares them against the Lean. If you change a declaration's *type*, re-read
   its blueprint statement by hand; that is where drift comes from.

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
- **Every control-theory result needs a `Reference:` line.** If a declaration states
  something about systems, trajectories, stability, controllability, observability or
  realizations — anything a reader could look up in a control textbook — its doc comment
  (or the module docstring, if it covers the whole file) must name the source, using the
  citation style above. Repeat it in the PR description so it's visible in review without
  opening every file.

  This is the one piece of documentation that makes a claim *checkable*: nothing verifies
  that a blueprint `statement` is true of the Lean it is attached to, and a reader
  auditing one can only do so against a source. A control-theory result with no reference
  is unauditable by anyone who wasn't there when it was written.

  **Supporting mathematics does not need one.** Real-analysis lemmas, order and topology
  facts, matrix algebra, the comparison-function library — cite a source if there is a
  natural one, but don't manufacture provenance for a lemma that exists because a proof
  needed it. Say what it's for instead, in a sentence, if that isn't obvious from the
  statement. (An earlier version of this rule asked for an explicit `Original.` marker in
  that case; it produced twenty copies of "formalization infrastructure for LeanForControl"
  and no information, so it's gone.)

  **Not a CI check** — `docBlame` verifies a docstring exists, not what it says. Treat
  this as required for new and changed results, not as a claim that the existing source
  already complies.
- **Blueprint annotations** (`@[blueprint "label" (statement := ...) (proof := ...)]`)
  follow visibility, not taste. **A public declaration gets a node** — if a result can't be
  found, it may as well not be proved, and being public is what makes it findable at all.
  **A `private` declaration** is a step in a proof, not a result, and needs nothing; if a
  declaration is public only because Lean forced it across a file boundary, the question to
  ask is whether it should be `private`, not whether to skip its node. A declaration nothing
  uses at all is a deletion candidate — but "unused" is worth keeping if it rounds out an
  API, in which case its node is the record of why it stays. The one carve-out: a lemma that
  merely restates a field of a
  structure whose definition already has a node gets nothing either, however widely it is
  used — the definition already said it, and a node would be LaTeX overhead. (These are
  usually `@[simp]`; see the eight `ClassK.*_iff` / `*_apply` lemmas in
  `Comparison/ClassK.lean`.)

  A node is invisible until `content.tex` has an `\inputleannode` for it, so add that in
  the same change. `@[blueprint]` needs `import Architect` in the file; without it the
  attribute doesn't exist and nothing in the file can be annotated at all.

  On an `axiom`, pass `(latexEnv := "lemma")` and no `proof`: Architect defaults an
  unproved declaration to `definition`, which would misrepresent an assumption as a
  definition.

  The `statement`/`proof` text is hand-written prose, not auto-extracted from the Lean
  signature — keep it tight and faithful, and treat the Lean source as ground truth if the
  two ever drift.
- **Don't regex across Lean source in this repo.** The trajectory-predicate patterns nest,
  so a blanket substitution over-matches: one such attempt corrupted six sites, including
  making an `abbrev` self-referential, and a second replaced text the previous replacement
  had just produced. Use explicit per-site edits and check the build between them.
- **Keep a living `plan.md`** in any actively-developed subject-area directory (see
  `Stability/plan.md` for the template: a status table of what's proved vs. planned,
  file-by-file notes, and a "lessons learned" section). Update it as part of the PR that
  changes that area's status — a roadmap that isn't updated with the code it describes
  is worse than no roadmap.

## Opening a PR

- Keep it focused: one subject area per PR.
- `lake build` green locally first (the Mathlib cache from `lake exe cache get` makes
  this fast after the first run).
- State the source of any new control-theory result in the PR description — see
  "Every control-theory result needs a `Reference:` line" above.
- If you're introducing a new subject-area directory meant for ongoing work, add a
  `plan.md` alongside it.

## Purpose

Work rigorously in this Lean project.

Produce small, compiling, reviewable progress.

Do not use `sorry`, `admit`, `axiom`, or other shortcuts unless explicitly requested.

## Ground rules

Prefer the next correct lemma over a grand plan.

Keep proofs short when possible, but not at the cost of clarity or robustness.

Do not invent definitions if an existing project definition already fits.

Do not rewrite working code without a reason.

Do not leave broken files behind.

Every change should build.

## Workflow

Before editing:

1. identify the target file
2. inspect nearby definitions and theorem names
3. check imports
4. confirm the current build status

While editing:

1. make one small change at a time
2. run Lean often
3. isolate helper lemmas when a proof starts to sprawl
4. prefer explicit statements over clever compressed code

After editing:

1. make sure the file compiles
2. make sure the project still builds
3. note any new lemmas worth reusing later

## Proof discipline

Prefer:

- exact statements
- reusable helper lemmas
- explicit assumptions
- structural proofs over brute force
- existing library lemmas over custom reproofs

Avoid:

- giant one-shot proofs
- fragile term code when a tactic proof is clearer
- unnecessary generality
- hidden coercions you do not understand
- changing theorem statements just to make a proof easy

If a proof is stuck:

1. restate the goal in a smaller lemma
2. inspect the types with `#check`
3. search for existing lemmas with `#find` and hover
4. reduce definitional clutter with `simp?`, `rw?`, or intermediate `have` statements

## Project hygiene

Keep experiments in a scratch file, not in main library files.

Move reusable facts out of scratch once they are stable.

Keep imports as light as practical, but do not waste time micro-optimizing imports early.

Name lemmas by what they prove, not by where they came from.

Add comments only when they help a future reader follow the mathematical idea.

## Build policy

A task is not done unless it compiles.

Prefer a smaller proved result over a larger unproved draft.

If a result depends on missing infrastructure, stop and add the missing infrastructure first.

## Communication

Be concise.

State:

- what file to edit
- what lemma to prove next
- what command to run
- what obstacle is blocking progress, if any

Do not pad responses with background the user did not ask for.

## Default tools

Use these constantly:

- `lake build`
- `#check`
- `#print`
- `#find`

When needed, inspect local hypotheses and exact goal state before guessing.

## First principle

No cheats.

If something is hard, cut it into smaller true statements and prove those.
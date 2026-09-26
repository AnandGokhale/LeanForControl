#!/usr/bin/env python3
"""Check blueprint label integrity.

Lean does not check that `@[blueprint "..."]` labels line up with `blueprint/src/content.tex`,
and the three ways they can fail have very different symptoms:

  * a dangling `\\inputleannode` hard-errors the blueprint build;
  * a dangling `\\cref` degrades silently to `??` in the rendered output;
  * a declared-but-never-inputted node produces *no diagnostic at all* — the LaTeX is written
    and compiled into `.lake/build/blueprint/library/`, and simply never rendered.

This catches all three in one pass.

Two traps this script exists to avoid re-learning:

  * The label regex matches `blueprint\\s+"..."`, not `@[blueprint`. Anchoring on `@[blueprint`
    misses `@[simp, blueprint "..."]` and reports false danglers.
  * `\\cref`s live inside other declarations' blueprint statements, not only in `content.tex`.
    Deleting a node can break a reference buried in a neighbouring Lean docstring, so Lean
    sources are scanned for `\\cref` too.

Exit status is 1 if any *dangling* reference is found. Declared-but-never-inputted nodes are
reported but do not fail the run: they are a backlog to work through, not a regression.

Usage:  python3 scripts/check_blueprint_labels.py
"""

from __future__ import annotations

import pathlib
import re
import sys

LEAN_ROOT = pathlib.Path("LeanForControl")
CONTENT_TEX = pathlib.Path("blueprint/src/content.tex")

# Matches the label in `@[blueprint "foo"]` and in `@[simp, blueprint "foo"]` alike.
LABEL_RE = re.compile(r'blueprint\s+"([^"]+)"')
INPUT_RE = re.compile(r"\\inputleannode\{([^}]+)\}")
CREF_RE = re.compile(r"\\cref\{([^}]+)\}")

# Known dangling reference, present at 5fb1630 and predating the trajectory unification work.
KNOWN_DANGLING_CREFS = {"lem:comparison-claim-1"}


def main() -> int:
    if not LEAN_ROOT.is_dir() or not CONTENT_TEX.is_file():
        print("error: run this from the repository root", file=sys.stderr)
        return 2

    lean_files = list(LEAN_ROOT.rglob("*.lean"))
    labels: set[str] = set()
    crefs: set[str] = set()
    for f in lean_files:
        text = f.read_text()
        labels |= set(LABEL_RE.findall(text))
        crefs |= set(CREF_RE.findall(text))

    tex = CONTENT_TEX.read_text()
    inputs = set(INPUT_RE.findall(tex))
    crefs |= set(CREF_RE.findall(tex))

    dangling_inputs = sorted(inputs - labels)
    dangling_crefs = sorted(crefs - labels - KNOWN_DANGLING_CREFS)
    never_inputted = sorted(labels - inputs)

    print(f"{len(labels)} blueprint labels across {len(lean_files)} Lean files")
    print(f"dangling \\inputleannode: {dangling_inputs or 'none'}")
    print(f"dangling \\cref:          {dangling_crefs or 'none'}")
    print(f"declared but never inputted ({len(never_inputted)}):")
    for label in never_inputted:
        print(f"    {label}")

    if dangling_inputs or dangling_crefs:
        print("\nFAIL: dangling blueprint references", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

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

def _uncommented(text: str) -> str:
    """Blank out full-line `--` comments.

    Both label scanners read Lean *source*, not what Lean elaborated, so a commented-out
    `@[blueprint ...]` would otherwise be reported as a declared label — and an
    `\\inputleannode` for it would pass this check while failing the blueprint build,
    because Architect never emitted the node.
    """
    return "\n".join("" if line.lstrip().startswith("--") else line
                      for line in text.splitlines())

# Matches the label in `@[blueprint "foo"]` and in `@[simp, blueprint "foo"]` alike.
LABEL_RE = re.compile(r'blueprint\s+"([^"]+)"')
INPUT_RE = re.compile(r"\\inputleannode\{([^}]+)\}")
CREF_RE = re.compile(r"\\cref\{([^}]+)\}")

# Dangling `\cref`s to tolerate. Empty, and should stay that way: a dangling reference renders
# as `??` with no diagnostic, so an entry here is a rendered defect nobody will be told about.
# The one that used to live here pointed at a `private` lemma, which by policy gets no node —
# the fix was to inline its content into the citing proof, not to exempt the reference.
KNOWN_DANGLING_CREFS: set[str] = set()


def main() -> int:
    if not LEAN_ROOT.is_dir() or not CONTENT_TEX.is_file():
        print("error: run this from the repository root", file=sys.stderr)
        return 2

    lean_files = list(LEAN_ROOT.rglob("*.lean"))
    labels: set[str] = set()
    crefs: set[str] = set()
    sites: dict[str, list[str]] = {}
    for f in lean_files:
        text = _uncommented(f.read_text())
        labels |= set(LABEL_RE.findall(text))
        crefs |= set(CREF_RE.findall(text))
        for i, line in enumerate(text.splitlines(), 1):
            for m in LABEL_RE.finditer(line):
                sites.setdefault(m.group(1), []).append(f"{f}:{i}")

    # Two declarations sharing a label is silent: the label still resolves, so nothing else here
    # complains, but only one of them can ever be rendered by `\inputleannode`.
    duplicates = {lab: locs for lab, locs in sites.items() if len(locs) > 1}

    tex = CONTENT_TEX.read_text()
    inputs = set(INPUT_RE.findall(tex))
    crefs |= set(CREF_RE.findall(tex))

    dangling_inputs = sorted(inputs - labels)
    dangling_crefs = sorted(crefs - labels - KNOWN_DANGLING_CREFS)
    never_inputted = sorted(labels - inputs)

    print(f"{len(labels)} blueprint labels across {len(lean_files)} Lean files")
    print(f"dangling \\inputleannode: {dangling_inputs or 'none'}")
    print(f"dangling \\cref:          {dangling_crefs or 'none'}")
    print(f"duplicate labels:        {sorted(duplicates) or 'none'}")
    for label, locs in sorted(duplicates.items()):
        for loc in locs:
            print(f"    {label}  {loc}")
    print(f"declared but never inputted ({len(never_inputted)}):")
    for label in never_inputted:
        print(f"    {label}")

    if dangling_inputs or dangling_crefs or duplicates:
        print("\nFAIL: blueprint label errors", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

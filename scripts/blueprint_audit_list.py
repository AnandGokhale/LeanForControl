#!/usr/bin/env python3
"""Generate `BLUEPRINT_AUDIT.md`: every declaration in the library, grouped by file, with its
`@[blueprint]` label (if any) and whether that label is actually rendered.

This is the worklist for the manual audit described in `INVENTORY.md` §1e — checking that each
blueprint `statement` is *true* of the declaration it is attached to, which nothing mechanical can
verify. `scripts/check_blueprint_labels.py` checks that labels resolve; this says what to read.

Regenerate after any declaration is added, renamed or moved:

    python3 scripts/blueprint_audit_list.py
"""

from __future__ import annotations

import pathlib
import re
import sys

LEAN_ROOT = pathlib.Path("LeanForControl")
CONTENT_TEX = pathlib.Path("blueprint/src/content.tex")
SIGNOFF = pathlib.Path("scripts/blueprint_audit_signoff.txt")
DEFER = pathlib.Path("scripts/blueprint_audit_defer.txt")
OUT = pathlib.Path("BLUEPRINT_AUDIT.md")


def read_signoff() -> set[str]:
    """Files whose annotated declarations have all been read and confirmed."""
    if not SIGNOFF.is_file():
        return set()
    return {
        line.strip()
        for line in SIGNOFF.read_text().splitlines()
        if line.strip() and not line.startswith("#")
    }


def read_defer() -> dict[str, str]:
    """Files deliberately held out, mapped to the stated reason.

    Kept apart from sign-off on purpose: signed off means read and confirmed, deferred means not
    looked at. Collapsing the two would make the remaining count read lower than it is.
    """
    if not DEFER.is_file():
        return {}
    out: dict[str, str] = {}
    for line in DEFER.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        path, _, reason = line.partition("#")
        out[path.strip()] = reason.strip() or "no reason given"
    return out

DECL_RE = re.compile(
    r"^(?P<priv>private\s+)?(?:noncomputable\s+)?(?:protected\s+)?"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|instance|axiom)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_.'′]*)"
)
def _uncommented(text: str) -> str:
    """Blank out full-line `--` comments.

    Both label scanners read Lean *source*, not what Lean elaborated, so a commented-out
    `@[blueprint ...]` would otherwise be reported as a declared label — and an
    `\\inputleannode` for it would pass this check while failing the blueprint build,
    because Architect never emitted the node.
    """
    return "\n".join("" if line.lstrip().startswith("--") else line
                      for line in text.splitlines())

LABEL_RE = re.compile(r'blueprint\s+"([^"]+)"')
INPUT_RE = re.compile(r"\\inputleannode\{([^}]+)\}")


def _norm(s: str) -> str:
    """Strip separators and case so `isControllable_iff_rank` and `isControllable-iff-rank` agree."""
    return re.sub(r"[^a-z0-9]", "", s.lower())


def diverges(label: str, name: str) -> bool:
    """True when the label's stem and the declaration name share no containment relation.

    A weak signal, not an error — many labels are legitimate abbreviations of long Lean names. But
    an annotation attached to the *wrong* declaration shows up here, which is the one thing the
    manual audit exists to catch and nothing else detects. Roughly one row in seven trips this.
    """
    stem = label.split(":", 1)[1] if ":" in label else label
    a, b = _norm(stem), _norm(name.split(".")[-1])
    return a not in b and b not in a


def main() -> int:
    if not LEAN_ROOT.is_dir() or not CONTENT_TEX.is_file():
        print("error: run this from the repository root", file=sys.stderr)
        return 2

    rendered = set(INPUT_RE.findall(CONTENT_TEX.read_text()))
    signed_off = read_signoff()
    deferred = read_defer()
    files = sorted(LEAN_ROOT.rglob("*.lean"))

    out: list[str] = []
    n_decl = n_ann = n_unrendered = 0
    per_file: list[tuple[pathlib.Path, list[tuple[str, str, str, bool]]]] = []

    texts = {f: _uncommented(f.read_text()) for f in files}
    sites: dict[str, list[str]] = {}
    for f in files:
        rows: list[tuple[str, str, str, bool]] = []
        pending: str | None = None
        for i, line in enumerate(texts[f].splitlines(), 1):
            m = LABEL_RE.search(line)
            if m:
                pending = m.group(1)
                sites.setdefault(pending, []).append(f"{f}:{i}")
                continue
            d = DECL_RE.match(line)
            if d:
                rows.append((d.group("name"), d.group("kind"), pending or "", bool(d.group("priv"))))
                pending = None
        per_file.append((f, rows))
        n_decl += len(rows)
        n_ann += sum(1 for r in rows if r[2])
        n_unrendered += sum(1 for r in rows if r[2] and r[2] not in rendered)

    # Reach: does anything outside the declaring file use this? That is the rule for whether a
    # declaration is part of the library's structure (and so needs a node) or an internal proof
    # step (which does not). Used nowhere at all is a deletion candidate — unless it is annotated,
    # in which case it is a top-level result with no internal callers by design.
    reach: dict[tuple[pathlib.Path, str], str] = {}
    for f, rows in per_file:
        for name, _k, _l, _p in rows:
            short = re.escape(name.split(".")[-1])
            pat = re.compile(r"(?<![A-Za-z0-9_'])" + short + r"(?![A-Za-z0-9_'])")
            ext = any(pat.search(t) for g, t in texts.items() if g != f)
            ins = len(pat.findall(texts[f])) - 1
            reach[(f, name)] = "external" if ext else ("internal" if ins else "unused")

    dupes = {lab: locs for lab, locs in sites.items() if len(locs) > 1}
    divergent = [
        (f, name, label)
        for f, rows in per_file
        for name, _k, label, _p in rows
        if label and diverges(label, name)
    ]

    done = [f for f, _ in per_file if str(f) in signed_off]
    held = [(f, rows) for f, rows in per_file if str(f) in deferred and rows]
    todo = [
        (f, rows)
        for f, rows in per_file
        if str(f) not in signed_off and str(f) not in deferred and rows
    ]
    left_ann = sum(1 for _f, rows in todo for r in rows if r[2])
    held_decl = sum(len(rows) for _f, rows in held)

    out.append("# Blueprint audit worklist\n")
    out.append(
        "Generated by `scripts/blueprint_audit_list.py` — **regenerate rather than hand-edit the\n"
        "tables**. To retire a file, add it to `scripts/blueprint_audit_signoff.txt`; it then\n"
        "drops out of the list below. To hold one back instead — because it needs work beyond\n"
        "annotation — add it to `scripts/blueprint_audit_defer.txt` with a reason.\n"
    )
    out.append(
        f"**{left_ann}** annotated declarations left to read, across **{len(todo)}** files.\n"
        f"Signed off so far: **{len(done)}**. Library totals: {n_decl} declarations in\n"
        f"{len(files)} files, {n_ann} annotated, {n_unrendered} never `\\inputleannode`d and so\n"
        "absent from the rendered blueprint (INVENTORY §1c).\n"
    )
    if done:
        out.append("**Signed off:** " + ", ".join(f"`{f}`" for f in done) + "\n")
    if held:
        out.append(
            f"**Deferred** ({len(held)} files, {held_decl} declarations) — held out of the audit on\n"
            "purpose, per `scripts/blueprint_audit_defer.txt`. Not read, not confirmed; annotating\n"
            "them now would document a shape that is about to change. They are excluded from the\n"
            "count above.\n"
        )
        for f, rows in held:
            out.append(f"- `{f}` ({len(rows)} decl) — {deferred[str(f)]}")
        out.append("")
    n_write = sum(
        1 for f, rows in todo for _n, _k, label, priv in rows if not label and not priv
    )

    out.append("## The rule\n")
    out.append(
        "A **public** declaration gets a blueprint node — if you cannot find a result, it may as\n"
        "well not be proved, and being public is what makes it findable at all. A **`private`**\n"
        "declaration is a step in a proof, not a result, and needs nothing. If something is public\n"
        "only because Lean forced it across a file boundary, the question is whether it should be\n"
        "`private`, not whether to skip its node.\n"
    )
    out.append(
        "One carve-out: a lemma that merely restates a field of a structure whose definition\n"
        "already has a node gets nothing either — the definition said it, and a node would be\n"
        "LaTeX overhead. These are usually `@[simp]`; see the eight `ClassK.*_iff` / `*_apply`\n"
        "lemmas. They still show as **write** below, since nothing mechanical can tell a\n"
        "restatement from a result.\n"
    )
    out.append("The `Do` column says which case each declaration is in:\n")
    out.append(
        f"- **read** — has a node; check the `statement` (and `proof`) is *true of the Lean*.\n"
        "  Nothing mechanical verifies this. Highest yield is any declaration whose **type**\n"
        "  changed in a migration.\n"
        f"- **write** ({n_write} left) — public, no node yet. Write one. The `Reach` column says\n"
        "  whether anything actually uses it; a public declaration nothing references is a\n"
        "  deletion candidate, but keeping it to round out an API is fine — its node is then the\n"
        "  record of why it stays.\n"
        "- **—** — `private`; a proof step. Leave alone.\n"
    )

    out.append("## Start here — what the generator can flag by itself\n")

    if dupes:
        out.append(
            "**Duplicate labels.** Two declarations carry the same label, so only one can ever be\n"
            "rendered and the other is silently invisible. `check_blueprint_labels.py` fails on\n"
            "these.\n"
        )
        for lab, locs in sorted(dupes.items()):
            out.append(f"- `{lab}`")
            for loc in locs:
                out.append(f"  - `{loc}`")
        out.append("")
    else:
        out.append("**Duplicate labels:** none.\n")

    if divergent:
        out.append(
            f"**Label does not resemble its declaration ({len(divergent)}).** A weak signal — most\n"
            "of these are legitimate abbreviations of long Lean names. But an annotation attached to\n"
            "the *wrong* declaration lands here, so read these first.\n"
        )
        out.append("| Blueprint label | Declaration | File |")
        out.append("|---|---|---|")
        for f, name, label in divergent:
            out.append(f"| `{label}` | `{name}` | `{f}` |")
        out.append("")
    else:
        out.append("**Label/declaration divergences:** none.\n")

    out.append("---\n")

    for f, rows in todo:
        ann = [r for r in rows if r[2]]
        head = f"### `{f}`"
        summary = f"{len(rows)} declaration" + ("s" if len(rows) != 1 else "")
        if ann:
            miss = sum(1 for r in ann if r[2] not in rendered)
            summary += f", {len(ann)} annotated"
            if miss:
                summary += f" ({miss} unrendered)"
        else:
            summary += ", none annotated"
        out.append(head)
        out.append(f"*{summary}*\n")
        out.append("| Do | Declaration | Kind | Reach | Blueprint label | Rendered / flags |")
        out.append("|---|---|---|---|---|---|")
        for name, kind, label, priv in rows:
            k = kind + (" · p" if priv else "")
            where = reach[(f, name)]
            if label:
                flags = ["yes" if label in rendered else "**no**"]
                if label in dupes:
                    flags.append("**duplicate**")
                if diverges(label, name):
                    flags.append("name≉label")
                do = "read"
            else:
                do = "— " if priv else "**write**"
                flags = ["—"]
            out.append(f"| {do} | `{name}` | {k} | {where} | `{label or '—'}` | {' · '.join(flags)} |")
        out.append("")

    OUT.write_text("\n".join(out) + "\n")
    print(f"wrote {OUT}: {n_decl} declarations, {n_ann} annotated, {n_unrendered} unrendered")
    return 0


if __name__ == "__main__":
    sys.exit(main())

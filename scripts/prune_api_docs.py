#!/usr/bin/env python3
"""Keep only LeanForControl's pages in a doc-gen4 output directory.

doc-gen4 renders every module that LeanForControl imports (Mathlib, Lean core, ...), which
makes the site several gigabytes. This script deletes those pages and points every link to
them at the official Mathlib documentation, which hosts the same modules:

- module pages and directories of other packages are deleted;
- the search index keeps only LeanForControl's declarations, modules and instances;
- the navigation bar lists only LeanForControl;
- every relative link to a deleted page now goes to the Mathlib documentation.

The Mathlib documentation follows Mathlib's master branch, so a declaration renamed since the
version LeanForControl pins can be missing there.

Usage: python3 scripts/prune_api_docs.py <doc-dir>
"""

import json
import posixpath
import re
import shutil
import sys
from pathlib import Path

PROJECT = "LeanForControl"
EXTERNAL = "https://leanprover-community.github.io/mathlib4_docs/"
INDEX = Path("declarations") / "declaration-data.bmp"


def is_project_module(name: str) -> bool:
    return name == PROJECT or name.startswith(PROJECT + ".")


def is_project_link(link: str) -> bool:
    path = link.split("#", 1)[0].removeprefix("./")
    return path == PROJECT + ".html" or path.startswith(PROJECT + "/")


def delete_other_packages(root: Path) -> None:
    """Module pages start with a capital letter; doc-gen4's own pages and folders do not."""
    for entry in root.iterdir():
        if not entry.name[:1].isupper() or entry.name in (PROJECT, PROJECT + ".html"):
            continue
        if entry.is_dir():
            shutil.rmtree(entry)
        elif entry.suffix == ".html":
            entry.unlink()


def prune_index(root: Path) -> None:
    path = root / INDEX
    data = json.loads(path.read_text(encoding="utf-8"))
    decls = {k: v for k, v in data["declarations"].items() if is_project_link(v["docLink"])}

    def kept(names):
        return [n for n in names if n in decls]

    data["declarations"] = decls
    for key in ("instances", "instancesFor"):
        data[key] = {k: kept(v) for k, v in data[key].items() if kept(v)}
    data["modules"] = {
        name: {**mod, "importedBy": [m for m in mod["importedBy"] if is_project_module(m)]}
        for name, mod in data["modules"].items()
        if is_project_module(name)
    }
    path.write_text(json.dumps(data, separators=(",", ":")), encoding="utf-8")


DETAILS = re.compile(r"<details\b|</details>")
DATA_PATH = re.compile(r'data-path="([^"]*)"')


def prune_navbar(root: Path) -> None:
    """Drop the top-level module trees of other packages from the navigation bar."""
    path = root / "navbar.html"
    html = path.read_text(encoding="utf-8")
    start = html.index('<div class="module_list">') + len('<div class="module_list">')
    out, pos, depth, block_start = [html[:start]], start, 0, None
    for m in DETAILS.finditer(html, start):
        if m.group() == "</details>":
            depth -= 1
            if depth == 0:
                block = html[block_start:m.end()]
                link = DATA_PATH.search(block)
                if link and is_project_link(link.group(1)):
                    out.append(block)
                pos = m.end()
            elif depth < 0:
                break
        else:
            if depth == 0:
                out.append(html[pos:m.start()])
                block_start = m.start()
            depth += 1
    out.append(html[pos:])
    path.write_text("".join(out), encoding="utf-8")


ATTR = re.compile(r'(href|src)="([^"]*)"')
ABSOLUTE = ("http:", "https:", "mailto:", "data:", "javascript:", "#", "/")


def redirect_links(root: Path) -> None:
    """Send relative links whose target was deleted to the Mathlib documentation."""
    for page in root.rglob("*.html"):
        folder = page.parent.relative_to(root).as_posix()

        def fix(m: re.Match) -> str:
            value = m.group(2)
            if not value or value.startswith(ABSOLUTE):
                return m.group(0)
            target, sep, fragment = value.partition("#")
            resolved = posixpath.normpath(posixpath.join(folder, target))
            if resolved.startswith("..") or (root / resolved).exists():
                return m.group(0)
            return f'{m.group(1)}="{EXTERNAL}{resolved}{sep}{fragment}"'

        html = page.read_text(encoding="utf-8")
        new = ATTR.sub(fix, html)
        if new != html:
            page.write_text(new, encoding="utf-8")


def main() -> None:
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    root = Path(sys.argv[1])
    delete_other_packages(root)
    prune_index(root)
    prune_navbar(root)
    redirect_links(root)


if __name__ == "__main__":
    main()

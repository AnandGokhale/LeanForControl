# Summary of blueprint node completeness: how many nodes carry a title, a proof sketch,
# and a source citation, with the no-source count broken down by directory.
# `Analysis/` is exempt from the source requirement (see INVENTORY Standing).
import re, pathlib, collections
root = pathlib.Path("LeanForControl")
nodes = []
for f in sorted(root.rglob("*.lean")):
    src = f.read_text()
    # each @[blueprint "label" ... ] block, balanced to the closing ]
    for m in re.finditer(r'@\[blueprint\s+"([^"]+)"', src):
        start = m.start()
        depth, i = 0, start + len("@[")
        depth = 1
        i = start + 2
        while i < len(src) and depth:
            if src[i] == '[': depth += 1
            elif src[i] == ']': depth -= 1
            i += 1
        body = src[start:i]
        nodes.append({
            "file": str(f), "label": m.group(1), "body": body,
            "proof": "(proof :=" in body,
            "title": "(title :=" in body,
            "env": "(latexEnv :=" in body,
            "ref": bool(re.search(r'Reference:|\\cite|\\cref', body)),
        })
print(f"{len(nodes)} blueprint nodes in {len(set(n['file'] for n in nodes))} files\n")
def pct(n): return f"{n:4d}  ({100*n//len(nodes):2d}%)"
print("has title   :", pct(sum(n['title'] for n in nodes)))
print("has proof   :", pct(sum(n['proof'] for n in nodes)))
print("has a source:", pct(sum(n['ref']  for n in nodes)))
print("\n--- no source, by directory ---")
c = collections.Counter(str(pathlib.Path(n['file']).parent) for n in nodes if not n['ref'])
for d, k in c.most_common(12): print(f"{k:4d}  {d}")
print("\n--- no proof field, by directory ---")
c = collections.Counter(str(pathlib.Path(n['file']).parent) for n in nodes if not n['proof'])
for d, k in c.most_common(8): print(f"{k:4d}  {d}")

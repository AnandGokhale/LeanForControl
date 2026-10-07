# Public theorems of 40+ lines that carry no blueprint proof sketch, longest first.
# Node detection is a 60-line-lookback heuristic: spot-check "NO NODE" before trusting it.
import re, pathlib, collections
root = pathlib.Path("LeanForControl")
rows = []
for f in sorted(root.rglob("*.lean")):
    lines = f.read_text().split("\n")
    decls = [i for i,l in enumerate(lines)
             if re.match(r'^(private |protected |noncomputable )*(theorem|lemma) ', l)]
    for k, i in enumerate(decls):
        end = decls[k+1] if k+1 < len(decls) else len(lines)
        priv = lines[i].startswith("private")
        name = re.sub(r'^(private |protected |noncomputable )*(theorem|lemma) ','',lines[i])
        name = re.split(r'[ ({:\n]', name)[0]
        back = "\n".join(lines[max(0,i-60):i])
        seg = back.rsplit("@[blueprint", 1)
        has_bp = len(seg) > 1 and "theorem " not in seg[1] and "lemma " not in seg[1]
        has_proof = has_bp and "(proof :=" in seg[1]
        rows.append((end-i, str(f), name, priv, has_bp, has_proof))
pub = [r for r in rows if not r[3] and r[0] >= 40 and not r[5]]
pub.sort(reverse=True)
print(f"PUBLIC theorems >= 40 lines with no blueprint proof sketch: {len(pub)}\n")
print(f"{'len':>4} {'node?':>6}  file / name")
print("-"*86)
for n,f,name,_,bp,_ in pub:
    print(f"{n:4d} {'has node' if bp else 'NO NODE':>8}  {f.replace('LeanForControl/','')} :: {name[:40]}")
print("\n--- by directory ---")
for d,k in collections.Counter(str(pathlib.Path(r[1]).parent) for r in pub).most_common():
    print(f"{k:4d}  {d}")

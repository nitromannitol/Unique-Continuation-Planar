#!/usr/bin/env python3
"""Register (or refresh) a frozen node in ledger/manifest.yaml.

    python3 tools/freeze.py ID FILE EXPORT KIND STATE "SOURCE"

KIND is `theorem` or `definition`; STATE is `DRAFT_SORRY`, `SEALED` or `FROZEN`.
The frozen SHA-256 is computed with the recipe of CORRESPONDENCE.md: the bytes
strictly between the markers, one leading newline dropped, the trailing newline
before the END marker kept (as `check_manifest.py` does).  An existing
node with the same ID is replaced and its `version` bumped, so a statement
change is visible in the manifest history.
"""
import hashlib, re, sys, pathlib, datetime

ROOT = pathlib.Path(__file__).resolve().parent.parent
MAN = ROOT / "ledger" / "manifest.yaml"
BEGIN, END = "-- FROZEN-STATEMENT-BEGIN", "-- FROZEN-STATEMENT-END"

def frozen_hash(path: pathlib.Path) -> str:
    t = path.read_text(encoding="utf-8")
    blk = t[t.index(BEGIN) + len(BEGIN):t.index(END)]
    if blk.startswith("\n"):
        blk = blk[1:]
    return hashlib.sha256(blk.encode("utf-8")).hexdigest()

def main():
    nid, file, export, kind, state, source = sys.argv[1:7]
    if ": " in source or source.startswith("'") or '"' in source:
        sys.exit("freeze.py: the source text must not contain ': ' (YAML); reword it")
    h = frozen_hash(ROOT / file)
    man = MAN.read_text(encoding="utf-8")
    head, *blocks = man.split("  - id: ")
    version = 1
    kept = []
    for b in blocks:
        if b.split("\n")[0].strip() == nid:
            m = re.search(r"version: (\d+)", b)
            version = int(m.group(1)) + 1 if m else 2
        else:
            kept.append(b)
    entry = (f"{nid}\n    version: {version}\n    kind: {kind}\n    source: {source}\n"
             f"    file: {file}\n    export: {export}\n    state: {state}\n"
             f"    frozen_sha256: {h}\n    provider: {export}\n"
             f"    approved: \"{datetime.date.today().isoformat()}\"\n\n")
    head = head.replace("nodes: []", "nodes:\n")
    if not head.rstrip().endswith("nodes:"):
        head = head.rstrip("\n") + "\n"
    MAN.write_text(head + "".join("  - id: " + b for b in kept) + "  - id: " + entry, encoding="utf-8")
    print(f"{nid}: version {version}, sha {h[:12]}…, state {state}")

main()

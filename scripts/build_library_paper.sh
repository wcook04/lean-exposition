#!/bin/sh
# Build one library paper (instances/<paper>/) into site/dist, for https://wcook04.github.io/library/<paper>/.
# Usage: scripts/build_library_paper.sh <paper>  (from the repository root; LEAN_EXPOSITION and PYTHON may name a venv's commands)
set -eu
paper=$1
LX=${LEAN_EXPOSITION:-lean-exposition}
PY=${PYTHON:-python3}
I=instances/$paper
pair() { if [ -f "$I/papers/$1/paper.md" ]; then echo "$I/papers/$1/paper.md $I/papers/$1/correspondence.json"; else echo "$I/papers/$1/absent.md $I/papers/$1/absent.json"; fi; }
rm -rf "build/$paper-edition"
# Topic colours are computed once per shared topic list over every paper that uses it, and stored
# beside each phrases file (alignment/colours-<slot>.json); this keeps them current.
node site/scripts/topic-colours.ts
"$LX" validate "$I/evidence-graph.json" > /dev/null
"$LX" check-alignment "$I/alignment" --lean-tree "$I/upstream/lean" --graph "$I/evidence-graph.json" \
  --paper long $(pair long | cut -d' ' -f1) --paper short $(pair short | cut -d' ' -f1) --paper expository $(pair expository | cut -d' ' -f1) > "build/$paper-alignment.json"
"$LX" assemble "$I/evidence-graph.json" --long $(pair long) --short $(pair short) --expository $(pair expository) --out "build/$paper-edition" > /dev/null
"$PY" site/scripts/export-static.py "build/$paper-edition" --lean-tree "$I/upstream/lean" --alignment "$I/alignment"
# The phrases placed on the authors' PDF, for the reader's PDF view (needs poppler's pdftotext).
rm -rf site/public/pdf-marks
for slot in long short expository; do
  if [ -f "$I/papers/$slot/paper.pdf" ] && [ -f "$I/papers/$slot/paper.md" ]; then
    "$PY" scripts/pdf_marks.py "$I/papers/$slot/paper.pdf" "$I/papers/$slot/paper.md" "site/public/edition/ties/$slot.json" "site/public/pdf-marks/$slot.json"
  fi
done
cd site
node scripts/library-instance.mjs "$paper"
LX_INSTANCE=library VITE_STATIC_EDITION=true VITE_BASE_PATH="/library/$paper/" LX_SITE_URL="https://wcook04.github.io/library/$paper/" npm run build
cd ..
# The paper's own addresses as static pages: its top (/) and each numbered result (/theorem-1.1/)
# get the main document's first screen, so they load with a 200 and a first paint of the text.
# Phrase (/@id) and Lean (/lean/name) addresses fall back to 404.html, the same shell.
"$PY" - "$paper" <<'PYEOF'
import json, shutil, sys
from pathlib import Path
paper = sys.argv[1]
inst = json.loads(Path(f"instances/{paper}/instance.json").read_text())
main = next(d for d in inst["documents"] if d.get("main"))
dist = Path("site/dist")
shell = (dist / "read" / main["slot"] / "index.html").read_text()
(dist / "index.html").write_text(shell)
results = json.loads(Path(f"instances/{paper}/alignment/results.json").read_text())["results"]
for address in results:
    (dist / address).mkdir(exist_ok=True)
    (dist / address / "index.html").write_text(shell)
print(f"static addresses: / and {len(results)} results")
PYEOF
# Put back the tracked placeholder that library-instance.mjs replaced.
git checkout -- site/src/instances/library/current.json 2>/dev/null || true

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
# An adapted edition (instances/<paper>/adapted/, scripts/adapted_edition.py) is built only when its
# edition.json says published, or for a local preview with LX_PREVIEW_ADAPTED=1. It is put into its
# document slot for the build and taken out again afterwards, whatever the build's outcome.
LX_ADAPTED=0
if "$PY" scripts/adapted_edition.py enabled "$paper"; then
  LX_ADAPTED=1
  "$PY" scripts/adapted_edition.py stage "$paper"
  trap '"$PY" scripts/adapted_edition.py unstage "$paper"' EXIT
fi
export LX_ADAPTED
# Topic colours are computed once per shared topic list over every paper that uses it, and stored
# beside each phrases file (alignment/colours-<slot>.json); this keeps them current.
node site/scripts/topic-colours.ts
"$LX" validate "$I/evidence-graph.json" > /dev/null
# The paper's three accounts are checked and exported here; its companion documents (phrases-<page>.json)
# each get an edition of their own below (build_companion_editions.py).
A="build/$paper-alignment-main"
rm -rf "$A" && mkdir -p "$A"
for f in "$I"/alignment/*; do
  case "$(basename "$f")" in
    phrases-*|references-*|colours-*) stage=$(basename "$f" .json); stage=${stage#*-}
      case "$stage" in long|short|expository) cp "$f" "$A/";; esac;;
    *) cp "$f" "$A/";;
  esac
done
"$LX" check-alignment "$A" --lean-tree "$I/upstream/lean" --graph "$I/evidence-graph.json" \
  --paper long $(pair long | cut -d' ' -f1) --paper short $(pair short | cut -d' ' -f1) --paper expository $(pair expository | cut -d' ' -f1) > "build/$paper-alignment.json"
"$LX" assemble "$I/evidence-graph.json" --long $(pair long) --short $(pair short) --expository $(pair expository) --out "build/$paper-edition" > /dev/null
# The Lean index the reader shows: the text scan with Lean's own dependencies, where the paper has them.
LEAN_TREE="$I/upstream/lean"
if [ -f "$I/generated/lean-facts.json" ]; then
  "$PY" scripts/enrich_lean_index.py "$I/upstream/lean" "$I/generated/lean-facts.json" "build/$paper-lean-index.json"
  LEAN_TREE="build/$paper-lean-index.json"
fi
"$PY" scripts/check_instance.py "$paper" "$LEAN_TREE"
"$PY" site/scripts/export-static.py "build/$paper-edition" --lean-tree "$LEAN_TREE" --alignment "$A"
if grep -q '"kind": "companion"' "$I/instance.json" || [ "$LX_ADAPTED" = 1 ]; then
  # Companion editions are kept between builds (build/<paper>-companion-editions) and rebuilt only when
  # their inputs change; the export above starts site/public/edition afresh, so they are copied in.
  "$PY" scripts/build_companion_editions.py "$paper" "$LEAN_TREE" "build/$paper-companion-editions" --jobs "${COMPANION_JOBS:-3}"
  cp -R "build/$paper-companion-editions/docs" site/public/edition/
fi
# The phrases placed on the authors' PDF, for the reader's PDF view (needs poppler's pdftotext).
rm -rf site/public/pdf-marks
for slot in long short expository $([ "$LX_ADAPTED" = 1 ] && "$PY" -c "import json; print(json.load(open('$I/adapted/edition.json'))['document']['slot'])"); do
  if [ -f "$I/papers/$slot/paper.pdf" ] && [ -f "$I/papers/$slot/paper.md" ]; then
    # An adapted edition's PDF marks its changes; its change map places them (scripts/adapted_edition.py).
    changes=""; [ -f "$I/alignment/changes-$slot.json" ] && changes="$I/alignment/changes-$slot.json"
    # A companion's ties are in its own edition (edition/docs/<page>/, the file its index names for /ties/short).
    ties="site/public/edition/ties/$slot.json"
    if [ -f "site/public/edition/docs/$slot/index.json" ]; then
      ties="site/public/edition/$("$PY" -c "import json,sys; print(json.load(open(sys.argv[1]))['responses']['/ties/short'])" "site/public/edition/docs/$slot/index.json")"
    fi
    "$PY" scripts/pdf_marks.py "$I/papers/$slot/paper.pdf" "$I/papers/$slot/paper.md" "$ties" "site/public/pdf-marks/$slot.json" $changes
  fi
done
cd site
node scripts/check-tex.mjs "$paper"
node scripts/library-instance.mjs "$paper"
# Where the paper is served: its id, or the instance's own path (a document of another paper, "pcp/reading-guide").
at=$("$PY" -c 'import json,sys; i=json.load(open(sys.argv[1])); print(i.get("path") or i["id"])' "../$I/instance.json")
LX_INSTANCE=library VITE_STATIC_EDITION=true VITE_BASE_PATH="/library/$at/" LX_SITE_URL="https://wcook04.github.io/library/$at/" npm run build
cd ..
# The paper's own addresses as static pages: its top (/) and each numbered result (/theorem-1.1/)
# get the main document's first screen, so they load with a 200 and a first paint of the text.
# Phrase (/@id) and Lean (/lean/name) addresses fall back to 404.html, the same shell.
"$PY" - "$paper" <<'PYEOF'
import json, shutil, sys
from pathlib import Path
paper = sys.argv[1]
inst = json.loads(Path(f"instances/{paper}/instance.json").read_text())
import os
if os.environ.get("LX_ADAPTED") == "1":
    inst["documents"].append(json.loads(Path(f"instances/{paper}/adapted/edition.json").read_text())["document"])
main = next(d for d in inst["documents"] if d.get("main"))
dist = Path("site/dist")
shell = (dist / "read" / main["slot"] / "index.html").read_text()
(dist / "index.html").write_text(shell)
results = json.loads(Path(f"instances/{paper}/alignment/results.json").read_text())["results"]
for address in results:
    (dist / address).mkdir(exist_ok=True)
    (dist / address / "index.html").write_text(shell)
# Companion pages (/<slug>/) open as their own document's first screen.
pages = [d for d in inst["documents"] if not d.get("main") and d.get("slug") and d.get("slot")]
for doc in pages:
    (dist / doc["slug"]).mkdir(exist_ok=True)
    shell_of = dist / "read" / doc["slot"] / "index.html"
    (dist / doc["slug"] / "index.html").write_text((shell_of if shell_of.is_file() else dist / "404.html").read_text())
# An adapted edition's other files: the auxiliary note's PDF with changes marked.
for doc in pages:
    aux = doc.get("aux_pdf")
    if aux:
        (dist / "pdf").mkdir(exist_ok=True)
        shutil.copy(Path(f"instances/{paper}/adapted/{aux['file']}"), dist / "pdf" / aux["name"])
# A page that moved (moved_pages) is served as its new page's shell; the reader then shows the new address.
slugs = {doc["slug"] for doc in pages}
for old, row in inst.get("moved_pages", {}).items():
    (dist / old).mkdir(exist_ok=True)
    (dist / old / "index.html").write_text((dist / row["to"] / "index.html").read_text() if row["to"] in slugs else shell)
print(f"static addresses: / and {len(results)} results and {len(pages)} pages and {len(inst.get('moved_pages', {}))} moved")
PYEOF
# Put back the tracked placeholder that library-instance.mjs replaced.
git checkout -- site/src/instances/library/current.json 2>/dev/null || true

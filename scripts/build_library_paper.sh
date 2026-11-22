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
    if doc.get("adapted") and not shell_of.is_file():
        raise SystemExit(f"{doc['slug']}: missing the adapted edition's pre-rendered opening ({shell_of})")
    (dist / doc["slug"] / "index.html").write_text((shell_of if shell_of.is_file() else dist / "404.html").read_text())
# An adapted edition's other files, each declared in its edition.json as {file, name, label?, bytes,
# sha256} and copied byte for byte after its size and digest are checked: the PDFs (the auxiliary
# note's with changes marked, and the ordinary reading copies of the edition and the note) to pdf/,
# and the TeX overlay and the result-by-result comparison to the edition's own folder, one level
# below the paper root, where the comparison's relative links resolve. The PDF with changes marked
# stays the reader's PDF and the source of its marks (the Vite paperPdfs plugin copies it).
import hashlib
def supplement(doc, entry, where):
    folder = Path(f"instances/{paper}/adapted").resolve()
    source = (folder / entry["file"]).resolve()
    if folder not in source.parents or not source.is_file():
        raise SystemExit(f"{doc['slug']}: declared file {entry['file']!r} is not in {folder}")
    if "/" in entry["name"] or entry["name"].startswith("."):
        raise SystemExit(f"{doc['slug']}: download name {entry['name']!r} is not a plain file name")
    data = source.read_bytes()
    if len(data) != entry["bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
        raise SystemExit(f"{doc['slug']}: {entry['file']} does not match its declared bytes and sha256")
    where.mkdir(parents=True, exist_ok=True)
    (where / entry["name"]).write_bytes(data)
for doc in pages:
    if not doc.get("adapted"):
        continue
    for key in ("aux_pdf", "reading_pdf", "aux_reading_pdf"):
        if doc.get(key):
            supplement(doc, doc[key], dist / "pdf")
    if doc.get("source_overlay"):
        supplement(doc, doc["source_overlay"], dist / doc["slug"])
    for key in ("reading", "data"):
        if (doc.get("result_comparison") or {}).get(key):
            supplement(doc, doc["result_comparison"][key], dist / doc["slug"])
# A page that moved (moved_pages) is served as its new page's shell; the reader then shows the new address.
slugs = {doc["slug"] for doc in pages}
for old, row in inst.get("moved_pages", {}).items():
    (dist / old).mkdir(exist_ok=True)
    (dist / old / "index.html").write_text((dist / row["to"] / "index.html").read_text() if row["to"] in slugs else shell)
# A guide or companion page the library no longer publishes (removed_pages) answers with a stub that
# sends the reader to the paper: it holds none of the page's former text. Its deeper addresses
# (/<old>/@id, /<old>/lean/...) fall to 404.html, whose reader sends them to the paper too.
for old in inst.get("removed_pages", []):
    if old in slugs:
        raise SystemExit(f"removed_pages: {old} is still a page of the paper")
    (dist / old).mkdir(exist_ok=True)
    (dist / old / "index.html").write_text(
        '<!doctype html><meta charset="utf-8"><meta name="robots" content="noindex">'
        # Only the pane's view (v=lean or v=graph) is carried to the paper; no old place is.
        '<script>var v=new URLSearchParams(location.search).get("v");'
        'location.replace("../"+(v==="lean"||v==="graph"?"?v="+v:""))</script>'
        f'<link rel="canonical" href="../"><meta http-equiv="refresh" content="0; url=../">'
        f'<title>{inst["title"]}</title>'
        f'<p><a href="../">{inst["title"]}</a></p>\n')
print(f"static addresses: / and {len(results)} results and {len(pages)} pages and {len(inst.get('moved_pages', {}))} moved and {len(inst.get('removed_pages', []))} removed")
PYEOF
# Every figure the paper's documents reference (an adapted edition's included, while it is staged) is in the build.
"$PY" scripts/check_figures.py "$paper" site/dist
# Put back the tracked placeholder that library-instance.mjs replaced.
git checkout -- site/src/instances/library/current.json 2>/dev/null || true

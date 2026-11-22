#!/bin/sh
# Re-import the Navier–Stokes library instance (instances/navier-stokes/) from its sources:
#   COPY   the checked reading copy of Alpöge and Buckmaster's paper, with paper_ties_held.json and
#          library-data/ (sentence ties, declaration titles and notes, companions, our_lean, ...);
#   PAGES  Proof Reader's papers/ folder at SOURCE_COMMIT: navier-stokes-paper (the paper's page,
#          its PDF and Lean) and the navier-stokes-* pages read for topics, titles and notes.
# The paper is staged by scripts/stage_held_ties.py and converted by scripts/from_proof_reader.py.
# instances/navier-stokes/authored/ (the paper's stated logic), check.args and idle.args are kept.
# Usage (from the repository root):
#   COPY=... PAGES=... scripts/reimport_navier_stokes.sh
# PYTHON and LEAN_EXPOSITION may name a venv's commands; STAGE is a scratch folder (made if absent).
set -eu
: "${COPY:?COPY names the checked reading copy folder (navier-stokes-paper-copy)}"
: "${PAGES:?PAGES names Proof Reader papers/ at SOURCE_COMMIT}"
SOURCE_COMMIT=${SOURCE_COMMIT:-3858afbe00b23dd8bba13ffa41409310b712723d}
STAGE=${STAGE:-build/navier-stokes-stage}
PY=${PYTHON:-python3}
LX=${LEAN_EXPOSITION:-lean-exposition}
CREDIT="Paper and Lean by Levent Alpöge and Tristan Buckmaster, from their repository tristanbuckmaster/navier-stokes at ad53419; their paper thanks Anthropic for supporting the collaboration from which it grew, and states that they used Anthropic's Claude models throughout the work."

# Topics, families, plain titles and reading notes: the first of these pages that has a value wins.
ALSO=""
for x in navier-stokes navier-stokes-digest navier-stokes-part-1 navier-stokes-part-2 navier-stokes-appendix-b \
         navier-stokes-index navier-stokes-routes navier-stokes-route-details navier-stokes-cell-guide \
         navier-stokes-cell-fidelity navier-stokes-certificate-checker navier-stokes-statement-files \
         navier-stokes-cell-reference $(cd "$PAGES" && ls -d navier-stokes-library-*); do
  ALSO="$ALSO --also $PAGES/$x"
done

rm -rf "$STAGE" && mkdir -p "$STAGE"
"$PY" scripts/stage_held_ties.py --copy "$COPY" --page "$PAGES/navier-stokes-paper" $ALSO \
  --out "$STAGE/navier-stokes-paper" --sentences "$COPY/library-data"
"$PY" scripts/from_proof_reader.py "$STAGE/navier-stokes-paper" --paper navier-stokes --out instances/navier-stokes \
  --source-commit "$SOURCE_COMMIT" --pdf "$PAGES/navier-stokes-paper/paper.pdf" --lean-exposition "$LX" --partial \
  --paper-logic instances/navier-stokes/authored/paper-logic.json \
  --companions-index "$COPY/library-data/companions/index.json" \
  --guide "$STAGE/navier-stokes-paper/guide.md" \
  --credit "$CREDIT"
# Topic colours are stored beside each phrases file; recompute them for the re-imported phrases.
(cd site && node scripts/topic-colours.ts)

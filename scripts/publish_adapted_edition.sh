#!/bin/sh
# Publish a paper's adapted edition, once its publication is agreed. Until then the edition is
# converted locally (scripts/adapted_edition.py convert, into instances/<paper>/adapted/, with
# `published: false`) and a build leaves it out, so the live paper does not change.
#
# This turns the flag on, checks the edition's files with the private-source guard, records the
# folder in this repository (a local commit), and publishes the paper to wcook04/library with
# scripts/publish_library.sh, which builds it, runs the guard and the secret scan again, and pushes.
# Usage: scripts/publish_adapted_edition.sh <paper> CHECKOUT   (CHECKOUT: a clone of wcook04/library)
set -eu
paper=$1
pub=$2
PY=${PYTHON:-python3}
edition=instances/$paper/adapted/edition.json
[ -f "$edition" ] || { echo "no adapted edition converted for $paper ($edition)"; exit 2; }
"$PY" scripts/private_guard.py "instances/$paper/adapted"
"$PY" - "$edition" <<'PYEOF'
import json, sys
from pathlib import Path
path = Path(sys.argv[1])
data = json.loads(path.read_text())
data["published"] = True
data["document"]["published"] = True
path.write_text(json.dumps(data, ensure_ascii=False, indent=1) + "\n")
print(f"{path}: published")
PYEOF
git add -f "instances/$paper/adapted"
AIW_ALLOW_RAW_GIT_COMMIT=1 git -c user.name=wcook04 -c user.email=46428721+wcook04@users.noreply.github.com \
  commit -q -m "Publish the adapted edition of $paper

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>" -- "instances/$paper/adapted"
scripts/publish_library.sh "$paper" "$pub"

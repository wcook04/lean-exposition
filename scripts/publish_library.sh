#!/bin/sh
# Build one library paper and publish it to wcook04/library (GitHub Pages from main), replacing
# only that paper's folder and the index. The same steps as .github/workflows/library.yml.
# Usage: scripts/publish_library.sh <paper> CHECKOUT
#        scripts/publish_library.sh --index CHECKOUT   (rebuild only the index, catalog and search data)
#   CHECKOUT is a clone of git@github.com:wcook04/library.git (made if absent).
# LEAN_EXPOSITION and PYTHON may name a venv's commands. Stops before pushing if the build, the
# private-source guard or the secret scan fails.
set -eu
paper=$1
pub=$2
PY=${PYTHON:-python3}
if [ "$paper" != "--index" ]; then
  scripts/build_library_paper.sh "$paper"
  "$PY" scripts/private_guard.py site/dist "instances/$paper"
fi
[ -d "$pub/.git" ] || git clone -q https://github.com/wcook04/library.git "$pub"
git -C "$pub" fetch -q origin 2>/dev/null || true
git -C "$pub" checkout -q main 2>/dev/null || git -C "$pub" checkout -q -b main
git -C "$pub" reset -q --hard origin/main 2>/dev/null || true
if [ "$paper" != "--index" ]; then
  # A paper's frozen editions (<paper>/editions/, published once by their own script, such as
  # scripts/quartic_editions.py) are kept across its republishes.
  kept=""
  if [ -d "$pub/$paper/editions" ]; then kept=$(mktemp -d); mv "$pub/$paper/editions" "$kept/editions"; fi
  rm -rf "${pub:?}/$paper"
  cp -R site/dist "$pub/$paper"
  if [ -n "$kept" ]; then mv "$kept/editions" "$pub/$paper/editions"; rmdir "$kept"; fi
fi
# Papers are the top-level folders; _index/ holds the index's own files.
published=$(cd "$pub" && ls -d */ 2>/dev/null | tr -d / | { grep -v '^_' || true; } | tr '\n' ' ')
"$PY" scripts/build_library_index.py "$pub" $published
"$PY" scripts/private_guard.py "$pub"
if grep -rIlE '(ghp_[A-Za-z0-9]{30,}|github_pat_|sk-[A-Za-z0-9]{32,}|AKIA[0-9A-Z]{16}|-----BEGIN [A-Z ]*PRIVATE KEY)' "$pub" --exclude-dir=.git; then
  echo "secret-shaped string found; not pushing"; exit 3
fi
sha=$(git rev-parse --short HEAD)
cd "$pub"
AIW_ALLOW_RAW_GIT_COMMIT=1 git add --all
if git diff --cached --quiet; then echo "nothing changed"; exit 0; fi
AIW_ALLOW_RAW_GIT_COMMIT=1 git -c user.name=wcook04 -c user.email=46428721+wcook04@users.noreply.github.com \
  commit -q -m "Publish ${paper#--} from lean-exposition $sha

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
git log -1 --oneline
git push -q origin main

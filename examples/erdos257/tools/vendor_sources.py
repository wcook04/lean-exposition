#!/usr/bin/env python3
"""Copy the pinned #257 Lean closure into upstream/ and write source-lock.json.

Inputs are read-only exports of wcook04/plectis-erdos at the pinned commit:

  --export DIR      a `git archive` export holding lean/ (the Lean tree)
  --root-files DIR  LICENSE, REUSE.toml, lean-toolchain, lakefile.toml and
                    lake-manifest.json from the repository root at the same
                    commit (raw.githubusercontent.com bytes)
  --closure FILE    JSON list of lean/... paths: the import closure of every
                    declaration the two evidence-mapped papers cite

The copy is byte for byte; nothing is rewritten. Rerunning with the same inputs
gives the same lock, apart from `acquired_at`, which is passed explicitly.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from pathlib import Path

REPOSITORY = "https://github.com/wcook04/plectis-erdos"
REVISION = "3368d1e69467aec111eb3244843ad3542171ff96"
LEAN_PIN = "436f55ebdafa67e4af0fff79f621c13f2ded12bf"
RAW = f"https://raw.githubusercontent.com/wcook04/plectis-erdos/{REVISION}/"
ROOT_FILES = ("LICENSE", "REUSE.toml", "lean-toolchain", "lakefile.toml", "lake-manifest.json")
HERE = Path(__file__).resolve().parents[1]


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def row(local: str, upstream: str, data: bytes) -> dict:
    return {"path": local, "url": RAW + upstream, "sha256": sha256(data), "bytes": len(data),
            "source": "plectis-erdos", "upstream_path": upstream}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export", type=Path, required=True)
    parser.add_argument("--root-files", type=Path, required=True)
    parser.add_argument("--closure", type=Path, required=True)
    parser.add_argument("--acquired-at", required=True)
    args = parser.parse_args()

    closure = json.loads(args.closure.read_text())
    if len(closure) != len(set(closure)) or not all(p.startswith("lean/") for p in closure):
        raise SystemExit("closure must be distinct lean/... paths")
    files = []
    for name in ROOT_FILES:
        data = (args.root_files / name).read_bytes()
        target = HERE / "upstream" / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        files.append(row(f"upstream/{name}", name, data))
    for upstream in sorted(closure):
        data = (args.export / upstream).read_bytes()
        target = HERE / "upstream" / upstream
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        files.append(row(f"upstream/{upstream}", upstream, data))

    licence = (args.root_files / "LICENSE").read_bytes()
    reuse = (args.root_files / "REUSE.toml").read_bytes()
    lock = {
        "schema_version": "1.0",
        "id": "erdos257",
        "repository": REPOSITORY,
        "revision": REVISION,
        "license": "Apache-2.0",
        "acquired_at": args.acquired_at,
        "lean_roots": ["Erdos249257", "ErdosProblems"],
        "sources": [{
            "id": "plectis-erdos",
            "repository": REPOSITORY,
            "revision": REVISION,
            "license": "Apache-2.0",
            "license_url": RAW + "LICENSE",
        }],
        "files": files,
        "selection": {
            "rule": ("The import closure, inside this repository, of every Lean declaration that "
                     "evidence/paper_evidence.json cites for the short paper "
                     "erdos-257-mersenne-support-subseries and the long record "
                     "erdos257-mersenne-reasoning-surface."),
            "lean_files": len(closure),
            "lean_pin_of_the_evidence_mapping": LEAN_PIN,
            "pin_note": ("The papers' evidence mapping cites Lean at " + LEAN_PIN + ". The files "
                         "under lean/ErdosProblems/Erdos257 and lean/Erdos249257 are byte-identical "
                         "at that commit and at " + REVISION + " (git diff empty)."),
            "toolchain": "leanprover/lean4:v4.29.1",
            "mathlib": "5e932f97dd25535344f80f9dd8da3aab83df0fe6",
            "build": ("The vendored subset is not a complete Lake package: lakefile.toml names "
                      "libraries and source directories that are not copied. Build the whole "
                      "repository at the revision instead."),
        },
        "license_evidence": {
            "root_license": {"path": "upstream/LICENSE", "url": RAW + "LICENSE",
                             "sha256": sha256(licence), "text": "Apache License, Version 2.0"},
            "reuse_toml": {"path": "upstream/REUSE.toml", "url": RAW + "REUSE.toml",
                           "sha256": sha256(reuse),
                           "rule": ("Blanket annotation path [\"**\"]: SPDX-License-Identifier "
                                    "Apache-2.0. Overrides cover listed PDFs and figures "
                                    "(CC-BY-4.0) and one skills directory (MIT-0); no vendored "
                                    "file is among them.")},
            "readme": ("README.md, section 'Citation and licence': code, scripts and documentation "
                       "are Apache-2.0; manuscript sources and PDFs are CC-BY-4.0."),
            "in_file_headers": ("None of the vendored Lean files carries an in-file SPDX header "
                                "(checked by text search); all are covered by the REUSE.toml "
                                "blanket annotation."),
            "manuscripts": ("The three papers are CC-BY-4.0 and are not vendored here; the "
                            "evidence graph binds them by hash as reference-only sources."),
        },
    }
    (HERE / "source-lock.json").write_text(json.dumps(lock, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"files": len(files), "lean_files": len(closure),
                      "bytes": sum(r["bytes"] for r in files)}))


if __name__ == "__main__":
    main()

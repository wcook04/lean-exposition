#!/usr/bin/env python3
"""Validate authored passage annotations against a captured Library edition."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
from shutil import copymode
from tempfile import NamedTemporaryFile


def unique_keys(items):
    result = {}
    for key, value in items:
        if key in result:
            raise ValueError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def authored_pairs(path):
    try:
        phrases = json.loads(path.read_bytes(), object_pairs_hook=unique_keys)
    except ValueError as exc:
        raise ValueError(f"{path}: {exc}") from exc
    if not isinstance(phrases, dict):
        raise ValueError(f"{path}: expected an object keyed by phrase ID")
    pairs = {}
    for phrase, notes in phrases.items():
        if not phrase.strip() or not isinstance(notes, dict) or not notes:
            raise ValueError(f"{path}: expected a nonempty object of Lean declarations for {phrase!r}")
        for name, note in notes.items():
            if not name.strip() or not isinstance(note, str) or not note.strip():
                raise ValueError(f"{path}: expected nonempty annotation text for {phrase!r} / {name!r}")
            pairs[phrase, name] = note
    return pairs


def document_slots(instance, edition):
    config = instance / "instance.json"
    if config.is_file():
        documents = json.loads(config.read_bytes())["documents"]
        slots = {doc["slot"]: doc.get("kind") == "companion" for doc in documents if doc.get("slot")}
    elif (instance / "reader.json").is_file():
        slots = {"short": False}  # The RH paper uses the custom export.
    else:
        raise ValueError(f"{instance}: missing instance or RH reader configuration")
    hidden = set()
    adapted = instance / "adapted/edition.json"
    if adapted.is_file():
        adapt = json.loads(adapted.read_bytes())
        slot = adapt["document"]["slot"]
        if (edition / "docs" / slot).exists():
            slots[slot] = True
        else:
            hidden.add(slot)
    return slots, hidden


def tie_file(edition, slot, companion):
    prefix = f"docs/{slot}/" if companion else ""
    stage = "short" if companion else slot
    index = edition / prefix / "index.json"
    route = f"/ties/{stage}"
    recorded = json.loads(index.read_bytes())["responses"].get(route)
    expected = f"{prefix}ties/{stage}.json"
    if recorded != expected:
        raise ValueError(f"{index}: {route} must name the fixed-path response {expected!r}. Found {recorded!r}.")
    target = edition / expected
    if target.resolve() != target or edition not in target.parents:
        raise ValueError(f"{target}: expected a regular path inside the captured edition")
    return target


def annotated_ties(path, pairs, *, complete):
    raw = path.read_bytes()
    payload = json.loads(raw)
    rows = {}
    for tie in payload["ties"]:
        if "phrase" not in tie:
            continue
        for row in tie.get("rows") or ():
            pair = (tie["phrase"], row["name"])
            if pair in rows and (pair in pairs or complete):
                raise ValueError(f"{path}: ambiguous phrase and Lean declaration {pair!r}")
            rows[pair] = row
    unmatched = pairs.keys() - rows.keys()
    if unmatched:
        raise ValueError(f"{path}: {len(unmatched)} authored pair(s) do not match exported ties, including {min(unmatched)!r}")
    missing = rows.keys() - pairs.keys()
    if complete and missing:
        raise ValueError(f"{path}: {len(missing)} exported pair(s) lack annotations, including {min(missing)!r}")
    changed = False
    for pair, row in rows.items():
        if pair in pairs:
            if row.get("annotation") != pairs[pair]:
                row["annotation"] = pairs[pair]
                changed = True
        elif "annotation" in row:
            del row["annotation"]
            changed = True
    if not changed:
        return None
    if raw.endswith(b"\n"):  # The RH build writes its JSON with a trailing newline.
        return (json.dumps(payload, ensure_ascii=False) + "\n").encode()
    return json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode()


def replace_bytes(path, data):
    with NamedTemporaryFile(dir=path.parent, prefix=f".{path.name}.", delete=False) as stream:
        temporary = Path(stream.name)
        try:
            stream.write(data)
            stream.close()
            copymode(path, temporary)
            os.replace(temporary, path)
        finally:
            temporary.unlink(missing_ok=True)


def apply_annotations(instance: Path, edition: Path, *, write=False, complete=False) -> dict[str, int]:
    """Join this instance's authored pair notes to static ties, or just validate the join."""
    sources = {path.stem: path for path in sorted((instance / "annotations").glob("*.json"))}
    if not sources and not complete:
        return {}
    if write and edition.is_symlink():
        raise ValueError(f"{edition}: write to a local copy of the captured edition")
    edition = edition.resolve()
    slots, hidden = document_slots(instance, edition)
    unknown = sources.keys() - slots.keys() - hidden
    if unknown:
        raise ValueError(f"{instance / 'annotations'}: unknown document slot(s): {', '.join(sorted(unknown))}")
    authored = {slot: authored_pairs(path) for slot, path in sources.items()}
    updates = {}
    counts = {}
    for slot in sorted(slots.keys() if complete else sources.keys() - hidden):
        path = tie_file(edition, slot, slots[slot])
        pairs = authored.get(slot, {})
        data = annotated_ties(path, pairs, complete=complete)
        if data is not None:
            updates[path] = data
        counts[slot] = len(pairs)
    if write:
        for path, data in updates.items():
            replace_bytes(path, data)
    return counts


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("instance", type=Path, help="instance directory containing the authored annotations")
    parser.add_argument("edition", type=Path, help="built edition directory, such as site/dist/edition")
    parser.add_argument("--write", action="store_true", help="write to a local copy after validating all targeted documents")
    parser.add_argument("--complete", action="store_true", help="require an annotation for every exported phrase and Lean declaration pair")
    args = parser.parse_args()
    try:
        counts = apply_annotations(args.instance, args.edition, write=args.write, complete=args.complete)
    except (KeyError, OSError, ValueError) as exc:
        parser.exit(1, f"{exc}\n")
    verb = "Applied" if args.write else "Validated"
    for slot, count in sorted(counts.items()):
        print(f"{verb} {count} passage annotations for {args.instance.name}/{slot}")

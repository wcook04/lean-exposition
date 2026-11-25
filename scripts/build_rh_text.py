"""Project the source-derived Riemann manuscript into the existing paper reader."""

from hashlib import sha256
import json
import re

from lean_exposition.consumer import _byte_span, _paper_sections


def add_text_format(edition, config, addresses, manuscript, binding_file):
    def read(path):
        return json.loads((edition / path).read_bytes())

    def write(path, payload):
        (edition / path).write_text(json.dumps(payload, ensure_ascii=False) + "\n", encoding="utf-8")

    index = read("index.json")
    source = index["proof_source"]
    data = manuscript.read_bytes()
    binding_bytes = binding_file.read_bytes()
    binding = json.loads(binding_bytes)
    digest = sha256(data).hexdigest()
    if (binding["sha256"], binding["paper_revision"]) != (digest, source["paper_revision"]):
        raise ValueError("Riemann text needs bindings from this manuscript and paper revision")
    spans = binding["spans"]
    short = read(index["responses"]["/ties/short"])
    if set(spans) != {tie["phrase"] for tie in short["ties"]} or binding.get("unresolved"):
        raise ValueError("Riemann text must have a source span for every PDF link")
    locations = {}
    long_ties = []
    for tie in short["ties"]:
        start, end = spans[tie["phrase"]]
        if not (0 <= start < end <= len(data)) or not data[start:end].decode().strip():
            raise ValueError(f"Bad source span for {tie['phrase']}")
        at = f"b{start}-{end}"
        row = {**tie, "at": at}
        long_ties.append(row)
        locations[tie["phrase"]] = {"record": row["record"], "at": at}
    canonical = {}
    for record, (i, _, _) in short["canonical"].items():
        canonical[record] = [i, *spans[long_ties[i]["phrase"]]]

    # Every part is a complete Markdown block, and spans remain valid across
    # headings or nested links. Split only between blocks outside a tied range.
    lines = [0, *(m.end() for m in re.finditer(rb"\n", data))]
    paper_ref = f"sha256:{digest}/papers/long.md"
    sections = _paper_sections(data, paper_ref, lines)
    edges = [0, len(data)]
    for section in sections:
        start = section["heading_span"]["start_byte"]
        if data[start-2:start] == b"\n\n" and not any(a < start < b for a, b in spans.values()):
            edges.append(start)
    bibliography = data.find(b"## References ")
    if bibliography >= 0:
        edges.extend(bibliography + m.start() for m in list(re.finditer(rb'(?m)^<a id="ref-', data[bibliography:]))[24::25])
    edges = sorted(set(edges))
    points = sorted(set(edges) | {b for span in spans.values() for b in span})
    segments = []
    ranges = [spans[row["phrase"]] for row in long_ties]
    for a, b in zip(points, points[1:]):
        covering = [i for i, (start, end) in enumerate(ranges) if start <= a < b <= end]
        if covering:
            segments.append([a, b, sorted(covering, key=lambda i: ranges[i][1] - ranges[i][0])])
    ties = {**short, "ties": long_ties, "canonical": canonical, "segments": segments}
    ties_file = "ties/long.json"
    write(ties_file, ties)

    def write_blob(payload):
        encoded = json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()
        filename = sha256(encoded).hexdigest() + ".json"
        (edition / filename).write_bytes(encoded)
        return filename

    stage = "long"
    route = f"/papers/{stage}/structure?representation=reader"
    parts = [
        {"kind": "unmapped_text", "ref": f"{paper_ref}/parts/{a}",
         "segment_ref": f"{paper_ref}/unmapped/{a}", "span": _byte_span(a, b, lines)}
        for a, b in zip(edges, edges[1:])
    ]
    first = read(index["responses"][route])
    binding_hash = sha256(binding_bytes).hexdigest()
    first["bundle"] = {**first["bundle"], "markdown_ref": paper_ref, "markdown_sha256": digest,
                       "mapping_ref": f"sha256:{binding_hash}/passage-ties-text.json",
                       "mapping_sha256": binding_hash}
    first["coverage"]["unmapped_bytes"] = len(data)
    first["meaning"] = "Typeset from the paper's TeX source. Passage links use the same reviewed Lean correspondences as the PDF."
    first["paper"] = {**first["paper"], "byte_length": len(data), "line_count": len(lines),
                      "sections": sections, "document_parts": parts,
                      "unmapped_segments": [{"ref": part["segment_ref"], "span": part["span"]} for part in parts],
                      "outline_links": [{"from": s["parent_ref"], "to": s["ref"], "kind": "subsection",
                                         "semantic_class": "document_outline", "source_ref": paper_ref,
                                         "derived": True} for s in sections if s["parent_ref"]],
                      "reading_order": [{"from": a["ref"], "to": b["ref"], "kind": "next_in_text",
                                         "semantic_class": "document_order", "source_ref": paper_ref,
                                         "derived": True} for a, b in zip(sections, sections[1:])]}
    index["responses"][route] = write_blob(first)
    index["responses"][f"/papers/{stage}/sections"] = write_blob(
        {"items": sections, "total": len(sections), "offset": 0, "limit": 200, "next": None}
    )
    index["responses"][f"/ties/{stage}"] = ties_file
    index["documents"][stage] = f"{digest}.md"
    (edition / index["documents"][stage]).write_bytes(data)
    write("index.json", index)

    main = next(doc for doc in config["documents"] if doc["main"])
    config["text_format"] = stage
    config["documents"].append({
        "id": "typeset-paper", "slot": stage, "slug": "text", "noun": "paper",
        "title": main["title"], "reader": "KaTeX text from the authors’ TeX source.",
    })
    addresses.setdefault("pages", {})["text"] = locations

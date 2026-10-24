"""Read-only views of the existing graph and versioned explanation bundle."""
from __future__ import annotations

import copy
import json
import re
from bisect import bisect_right
from collections import deque
from pathlib import Path
from urllib.parse import quote

from .bundle import STAGES, load_bundle
from .contracts import (
    ARGUMENT_EDGES, LEAN_EDGES, ContractError, closure, decode_json, digest,
    encoded, require_refs, required_citation_ids, select, validate_graph,
)

PAPER_VIEW_VERSION = "0.1.1"
PAPER_QUERY_VERSION = "0.1.1"


# Meanings of projected links, not an additional graph schema or edge authority.
_RELATION_SEMANTICS = {
    "lean_type_dependency": ("lean_syntactic_dependency", "declaration_to_constant_in_elaborated_type", "graph_edge"),
    "lean_value_dependency": ("lean_syntactic_dependency", "declaration_to_constant_in_elaborated_value", "graph_edge"),
    "lean_structural_dependency": ("lean_syntactic_dependency", "declaration_to_structural_reference", "graph_edge"),
    "supports": ("curated_argument_support", "claim_to_recorded_ingredient", "graph_edge"),
    "formalizes": ("formalization_correspondence", "informal_claim_to_formal_declaration", "graph_edge"),
    "cites": ("citation_reference", "citing_node_to_referenced_node", "graph_edge"),
    "platform_decomposition": ("platform_reported_decomposition", "platform_item_to_reported_child", "graph_edge"),
    "assumption_ids": ("explicit_assumption_reference", "node_to_named_assumption", "node_field"),
    "source_id": ("provenance_field_reference", "field_owner_to_source_record", "record_field"),
    "source_ids": ("provenance_field_reference", "evidence_to_source_record", "record_field"),
    "evidence_ids": ("provenance_field_reference", "field_owner_to_evidence_record", "record_field"),
    "citation_ids": ("provenance_field_reference", "node_to_citation_record", "record_field"),
    "subject_ids": ("provenance_field_reference", "evidence_to_subject_node", "record_field"),
    "from": ("edge_endpoint_reference", "edge_record_to_its_stored_from_node", "graph_edge_field"),
    "to": ("edge_endpoint_reference", "edge_record_to_its_stored_to_node", "graph_edge_field"),
    "next_in_text": ("document_order", "earlier_to_next_section_or_passage_start", "markdown_byte_positions"),
    "subsection": ("document_outline", "parent_section_to_child_section", "markdown_heading_levels"),
    "contains_passage": ("document_containment", "enclosing_section_to_passage_block", "markdown_byte_spans"),
    "text_overlap": ("document_overlap", "section_to_passage_with_intersecting_content_bytes", "markdown_byte_spans"),
    "maps_claim": ("passage_correspondence", "passage_to_mapped_claim_or_declaration", "mapping_claim_ids"),
    "maps_citation": ("passage_correspondence", "passage_to_mapped_citation", "mapping_citation_ids"),
    "maps_assumption": ("passage_correspondence", "passage_to_mapped_assumption", "mapping_assumption_ids"),
}


def _relation_semantics(kinds: set[str]) -> dict:
    return {kind: {"semantic_class": _RELATION_SEMANTICS[kind][0],
                   "orientation": _RELATION_SEMANTICS[kind][1],
                   "source": _RELATION_SEMANTICS[kind][2]}
            for kind in sorted(kinds)}


def inspect_graph(graph: dict, goals: list[str] | None = None) -> dict:
    """Describe every record, marking its relationship to the chosen goals.

    Selection changes only this view. Evidence outside the selection stays visible;
    a relevance flag never changes an evidence kind, status or certification claim.
    """
    selected = select(graph, goals) if goals is not None else graph
    summary = validate_graph(selected)
    argument = set(summary["argument_closure"])
    platform = set(summary["platform_closure"])

    def related_evidence(node_ids: set[str], edge_kinds: set[str]) -> set[str]:
        identifiers = {
            evidence_id
            for node in selected["nodes"] if node["id"] in node_ids
            for evidence_id in node["evidence_ids"]
        }
        identifiers.update(
            evidence_id
            for edge in selected["edges"]
            if edge["from"] in node_ids and edge["kind"] in edge_kinds
            for evidence_id in edge["evidence_ids"]
        )
        identifiers.update(
            item["id"] for item in selected["evidence"]
            if node_ids.intersection(item["subject_ids"])
        )
        return identifiers

    argument_evidence = related_evidence(argument, ARGUMENT_EDGES | {"cites"})
    platform_evidence = related_evidence(platform, {"platform_decomposition"})
    result = copy.deepcopy(summary)
    result.update({
        "schema_version": selected["schema_version"],
        "title": selected["title"],
        "scope": selected["scope"],
        "notes": copy.deepcopy(selected["notes"]),
        "nodes": [
            {
                **copy.deepcopy(node),
                "selected": node["id"] in selected["selected_goals"],
                "in_argument_closure": node["id"] in argument,
                "in_platform_closure": node["id"] in platform,
            }
            for node in sorted(selected["nodes"], key=lambda row: row["id"])
        ],
        "edges": copy.deepcopy(sorted(
            selected["edges"], key=lambda row: (row["from"], row["to"], row["kind"])
        )),
        "evidence": [
            {
                **copy.deepcopy(item),
                "relevant_to_argument": item["id"] in argument_evidence,
                "relevant_to_platform": item["id"] in platform_evidence,
            }
            for item in sorted(selected["evidence"], key=lambda row: row["id"])
        ],
        "sources": copy.deepcopy(sorted(selected["sources"], key=lambda row: row["id"])),
        "citations": copy.deepcopy(sorted(selected["citations"], key=lambda row: row["id"])),
    })
    return result


def inspect_bundle(path: Path) -> dict:
    """Inspect one validated capture without extracting ZIP members or reading sources."""
    payload = load_bundle(path)
    manifest = decode_json(payload["manifest.json"])
    graph = decode_json(payload["graph.json"])
    papers = []
    for stage in STAGES:
        mapping = decode_json(payload[f"papers/{stage}.json"])
        papers.append({"mapping_path": f"papers/{stage}.json", **mapping})
    return {
        "schema_version": manifest["schema_version"],
        "bundle_version": manifest["bundle_version"],
        "bundle_id": manifest["bundle_id"],
        "status": manifest["status"],
        "publication": manifest["publication"],
        "manifest_sha256": digest(payload["manifest.json"]),
        "files": copy.deepcopy(manifest["files"]),
        "contract_valid": True,
        "semantic_certification": False,
        "graph": inspect_graph(graph),
        "papers": papers,
        "external_resources": {
            "sources": [
                {**copy.deepcopy(source), "included": False}
                for source in sorted(graph["sources"], key=lambda row: row["id"])
            ],
            "receipts": [
                {
                    "evidence_id": item["id"],
                    "path": item["receipt_path"],
                    "sha256": item["receipt_sha256"],
                    "included": False,
                }
                for item in sorted(graph["evidence"], key=lambda row: row["id"])
                if "receipt_path" in item
            ],
        },
    }


def _view_ref(graph_hash: str, table: str, identity: str) -> str:
    """A snapshot reference, not a claim of identity across revisions."""
    return f"sha256:{graph_hash}/{table}/{quote(identity, safe='')}"


def _view_reach(seeds: set[str], links: list[dict], reverse: bool = False) -> set[str]:
    neighbors: dict[str, set[str]] = {}
    for link in links:
        a, b = link["from"], link["to"]
        if reverse:
            a, b = b, a
        neighbors.setdefault(a, set()).add(b)
    reached, pending = set(), sorted(seeds, reverse=True)
    while pending:
        current = pending.pop()
        if current in reached:
            continue
        reached.add(current)
        pending.extend(sorted(neighbors.get(current, ()), reverse=True))
    return reached


def _view_components(vertices: set[str], links: list[dict]) -> tuple[list, list]:
    """Iterative Kosaraju on the returned relation set; singleton loops count."""
    forward = {v: set() for v in vertices}
    backward = {v: set() for v in vertices}
    for link in links:
        forward[link["from"]].add(link["to"])
        backward[link["to"]].add(link["from"])
    visited, order = set(), []
    for root in sorted(vertices):
        if root in visited:
            continue
        visited.add(root)
        stack = [(root, iter(sorted(forward[root])))]
        while stack:
            current, remaining = stack[-1]
            target = next(remaining, None)
            if target is None:
                order.append(current)
                stack.pop()
            elif target not in visited:
                visited.add(target)
                stack.append((target, iter(sorted(forward[target]))))
    assigned, components, membership = set(), [], {}
    for root in reversed(order):
        if root in assigned:
            continue
        members, pending = set(), [root]
        while pending:
            current = pending.pop()
            if current in assigned:
                continue
            assigned.add(current)
            members.add(current)
            pending.extend(sorted(backward[current], reverse=True))
        identity = "scc:" + digest(encoded({"members": sorted(members)}))
        for member in members:
            membership[member] = identity
        components.append({"id": identity, "members": sorted(members),
                           "cyclic": len(members) > 1, "internal_link_ids": [],
                           "internal_link_kinds": []})
    by_id = {component["id"]: component for component in components}
    between: dict[tuple[str, str], list[dict]] = {}
    for link in links:
        pair = (membership[link["from"]], membership[link["to"]])
        if pair[0] == pair[1]:
            component = by_id[pair[0]]
            component["internal_link_ids"].append(link["id"])
            component["internal_link_kinds"].append(link["kind"])
            component["cyclic"] = True
        else:
            between.setdefault(pair, []).append(link)
    for component in components:
        component["internal_link_ids"].sort()
        component["internal_link_kinds"] = sorted(set(component["internal_link_kinds"]))
    condensation = [{"from": a, "to": b,
                     "link_ids": sorted(link["id"] for link in grouped),
                     "link_kinds": sorted({link["kind"] for link in grouped})}
                    for (a, b), grouped in sorted(between.items())]
    return sorted(components, key=lambda c: c["members"]), condensation


def _byte_span(start: int, end: int, line_starts: list[int]) -> dict:
    """Half-open UTF-8 byte span and inclusive one-based line range."""
    return {"start_byte": start, "end_byte": end,
            "start_line": bisect_right(line_starts, start),
            "end_line": bisect_right(line_starts, max(start, end - 1))}


def _paper_sections(content: bytes, paper_ref: str, line_starts: list[int]) -> list[dict]:
    """ATX outline in source order, excluding YAML front matter and fenced code."""
    headings = []
    fence_char, fence_width, yaml = None, 0, content.startswith((b"---\n", b"---\r"))
    offset = 0
    for line in content.splitlines(keepends=True):
        stripped = line.rstrip(b"\r\n")
        if yaml:
            if offset and stripped in (b"---", b"..."):
                yaml = False
            offset += len(line)
            continue
        fence = re.match(rb"^ {0,3}(`{3,}|~{3,})(.*)$", stripped)
        if fence:
            marker = fence.group(1)
            if fence_char is None:
                fence_char, fence_width = marker[:1], len(marker)
            elif marker[:1] == fence_char and len(marker) >= fence_width and not fence.group(2).strip():
                fence_char, fence_width = None, 0
            offset += len(line)
            continue
        if fence_char is None:
            match = re.match(rb"^ {0,3}(#{1,6})(?:[ \t]+(.*)|[ \t]*)$", stripped)
            if match:
                title = (match.group(2) or b"").strip()
                title = re.sub(rb"[ \t]+#+[ \t]*$", b"", title).decode("utf-8")
                headings.append({"ref": f"{paper_ref}/sections/{offset}",
                                 "level": len(match.group(1)), "title": title,
                                 "heading_span": _byte_span(offset, offset + len(line), line_starts),
                                 "_start": offset})
        offset += len(line)
    stack = []
    for heading in headings:
        while stack and stack[-1]["level"] >= heading["level"]:
            previous = stack.pop()
            previous["span"] = _byte_span(previous["_start"], heading["_start"], line_starts)
        heading["parent_ref"] = stack[-1]["ref"] if stack else None
        stack.append(heading)
    for heading in stack:
        heading["span"] = _byte_span(heading["_start"], len(content), line_starts)
    for heading in headings:
        del heading["_start"]
    return headings


def project_paper(bundle_path: Path, stage: str, passages: list[str] | None = None) -> dict:
    """Project one validated paper and its recorded prerequisite subgraph.

    This is a read-only view of exact bundle bytes, not another graph authority.
    Text order and proof dependence are independent relations.
    """
    if stage not in STAGES:
        raise ContractError("unknown paper stage")
    return _project_paper(load_bundle(bundle_path), stage, passages)


def _project_paper(payload: dict[str, bytes], stage: str, passages: list[str] | None = None) -> dict:
    """Project an already validated capture; callers must not mutate its bytes."""
    manifest = decode_json(payload["manifest.json"])
    graph_bytes = payload["graph.json"]
    graph = decode_json(graph_bytes)
    markdown_name, mapping_name = f"papers/{stage}.md", f"papers/{stage}.json"
    content, mapping_bytes = payload[markdown_name], payload[mapping_name]
    mapping = decode_json(mapping_bytes)
    graph_hash, paper_hash, mapping_hash = map(digest, (graph_bytes, content, mapping_bytes))
    paper_ref = f"sha256:{paper_hash}/{markdown_name}"
    mapping_ref = f"sha256:{mapping_hash}/{mapping_name}"
    if passages is not None and (not isinstance(passages, list)
            or any(not isinstance(anchor, str) or not anchor for anchor in passages)
            or len(passages) != len(set(passages))):
        raise ContractError("passage selection must be a list of distinct anchors")
    available = {row["anchor"] for row in mapping["passages"]}
    if passages is not None and set(passages) - available:
        raise ContractError("unknown paper passage anchor: " + ", ".join(sorted(set(passages) - available)))
    selected = available if passages is None else set(passages)
    # Markdown recognizes LF, CRLF and bare CR. Keep exact source bytes and count
    # each line ending once, so navigation agrees with the outline's splitlines.
    line_starts = [0] + [match.end() for match in re.finditer(rb"\r\n?|\n", content)]
    sections = _paper_sections(content, paper_ref, line_starts)
    paper_passages = []
    for row in mapping["passages"]:
        anchor = row["anchor"]
        opening = f"<!-- passage:{anchor} -->".encode("utf-8")
        closing = f"<!-- /passage:{anchor} -->".encode("utf-8")
        block_start = content.index(opening)
        start = block_start + len(opening)
        end = content.index(closing)
        block_end = end + len(closing)
        enclosing = [section for section in sections
                     if section["span"]["start_byte"] <= block_start
                     and block_end <= section["span"]["end_byte"]]
        row_ref = f"{paper_ref}/{mapping_ref}/passages/{quote(anchor, safe='')}"
        paper_passages.append({
            "ref": row_ref, "anchor": anchor, "selected": anchor in selected,
            "text": content[start:end].decode("utf-8"),
            "content_span": _byte_span(start, end, line_starts),
            "block_span": _byte_span(block_start, block_end, line_starts),
            "section_ref": enclosing[-1]["ref"] if enclosing else None,
            "evidence_class": row["evidence_class"], "rationale": row["rationale"],
            "claim_ids": copy.deepcopy(row["claim_ids"]),
            "citation_ids": copy.deepcopy(row["citation_ids"]),
            "assumption_ids": copy.deepcopy(row["assumption_ids"]),
        })
    paper_passages.sort(key=lambda row: row["block_span"]["start_byte"])
    unmapped = []
    cursor = 0
    for item in paper_passages:
        start, end = item["block_span"]["start_byte"], item["block_span"]["end_byte"]
        if cursor < start:
            unmapped.append({"ref": f"{paper_ref}/unmapped/{cursor}",
                             "text": content[cursor:start].decode("utf-8"),
                             "span": _byte_span(cursor, start, line_starts)})
        cursor = end
    if cursor < len(content):
        unmapped.append({"ref": f"{paper_ref}/unmapped/{cursor}",
                         "text": content[cursor:].decode("utf-8"),
                         "span": _byte_span(cursor, len(content), line_starts)})
    order = sorted([(s["heading_span"]["start_byte"], s["ref"]) for s in sections] +
                   [(p["block_span"]["start_byte"], p["ref"]) for p in paper_passages])
    reading_order = [{"from": left[1], "to": right[1], "kind": "next_in_text",
                      "semantic_class": "document_order", "derived": True,
                      "source_ref": paper_ref}
                     for left, right in zip(order, order[1:])]
    outline_links = ([{"from": s["parent_ref"], "to": s["ref"], "kind": "subsection",
                       "semantic_class": "document_outline", "derived": True,
                       "source_ref": paper_ref}
                      for s in sections if s["parent_ref"]] +
                     [{"from": p["section_ref"], "to": p["ref"], "kind": "contains_passage",
                       "semantic_class": "document_containment", "derived": True,
                       "source_ref": paper_ref}
                      for p in paper_passages if p["section_ref"]])
    section_passage_links = []
    for passage in paper_passages:
        content_span = passage["content_span"]
        for section in sections:
            section_span = section["span"]
            start = max(content_span["start_byte"], section_span["start_byte"])
            end = min(content_span["end_byte"], section_span["end_byte"])
            if start < end:
                section_passage_links.append({
                    "from": section["ref"], "to": passage["ref"],
                    "kind": "text_overlap", "overlap_span": _byte_span(start, end, line_starts),
                    "semantic_class": "document_overlap", "derived": True,
                    "source_ref": paper_ref,
                })

    selected_passages = [p for p in paper_passages if p["selected"]]
    claim_ids = {identifier for p in selected_passages for identifier in p["claim_ids"]}
    assumption_ids = {identifier for p in selected_passages for identifier in p["assumption_ids"]}
    node_ids = closure(graph, sorted(claim_ids | assumption_ids))
    tables = {table: {row["id"]: row for row in graph[table]}
              for table in ("nodes", "citations", "sources", "evidence")}
    ref = lambda table, identity: _view_ref(graph_hash, table, identity)
    argument_links, chosen_edges = [], []
    for edge in graph["edges"]:
        if edge["kind"] not in ARGUMENT_EDGES or edge["from"] not in node_ids or edge["to"] not in node_ids:
            continue
        identity = json.dumps([edge["from"], edge["to"], edge["kind"]],
                              ensure_ascii=False, separators=(",", ":"))
        edge_ref = ref("edges", identity)
        chosen_edges.append({"ref": edge_ref, "record": copy.deepcopy(edge)})
        argument_links.append({"id": edge_ref, "from": ref("nodes", edge["from"]),
                            "to": ref("nodes", edge["to"]), "kind": edge["kind"],
                            "semantic_class": _RELATION_SEMANTICS[edge["kind"]][0],
                            "derived": False, "record_ref": edge_ref})
    for identifier in sorted(node_ids):
        for target in tables["nodes"][identifier]["assumption_ids"]:
            if target in node_ids:
                source_ref, target_ref = ref("nodes", identifier), ref("nodes", target)
                argument_links.append({"id": "field:" + digest(encoded({"from": source_ref,
                                   "to": target_ref, "field": "assumption_ids"})),
                                    "from": source_ref, "to": target_ref,
                                    "kind": "assumption_ids", "derived": True,
                                    "semantic_class": "explicit_assumption_reference",
                                    "owner_ref": source_ref, "source_field": "assumption_ids"})
    citation_ids = {identifier for p in selected_passages for identifier in p["citation_ids"]}
    citation_ids |= required_citation_ids(graph, sorted(claim_ids))
    citation_ids |= {c for n in node_ids for c in tables["nodes"][n]["citation_ids"]}
    evidence_ids = {e for n in node_ids for e in tables["nodes"][n]["evidence_ids"]}
    evidence_ids |= {e for edge in chosen_edges for e in edge["record"]["evidence_ids"]}
    evidence_ids |= {e["id"] for e in graph["evidence"] if node_ids.intersection(e["subject_ids"])}
    source_ids = {tables["nodes"][n]["source_id"] for n in node_ids
                  if "source_id" in tables["nodes"][n]}
    source_ids |= {tables["citations"][c]["source_id"] for c in citation_ids}
    source_ids |= {s for e in evidence_ids for s in tables["evidence"][e]["source_ids"]}
    records = {table: [{"ref": ref(table, identity), "record": copy.deepcopy(tables[table][identity])}
                       for identity in sorted(identifiers)]
               for table, identifiers in (("nodes", node_ids), ("citations", citation_ids),
                                          ("sources", source_ids), ("evidence", evidence_ids))}
    records["edges"] = sorted(chosen_edges, key=lambda row: row["ref"])
    correspondence_links = []
    for passage in selected_passages:
        for field, table, kind in (("claim_ids", "nodes", "maps_claim"),
                                   ("citation_ids", "citations", "maps_citation"),
                                   ("assumption_ids", "nodes", "maps_assumption")):
            correspondence_links.extend({"from": passage["ref"], "to": ref(table, identity),
                                         "kind": kind, "semantic_class": "passage_correspondence",
                                         "derived": True, "source_ref": mapping_ref,
                                         "source_anchor": passage["anchor"], "source_field": field}
                                        for identity in passage[field])
    provenance_links = []
    def field_links(owner_table: str, owner_id: str, field: str, target_table: str, targets):
        owner_ref = ref(owner_table, owner_id)
        provenance_links.extend({"from": owner_ref,
                                 "to": ref(target_table, target), "kind": field,
                                 "semantic_class": _RELATION_SEMANTICS[field][0],
                                 "derived": True, "owner_ref": owner_ref,
                                 "source_field": field}
                                for target in targets)
    for identifier in sorted(node_ids):
        node = tables["nodes"][identifier]
        field_links("nodes", identifier, "evidence_ids", "evidence", node["evidence_ids"])
        field_links("nodes", identifier, "citation_ids", "citations", node["citation_ids"])
        if "source_id" in node:
            field_links("nodes", identifier, "source_id", "sources", [node["source_id"]])
    for identifier in sorted(citation_ids):
        field_links("citations", identifier, "source_id", "sources",
                    [tables["citations"][identifier]["source_id"]])
    for identifier in sorted(evidence_ids):
        evidence = tables["evidence"][identifier]
        field_links("evidence", identifier, "source_ids", "sources", evidence["source_ids"])
        field_links("evidence", identifier, "subject_ids", "nodes",
                    [n for n in evidence["subject_ids"] if n in node_ids])
    for edge in chosen_edges:
        identity = edge["ref"]
        provenance_links.extend({"from": identity, "to": ref("nodes", edge["record"][field]),
                                 "kind": field, "semantic_class": "edge_endpoint_reference",
                                 "derived": True, "owner_ref": identity,
                                 "source_field": field} for field in ("from", "to"))
        provenance_links.extend({"from": identity, "to": ref("evidence", e),
                                 "kind": "evidence_ids", "semantic_class": "provenance_field_reference",
                                 "derived": True, "owner_ref": identity,
                                 "source_field": "evidence_ids"}
                                for e in edge["record"]["evidence_ids"])
    argument_links.sort(key=lambda row: row["id"])
    components, condensation = _view_components({ref("nodes", n) for n in node_ids}, argument_links)
    mapped_bytes = sum(p["content_span"]["end_byte"] - p["content_span"]["start_byte"]
                       for p in paper_passages)
    marker_bytes = sum(p["block_span"]["end_byte"] - p["block_span"]["start_byte"] -
                       p["content_span"]["end_byte"] + p["content_span"]["start_byte"]
                       for p in paper_passages)
    paper_link_kinds = {link["kind"] for group in (reading_order, outline_links,
                        section_passage_links, correspondence_links, argument_links,
                        provenance_links) for link in group}
    return {
        "paper_view_version": PAPER_VIEW_VERSION, "stage": stage, "state": mapping["state"],
        "review_state": mapping["review_state"], "semantic_certification": False,
        "relation_semantics": _relation_semantics(paper_link_kinds),
        "bundle": {"bundle_id": manifest["bundle_id"], "bundle_version": manifest["bundle_version"],
                   "publication": manifest["publication"],
                   "manifest_sha256": digest(payload["manifest.json"]),
                   "manifest_ref": f"sha256:{digest(payload['manifest.json'])}/manifest.json",
                   "graph_sha256": graph_hash, "graph_ref": f"sha256:{graph_hash}/graph.json",
                   "markdown_sha256": paper_hash, "markdown_ref": paper_ref,
                   "mapping_sha256": mapping_hash, "mapping_ref": mapping_ref},
        "selection": {"requested_anchors": copy.deepcopy(passages),
                      "available_anchors": [p["anchor"] for p in paper_passages],
                      "selected_anchors": [p["anchor"] for p in selected_passages],
                      "omitted_by_selector": [p["anchor"] for p in paper_passages if not p["selected"]]},
        "paper": {"path": markdown_name, "text": content.decode("utf-8"),
                  "byte_length": len(content), "line_count": len(content.splitlines()),
                  "sections": sections, "passages": paper_passages,
                  "unmapped_segments": unmapped,
                  "reading_order": reading_order, "outline_links": outline_links,
                  "section_passage_links": section_passage_links},
        "correspondence_links": correspondence_links,
        "graph": {"graph_id": graph["id"], "schema_version": graph["schema_version"],
                  "graph_sha256": graph_hash, "recorded_extraction_status": graph["extraction_status"],
                  "relation_scope": "recorded_argument_relation_reachability",
                  "selected_claim_refs": [ref("nodes", n) for n in sorted(claim_ids)],
                  "selected_assumption_refs": [ref("nodes", n) for n in sorted(assumption_ids)],
                  "records": records, "argument_links": argument_links,
                  "provenance_links": provenance_links, "components": components,
                  "condensation": condensation},
        "coverage": {"mapped_content_bytes": mapped_bytes, "marker_bytes": marker_bytes,
                     "unmapped_bytes": sum(s["span"]["end_byte"] - s["span"]["start_byte"] for s in unmapped),
                     "source_bytes_opened": False, "receipt_bytes_opened": False,
                     "per_root_dependency_completeness": "unknown",
                     "heading_syntax": "ATX headings only; Setext and HTML headings are not parsed",
                     "scope": "Mapped passages are correspondences, not sentence-level formal support. Section-passage overlaps are document structure, not claim or proof implications. Unmapped text and passages omitted by the selector remain in the validated paper. Graph records outside the selected prerequisite closure remain in the bundle and are not asserted absent. Argument links combine recorded Lean references, curated support, formalization correspondence and explicit assumptions; their SCCs describe only that mixed recorded reachability. Reading order and platform decomposition are separate."},
    }


def _query_selector(values, name: str) -> list[str] | None:
    if values is None:
        return None
    if (not isinstance(values, list)
            or any(not isinstance(value, str) or not value for value in values)
            or len(values) != len(set(values))):
        raise ContractError(f"{name} selection must be a list of distinct nonempty strings")
    return sorted(values)


def _argument_adjacency(graph: dict, graph_hash: str) -> dict[str, list[dict]]:
    """Index the existing argument relation for one query, retaining its kinds."""
    ref = lambda identity: _view_ref(graph_hash, "nodes", identity)
    adjacency: dict[str, list[dict]] = {node["id"]: [] for node in graph["nodes"]}
    for edge in graph["edges"]:
        if edge["kind"] not in ARGUMENT_EDGES:
            continue
        identity = json.dumps([edge["from"], edge["to"], edge["kind"]],
                              ensure_ascii=False, separators=(",", ":"))
        edge_ref = _view_ref(graph_hash, "edges", identity)
        adjacency[edge["from"]].append({
            "id": edge_ref, "from": ref(edge["from"]), "to": ref(edge["to"]),
            "from_node_id": edge["from"], "to_node_id": edge["to"],
            "kind": edge["kind"], "semantic_class": _RELATION_SEMANTICS[edge["kind"]][0],
            "derived": False, "record_ref": edge_ref,
        })
    for node in graph["nodes"]:
        for target in node["assumption_ids"]:
            source_ref, target_ref = ref(node["id"]), ref(target)
            adjacency[node["id"]].append({
                "id": "field:" + digest(encoded({"from": source_ref, "to": target_ref,
                                                 "field": "assumption_ids"})),
                "from": source_ref, "to": target_ref,
                "from_node_id": node["id"], "to_node_id": target,
                "kind": "assumption_ids", "semantic_class": "explicit_assumption_reference",
                "derived": True, "owner_ref": source_ref, "source_field": "assumption_ids",
            })
    for links in adjacency.values():
        links.sort(key=lambda link: (link["to_node_id"], link["kind"], link["id"]))
    return adjacency


def _witness_tree(adjacency: dict[str, list[dict]], roots: set[str]) -> dict[str, tuple]:
    """Deterministic shortest recorded paths, including cycles without recursion."""
    paths = {root: (root, None) for root in sorted(roots)}
    pending = deque(sorted(roots))
    while pending:
        node = pending.popleft()
        for link in adjacency[node]:
            target = link["to_node_id"]
            if target not in paths:
                paths[target] = (paths[node][0], link)
                pending.append(target)
    return paths


def _query_witness(target: str, paths: dict[str, tuple], graph_hash: str,
                   root_field: str) -> dict:
    current, links = target, []
    root = paths[target][0]
    while paths[current][1] is not None:
        link = paths[current][1]
        links.append(copy.deepcopy(link))
        current = link["from_node_id"]
    links.reverse()
    return {"root_node_id": root, "root_ref": _view_ref(graph_hash, "nodes", root),
            "root_mapping_field": root_field, "target_node_id": target,
            "target_ref": _view_ref(graph_hash, "nodes", target),
            "links": links, "relation_scope": "recorded_argument_relation_reachability",
            "semantic_certification": False}


def query_papers(
    bundle_path: Path, *, stage: str | None = None,
    passages: list[str] | None = None, section_refs: list[str] | None = None,
    node_ids: list[str] | None = None, relation: str = "direct",
    expected_manifest_sha256: str | None = None,
) -> dict:
    """Query passage correspondence in one validated bundle capture.

    Selectors are unions within a family and intersections between families.
    Sections select complete passages by non-whitespace content overlap. ``direct``
    matches claim/assumption fields; ``prerequisites`` also follows the existing
    argument relation. Neither search infers an unstored relation or acceptance.
    The result is derived data, with no new persistent authority or bundle member.
    An expected manifest digest pins the request to one exact validated edition.
    """
    if stage is not None and (not isinstance(stage, str) or stage not in STAGES):
        raise ContractError("unknown paper stage")
    passages = _query_selector(passages, "passage")
    section_refs = _query_selector(section_refs, "section")
    node_ids = _query_selector(node_ids, "node")
    if stage is None and (passages is not None or section_refs is not None):
        raise ContractError("passage and section selectors require one paper stage")
    if not isinstance(relation, str) or relation not in {"direct", "prerequisites"}:
        raise ContractError("unknown paper query relation")
    if expected_manifest_sha256 is not None and (
            not isinstance(expected_manifest_sha256, str)
            or re.fullmatch(r"[0-9a-f]{64}", expected_manifest_sha256) is None):
        raise ContractError("expected manifest SHA-256 must be 64 lowercase hexadecimal characters")
    payload = load_bundle(bundle_path)
    manifest = decode_json(payload["manifest.json"])
    graph = decode_json(payload["graph.json"])
    graph_hash, manifest_hash = digest(payload["graph.json"]), digest(payload["manifest.json"])
    if expected_manifest_sha256 is not None and expected_manifest_sha256 != manifest_hash:
        raise ContractError("bundle manifest SHA-256 differs from the requested edition")
    nodes = {row["id"]: row for row in graph["nodes"]}
    if node_ids is not None:
        require_refs(node_ids, nodes, "paper query node")
    adjacency = _argument_adjacency(graph, graph_hash)
    query = {"stage": stage, "passages": passages, "section_refs": section_refs,
             "node_ids": node_ids, "relation": relation,
             "combination": "union_within_family_intersection_between_families",
             "section_policy": "whole_passage_on_nonwhitespace_content_overlap"}
    papers = []
    stages = [stage] if stage is not None else list(STAGES)
    for paper_stage in stages:
        full = _project_paper(payload, paper_stage)
        available_passages = {p["anchor"] for p in full["paper"]["passages"]}
        sections = {s["ref"]: s for s in full["paper"]["sections"]}
        if passages is not None:
            require_refs(passages, available_passages, "paper passage anchor")
        if section_refs is not None:
            require_refs(section_refs, sections, "paper section reference (exact Markdown edition required)")
        matches = []
        for passage in full["paper"]["passages"]:
            if passages is not None and passage["anchor"] not in passages:
                continue
            overlaps = [link for link in full["paper"]["section_passage_links"]
                        if link["to"] == passage["ref"]
                        and section_refs is not None and link["from"] in section_refs
                        and full["paper"]["text"].encode("utf-8")[
                            link["overlap_span"]["start_byte"]:link["overlap_span"]["end_byte"]
                        ].decode("utf-8").strip()]
            if section_refs is not None and not overlaps:
                continue
            claim_seeds, assumption_seeds = set(passage["claim_ids"]), set(passage["assumption_ids"])
            direct = claim_seeds | assumption_seeds
            paths = _witness_tree(adjacency, direct) if relation == "prerequisites" else {}
            candidates = direct if relation == "direct" else set(paths)
            matched_ids = sorted(candidates.intersection(node_ids)) if node_ids is not None else []
            if node_ids is not None and not matched_ids:
                continue
            witnesses = []
            for target in matched_ids:
                if relation == "direct":
                    field = "claim_ids" if target in claim_seeds else "assumption_ids"
                    witness_paths = {target: (target, None)}
                else:
                    field = "claim_ids" if paths[target][0] in claim_seeds else "assumption_ids"
                    witness_paths = paths
                witnesses.append(_query_witness(target, witness_paths, graph_hash, field))
            content_span = passage["content_span"]
            covered_until = content_span["start_byte"]
            for link in sorted(overlaps, key=lambda item: item["overlap_span"]["start_byte"]):
                span = link["overlap_span"]
                if span["start_byte"] > covered_until:
                    break
                covered_until = max(covered_until, span["end_byte"])
            crosses = section_refs is not None and covered_until < content_span["end_byte"]
            matches.append({
                "stage": paper_stage, "anchor": passage["anchor"], "passage_ref": passage["ref"],
                "evidence_class": passage["evidence_class"],
                "matched_node_ids": matched_ids,
                "direct_claim_ids": sorted(claim_seeds),
                "direct_assumption_ids": sorted(assumption_seeds),
                "section_overlaps": copy.deepcopy(overlaps),
                "whole_passage_extends_beyond_selected_sections": crosses,
                "witnesses": witnesses,
            })
        selected = [match["anchor"] for match in matches]
        view = _project_paper(payload, paper_stage, selected)
        selected_passages = [p for p in view["paper"]["passages"] if p["selected"]]
        claims = {n for p in selected_passages for n in p["claim_ids"]}
        assumptions = {n for p in selected_passages for n in p["assumption_ids"]}
        paths = _witness_tree(adjacency, claims | assumptions)
        required = set(paths)
        prerequisite_only = required - claims
        boundary_witnesses = []
        for target in sorted(prerequisite_only):
            field = "claim_ids" if paths[target][0] in claims else "assumption_ids"
            boundary_witnesses.append(_query_witness(target, paths, graph_hash, field))
        boundary = {
            "mapped_claim_ids": sorted(claims), "mapped_assumption_ids": sorted(assumptions),
            "seed_node_ids": sorted(claims | assumptions),
            "retained_node_ids": sorted(required),
            "not_mapped_as_claim_ids": sorted(prerequisite_only),
            "required_assumption_ids": sorted(n for n in required if nodes[n]["kind"] == "assumption"),
            "unresolved_node_ids": sorted(n for n in required if nodes[n]["status"] in
                                          {"open", "unverified", "external", "conditional"}),
            "outside_closure_node_ids": sorted(set(nodes) - required),
            "recorded_boundaries": [{"node_id": n, "ref": _view_ref(graph_hash, "nodes", n),
                                      "text": nodes[n]["boundary"]}
                                     for n in sorted(required) if "boundary" in nodes[n]],
            "witnesses": boundary_witnesses,
            "meaning": "Not mapped as a claim means absent from the selected passages' claim_ids, not absent from their prose. Explicit assumption references and all recorded prerequisites are retained. No sentence-level explanation coverage is inferred.",
        }
        papers.append({"stage": paper_stage, "matches": matches,
                       "selected_section_refs": section_refs if section_refs is not None else [],
                       "support_boundary": boundary, "view": view})
    return {
        "paper_query_version": PAPER_QUERY_VERSION, "query": query,
        "snapshot": {"bundle_id": manifest["bundle_id"], "bundle_version": manifest["bundle_version"],
                     "manifest_sha256": manifest_hash, "graph_sha256": graph_hash},
        "cache_key": f"paper-query-v{PAPER_QUERY_VERSION}:" + digest(encoded({"manifest_sha256": manifest_hash,
                                                            "query": query})),
        "match_count": sum(len(paper["matches"]) for paper in papers),
        "papers": papers,
        "relation_semantics": _relation_semantics(ARGUMENT_EDGES | {"assumption_ids"}),
        "coverage": {
            "recorded_extraction_status": graph["extraction_status"],
            "stored_traversal_exhausted": True, "query_truncated": False,
            "per_root_dependency_completeness": "unknown",
            "source_bytes_opened": False, "receipt_bytes_opened": False,
            "empty_result_meaning": "No matching recorded passage correspondence. An unmapped section may contain mathematics; zero matches do not establish independence or absence of a prerequisite.",
            "scope": "One validated bundle capture. Direct matches use claim_ids and assumption_ids only. Prerequisite matches follow stored Lean, support, formalization and explicit assumption links, retaining each kind; citations, document order and platform decomposition never become premises. Witnesses show one deterministic shortest recorded path, not a proof or complete explanation.",
        },
        "semantic_certification": False,
    }


def project_graph(
    graph_bytes: bytes, view: str, roots: list[str] | None = None, *,
    direction: str = "prerequisites", include_assumptions: bool = False,
) -> dict:
    """Project recorded relations without mutating graph or receipt authority.

    Snapshot references bind the exact supplied bytes. Coverage and statuses are
    reported, never upgraded. This view does not fetch source or receipt files.
    """
    kinds = {"declarations": LEAN_EDGES, "arguments": {"supports", "formalizes"},
             "citations": {"cites"}, "platform": {"platform_decomposition"},
             "provenance": set()}
    provenance_kinds = {"source_id", "source_ids", "evidence_ids", "citation_ids",
                        "assumption_ids", "subject_ids", "from", "to"}
    if not isinstance(view, str) or view not in kinds:
        raise ContractError("unknown graph view")
    if not isinstance(direction, str) or direction not in {"prerequisites", "consumers"}:
        raise ContractError("unknown traversal direction")
    if direction == "consumers" and view in {"citations", "provenance"}:
        raise ContractError("reverse traversal is not defined for this view")
    if type(include_assumptions) is not bool:
        raise ContractError("include_assumptions must be a boolean")
    if include_assumptions and view not in {"declarations", "arguments"}:
        raise ContractError("explicit assumption traversal belongs to declaration or argument views")
    if not isinstance(graph_bytes, bytes):
        raise ContractError("graph view requires exact graph bytes")
    graph = decode_json(graph_bytes)
    validate_graph(graph)
    graph_hash = digest(graph_bytes)
    tables = {name: {row["id"]: row for row in graph[name]}
              for name in ("nodes", "sources", "citations", "evidence")}
    chosen = graph["selected_goals"] if roots is None else roots
    if (not isinstance(chosen, list) or not chosen
            or any(not isinstance(r, str) or not r for r in chosen)
            or len(set(chosen)) != len(chosen)):
        raise ContractError("view roots must be a nonempty list of distinct node IDs")
    require_refs(chosen, tables["nodes"], "view root")
    if view == "declarations" and any(
        tables["nodes"][r]["kind"] not in {"declaration", "assumption"} for r in chosen
    ):
        raise ContractError("declaration view roots must be declarations or assumptions; choose the formalized declaration explicitly")
    ref = lambda table, identity: _view_ref(graph_hash, table, identity)
    edge_rows = {}
    for edge in graph["edges"]:
        identity = json.dumps([edge["from"], edge["to"], edge["kind"]],
                              ensure_ascii=False, separators=(",", ":"))
        edge_rows[identity] = edge
    tables["edges"] = edge_rows
    links = []

    def field_link(table, identity, field, target_table, target):
        a, b = ref(table, identity), ref(target_table, target)
        key = digest(encoded({"from": a, "to": b, "field": field}))
        links.append({"id": "field:" + key, "from": a, "to": b,
                      "kind": field, "semantic_class": _RELATION_SEMANTICS[field][0],
                      "derived": True, "owner_ref": a, "source_field": field})

    seed_node_ids = set(chosen)
    if view == "citations":
        seed_node_ids = closure(graph, chosen)
    seeds = {ref("nodes", identity) for identity in seed_node_ids}
    if view == "provenance":
        for identity, node in tables["nodes"].items():
            if "source_id" in node:
                field_link("nodes", identity, "source_id", "sources", node["source_id"])
            for field, target_table in (("evidence_ids", "evidence"),
                                        ("citation_ids", "citations"),
                                        ("assumption_ids", "nodes")):
                for target in node[field]:
                    field_link("nodes", identity, field, target_table, target)
        for identity, citation in tables["citations"].items():
            field_link("citations", identity, "source_id", "sources", citation["source_id"])
        for identity, evidence in tables["evidence"].items():
            if set(chosen).intersection(evidence["subject_ids"]):
                seeds.add(ref("evidence", identity))
            for field, target_table in (("subject_ids", "nodes"), ("source_ids", "sources")):
                for target in evidence[field]:
                    field_link("evidence", identity, field, target_table, target)
        for identity, edge in edge_rows.items():
            if edge["from"] in chosen or edge["to"] in chosen:
                seeds.add(ref("edges", identity))
            for field in ("from", "to"):
                field_link("edges", identity, field, "nodes", edge[field])
            for target in edge["evidence_ids"]:
                field_link("edges", identity, "evidence_ids", "evidence", target)
    else:
        for identity, edge in edge_rows.items():
            if edge["kind"] in kinds[view]:
                links.append({"id": ref("edges", identity),
                              "from": ref("nodes", edge["from"]),
                              "to": ref("nodes", edge["to"]),
                              "kind": edge["kind"],
                              "semantic_class": _RELATION_SEMANTICS[edge["kind"]][0],
                              "derived": False,
                              "record_ref": ref("edges", identity)})
        if include_assumptions:
            for identity, node in tables["nodes"].items():
                for target in node["assumption_ids"]:
                    field_link("nodes", identity, "assumption_ids", "nodes", target)
    reached = _view_reach(seeds, links, direction == "consumers")
    links = sorted((link for link in links
                    if link["from"] in reached and link["to"] in reached), key=lambda l: l["id"])
    visible = {table: {identity for identity in rows if ref(table, identity) in reached}
               for table, rows in tables.items()}
    link_ids = {link["id"] for link in links}
    visible["edges"].update(identity for identity, edge in edge_rows.items()
                            if ref("edges", identity) in link_ids)
    node_ids = visible["nodes"]
    relevant_evidence = set(visible["evidence"])
    relevant_evidence.update(e for n in node_ids for e in tables["nodes"][n]["evidence_ids"])
    relevant_evidence.update(e for n in visible["edges"] for e in edge_rows[n]["evidence_ids"])
    relevant_evidence.update(e["id"] for e in graph["evidence"]
                             if node_ids.intersection(e["subject_ids"]))
    visible["citations"].update(c for n in node_ids for c in tables["nodes"][n]["citation_ids"])
    visible["sources"].update(tables["nodes"][n]["source_id"] for n in node_ids
                              if "source_id" in tables["nodes"][n])
    visible["sources"].update(tables["citations"][c]["source_id"] for c in visible["citations"])
    visible["sources"].update(s for e in relevant_evidence for s in tables["evidence"][e]["source_ids"])
    visible["evidence"] = set(tables["evidence"])
    records = {table: [{"ref": ref(table, identity), "record": copy.deepcopy(rows[identity]),
                        **({"relevant": identity in relevant_evidence} if table == "evidence" else {})}
                       for identity in sorted(visible[table])]
               for table, rows in tables.items()}
    components, condensation = _view_components(reached, links)
    platform_fields = ("platform_closure_status", "local_verification", "assumption_audit",
                       "limits", "omissions", "hidden_relations")
    observations = [{"evidence_id": e["id"], "status": e["status"],
                     "relevant": e["id"] in relevant_evidence,
                     "recorded": {k: copy.deepcopy(e.get("receipt", {})[k])
                                  for k in platform_fields if k in e.get("receipt", {})}}
                    for e in sorted(graph["evidence"], key=lambda e: e["id"])
                    if e["kind"] == "platform_observation"]
    described_kinds = (provenance_kinds if view == "provenance" else
                       kinds[view] | ({"assumption_ids"} if include_assumptions else set()))
    return {
        "view_version": "0.1.0", "view": view,
        "relation_scope": "recorded_relation_reachability",
        "relation_semantics": _relation_semantics(described_kinds),
        "graph_id": graph["id"], "graph_schema_version": graph["schema_version"],
        "graph_sha256": graph_hash, "selected_goals": copy.deepcopy(graph["selected_goals"]),
        "requested_roots": list(chosen), "seed_node_ids": sorted(seed_node_ids),
        "seed_record_refs": sorted(seeds), "selected_record_refs": sorted(reached),
        "traversal": {"direction": direction, "edge_kinds": sorted(kinds[view]),
                      "include_assumptions": include_assumptions,
                      "citation_seeds": "argument_closure" if view == "citations" else None,
                      "provenance_edge_seeds": "edges incident to requested roots" if view == "provenance" else None,
                      "provenance_evidence_seeds": "evidence with a requested root as subject" if view == "provenance" else None,
                      "recorded_from_to": True,
                      "orientation_by_kind": {kind: _RELATION_SEMANTICS[kind][1]
                                              for kind in sorted(described_kinds)}},
        "records": records, "links": links, "components": components,
        "condensation": condensation,
        "coverage": {
            "recorded_extraction_status": graph["extraction_status"],
            "stored_traversal_exhausted": True,
            "query_truncated": False,
            "per_root_dependency_completeness": "unknown",
            "claim": "Reachability in recorded relations only; completeness beyond them is not established.",
            "output_scope": "selected_record_refs and links define traversal; supplementary or off-selection evidence may reference original graph records not returned. This output is not self-contained graph JSON.",
            "empty_result_meaning": "No recorded relation in this view; not a proof of independence.",
            "boundaries": [{"node_id": n, "text": tables["nodes"][n]["boundary"]}
                           for n in sorted(node_ids) if "boundary" in tables["nodes"][n]],
            "platform_observations": observations,
            "platform_grouping": "union_for_navigation; group membership unavailable from graph edges",
            "source_bytes_opened": False,
            "locator_semantics": "Recorded free-text navigation hint; coordinates are not checked by this view.",
        },
        "semantic_certification": False,
    }

// A derived transport for the reading website, captured by export-static.py.
// This supports the site's requests; it does not advertise a replacement API.
import type { Snapshot } from "./types";

type Row = Record<string, any>;
export interface StaticIndex {
  version: number;
  api_version: string;
  snapshot: Snapshot;
  responses: Record<string, string>;
  documents: Record<string, string>;
  search: string;
  /** Whole-edition files, in version 1 editions only. */
  records?: string;
  summaries?: string;
  /** Per-table files; version 1 editions may have only the whole-edition files. */
  records_by_table?: Record<string, string>;
  summaries_by_table?: Record<string, string>;
  /** Route to a file of `key -> response file`, loaded when that route is first asked for. */
  route_maps?: Record<string, string>;
}
export interface SearchIndex {
  rows: Row[];
  casefold: Record<string, string>;
  whitespace: string;
}
const root = `${import.meta.env.BASE_URL}edition/`;
const files = new Map<string, Promise<any>>();
function load<T>(name: string): Promise<T> {
  let value = files.get(name);
  if (!value) {
    value = fetch(root + name).then((r) => {
      if (!r.ok) throw new Error(`Could not load the captured edition (${r.status}).`);
      return r.json();
    }).catch((error) => { files.delete(name); throw error; });
    files.set(name, value);
  }
  return value;
}
function key(route: string, params: URLSearchParams): string {
  const sorted = new URLSearchParams(params);
  sorted.sort();
  return route + (sorted.size ? `?${sorted}` : "");
}
function page(items: Row[], params: URLSearchParams, route: string, manifest: string): Row {
  const offset = Number(params.get("offset") ?? 0), limit = Number(params.get("limit") ?? 50);
  if (!Number.isInteger(offset) || offset < 0 || !Number.isInteger(limit) || limit < 1 || limit > 200) {
    throw new Error("Invalid captured-edition page.");
  }
  const next = new URLSearchParams({ manifest });
  for (const [name, value] of params) if (!["manifest", "offset", "limit"].includes(name)) next.append(name, value);
  next.set("offset", String(offset + limit)); next.set("limit", String(limit));
  return { items: items.slice(offset, offset + limit), total: items.length, offset, limit,
    next: offset + limit < items.length ? `/api/v1${route}?${next}` : null };
}

export function search(index: SearchIndex, params: URLSearchParams, manifest: string): Row {
  const fold = (text: string) => Array.from(text, (c) => index.casefold[c] ?? c).join("");
  const q = params.get("q") ?? "";
  const tokens = fold(q).split(new RegExp(`[${index.whitespace}]+`, "u")).filter(Boolean);
  if (!tokens.length || tokens.length > 16 || Array.from(q).length > 256) throw new Error("Invalid search.");
  const rows = index.rows.filter((row) => (!params.has("table") || row.table === params.get("table")) &&
    (!params.has("paper") || row.papers.includes(params.get("paper"))) &&
    tokens.every((token) => fold(row.text).includes(token)));
  const result = page(rows, params, "/search", manifest);
  result.items = result.items.map((row: Row) => {
    const points = Array.from(row.text as string), folded = fold(row.text);
    const boundaries = [0];
    for (const point of points) boundaries.push(boundaries.at(-1)! + Array.from(fold(point)).length);
    const matches = tokens.map((term) => {
      const start = Array.from(folded.slice(0, folded.indexOf(term))).length;
      let left = 0, right = 0;
      while (left + 1 < boundaries.length && boundaries[left + 1] <= start) left++;
      while (right < boundaries.length && boundaries[right] < start + Array.from(term).length) right++;
      return { term, start_character: left, end_character: right };
    });
    const start = Math.min(Math.max(0, Math.min(...matches.map((m) => m.start_character)) - 80), Math.max(0, points.length - 280));
    const { text: _text, ...rest } = row;
    return { ...rest, excerpt: points.slice(start, start + 280).join(""), excerpt_truncated: points.length > 280,
      excerpt_start_character: start, matches,
      match_coordinates: "Unicode code-point offsets in indexed text, not UTF-8 manuscript bytes" };
  });
  return { ...result, matching: "literal_casefolded_AND", ranking: "table_then_exact_ref" };
}

export function selectionMatches(data: Row, structure: Row, bytes: Uint8Array, start: number, end: number): Row {
  if (!Number.isInteger(start) || !Number.isInteger(end) || start < 0 || start >= end || end > bytes.length ||
      [start, end].some((i) => i < bytes.length && (bytes[i] & 0xc0) === 0x80)) throw new Error("Invalid UTF-8 selection.");
  const spans = new Map<string, Row>(structure.paper.passages.map((p: Row) => [p.anchor, p.content_span]));
  const decoder = new TextDecoder();
  // The inspector consumes whole-passage matches and coverage, not a support
  // projection. Never reuse an unfiltered support boundary for a selection.
  return { coverage: data.coverage, papers: data.papers.map((paper: Row) => ({ stage: paper.stage,
    matches: paper.matches.flatMap((match: Row) => {
      const span = spans.get(match.anchor)!;
      const left = Math.max(start, span.start_byte), right = Math.min(end, span.end_byte);
      if (left >= right || !decoder.decode(bytes.slice(left, right)).trim()) return [];
      return [{ ...match, byte_overlaps: [{ requested_range: { start_byte: start, end_byte: end },
        overlap_span: { start_byte: left, end_byte: right } }],
        whole_passage_extends_beyond_selected_ranges: left > span.start_byte || right < span.end_byte }];
    }) })) };
}

const documentsLoaded = new Map<string, Promise<Uint8Array>>();
function documentFile(name: string): Promise<Uint8Array> {
  let value = documentsLoaded.get(name);
  if (!value) {
    value = fetch(root + name).then((r) => {
      if (!r.ok) throw new Error(`Could not load the captured edition (${r.status}).`);
      return r.arrayBuffer();
    }).then((buffer) => new Uint8Array(buffer)).catch((error) => { documentsLoaded.delete(name); throw error; });
    documentsLoaded.set(name, value);
  }
  return value;
}

/** Passage text is exported once, as the paper; restore it to the server's record response. */
async function withPassageText(index: StaticIndex, data: Row): Promise<Row> {
  const passages: Row[] | undefined = data.aligned_passages;
  if (!passages?.some((passage) => passage.text === undefined)) return data;
  const decoder = new TextDecoder();
  const restored = await Promise.all(passages.map(async (passage) => {
    const bytes = await documentFile(index.documents[passage.stage]);
    return { ...passage, text: decoder.decode(bytes.slice(passage.span.start_byte, passage.span.end_byte)) };
  }));
  return { ...data, aligned_passages: restored };
}

/** The response file for a key: the startup index first, then its route's own map. */
async function responseFile(index: StaticIndex, route: string, name: string): Promise<string | undefined> {
  const file = index.responses[name];
  if (file) return file;
  const map = index.route_maps?.[route];
  return map ? (await load<Record<string, string>>(map))[name] : undefined;
}

/** Every record of the selected tables, from per-table files where the edition has them. */
async function loadRecords(index: StaticIndex, summary: boolean, table: string | null): Promise<Row[]> {
  const tableFiles = summary ? index.summaries_by_table : index.records_by_table;
  if (tableFiles && table && Object.hasOwn(tableFiles, table)) return load<Row[]>(tableFiles[table]);
  const whole = summary ? index.summaries : index.records;
  if (whole) {
    const all = await load<Record<string, Row[]>>(whole);
    return table ? all[table] ?? [] : Object.values(all).flat();
  }
  if (table || !tableFiles) return [];
  return (await Promise.all(Object.values(tableFiles).map((file) => load<Row[]>(file)))).flat();
}

export async function staticRequest(url: string): Promise<Response> {
  const index = await load<StaticIndex>("index.json");
  if (index.version !== 1 && index.version !== 2) throw new Error("Unsupported captured-edition format.");
  const request = new URL(url, window.location.origin);
  const route = request.pathname.replace(/^\/api\/v1/, "");
  const params = new URLSearchParams(request.search);
  const pin = params.get("manifest"); params.delete("manifest");
  const envelope = (data: Row) => Response.json({ api_version: index.api_version, snapshot: index.snapshot, data });
  if (pin && pin !== index.snapshot.manifest_sha256) {
    return Response.json({ error: { code: "edition_mismatch", message: "Reload to open the published edition." } }, { status: 409 });
  }
  const document = route.match(/^\/papers\/([^/]+)\/document$/);
  if (document && index.documents[document[1]]) return fetch(root + index.documents[document[1]]);
  if (route === "/search") return envelope(search(await load<SearchIndex>(index.search), params, index.snapshot.manifest_sha256));
  if (route === "/records") {
    const summary = params.get("representation") === "summary";
    const refs = params.getAll("ref"), table = params.get("table");
    const records = await loadRecords(index, summary, table);
    const rows = records.filter((row) => !refs.length || refs.includes(row.ref))
      .sort((a, b) => a.ref < b.ref ? -1 : a.ref > b.ref ? 1 : 0);
    return envelope(page(rows, params, route, index.snapshot.manifest_sha256));
  }
  if (route === "/papers/query" && params.has("start") && params.has("end")) {
    const stage = params.get("paper")!;
    const matchParams = new URLSearchParams({ paper: stage, representation: "matches" });
    const [data, structure, document] = await Promise.all([
      load<Row>((await responseFile(index, route, key(route, matchParams)))!),
      load<Row>(index.responses[`/papers/${stage}/structure?representation=reader`] ?? index.responses[`/papers/${stage}/structure`]),
      fetch(root + index.documents[stage]).then((r) => r.arrayBuffer()),
    ]);
    return envelope(selectionMatches(data, structure, new Uint8Array(document), Number(params.get("start")), Number(params.get("end"))));
  }
  const normalized = new URLSearchParams(params);
  normalized.delete("offset"); normalized.delete("limit");
  // Older captured editions retain the complete structure at the original
  // route; a new reader can still open them without the optional projection.
  const readerStructure = /^\/papers\/(long|short|expository)\/structure$/.test(route)
    && normalized.size === 1 && normalized.get("representation") === "reader";
  const file = await responseFile(index, route, key(route, normalized)) ?? (readerStructure ? index.responses[route] : undefined);
  if (!file) return Response.json({ error: { code: "not_found", message: "This request is not part of the captured reading website." } }, { status: 404 });
  const data = await withPassageText(index, await load<Row>(file));
  return envelope(Array.isArray(data.items) && "total" in data ? { ...data, ...page(data.items, params, route, index.snapshot.manifest_sha256) } : data);
}

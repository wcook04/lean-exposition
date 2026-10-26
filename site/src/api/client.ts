// A small client for the read-only lean-exposition web API.
//
// Every request after discovery carries the manifest pin of the edition the
// reader opened, so a server restarted on a new edition answers 409 rather
// than silently mixing editions. Pinned links returned by the API are followed
// as given. Responses are cached in memory for the session; the browser's own
// HTTP cache revalidates them with the server's ETags.

import type { ApiErrorBody, Discovery, Envelope, Snapshot } from "./types";

const API_ORIGIN: string = (import.meta.env.VITE_API_ORIGIN as string | undefined) ?? "";
const API_BASE = "/api/v1";

export class ApiError extends Error {
  readonly status: number;
  readonly code: string;
  readonly url: string;
  constructor(status: number, code: string, message: string, url: string) {
    super(message);
    this.status = status;
    this.code = code;
    this.url = url;
  }
}

export class EditionChangedError extends ApiError {}

type Params = Record<string, string | number | boolean | readonly string[] | undefined | null>;

const listeners = new Set<(error: EditionChangedError) => void>();

/** Subscribe to the moment the server stops serving the pinned edition. */
export function onEditionChanged(listener: (error: EditionChangedError) => void): () => void {
  listeners.add(listener);
  return () => listeners.delete(listener);
}

let pin: Snapshot | null = null;
let discovery: Discovery | null = null;
const cache = new Map<string, Promise<unknown>>();

export function snapshot(): Snapshot {
  if (!pin) throw new Error("The API edition has not been opened yet.");
  return pin;
}

export function discoveryInfo(): Discovery | null {
  return discovery;
}

function absolute(pathOrHref: string): string {
  if (/^https?:\/\//.test(pathOrHref)) return pathOrHref;
  return API_ORIGIN + pathOrHref;
}

function withParams(path: string, params: Params = {}, pinned = true): string {
  const query = new URLSearchParams();
  if (pinned && pin && !("manifest" in params)) query.set("manifest", pin.manifest_sha256);
  for (const [key, value] of Object.entries(params)) {
    if (value === undefined || value === null) continue;
    if (Array.isArray(value)) value.forEach((v) => query.append(key, v));
    else query.set(key, String(value));
  }
  const text = query.toString();
  return `${API_BASE}${path}${text ? `?${text}` : ""}`;
}

async function request(url: string, init?: RequestInit): Promise<Response> {
  let response: Response;
  try {
    response = await fetch(absolute(url), { headers: { Accept: "application/json" }, ...init });
  } catch (cause) {
    throw new ApiError(0, "network", "The reading server could not be reached.", url);
  }
  if (!response.ok) {
    let code = `http_${response.status}`;
    let message = response.statusText || "Request failed";
    try {
      const body = (await response.json()) as ApiErrorBody;
      code = body.error.code;
      message = body.error.message;
    } catch {
      /* The error body was not JSON; keep the HTTP status. */
    }
    if (response.status === 409) {
      const error = new EditionChangedError(409, code, message, url);
      listeners.forEach((listener) => listener(error));
      throw error;
    }
    throw new ApiError(response.status, code, message, url);
  }
  return response;
}

async function json<T>(url: string, signal?: AbortSignal): Promise<Envelope<T>> {
  const response = await request(url, { signal });
  return (await response.json()) as Envelope<T>;
}

/** Open the edition the server currently serves and pin it for this session. */
export async function openEdition(): Promise<{ snapshot: Snapshot; discovery: Discovery }> {
  const envelope = await json<Discovery>(withParams("", {}, false));
  pin = envelope.snapshot;
  discovery = envelope.data;
  return { snapshot: envelope.snapshot, discovery: envelope.data };
}

/** GET a route under /api/v1 with the edition pin; cached for the session. */
export function get<T>(path: string, params: Params = {}): Promise<Envelope<T>> {
  return follow<T>(withParams(path, params));
}

/** Follow a pinned href returned by the API. */
export function follow<T>(href: string): Promise<Envelope<T>> {
  const hit = cache.get(href);
  if (hit) return hit as Promise<Envelope<T>>;
  const pending = json<T>(href).catch((error: unknown) => {
    cache.delete(href);
    throw error;
  });
  cache.set(href, pending);
  return pending;
}

/** GET without caching, for queries the reader types (search). */
export function query<T>(path: string, params: Params, signal?: AbortSignal): Promise<Envelope<T>> {
  return json<T>(withParams(path, params), signal);
}

/** Append extra parameters to a pinned href returned by the API. */
export function extend(href: string, params: Params): string {
  const [path, existing = ""] = href.split("?");
  const query = new URLSearchParams(existing);
  for (const [key, value] of Object.entries(params)) {
    if (value === undefined || value === null) continue;
    if (Array.isArray(value)) value.forEach((v) => query.append(key, v));
    else query.set(key, String(value));
  }
  return `${path}?${query.toString()}`;
}

const documents = new Map<string, Promise<Uint8Array>>();

/** The exact captured Markdown bytes of a paper. */
export function documentBytes(stage: string): Promise<Uint8Array> {
  const url = withParams(`/papers/${stage}/document`);
  const hit = documents.get(url);
  if (hit) return hit;
  const pending = request(url, { headers: { Accept: "text/markdown, text/plain" } })
    .then((response) => response.arrayBuffer())
    .then((buffer) => new Uint8Array(buffer))
    .catch((error: unknown) => {
      documents.delete(url);
      throw error;
    });
  documents.set(url, pending);
  return pending;
}

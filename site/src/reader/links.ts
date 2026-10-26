// Link classification and local companion resolution.
//
// Rule (docs/web-api.md, "Resolve captured companion links"): a relative href
// is resolved against the current document's logical directory with POSIX
// normalisation; it resolves only when the result exactly equals one declared
// logical path. Query strings are never silently dropped (they leave the link
// unresolved), parent components may not escape the logical root, and no stage
// is guessed from file names.

export type LinkTarget =
  | { kind: "fragment"; href: string }
  | { kind: "external"; href: string }
  | { kind: "mailto"; href: string }
  | { kind: "companion"; stage: string; fragment: string; href: string }
  | { kind: "unresolved"; original: string; reason: string }
  | { kind: "blocked"; original: string };

const SCHEME = /^([a-z][a-z0-9+.-]*):/i;

function safeDecode(s: string): string {
  try {
    return decodeURIComponent(s);
  } catch {
    return s;
  }
}

/** Normalise a POSIX path; returns null if it escapes the root or is absolute. */
export function normalizePosix(path: string): string | null {
  if (path.startsWith("/")) return null;
  const out: string[] = [];
  for (const seg of path.split("/")) {
    if (seg === "" || seg === ".") continue;
    if (seg === "..") {
      if (out.length === 0) return null;
      out.pop();
    } else out.push(seg);
  }
  return out.join("/");
}

function dirOf(path: string): string {
  const i = path.lastIndexOf("/");
  return i < 0 ? "" : path.slice(0, i + 1);
}

export function classifyHref(
  href: string,
  documentPath: string,
  documentPaths: Record<string, string>,
): LinkTarget {
  const raw = href.trim();
  if (raw.startsWith("#")) return { kind: "fragment", href: raw };
  const scheme = SCHEME.exec(raw);
  if (scheme) {
    const s = scheme[1].toLowerCase();
    if (s === "http" || s === "https") return { kind: "external", href: raw };
    if (s === "mailto") return { kind: "mailto", href: raw };
    return { kind: "blocked", original: raw };
  }
  if (raw.startsWith("//")) return { kind: "blocked", original: raw };
  if (raw.includes("\\")) return { kind: "unresolved", original: raw, reason: "backslash" };

  const hashAt = raw.indexOf("#");
  const beforeHash = hashAt < 0 ? raw : raw.slice(0, hashAt);
  const fragment = hashAt < 0 ? "" : safeDecode(raw.slice(hashAt + 1));
  if (beforeHash.includes("?")) return { kind: "unresolved", original: raw, reason: "query" };
  if (beforeHash === "") return { kind: "fragment", href: raw };

  const joined = normalizePosix(dirOf(documentPath) + safeDecode(beforeHash));
  if (joined === null) return { kind: "unresolved", original: raw, reason: "outside-root" };
  for (const [stage, declared] of Object.entries(documentPaths)) {
    if (declared === joined) {
      const target = `/read/${encodeURIComponent(stage)}` + (fragment ? `#${encodeURIComponent(fragment)}` : "");
      return { kind: "companion", stage, fragment, href: target };
    }
  }
  return { kind: "unresolved", original: raw, reason: "undeclared" };
}

/** Prefix every declared path, e.g. for documents written one directory above the bundle. */
export function prefixPaths(paths: Record<string, string>, prefix: string): Record<string, string> {
  const out: Record<string, string> = {};
  for (const [k, v] of Object.entries(paths)) out[k] = prefix + v;
  return out;
}

// The table of runs on the What ran page, read at build time from the graph's evidence
// records and the receipt files they name (receipt_path). Each row says what ran, where,
// at which commit, when, with what outcome, and what that shows and does not show. Failed,
// cancelled and unavailable runs are rows like any other. Nothing is inferred: a field the
// record or receipt does not give is null, and the page shows a dash.
//
// Pure functions over parsed JSON, so tests run them on a fixture; vite.config.ts reads the
// files and publishes each receipt under verification/. The receipt shapes are documented in
// src/instances/erdos257/README.md.

export type RunType = "github_actions_run" | "comparator_receipt" | "evidence";

export interface RunRow {
  /** The evidence record's id, or for a receipt listed in an index, the index's id and the entry. */
  id: string;
  /** The evidence record's kind of check. */
  kind: string;
  type: RunType;
  /** passed, failed, unavailable or not_run: the evidence record's own, or a listed receipt's. */
  status: string;
  /** What ran: a workflow's name, a Comparator entry, or the record's tool. */
  what: string;
  /** Where it ran. */
  where: { label: string; url: string | null } | null;
  commit: { sha: string; url: string | null } | null;
  /** "23 September 2026", and a sortable key. */
  date: string | null;
  dateKey: string | null;
  /** The outcome in the receipt's own terms, in words: "success", "accepted by both kernels". */
  outcome: string;
  shows: string | null;
  doesNotShow: string | null;
  /** The receipt's path under the site's base, when one is published. */
  receipt: string | null;
  /** Exact log lines for declarations named in an upstream report, by edition record id. */
  targetLinks?: Record<string, string>;
  /** Comparator only. */
  entry?: string;
  theorems?: string[];
  kernels?: string[];
  axioms?: string[];
}

export interface RunGroup {
  type: RunType;
  title: string;
  rows: RunRow[];
  counts: Record<string, number>;
}

export interface RunLedger {
  groups: RunGroup[];
  /** Receipt files an evidence record names that were not found; the build warns about each. */
  missing: string[];
}

export interface EvidenceInput {
  id: string;
  kind: string;
  status: string;
  tool?: string;
  details?: string;
  command?: string[];
  receipt_path?: string;
}

const MONTHS = ["January", "February", "March", "April", "May", "June", "July", "August", "September", "October", "November", "December"];

export function dateWords(iso: string | null | undefined): { text: string; key: string } | null {
  const m = typeof iso === "string" ? /^(\d{4})-(\d{2})-(\d{2})/.exec(iso) : null;
  if (!m) return null;
  const month = Number(m[2]);
  if (month < 1 || month > 12) return null;
  return { text: `${Number(m[3])} ${MONTHS[month - 1]} ${m[1]}`, key: iso!.slice(0, 19) };
}

const str = (value: unknown): string | null => (typeof value === "string" && value.trim() ? value : typeof value === "number" ? String(value) : null);
const strings = (value: unknown): string[] => (Array.isArray(value) ? value.filter((item): item is string => typeof item === "string") : []);

/** GitHub's conclusion for a run, as an outcome of the site's four. */
export function conclusionStatus(conclusion: string | null): string {
  if (conclusion === "success") return "passed";
  if (conclusion === "failure" || conclusion === "startup_failure") return "failed";
  if (conclusion === "cancelled" || conclusion === "timed_out" || conclusion === "skipped" || conclusion === "action_required" || conclusion === "stale" || conclusion === "unavailable") return "unavailable";
  return "not_run";
}

const CONCLUSION_WORDS: Record<string, string> = {
  success: "succeeded",
  failure: "failed",
  startup_failure: "failed to start",
  cancelled: "was cancelled",
  timed_out: "timed out",
  skipped: "was skipped",
  action_required: "waited for approval and did not run",
  stale: "went stale and did not run",
  unavailable: "could not be read back from GitHub",
};

const repoUrl = (repository: string | null) => (repository && /^[\w.-]+\/[\w.-]+$/.test(repository) ? `https://github.com/${repository}` : null);

function actionsRow(evidence: EvidenceInput, receipt: Record<string, unknown>, published: string | null): RunRow {
  const repository = str(receipt.repository);
  const runId = str(receipt.run_id);
  const url = str(receipt.url) ?? (repoUrl(repository) && runId ? `${repoUrl(repository)}/actions/runs/${runId}` : null);
  const sha = str(receipt.commit);
  const date = dateWords(str(receipt.completed_at) ?? str(receipt.started_at) ?? str(receipt.date));
  const conclusion = str(receipt.conclusion);
  const attempt = str(receipt.run_attempt);
  return {
    id: evidence.id,
    kind: evidence.kind,
    type: "github_actions_run",
    status: evidence.status,
    what: str(receipt.workflow) ?? evidence.tool ?? evidence.id,
    where: repository || runId ? { label: [repository, runId ? `run ${runId}${attempt && attempt !== "1" ? `, attempt ${attempt}` : ""}` : null].filter(Boolean).join(", "), url } : null,
    commit: sha ? { sha, url: repoUrl(repository) ? `${repoUrl(repository)}/commit/${sha}` : null } : null,
    date: date?.text ?? null,
    dateKey: date?.key ?? null,
    outcome: conclusion ? `The run ${CONCLUSION_WORDS[conclusion] ?? conclusion}` : "GitHub's conclusion is not recorded",
    shows: str(receipt.shows),
    doesNotShow: str(receipt.does_not_show),
    receipt: published,
  };
}

const KERNEL_NAMES: Record<string, string> = { lean_default: "Lean’s default kernel", nanoda: "nanoda" };

/** A Comparator receipt: the generic shape, or a Palomar replay receipt (schema palomar_replay_receipt_v1). */
function comparatorRow(id: string, evidence: EvidenceInput, receipt: Record<string, unknown>, published: string | null, status: string): RunRow {
  const github = (receipt.github ?? receipt.run ?? {}) as Record<string, unknown>;
  const repository = str(github.repository);
  const runId = str(github.run_id);
  const url = str(github.url) ?? (repoUrl(repository) && runId ? `${repoUrl(repository)}/actions/runs/${runId}` : null);
  const sha = str(github.sha) ?? str(github.commit);
  const date = dateWords(str(receipt.generated_at) ?? str(github.date) ?? str(receipt.date));
  const entry = str(receipt.entry) ?? str(receipt.entry_id) ?? id;
  const pairs = Array.isArray(receipt.theorem_pairs)
    ? (receipt.theorem_pairs as Record<string, unknown>[]).map((pair) => str(pair.challenge) ?? str(pair.solution) ?? "").filter(Boolean)
    : strings(receipt.theorem_names);
  const acceptance = (receipt.kernel_acceptance ?? {}) as Record<string, unknown>;
  const kernels = Array.isArray(receipt.kernels) ? strings(receipt.kernels) : Object.keys(acceptance).map((k) => KERNEL_NAMES[k] ?? k);
  const accepted = Object.entries(acceptance).filter(([, ok]) => ok === true).map(([k]) => KERNEL_NAMES[k] ?? k);
  const refused = Object.entries(acceptance).filter(([, ok]) => ok === false).map(([k]) => KERNEL_NAMES[k] ?? k);
  const verification = (receipt.verification ?? {}) as Record<string, unknown>;
  const outcomeRaw = str(receipt.outcome) ?? str(verification.outcome);
  const stage = str(verification.failure_stage);
  const axioms = strings(receipt.axioms).length ? strings(receipt.axioms) : strings(receipt.permitted_axioms);
  const list = (items: string[]) => (items.length < 2 ? items.join("") : `${items.slice(0, -1).join(", ")} and ${items[items.length - 1]}`);
  const outcome = [
    outcomeRaw ? `Comparator ${outcomeRaw === "passed" || outcomeRaw === "accepted" ? "accepted" : outcomeRaw === "failed" || outcomeRaw === "rejected" ? "rejected" : `reported “${outcomeRaw}” for`} ${pairs.length === 1 ? "the theorem" : `the ${pairs.length} theorems`}` : "Comparator's outcome is not recorded",
    accepted.length ? `; accepted by ${list(accepted)}` : "",
    refused.length ? `; refused by ${list(refused)}` : "",
    stage ? `; stopped at ${stage.replace(/_/g, " ")}` : "",
  ].join("");
  return {
    id,
    kind: evidence.kind,
    type: "comparator_receipt",
    status,
    what: `Comparator, ${entry}`,
    where: repository || runId ? { label: [repository, runId ? `run ${runId}` : null].filter(Boolean).join(", "), url } : null,
    commit: sha ? { sha, url: repoUrl(repository) ? `${repoUrl(repository)}/commit/${sha}` : null } : null,
    date: date?.text ?? null,
    dateKey: date?.key ?? null,
    outcome,
    shows:
      str(receipt.shows) ??
      `That each solution proof proves the challenge statement of the same name${kernels.length ? `, checked by ${list(kernels)}` : ""}${axioms.length ? `, using no axioms beyond ${list(axioms)}` : ""}.`,
    doesNotShow: str(receipt.does_not_show) ?? "Whether the challenge statements say what the papers say. That is the comparison on each step.",
    receipt: published,
    entry,
    theorems: pairs,
    kernels,
    axioms,
  };
}

function evidenceRow(evidence: EvidenceInput, published: string | null): RunRow {
  const date = dateWords(/\b\d{4}-\d{2}-\d{2}(?:T[\d:.]+)?/.exec(evidence.details ?? "")?.[0]);
  return {
    id: evidence.id,
    kind: evidence.kind,
    type: "evidence",
    status: evidence.status,
    what: evidence.tool || evidence.id,
    where: null,
    commit: null,
    date: date?.text ?? null,
    dateKey: date?.key ?? null,
    outcome: evidence.command?.length ? `\`${evidence.command.join(" ")}\`` : "",
    shows: null,
    doesNotShow: null,
    receipt: published,
  };
}

/** An observed upstream run with links to its pinned source logs. */
function upstreamRow(evidence: EvidenceInput, receipt: Record<string, unknown>, published: string | null): RunRow {
  const label = str(receipt.where);
  const repository = str(receipt.repository)?.match(/^https:\/\/github\.com\/([\w.-]+\/[\w.-]+)$/)?.[1] ?? null;
  const repo = repoUrl(repository);
  const sha = str(receipt.commit);
  const source = repo && sha ? `${repo}/blob/${sha}/` : null;
  const logs = Array.isArray(receipt.logs) ? receipt.logs.map((log) => str(log?.url)).filter((url): url is string => Boolean(source && url?.startsWith(source))) : [];
  const targetLinks = Array.isArray(receipt.targets) ? Object.fromEntries(receipt.targets.flatMap((target) => {
    const id = str(target?.record);
    const url = str(target?.url);
    return id && url && /^.+#L\d+$/.test(url) && logs.includes(url.split("#")[0]) ? [[id, url]] : [];
  })) : undefined;
  const date = dateWords(str(receipt.date));
  return {
    ...evidenceRow(evidence, published),
    where: label ? { label, url: logs[0] ?? null } : null,
    commit: sha ? { sha, url: repo ? `${repo}/commit/${sha}` : null } : null,
    date: date?.text ?? null,
    dateKey: date?.key ?? null,
    outcome: str(receipt.outcome) ?? "",
    shows: str(receipt.shows),
    doesNotShow: str(receipt.does_not_show),
    targetLinks,
  };
}

/** The status a listed receipt gives itself, as one of the site's four outcomes. */
function receiptStatus(receipt: Record<string, unknown>): string {
  const verification = (receipt.verification ?? {}) as Record<string, unknown>;
  const outcome = str(receipt.outcome) ?? str(verification.outcome) ?? str(receipt.status);
  if (outcome === "passed" || outcome === "accepted") return "passed";
  if (outcome === "failed" || outcome === "rejected") return "failed";
  if (outcome === "unavailable" || outcome === "error" || outcome === "timed_out" || outcome === "cancelled") return "unavailable";
  return "not_run";
}

const RUN_KINDS = new Set(["lean_build", "comparator", "extraction"]);

const GROUP_TITLES: Record<RunType, string> = {
  github_actions_run: "GitHub Actions runs",
  comparator_receipt: "Comparator receipts",
  evidence: "Other run records",
};

/**
 * The ledger. `read(path)` returns a receipt's parsed JSON by its path relative to the
 * example folder, or null when the file is absent; `publish(path)` gives its address on
 * the site. An evidence record with no receipt still has a row, from its own fields.
 */
export function buildRunLedger(
  evidence: readonly EvidenceInput[],
  read: (path: string) => unknown,
  publish: (path: string) => string = (path) => `verification/${path.replace(/^verification\//, "")}`,
): RunLedger {
  const rows: RunRow[] = [];
  const missing: string[] = [];
  const parentOf = (path: string) => path.slice(0, path.lastIndexOf("/") + 1);
  for (const record of evidence) {
    // Runs only: a record with a receipt, or a build, Comparator or extraction record. Hash
    // comparisons and written reviews are listed by kind on the same page.
    if (!record.receipt_path && !RUN_KINDS.has(record.kind)) continue;
    const path = record.receipt_path ?? null;
    const receipt = path ? (read(path) as Record<string, unknown> | null) : null;
    if (path && !receipt) missing.push(path);
    const published = path && receipt ? publish(path) : null;
    if (!receipt || typeof receipt !== "object") {
      rows.push(evidenceRow(record, published));
      continue;
    }
    if (receipt.record_type === "receipt_index") {
      // One evidence record for many receipts: each listed file is a row of its own.
      for (const listed of strings(receipt.receipts)) {
        const at = parentOf(path!) + listed;
        const body = read(at) as Record<string, unknown> | null;
        if (!body) {
          missing.push(at);
          continue;
        }
        rows.push(comparatorRow(`${record.id}:${str(body.entry) ?? str(body.entry_id) ?? listed}`, record, body, publish(at), receiptStatus(body)));
      }
      continue;
    }
    if (receipt.record_type === "github_actions_run") rows.push(actionsRow(record, receipt, published));
    else if (receipt.record_type === "comparator_receipt" || receipt.schema === "palomar_replay_receipt_v1") rows.push(comparatorRow(record.id, record, receipt, published, record.status));
    else if (receipt.record_type === "upstream_run_observation") rows.push(upstreamRow(record, receipt, published));
    else rows.push(evidenceRow(record, published));
  }
  const order: RunType[] = ["github_actions_run", "comparator_receipt", "evidence"];
  const groups = order
    .map((type) => {
      const list = rows.filter((row) => row.type === type).sort((a, b) => (a.dateKey ?? "9").localeCompare(b.dateKey ?? "9") || a.id.localeCompare(b.id));
      const counts: Record<string, number> = {};
      for (const row of list) counts[row.status] = (counts[row.status] ?? 0) + 1;
      return { type, title: GROUP_TITLES[type], rows: list, counts };
    })
    .filter((group) => group.rows.length);
  return { groups, missing };
}

/** Over this many rows, a group shows one summary row with its counts and an expandable list. */
export const SUMMARY_OVER = 8;

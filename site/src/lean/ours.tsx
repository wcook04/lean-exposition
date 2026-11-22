// Our own Lean statements, shown beside the authors' declaration on a phrase's card. They were
// written and proved by this reader's maintainer from the authors' Lean library; they are not the
// authors' Lean, and every block says so in words and in its own style (lean/ours.css).
// Data: a library paper's ours.json (site/scripts/library-instance.mjs), loaded once, on demand.

import { useEffect, useState } from "react";
import site from "@instance/site";
import { noteHtml } from "../reader/page/PhraseCard";
import { isFidelity, phraseVerdict } from "../compare/fidelityWords";
import { libraryChecks, type LaterCheck } from "../app/libraryAddress";
import "./ours.css";

interface OurDeclaration {
  title: string;
  summary?: string;
  note?: string;
  source: string;
  file: string;
  status?: { compiled?: string; axioms?: string[]; comparator?: string };
}
interface Ours {
  declarations: Record<string, OurDeclaration>;
  byPhrase: Record<string, { lean: string; fidelity: string; note: string }[]>;
  /** Forms stated but not yet proved, each with what a proof still needs (open_targets.json). */
  openTargets?: Record<string, { title: string; missing: string; of?: string[] }>;
}

/** The namespace a Lean name sits in, its first segment: Theorem11 for Theorem11.theorem11Space. */
const namespaceOf = (name: string) => name.split(".")[0];

/** The premise a statement is conditional on, when its own words say so ("Conditional on the profile premise"). */
function conditionOf(decl: OurDeclaration | undefined): string | null {
  const m = `${decl?.summary ?? ""} ${decl?.source ?? ""}`.match(/Conditional on the ([a-z ]+? premise)/);
  return m ? `Conditional on the ${m[1]}` : null;
}

let loading: Promise<Ours | null> | null = null;
/** The statements once they have arrived (undefined until then), so a card mounted later has them in its first render. */
let arrived: Ours | null | undefined = site.library ? undefined : null;

/** Whether our statements have arrived (or there are none to wait for). */
export const oursArrived = () => arrived !== undefined;

export function loadOurs(): Promise<Ours | null> {
  if (!site.library) return Promise.resolve(null);
  loading ??= fetch(`${import.meta.env.BASE_URL}ours.json`)
    .then((r) => (r.ok ? (r.json() as Promise<Ours>) : null))
    .catch(() => null)
    .then((data: Ours | null) => (arrived = data));
  return loading;
}

const REPOSITORY = "https://github.com/wcook04/proof-reader/blob/main/";
const RUNS = "https://github.com/wcook04/proof-reader/actions/runs/";

/** An accepted Comparator verdict ("accepted: … run 44961961637 …"): the run that judged it, or null. */
function acceptedRun(comparator: string | undefined): string | null {
  if (!comparator?.startsWith("accepted")) return null;
  return comparator.match(/run (\d{6,})/)?.[1] ?? "";
}

/** A pull request named "owner/repo#N", as its address. */
function pullHref(pr: string): string | null {
  const m = pr.match(/^([\w.-]+\/[\w.-]+)#(\d+)$/);
  return m ? `https://github.com/${m[1]}/pull/${m[2]}` : null;
}

/** Our statements compared with this phrase, each as a block of its own, under the authors' card. */
export function OurStatements({ phrase }: { phrase: string | undefined }) {
  const [ours, setOurs] = useState<Ours | null>(() => arrived ?? null);
  useEffect(() => {
    if (arrived !== undefined) return setOurs(arrived);
    let live = true;
    if (phrase) void loadOurs().then((data) => live && setOurs(data));
    return () => {
      live = false;
    };
  }, [phrase]);
  const rows = phrase ? (ours?.byPhrase[phrase] ?? []) : [];
  if (!rows.length) return null;
  // The forms of the same results that are stated but not yet proved, once, after our statements.
  // A target names the statements it would complete (`of`); one without that list goes with its namespace.
  const leans = new Set(rows.map((row) => row.lean));
  const spaces = new Set(rows.map((row) => namespaceOf(row.lean)));
  const open = Object.entries(ours?.openTargets ?? {}).filter(([name, target]) =>
    target.of ? target.of.some((lean) => leans.has(lean)) : spaces.has(namespaceOf(name)));
  return (
    <>
      {rows.map((row, i) => {
        const decl = ours!.declarations[row.lean];
        const verdict = isFidelity(row.fidelity) ? phraseVerdict(row.fidelity) : null;
        const run = acceptedRun(decl?.status?.comparator);
        const condition = conditionOf(decl);
        return (
          <section key={`${row.lean}:${i}`} className="ours" aria-label="Our statement, proved from the authors' Lean library">
            <p className="ours__badge">Our statement, proved from the authors' Lean library. Not the authors' Lean.</p>
            <h4 className="ours__title">
              {decl?.title ?? row.lean} <code className="ours__name">{row.lean}</code>
            </h4>
            {run !== null && (
              <p className="ours__checked">
                {run ? (
                  <a href={`${RUNS}${run}`} target="_blank" rel="noopener">Checked by Comparator against its statement</a>
                ) : (
                  "Checked by Comparator against its statement"
                )}
              </p>
            )}
            {condition && <p className="ours__condition">{condition}</p>}
            {verdict && (
              <p className="ours__fidelity">
                <strong>{verdict}</strong>: <span dangerouslySetInnerHTML={{ __html: noteHtml(row.note).html }} /> <span className="ours__who">AI-assessed</span>
              </p>
            )}
            {decl?.summary && <p className="ours__summary" dangerouslySetInnerHTML={{ __html: noteHtml(decl.summary).html }} />}
            {decl && (
              <details className="ours__more">
                <summary>Its Lean, and how it was checked</summary>
                {decl.note && <p dangerouslySetInnerHTML={{ __html: noteHtml(decl.note).html }} />}
                <pre className="ours__source"><code>{decl.source}</code></pre>
                <p className="ours__status">
                  In <a href={`${REPOSITORY}${decl.file}`} target="_blank" rel="noopener">wcook04/proof-reader, {decl.file}</a>.
                  {decl.status?.compiled && <> Compiled on {decl.status.compiled}.</>}
                  {decl.status?.axioms?.length ? <> Axioms: {decl.status.axioms.join(", ")}.</> : null}
                  {decl.status?.comparator && (run !== null
                    ? <> Comparator: {decl.status.comparator.replace(/^accepted:\s*/, "")}.</>
                    : <> Comparator: {decl.status.comparator}.</>)}
                </p>
              </details>
            )}
          </section>
        );
      })}
      {open.length > 0 && (
        <section className="ours ours--open" aria-label="Not yet formalized">
          <p className="ours__badge">Not yet formalized</p>
          <ul className="ours__open">
            {open.map(([name, target]) => (
              <li key={name}>
                <strong>{target.title.replace(/^Open:\s*/, "")}.</strong>{" "}
                Missing: <span dangerouslySetInnerHTML={{ __html: noteHtml(target.missing).html }} />
              </li>
            ))}
          </ul>
        </section>
      )}
    </>
  );
}

/**
 * A later check on a passage or a Lean card that mentions what it concerns: the question a reader
 * may ask, our answer, and the runs and pull request behind it. Ours, not the authors'.
 */
export function LaterCheckNote({ check }: { check: LaterCheck }) {
  const pr = check.pr ? pullHref(check.pr) : null;
  return (
    <aside className="later-check" data-check={check.constant}>
      <p className="later-check__badge">Checked since</p>
      <p className="later-check__question">{check.question}</p>
      <p className="later-check__answer">{check.answer}</p>
      {(check.runs?.length || pr) && (
        <p className="later-check__runs">
          {check.runs?.length ? <>Actions {check.runs.length > 1 ? "runs" : "run"}{" "}
            {check.runs.map((id, i) => (
              <span key={id}>{i ? (i === check.runs!.length - 1 ? " and " : ", ") : ""}<a href={`${RUNS}${id}`} target="_blank" rel="noopener">{id}</a></span>
            ))}</> : null}
          {pr && <>{check.runs?.length ? "; " : ""}<a href={pr} target="_blank" rel="noopener">{check.pr}</a></>}.
        </p>
      )}
    </aside>
  );
}

/** The later checks a passage's text mentions: it names the constant and Comparator. */
export function checksMentionedBy(text: string): LaterCheck[] {
  const checks = libraryChecks();
  if (!checks.length || !text.includes("Comparator")) return [];
  return checks.filter((c) => new RegExp(`(^|[^\\w])${c.constant.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}($|[^\\w])`).test(text));
}

/** The later checks on one Lean constant, by its full name. */
export function checksOnConstant(name: string): LaterCheck[] {
  return libraryChecks().filter((c) => name === c.constant || name.endsWith(`.${c.constant}`));
}

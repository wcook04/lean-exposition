// Every run the instance publishes a receipt for, in one table: what ran, where, at which
// commit, when, its outcome, and what that shows and does not show. Failed, cancelled and
// unavailable runs are rows like the passes. A kind with many receipts (the Comparator
// replay's, one per entry) is one summary row with its counts and a list that opens. The
// rows are read at build time (runLedger.ts); an instance with none shows nothing.

import { RUN_LEDGER } from "virtual:run-ledger";
import { countsInWords, OUTCOME_NAMES } from "./summary";
import { SUMMARY_OVER, type RunGroup, type RunLedger, type RunRow } from "./runLedger";

const base = import.meta.env.BASE_URL;
const dash = <span className="runs__none">—</span>;

function Status({ status }: { status: string }) {
  return <span className={`runs__status runs__status--${status}`}>{OUTCOME_NAMES[status] ?? status.replace(/_/g, " ")}</span>;
}

function Cells({ row }: { row: RunRow }) {
  return (
    <>
      <th scope="row" className="runs__what">
        {row.what}
        {row.receipt && (
          <a className="runs__receipt" href={`${base}${row.receipt}`}>
            Receipt
          </a>
        )}
      </th>
      <td>{row.where ? row.where.url ? <a href={row.where.url}>{row.where.label}</a> : row.where.label : dash}</td>
      <td className="runs__commit">{row.commit ? row.commit.url ? <a href={row.commit.url}><code translate="no">{row.commit.sha.slice(0, 7)}</code></a> : <code translate="no">{row.commit.sha.slice(0, 7)}</code> : dash}</td>
      <td className="runs__date">{row.date ?? dash}</td>
      <td>
        <Status status={row.status} />
        {row.outcome && <span className="runs__outcome">{row.outcome}.</span>}
      </td>
      <td>{row.shows ?? dash}</td>
      <td>{row.doesNotShow ?? dash}</td>
    </>
  );
}

function Detail({ row }: { row: RunRow }) {
  if (!row.theorems?.length) return null;
  return (
    <details className="runs__theorems">
      <summary>{row.theorems.length === 1 ? "The theorem" : `The ${row.theorems.length} theorems`}</summary>
      <ul>
        {row.theorems.map((name) => (
          <li key={name}>
            <code translate="no">{name}</code>
          </li>
        ))}
      </ul>
    </details>
  );
}

function GroupRows({ group }: { group: RunGroup }) {
  if (group.rows.length <= SUMMARY_OVER) {
    return (
      <>
        {group.rows.map((row) => (
          <tr key={row.id} id={`run-${row.id}`} className={`runs__row runs__row--${row.status}`}>
            <Cells row={row} />
          </tr>
        ))}
      </>
    );
  }
  // A run that did not pass stays in view, with every other record of the same run (a
  // re-run attempt that passed), above the summary row that counts them all.
  const notPassed = group.rows.filter((row) => row.status !== "passed");
  const runOf = (row: RunRow) => row.where?.label.replace(/, attempt \d+$/, "") ?? null;
  const shown = group.rows.filter((row) => row.status !== "passed" || notPassed.some((other) => other !== row && runOf(other) !== null && runOf(other) === runOf(row)));
  const theorems = group.rows.reduce((n, row) => n + (row.theorems?.length ?? 0), 0);
  const dates = [...new Set(group.rows.map((row) => row.date).filter(Boolean))];
  const commits = [...new Set(group.rows.map((row) => row.commit?.sha).filter(Boolean))];
  const places = [...new Map(group.rows.filter((row) => row.where).map((row) => [row.where!.label, row.where!])).values()];
  return (
    <>
    {shown.map((row) => (
      <tr key={`shown-${row.id}`} className={`runs__row runs__row--${row.status}`}>
        <Cells row={row} />
      </tr>
    ))}
    <tr className="runs__row runs__row--summary">
      <th scope="row" className="runs__what">
        {group.title}: {group.rows.length.toLocaleString("en-GB")}
        {theorems ? <span className="runs__sub">{theorems.toLocaleString("en-GB")} theorems</span> : null}
      </th>
      <td>{places.length === 1 ? places[0].url ? <a href={places[0].url}>{places[0].label}</a> : places[0].label : places.length ? `${places.length} places` : dash}</td>
      <td className="runs__commit">{commits.length === 1 ? <code translate="no">{commits[0]!.slice(0, 7)}</code> : commits.length ? `${commits.length} commits` : dash}</td>
      <td className="runs__date">{dates.length === 1 ? dates[0] : dates.length ? `${dates[0]} to ${dates[dates.length - 1]}` : dash}</td>
      <td>{countsInWords(group.counts)}</td>
      <td colSpan={2}>
        <details className="runs__list">
          <summary>Each of the {group.rows.length.toLocaleString("en-GB")}, with its outcome</summary>
          <table className="runs__inner">
            <caption className="visually-hidden">{group.title}, one row each</caption>
            <thead>
              <tr>
                <th scope="col">What ran</th>
                <th scope="col">Outcome</th>
                <th scope="col">Shows</th>
              </tr>
            </thead>
            <tbody>
              {group.rows.map((row) => (
                <tr key={row.id} id={`run-${row.id}`} className={`runs__row runs__row--${row.status}`}>
                  <th scope="row">
                    {row.what}
                    {row.receipt && (
                      <a className="runs__receipt" href={`${base}${row.receipt}`}>
                        Receipt
                      </a>
                    )}
                    <Detail row={row} />
                  </th>
                  <td>
                    <Status status={row.status} />
                    <span className="runs__outcome">{row.outcome}.</span>
                  </td>
                  <td>{row.shows ?? dash}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </details>
      </td>
    </tr>
    </>
  );
}

export function RunTable({ ledger = RUN_LEDGER }: { ledger?: RunLedger }) {
  if (!ledger.groups.length) return null;
  const total = ledger.groups.reduce((n, group) => n + group.rows.length, 0);
  return (
    <section className="checks__band runs" aria-labelledby="runs-title">
      <h2 id="runs-title">Every run, where and when it ran</h2>
      <p className="checks__intro">
        {total.toLocaleString("en-GB")} {total === 1 ? "run" : "runs"} with {total === 1 ? "its" : "their"} receipts, passed or not. Each outcome is the one its receipt
        records, for that run alone.
      </p>
      <div className="runs__wrap">
        <table className="runs__table">
          <caption className="visually-hidden">Every run with a receipt: what ran, where, commit, date, outcome, and what it shows and does not show</caption>
          <thead>
            <tr>
              <th scope="col">What ran</th>
              <th scope="col">Where</th>
              <th scope="col">Commit</th>
              <th scope="col">Date</th>
              <th scope="col">Outcome</th>
              <th scope="col">What it shows</th>
              <th scope="col">What it does not show</th>
            </tr>
          </thead>
          {ledger.groups.map((group) => (
            <tbody key={group.type} aria-label={group.title}>
              <tr className="runs__group">
                <th scope="rowgroup" colSpan={7}>
                  {group.title} <span className="runs__counts">{countsInWords(group.counts)}</span>
                </th>
              </tr>
              <GroupRows group={group} />
            </tbody>
          ))}
        </table>
      </div>
    </section>
  );
}

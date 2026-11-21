// The recorded checks by kind and outcome, one row per kind and one column per outcome,
// every number counted from the edition's run records. The front page of each instance
// shows it beside its own words on what ran.

import { useEdition } from "../app/data";
import { CHECK_KINDS, CHECK_ORDER, STATUS_WORDS, outcomeCounts } from "../checks/summary";

const COLUMNS = ["passed", "failed", "unavailable", "not_run"] as const;

export function CheckCounts() {
  const { map } = useEdition();
  const counts = outcomeCounts(map.records.evidence);
  return (
    <table className="checktable">
      <caption className="visually-hidden">The runs this site records, by kind and outcome</caption>
      <thead>
        <tr>
          <th scope="col">Kind of test</th>
          {COLUMNS.map((status) => (
            <th key={status} scope="col" className="checktable__n">
              {STATUS_WORDS[status].replace(/^./, (c) => c.toUpperCase())}
            </th>
          ))}
        </tr>
      </thead>
      <tbody>
        {CHECK_ORDER.filter((kind) => counts.has(kind)).map((kind) => (
          <tr key={kind}>
            <th scope="row">{CHECK_KINDS[kind]?.title ?? kind}</th>
            {COLUMNS.map((status) => {
              const n = counts.get(kind)?.[status] ?? 0;
              return (
                <td key={status} className={`checktable__n${n === 0 ? " is-none" : ""}${status === "failed" && n ? " is-failed" : ""}`}>
                  {n}
                </td>
              );
            })}
          </tr>
        ))}
      </tbody>
    </table>
  );
}

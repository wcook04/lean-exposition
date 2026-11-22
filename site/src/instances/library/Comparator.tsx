// About's account of a library paper's Comparator run: what was accepted, by which kernels, under
// which axioms, and which altered statements were rejected.
import { useComparator, type ComparatorReceipt } from "../../lean/comparatorMark";

export function ComparatorSection() {
  const r = useComparator();
  if (r?.runs?.length) return <ComparatorRuns r={r} />;
  if (!r?.accepted?.theorem_names?.length) return null;
  const controls = [r.rejected_control, ...Object.values(r.other_rejected_controls ?? {})].filter((c) => c?.change);
  return (
    <section aria-labelledby="about-comparator" id="comparator">
      <h2 id="about-comparator">What Comparator checked</h2>
      {r.what ? <p>{r.what}</p> : null}
      <p>
        Accepted: {r.accepted.theorem_names.map((n, i) => <span key={n}>{i ? " and " : ""}<code>{n}</code></span>)}, by{" "}
        {(r.kernels ?? []).join(", ")}, permitting only the axioms {(r.permitted_axioms ?? []).join(", ")}.
        {r.commit ? ` The authors’ commit ${r.commit.slice(0, 7)}.` : ""}
        {r.run ? <> <a href={r.run} target="_blank" rel="noopener">The Actions run</a>{r.date ? `, ${r.date}` : ""}.</> : null}
      </p>
      {r.mode ? <p>{r.mode}.</p> : null}
      {controls.length ? (
        <>
          <p>To show the check can fail, {controls.length} altered statements were given to it, and each was rejected:</p>
          <ul>
            {controls.map((c) => (
              <li key={c!.change}>
                {c!.change}: <code>{c!.output?.[0] ?? "rejected"}</code>
              </li>
            ))}
          </ul>
        </>
      ) : null}
    </section>
  );
}

/** A paper checked by several Comparator configurations: each with what it accepted and what it rejected. */
function ComparatorRuns({ r }: { r: ComparatorReceipt }) {
  const runs = r.runs ?? [];
  return (
    <section aria-labelledby="about-comparator" id="comparator">
      <h2 id="about-comparator">What Comparator checked</h2>
      {r.what ? <p>{r.what}</p> : null}
      <ul>
        {runs.map((run) => {
          const controls = (run.rejected_controls ?? []).filter((c) => c.change);
          return (
            <li key={run.name}>
              <strong>{run.name}.</strong> Accepted{" "}
              {run.accepted.theorem_names.map((n, i) => <span key={n}>{i ? (i === run.accepted.theorem_names.length - 1 ? " and " : ", ") : ""}<code>{n}</code></span>)}, by{" "}
              {(run.kernels ?? []).join(", ")}, permitting only the axioms {(run.permitted_axioms ?? []).join(", ")}.
              {run.mode ? ` ${run.mode}.` : ""}
              {run.run ? <> <a href={run.run} target="_blank" rel="noopener">The Actions run</a>{run.date ? `, ${run.date}` : ""}.</> : null}
              {controls.length ? <> {controls.length === 1 ? "One altered statement was" : `${controls.length} altered statements were`} rejected: {controls.map((c, i) => <span key={c.change}>{i ? "; " : ""}{c.change}</span>)}.</> : null}
            </li>
          );
        })}
      </ul>
    </section>
  );
}

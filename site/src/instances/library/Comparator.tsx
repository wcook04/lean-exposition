// About's account of a library paper's Comparator run: what was accepted, by which kernels, under
// which axioms, and which altered statements were rejected.
import { useComparator } from "../../lean/comparatorMark";

export function ComparatorSection() {
  const r = useComparator();
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

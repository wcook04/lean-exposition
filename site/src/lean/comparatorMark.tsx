// "Comparator-checked" on the Lean card of a theorem a library paper's Comparator receipt accepted
// (comparator.json, published from the instance's generated/comparator/receipt.json), with the
// kernels and a link to the run. About gives the whole receipt.
import { useEffect, useState } from "react";
import site from "@instance/site";

export interface ComparatorReceipt {
  what?: string;
  run?: string;
  date?: string;
  commit?: string;
  kernels?: string[];
  permitted_axioms?: string[];
  mode?: string;
  accepted?: { theorem_names?: string[] };
  rejected_control?: { change?: string; output?: string[] };
  other_rejected_controls?: Record<string, { change?: string; output?: string[] }>;
  /** What the statements were checked against, in place of "the authors’ definitions". */
  against?: string;
  /** A paper checked by several Comparator configurations: one entry per configuration, each with
   *  its own accepted names, kernels and controls. A name's mark comes from the entry accepting it. */
  runs?: ComparatorRun[];
}

export interface ComparatorRun {
  name: string;
  what?: string;
  run?: string;
  date?: string;
  commit?: string;
  kernels?: string[];
  permitted_axioms?: string[];
  mode?: string;
  receipt?: string;
  accepted: { theorem_names: string[] };
  /** Declarations whose checked solution is one exact application of them, with the checked name. */
  applies?: Record<string, string>;
  rejected_controls?: { change?: string; output?: string[] }[];
}

/** The configuration that accepted a declaration: the receipt itself, or one of its runs. */
export function acceptedBy(receipt: ComparatorReceipt | null, name: string): ComparatorReceipt | ComparatorRun | null {
  if (!receipt) return null;
  if (receipt.accepted?.theorem_names?.includes(name)) return receipt;
  return receipt.runs?.find((r) => r.accepted.theorem_names.includes(name)) ?? null;
}

/** The checked name whose solution is one exact application of this declaration, with its configuration. */
export function appliedIn(receipt: ComparatorReceipt | null, name: string): { run: ComparatorRun; target: string } | null {
  for (const run of receipt?.runs ?? []) if (run.applies?.[name]) return { run, target: run.applies[name] };
  return null;
}

let loading: Promise<ComparatorReceipt | null> | null = null;
export function loadComparator(): Promise<ComparatorReceipt | null> {
  if (!site.library) return Promise.resolve(null);
  loading ??= fetch(`${import.meta.env.BASE_URL}comparator.json`)
    .then((r) => (r.ok ? r.json() : null))
    .catch(() => null);
  return loading;
}

export function useComparator(): ComparatorReceipt | null {
  const [receipt, setReceipt] = useState<ComparatorReceipt | null>(null);
  useEffect(() => {
    let live = true;
    void loadComparator().then((r) => live && setReceipt(r));
    return () => {
      live = false;
    };
  }, []);
  return receipt;
}

export function ComparatorMark({ name }: { name: string }) {
  const all = useComparator();
  const receipt = acceptedBy(all, name);
  const applied = receipt ? null : appliedIn(all, name);
  if (applied) {
    return (
      <p className="lean-block__relation comparator-mark">
        <strong>Comparator-checked through <code>{applied.target}</code>.</strong> That statement’s checked solution is one exact
        application of this theorem ({applied.run.name}).{" "}
        {applied.run.run ? <a href={applied.run.run} target="_blank" rel="noopener">The run</a> : null}
        {" · "}
        <a href={`${import.meta.env.BASE_URL}about/#comparator`}>What was checked</a>
      </p>
    );
  }
  if (!receipt) return null;
  const kernels = receipt.kernels ?? [];
  return (
    <p className="lean-block__relation comparator-mark">
      <strong>Comparator-checked.</strong> Accepted against {all?.against ?? "the authors’ definitions"} by{" "}
      {kernels.length === 1 ? kernels[0] : `${kernels.length} kernels`}
      {receipt.permitted_axioms?.length ? `, permitting only ${receipt.permitted_axioms.join(", ")}` : ""}.{" "}
      {receipt.run ? <a href={receipt.run} target="_blank" rel="noopener">The run</a> : null}
      {" · "}
      <a href={`${import.meta.env.BASE_URL}about/#comparator`}>What was checked</a>
    </p>
  );
}

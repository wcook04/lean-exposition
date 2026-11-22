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
}

let loading: Promise<ComparatorReceipt | null> | null = null;
/** The receipt once it has arrived (undefined until then), so a card mounted later shows it in its first render. */
let arrived: ComparatorReceipt | null | undefined = site.library ? undefined : null;

/** Whether the receipt has arrived (or there is none to wait for). */
export const comparatorArrived = () => arrived !== undefined;
export function loadComparator(): Promise<ComparatorReceipt | null> {
  if (!site.library) return Promise.resolve(null);
  loading ??= fetch(`${import.meta.env.BASE_URL}comparator.json`)
    .then((r) => (r.ok ? r.json() : null))
    .catch(() => null)
    .then((r: ComparatorReceipt | null) => (arrived = r));
  return loading;
}

export function useComparator(): ComparatorReceipt | null {
  const [receipt, setReceipt] = useState<ComparatorReceipt | null>(() => arrived ?? null);
  useEffect(() => {
    if (arrived !== undefined) return;
    let live = true;
    void loadComparator().then((r) => live && setReceipt(r));
    return () => {
      live = false;
    };
  }, []);
  return receipt;
}

export function ComparatorMark({ name }: { name: string }) {
  const receipt = useComparator();
  if (!receipt?.accepted?.theorem_names?.includes(name)) return null;
  const kernels = receipt.kernels ?? [];
  return (
    <p className="lean-block__relation comparator-mark">
      <strong>Comparator-checked.</strong> Accepted against the authors’ definitions by {kernels.length} kernels
      {receipt.permitted_axioms?.length ? `, permitting only ${receipt.permitted_axioms.join(", ")}` : ""}.{" "}
      {receipt.run ? <a href={receipt.run} target="_blank" rel="noopener">The run</a> : null}
      {" · "}
      <a href={`${import.meta.env.BASE_URL}about/#comparator`}>What was checked</a>
    </p>
  );
}

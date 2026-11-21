// The supplementary checks of a library paper: theorems written for this reader and compiled
// against the authors' Lean (checks.json from Proof Reader), each with its code and its axioms.
import { useEffect, useState } from "react";

interface Check { name: string; title?: string; keyword: string; code: string; axioms?: string[]; doc?: string; file?: string }

export function SupplementaryChecks() {
  const [checks, setChecks] = useState<{ checks: Check[]; compiled_by?: string } | null>(null);
  useEffect(() => {
    let live = true;
    fetch(`${import.meta.env.BASE_URL}checks.json`)
      .then((r) => (r.ok ? r.json() : null))
      .then((data) => live && setChecks(data))
      .catch(() => {});
    return () => {
      live = false;
    };
  }, []);
  if (!checks?.checks?.length) return null;
  return (
    <section aria-labelledby="about-checks" id="supplementary-checks">
      <h2 id="about-checks">Supplementary checks</h2>
      <p>
        These {checks.checks.length} theorems were written for this reader, not by the authors, and compiled against their Lean.
        {checks.compiled_by ? <> They were <a href={checks.compiled_by} target="_blank" rel="noopener">compiled on GitHub Actions</a>.</> : null} Each lists the axioms Lean reports it uses.
      </p>
      {checks.checks.map((check) => (
        <details key={check.name} className="supplementary-check">
          <summary>
            {check.title ?? check.name} <code>{check.name}</code>
          </summary>
          {check.doc ? <p>{check.doc}</p> : null}
          <pre className="lean-code"><code>{check.code}</code></pre>
          {check.axioms?.length ? <p>Axioms: {check.axioms.join(", ")}.</p> : null}
        </details>
      ))}
    </section>
  );
}

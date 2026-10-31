// How the Lean makes one step of the argument. The map's steps are authored; where both
// records have Lean links, this follows the names in OpenAI's source from one to the
// other, so a reader can see the step in the code. It reports what the source scan found
// and nothing more: a chain of names shows a use, and a missing chain shows nothing.

import { routeHref } from "../app/router";
import { useAlignment } from "../compare/useAlignment";

export function LeanRoute({ edgeKey }: { edgeKey: string }) {
  const step = useAlignment()?.steps?.[edgeKey];
  if (!step) return null;
  return (
    <section className="step__leanroute" aria-labelledby="step-leanroute">
      <h3 id="step-leanroute" className="panel__group">
        In the Lean source
      </h3>
      {step.route ? (
        <>
          <p className="panel__note">
            {step.route.length === 1
              ? "One declaration in OpenAI’s Lean carries both records."
              : "In OpenAI’s Lean, each declaration here names the next in its source, from the result down to what it uses."}
          </p>
          <ol className="step__leanchain">
            {step.route.map((name) => (
              <li key={name}>
                <a className="lean" href={routeHref({ view: "lean", decl: name })} translate="no">
                  {name.split(".").pop()}
                </a>
              </li>
            ))}
          </ol>
        </>
      ) : (
        <p className="panel__note">
          No chain of names was found between the Lean linked to these two records. Names reached only through tactics or
          notation are outside this scan, so the step may still be there.
        </p>
      )}
    </section>
  );
}

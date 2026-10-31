// How the Lean makes one step of the argument. The map's steps are authored; where both
// records have Lean links, this follows the names in OpenAI's source from one to the
// other, so a reader can see the step in the code. A chain of names shows a use. A missing
// chain shows nothing, because names reached through tactics or notation are outside the
// scan, so the panel says nothing in that case.

import { routeHref } from "../app/router";
import { useAlignment } from "../compare/useAlignment";

export function LeanRoute({ edgeKey }: { edgeKey: string }) {
  const route = useAlignment()?.steps?.[edgeKey]?.route;
  if (!route) return null;
  return (
    <section className="step__leanroute" aria-labelledby="step-leanroute">
      <h3 id="step-leanroute" className="panel__group">
        In the Lean source
      </h3>
      <p className="panel__note">
        {route.length === 1
          ? "One declaration in OpenAI’s Lean carries both records."
          : "In OpenAI’s Lean, each declaration here names the next in its source, from the result down to what it uses."}
      </p>
      <ol className="step__leanchain">
        {route.map((name) => (
          <li key={name}>
            <a className="lean" href={routeHref({ view: "lean", decl: name })} translate="no">
              {name.split(".").pop()}
            </a>
          </li>
        ))}
      </ol>
    </section>
  );
}

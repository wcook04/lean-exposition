// How the Lean makes one step of the argument. The map's steps are authored; where both
// records have Lean links, this follows the names in OpenAI's source from one to the
// other, so a reader can see the step in the code. Where none was found the panel says so,
// and says why that shows nothing about the Lean: names reached through tactics or
// notation are outside the scan.

import { routeHref } from "../app/router";
import { useAlignment } from "../compare/useAlignment";
import { declTitle } from "../model/declTitle";
import type { LeanStep } from "./model";

export function LeanRoute({ edgeKey, onWalk }: { edgeKey: string; onWalk?(walk: LeanStep): void }) {
  const alignment = useAlignment();
  if (!alignment) return null;
  const step = alignment.steps?.[edgeKey];
  const route = step?.route;
  const plain = (name: string) => declTitle(alignment, name);
  return (
    <section className="step__leanroute" aria-labelledby="step-leanroute">
      <h3 id="step-leanroute" className="panel__group">
        In the Lean source
      </h3>
      {!route ? (
        <p className="panel__note">
          {step
            ? "No chain of names was found between these two steps. The search is a text scan, which misses names reached through tactics or notation, so this does not show that the Lean lacks the step."
            : "One of these steps has no Lean link, so there is no chain of names to look for."}
        </p>
      ) : (
        <>
          <p className="panel__note">
            {route.length === 1
              ? "One declaration in OpenAI’s Lean carries both steps."
              : "In OpenAI’s Lean, each declaration here names the next in its source, from the result down to what it uses."}
          </p>
          <ol className="step__leanchain">
            {route.map((name) => (
              <li key={name}>
                <a
                  className={plain(name) ? undefined : "lean"}
                  title={name}
                  href={routeHref({ view: "lean", decl: name })}
                  translate="no"
                  onClick={(event) => {
                    if (!onWalk || event.metaKey || event.ctrlKey || event.shiftKey) return;
                    event.preventDefault();
                    onWalk({ name, module: moduleOf(alignment, name) });
                  }}
                >
                  {plain(name) ?? name.split(".").pop()}
                </a>
              </li>
            ))}
          </ol>
        </>
      )}
    </section>
  );
}

/** A chain's names are linked declarations, so a record's row holds each one's module. */
function moduleOf(alignment: NonNullable<ReturnType<typeof useAlignment>>, name: string): string {
  for (const record of Object.values(alignment.records)) for (const row of record.lean) if (row.name === name) return row.module;
  return "";
}

// The Erdős #257 Lean index landing: the tree's revision and size, the main theorem found
// (site.ts names it; else the declaration the graph's first goal formalises), the declarations linked to the
// papers, then the shared reading guide and folders. Nothing here names a declaration.

import { MAIN_THEOREM, type LeanShell } from "../../lean/data";
import { count, declHref, Folders, HowToRead, Start, stated } from "../../lean/LeanPage";
import { LeanBlock } from "../../lean/LeanBlock";
import { findDecl } from "../../lean/resolve";
import { useCheckedWords } from "../../lean/checked";
import { useEdition } from "../../app/data";
import { routeHref } from "../../app/router";

/** The instance's main theorem (site.ts), else the declaration the graph's first goal formalises. */
function useMainDeclaration(): string | null {
  const { graph } = useEdition();
  if (MAIN_THEOREM) return MAIN_THEOREM;
  for (const goal of graph.goals) {
    const edge = (graph.out.get(goal) ?? []).find((e) => e.kind === "formalizes");
    const node = edge ? graph.nodes.get(edge.to) : undefined;
    if (node) return node.label;
  }
  return null;
}

export function LeanLanding({ shell, slot }: { shell: LeanShell; slot: HTMLElement | null }) {
  const { modules } = shell;
  const name = useMainDeclaration();
  const main = name ? findDecl(shell.index, name) : undefined;
  const revisionUrl = modules.base_url ? modules.base_url.replace(/\/blob\//, "/tree/") : null;
  const checked = useCheckedWords();
  return (
    <>
      <header className="lean-intro">
        <h1>Lean index</h1>
        <p>
          The index at the back of the book, for anyone who wants the files and declarations themselves. To read the mathematics,{" "}
          <a href={routeHref({ view: "read", stage: "short" })}>open a paper</a>: click an underlined phrase there and the Lean that states it opens beside the text, with a plain title, a comparison and an AI-drafted reading note.
        </p>
        <p>
          This is the Lean
          {modules.revision ? (
            <>
              {" "}at commit{" "}
              {revisionUrl ? (
                <a href={revisionUrl} target="_blank" rel="noreferrer">
                  <code>{modules.revision.slice(0, 7)}</code>
                </a>
              ) : (
                <code>{modules.revision.slice(0, 7)}</code>
              )}
            </>
          ) : null}
          {modules.toolchain ? (
            <>
              {" "}on <code>{modules.toolchain.split(":").pop()}</code>
            </>
          ) : null}
          : {count(modules.counts.modules)} modules and {count(modules.counts.declarations)} declarations.
        </p>
        <p className="lean-intro__checked">
          {checked} <a href={routeHref({ view: "checks" })}>Every recorded run</a>
        </p>
      </header>
      <div className="lean-landing">
        <section className="lean-start" aria-labelledby="lean-start">
          <h2 id="lean-start">Start here</h2>
          <ul>
            {main && (
              <Start href={declHref(main)} name={main.short} title="The main theorem">
                {stated(shell, main.name)}.
              </Start>
            )}
            <Start href={routeHref({ view: "lean", index: "papers" })} title={`The ${count(shell.linked.size)} declarations linked to the papers`}>
              Each with the step that links it and where the papers state it.
            </Start>
          </ul>
        </section>
        <section className="lean-landing__main" aria-label="The main theorem">
          {main && <LeanBlock name={main.name} module={main.module} noDependencies noPapers noTerms previewSlot={slot} />}
        </section>
      </div>
      <HowToRead />
      <Folders shell={shell} />
    </>
  );
}

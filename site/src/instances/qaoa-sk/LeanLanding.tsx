// The SK site's Lean index landing: OpenAI's two proof trees, the main theorem, its hypothesis,
// the value theorem and the Comparator challenge files, then the shared reading guide and folders.

import type { LeanShell } from "../../lean/data";
import { CHALLENGE_FILE, MAIN_THEOREM, MINIMIZER, VALUE_CHALLENGE_FILE, VALUE_THEOREM } from "../../lean/data";
import { count, declHref, Folders, HowToRead, Start, stated, treeOf } from "../../lean/LeanPage";
import { LeanBlock } from "../../lean/LeanBlock";
import { Prose } from "../../lean/ReadingStrip";
import { findDecl } from "../../lean/resolve";
import { useCheckedWords } from "../../lean/checked";
import { FOLDER_WORDS } from "../../lean/folders";
import { routeHref } from "../../app/router";

export function LeanLanding({ shell, slot }: { shell: LeanShell; slot: HTMLElement | null }) {
  const { modules } = shell;
  const main = findDecl(shell.index, MAIN_THEOREM);
  const value = findDecl(shell.index, VALUE_THEOREM);
  const minimizer = findDecl(shell.index, MINIMIZER);
  const support = treeOf(shell, "OAI/Probability/SKSupport");
  const scalar = treeOf(shell, "OAI/Probability/SKValue");
  const revisionUrl = modules.base_url.replace(/\/blob\//, "/tree/");
  const checked = useCheckedWords();
  const resting = shell.linked.size;
  return (
    <>
      <header className="lean-intro">
        <h1>Lean index</h1>
        <p>
          The index at the back of the book, for anyone who wants the files and declarations themselves. In this Lean the order parameter γ is called the coefficient. To read the mathematics,{" "}
          <a href={routeHref({ view: "read", stage: "short" })}>open a paper</a>: click an underlined phrase there and the Lean that states it opens beside the text, with a plain title, a comparison and an AI-drafted reading note.
        </p>
        <p>
          OpenAI's proof of a theorem about the Sherrington–Kirkpatrick (SK) spin glass is written in Lean, a programming language whose compiler rejects a proof with a wrong step. This is that Lean at commit{" "}
          <a href={revisionUrl} target="_blank" rel="noreferrer">
            <code>{modules.revision.slice(0, 7)}</code>
          </a>{" "}
          on <code>{modules.toolchain.split(":").pop()}</code>: {count(modules.counts.modules)} modules and {count(modules.counts.declarations)} declarations. It has two proof trees,{" "}
          <a href={routeHref({ view: "lean", folder: support.path })}>
            <code>SKSupport</code>
          </a>{" "}
          with {count(support.modules)} modules, whose last theorem is <code>full_support</code>, and{" "}
          <a href={routeHref({ view: "lean", folder: scalar.path })}>
            <code>SKValue</code>
          </a>{" "}
          with {count(scalar.modules)}, whose last theorem is <code>value_consequences</code>, and two challenge files for Comparator, a program that compares a Lean proof with a separately written statement.
        </p>
        <p className="lean-intro__checked">
          {checked}{" "}
          <a href={routeHref({ view: "checks" })}>Every recorded run</a>
        </p>
      </header>
      <div className="lean-landing">
        <section className="lean-start" aria-labelledby="lean-start">
          <h2 id="lean-start">Start here</h2>
          <ul>
            {main && (
              <Start href={declHref(main)} name={main.short} title="The main theorem">
                {stated(shell, main.name)}, in <code>SKSupport/Main.lean</code>.
              </Start>
            )}
            {minimizer && (
              <Start href={declHref(minimizer)} name={minimizer.short} title="Its hypothesis">
                {shell.terms.get(minimizer.name) ? <Prose text={shell.terms.get(minimizer.name)!.words} /> : "What it assumes of the order parameter."}
              </Start>
            )}
            {value && (
              <Start href={declHref(value)} name={value.short} title="The value theorem">
                {stated(shell, value.name)}, in <code>SKValue/Main.lean</code>.
              </Start>
            )}
            <Start href={routeHref({ view: "lean", module: CHALLENGE_FILE })} name="SKFullSupport.lean" title="The Comparator challenge file">
              {FOLDER_WORDS.ComparatorChallenges} The other is{" "}
              <a href={routeHref({ view: "lean", module: VALUE_CHALLENGE_FILE })}>
                <code>SKValue.lean</code>
              </a>
              .
            </Start>
            <Start href={routeHref({ view: "lean", index: "papers" })} title={`The ${count(resting)} declarations linked to the papers`}>
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


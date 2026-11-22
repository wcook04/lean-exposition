// Parts of the About page that every instance shows the same way: how to use the site, how
// the map is drawn, and the edition being read. The SK page's markup is unchanged; it now
// comes from here.

import { useEffect, useState } from "react";
import { routeHref } from "../app/router";
import { useEdition } from "../app/data";
import { citationText, copyText, editionLink } from "../app/cite";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { LINKS } from "../app/author";
import { Out } from "../app/Out";
import { KeyList } from "../app/KeysHelp";
import { mainGoalOf } from "../app/mainGoal";

const RECORD_MEANINGS: { table: string; noun: string; meaning: string }[] = [
  { table: "nodes", noun: "steps", meaning: "claims, assumptions, main results and Lean declarations" },
  { table: "edges", noun: "links", meaning: "each saying that one step is used in the argument for another, that a Lean declaration corresponds to a result, or that one step cites another" },
  { table: "citations", noun: "citations", meaning: "links from a step to a place in a source" },
  { table: "sources", noun: "sources", meaning: "papers and files, identified by address and, for files, by a hash of their bytes" },
  { table: "evidence", noun: "run records", meaning: "runs, including those planned but not started" },
];

const STATE_WORDS: Record<string, string> = {
  draft: "draft",
  needs_revision: "no independent mathematician has accepted it yet",
  approved: "approved",
  reviewed: "reviewed",
};

function words(value: string): string {
  return STATE_WORDS[value] ?? value.replace(/_/g, " ");
}

export function AboutUsing() {
  return (
  <section className="about__using" id="using" aria-labelledby="using-title">
    <h2 id="using-title">How to use this site</h2>
    <div className="about__usegrid">
      <div>
        <h3>What the marks mean</h3>
        <ul>
          <li>Linked text has a light tint. With topic colours on, the margin shows each line’s topics from top to bottom in phrase order.</li>
          <li>The highlighter marks the statement you are on, in the same ink as the Lean lines it maps to.</li>
          <li>On a graph, a green card is a step stated and proved in Lean, or defined there. A paler green card has some of that.</li>
        </ul>
        <h3>What a click does</h3>
        <ul>
          <li>Scrolling needs no click. The statement about a third of the way down the window takes the highlighter, and the graph and the Lean beside the paper move to it.</li>
          <li>Pointing at a marked statement or a Lean name lights it everywhere and previews it. Nothing moves.</li>
          <li>Select a statement to open its Lean at the exact lines. Select a margin mark to see the links in that paragraph.</li>
          <li>Clicking a reference opens it in place under the paragraph, with a link to go there.</li>
          <li>Every jump has a named Back, which is the browser’s own Back button.</li>
        </ul>
      </div>
      <div>
        <h3>Keys</h3>
        <KeyList />
        <h3>Feedback</h3>
        <p>
          If a tie is wrong or a click loses your place, <Out href="https://github.com/wcook04/lean-exposition/issues">open an issue on the repository</Out> or write through the{" "}
          <Out href={LINKS.contact}>contact page on Plectis</Out>. The address in your browser names the exact statement, so paste it in.
        </p>
      </div>
    </div>
  </section>
  );
}

export function AboutKey() {
  return (
  <section className="about__key" aria-labelledby="about-key">
    <h2 id="about-key">How the argument map is drawn</h2>
    <ul className="about__keylist">
      <li>
        <span className="about__sample about__sample--lines" aria-hidden="true">
          <span className="rel-sample" />
          <span className="rel-sample rel-sample--formalizes" />
        </span>
        <span>
          A line joins a step to a result whose argument uses it, with the arrowhead at the result. A grey, solid line
          is a recorded use. A cyan, dashed line joins a result to the Lean declaration recorded as corresponding to it.
        </span>
      </li>
      <li>
        <span className="about__sample" aria-hidden="true">
          <span className="about__tag">Assumes</span>
        </span>
        <span>
          An assumption is a violet tag with a dotted border, shown on each result that assumes it. When several results
          use a step that has no recorded inputs of its own, the step is drawn under each of them, with a coloured
          band along the bottom of each copy.
        </span>
      </li>
      <li>
        <span className="about__sample" aria-hidden="true">
          <span className="rel-sample rel-sample--lit" />
        </span>
        <span>
          Amber outlines the step or link you have selected, and the keyboard focus. When you trace what a step depends on, its grey lines turn amber; assumption tags and Lean lines on the traced route keep their own colours and
          are drawn brighter.
        </span>
      </li>
    </ul>
    <p className="about__keynote">
      The <a href={routeHref({ view: "map" })}>argument map</a>’s Key button says the rest in words, with its keyboard
      controls. On the What ran page each outcome is written as a word, and only a failed outcome is shown in colour.
    </p>
  </section>
  );
}

/** The edition's facts; `copied` says what else the build copies beside it. */
export function AboutEdition({ copied }: { copied: string }) {
  const { snapshot, overview, graph } = useEdition();
  const papers = STAGE_ORDER.map((stage) => overview.papers.find((p) => p.stage === stage)).filter((p) => !!p);
  const long = overview.papers.find((p) => p.stage === "long");
  const goal = mainGoalOf(long?.paper_scope.selected_goal_ids, graph.goals, (g) => graph.nodes.has(g));
  const goalLabel = goal ? graph.nodes.get(goal)!.label : null;
  return (
  <section className="about__serves" id="edition" aria-labelledby="serves">
    <h2 id="serves">The edition you are reading</h2>
    <p>
      The steps and the three papers belong to one captured edition, a fixed set of files identified below. The
      published website includes that capture. When run against the local read-only server, the site pins requests to
      the same edition and asks you to reload if the server changes it. {copied}
    </p>
    <dl className="facts">
      <div>
        <dt>Edition</dt>
        <dd>
          Bundle <code translate="no">{snapshot.bundle_id}</code>, version {snapshot.bundle_version}. Manifest SHA-256{" "}
          <code translate="no" className="about__hash">
            {snapshot.manifest_sha256}
          </code>
          <span className="about__copies">
            <CopyButton label="Copy link to this edition" text={() => editionLink({ view: "map" }, snapshot)} />
            <CopyButton
              label="Copy citation"
              text={() => citationText({ place: goalLabel ?? undefined }, { view: "map", node: goal }, snapshot)}
            />
          </span>
        </dd>
      </div>
      <div>
        <dt>Papers</dt>
        <dd>
          <ul>
            {papers.map((p) => (
              <li key={p.stage}>
                <a href={routeHref({ view: "read", stage: p.stage })}>{PAPER_NAMES[p.stage].short}</a>: {words(p.state)},{" "}
                {words(p.review_state)}; {p.passages} passages linked to steps, in {p.sections} sections.
              </li>
            ))}
          </ul>
        </dd>
      </div>
      <div>
        <dt>Counts</dt>
        <dd>
          <ul>
            {RECORD_MEANINGS.filter((r) => overview.record_counts[r.table] !== undefined).map((r) => (
              <li key={r.table}>
                <span className="num">{overview.record_counts[r.table]}</span> {r.noun}: {r.meaning}.
              </li>
            ))}
          </ul>
        </dd>
      </div>
      <div>
        <dt>Run it yourself</dt>
        <dd>
          <code>lean-exposition serve</code> starts the read-only server, and <code>npm run dev</code> in <code>site/</code>{" "}
          starts this site. The repository’s <code>site/README.md</code> lists the full commands.
        </dd>
      </div>
    </dl>
  </section>
  );
}

export /** A copy action that says what happened, and offers the text when the browser refuses. */
function CopyButton({ label, text }: { label: string; text: () => string }) {
  const [state, setState] = useState<{ status: "idle" } | { status: "copied" } | { status: "manual"; text: string }>({ status: "idle" });
  useEffect(() => {
    if (state.status !== "copied") return;
    const timer = window.setTimeout(() => setState({ status: "idle" }), 2400);
    return () => window.clearTimeout(timer);
  }, [state]);
  return (
    <span className="copyact">
      <button
        type="button"
        className="control copyact__button"
        onClick={async () => {
          const value = text();
          setState((await copyText(value)) ? { status: "copied" } : { status: "manual", text: value });
        }}
      >
        {label}
      </button>
      <span className="copyact__status" role="status">
        {state.status === "copied" ? "Copied" : ""}
      </span>
      {state.status === "manual" && (
        <textarea className="copyact__manual" readOnly value={state.text} aria-label={`${label}: select and copy`} rows={3} onFocus={(e) => e.currentTarget.select()} />
      )}
    </span>
  );
}

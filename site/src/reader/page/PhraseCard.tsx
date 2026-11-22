// What a phrase's declaration card adds to its Lean: the topic the phrase belongs to, how the
// Lean compares with the phrase in words, and a reading note. The comparison, the note and the
// topic were all drafted by an AI agent, and the card says so; nothing here rests on colour.
// The note's mathematics is typeset with KaTeX, and its `names` are set as code.

import { useEffect, useMemo, useState } from "react";
import { loadPhraseNotes, type ComparisonMatters, type MergedPhrase, type PhraseAssessment, type PhraseExplanation, type PhraseLean, type PhraseNotes, type PhraseTopic } from "../../api/lean";
import type { Stage } from "../../api/types";
import { FIDELITIES, isFidelity, NOT_ASSESSED, NOT_ASSESSED_DETAIL, phraseVerdict, type Fidelity } from "../../compare/fidelityWords";
import { cardKeys, conventionsFor, useAids } from "../aids";
import { renderTex } from "../math";
import site from "@instance/site";
import { Signal } from "./signal";
import { useLeanNote } from "../../lean/noteSummaries";

const cache = new Map<Stage, Promise<PhraseNotes | null>>();
/** Each paper's notes once they have arrived, so a card mounted later has them in its first render. */
const arrived = new Map<Stage, PhraseNotes | null>();

/**
 * Each part's titles and notes for one paper, loaded once; null for a paper without them, and
 * undefined while they are on their way (or not wanted).
 */
export function usePhraseNotes(stage: Stage, wanted: boolean): PhraseNotes | null | undefined {
  const [notes, setNotes] = useState<PhraseNotes | null | undefined>(() => arrived.get(stage));
  useEffect(() => {
    if (!wanted) return;
    if (arrived.has(stage)) {
      setNotes(arrived.get(stage));
      return;
    }
    let live = true;
    let pending = cache.get(stage);
    if (!pending) {
      pending = loadPhraseNotes(stage)
        .catch(() => null)
        .then((found) => {
          arrived.set(stage, found);
          return found;
        });
      cache.set(stage, pending);
    }
    void pending.then((found) => live && setNotes(found));
    return () => {
      live = false;
    };
  }, [stage, wanted]);
  return wanted ? notes : null;
}

/** The declaration a phrase's card shows (its selected tab), for the graph above it. */
export const dockDecl = new Signal<{ name: string; module: string } | null>(null, (a, b) => a?.name === b?.name && a?.module === b?.module);

/** A declaration pointed at in the Lean pane; the paper lights the phrases it states. */
export const declLight = new Signal<string | null>(null);

const escapeHtml = (s: string) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

/**
 * A reading note as HTML: `$…$` typeset by KaTeX, `name` as code, the rest as text.
 * `errors` lists any formula KaTeX could not set; the formula then shows as its source.
 */
export function noteHtml(text: string): { html: string; errors: string[] } {
  let html = "";
  const errors: string[] = [];
  let i = 0;
  while (i < text.length) {
    const c = text[i];
    if (c === "\\" && text[i + 1] === "$") {
      html += "$";
      i += 2;
    } else if (c === "$") {
      let j = i + 1;
      while (j < text.length && !(text[j] === "$" && text[j - 1] !== "\\")) j++;
      const math = renderTex(text.slice(i + 1, j), false);
      if (math.error) errors.push(math.error);
      // Punctuation straight after a formula keeps to its line.
      const glued = /^[.,;:!?)\]’”]+/.exec(text.slice(j + 1))?.[0] ?? "";
      html += glued ? `<span class="nowrap">${math.html}${escapeHtml(glued)}</span>` : math.html;
      i = j + 1 + glued.length;
    } else if (c === "`") {
      const j = text.indexOf("`", i + 1);
      if (j < 0) {
        html += escapeHtml(text.slice(i));
        break;
      }
      html += `<code>${escapeHtml(text.slice(i + 1, j))}</code>`;
      i = j + 1;
    } else {
      let j = i;
      while (j < text.length && text[j] !== "$" && text[j] !== "`" && !(text[j] === "\\" && text[j + 1] === "$")) j++;
      html += escapeHtml(text.slice(i, j));
      i = j;
    }
  }
  return { html, errors };
}

/**
 * A reading note in a card: its summary first when it has one, with a "more" control that expands
 * the whole note in place; a note without a summary shows whole, as before.
 */
export function NoteBody({ text, summary, className = "phrase-card__text" }: { text: string; summary?: string; className?: string }) {
  const [open, setOpen] = useState(false);
  if (!summary || summary.trim() === text.trim()) return <p className={className} dangerouslySetInnerHTML={{ __html: noteHtml(text).html }} />;
  return (
    <>
      <p className={`${className} note-summary`}>
        <span dangerouslySetInnerHTML={{ __html: noteHtml(open ? text : summary).html }} />{" "}
        <button type="button" className="note-more" aria-expanded={open} onClick={() => setOpen(!open)}>
          {open ? "less" : "more"}
        </button>
      </p>
    </>
  );
}

/**
 * The opening words of a merged phrase, enough to tell it from the others: display formulas become
 * an ellipsis, Markdown emphasis is dropped, and the cut falls between words outside any formula.
 */
export function phraseOpening(quote: string, most = 14): string {
  const flat = quote.replace(/\$\$[\s\S]*?\$\$/g, " … ").replace(/\*\*|__/g, "").replace(/\\([[\]])/g, "$1").replace(/\[([^\]]*)\]\([^)]*\)/g, "$1").replace(/\s+/g, " ").trim();
  const words = flat.split(" ");
  let out = "";
  let open = false;
  for (let i = 0; i < words.length; i++) {
    const word = words[i];
    out += (out ? " " : "") + word;
    for (let j = 0; j < word.length; j++) if (word[j] === "$" && word[j - 1] !== "\\") open = !open;
    if (i + 1 >= most && !open) return i + 1 < words.length ? `${out} …` : out;
  }
  return open ? out.replace(/\$/g, "") : out;
}

/**
 * One comparison of the phrase with its Lean, in words: the verdict and every qualification the
 * source wrote, "Not assessed" where none is recorded, or the paper's held text. A note is shown
 * whatever the verdict, "same" included: a qualification is never hidden behind agreement.
 */
export function Verdict({ assessment, words }: { assessment: Pick<PhraseAssessment, "fidelity" | "fidelity_note">; words?: string | null }) {
  const { fidelity, fidelity_note: note } = assessment;
  const lead = words ? <span className="phrase-card__for">For “<span dangerouslySetInnerHTML={{ __html: noteHtml(words).html }} />”: </span> : null;
  if (fidelity === "held") {
    return (
      <p className="phrase-card__fidelity" data-fidelity="held">
        {lead}
        {site.comparisonsHeld ?? note ?? "This comparison is held."}
      </p>
    );
  }
  if (!isFidelity(fidelity)) {
    return (
      <p className="phrase-card__fidelity" data-fidelity="unassessed">
        {lead}
        <strong>{NOT_ASSESSED}</strong>. {NOT_ASSESSED_DETAIL}
      </p>
    );
  }
  return (
    <p className="phrase-card__fidelity" data-fidelity={fidelity}>
      {lead}
      <strong>{phraseVerdict(fidelity)}</strong>
      {note ? (
        <>
          : <span dangerouslySetInnerHTML={{ __html: noteHtml(note).html }} />
        </>
      ) : (
        "."
      )}{" "}
      <span className="phrase-card__who">AI-assessed</span>
    </p>
  );
}

/**
 * The comparisons a card shows for one Lean row. A tie that holds several overlapping phrases
 * shows each phrase's own comparison with that phrase's words, so a verdict about one phrase is
 * never read as a verdict about the others; a tie of one phrase shows its single comparison.
 */
export function assessmentsOf(row: PhraseLean, merged: readonly MergedPhrase[] | undefined): { assessment: Pick<PhraseAssessment, "fidelity" | "fidelity_note">; words: string | null }[] {
  const own = row.assessments ?? [];
  if (merged && merged.length > 1 && own.length) {
    const words = new Map(merged.map((m) => [m.id, m.quote]));
    return own.map((a) => ({ assessment: a, words: words.has(a.phrase) ? phraseOpening(words.get(a.phrase)!) : null }));
  }
  return [{ assessment: { fidelity: row.fidelity ?? "unassessed", fidelity_note: row.fidelity_note }, words: null }];
}

/** What each comparison means, in one sentence of mathematical terms (docs/reader-design.md, "The legend"). */
const FIDELITY_MEANING: Record<Fidelity, string> = {
  same: "The formal statement asserts what the quoted words assert, after the translation the note states.",
  stronger: "The formal statement has fewer hypotheses, more conclusions or a sharper bound; the note names the difference.",
  weaker: "The formal statement has more hypotheses, fewer conclusions or a looser bound; the note names the difference.",
  different: "Neither implies the other as stated: for example, a definition linked to a sentence about a construction.",
};

/**
 * Each comparison as the card words it, with its meaning: the four verdicts in `phraseVerdict`'s
 * words, "Not assessed" as `NOT_ASSESSED`, and a withheld comparison.
 */
export const COMPARISON_LEGEND: readonly (readonly [string, string])[] = [
  ...FIDELITIES.map((f) => [phraseVerdict(f), FIDELITY_MEANING[f]] as const),
  [NOT_ASSESSED, "No comparison has been recorded for this pair. That says nothing about whether they agree."],
  ["Withheld", "A comparison was drafted and is not shown, for the reason given beside it."],
];

/**
 * The legend under every comparison: closed until asked for, and the same words wherever it
 * stands. Its words are written only once it is opened, so a closed legend never sets a verdict's
 * name ("same" among them) beside a comparison that is not that verdict.
 */
export function ComparisonLegend() {
  const [open, setOpen] = useState(false);
  return (
    <details className="phrase-card__legend" onToggle={(e) => setOpen(e.currentTarget.open)}>
      <summary>What do these words mean?</summary>
      {open && (
        <>
          <dl>
            {COMPARISON_LEGEND.map(([word, meaning]) => (
              <div key={word}>
                <dt>{word}</dt>
                <dd>{meaning}</dd>
              </div>
            ))}
          </dl>
          <p>{site.library && (
          <>
            <a href={`${import.meta.env.BASE_URL}about/#differences`}>Differences between the paper and the Lean</a>{". "}
          </>
        )}
        A comparison concerns the quoted words only. A shared name or number is not evidence that two statements agree, and a check of the Lean by its kernel is not a check of this comparison.</p>
        </>
      )}
    </details>
  );
}

/** The paper's formal conventions that bear on this card, each opening to its statement as mathematics. */
function Conventions({ keys }: { keys: readonly string[] }) {
  const aids = useAids(keys.length > 0);
  const found = useMemo(() => conventionsFor(aids, keys), [aids, keys]);
  if (!found.length) return null;
  return (
    <div className="phrase-card__conventions">
      <p className="phrase-card__label">
        Conventions used here <span>AI-drafted</span>
      </p>
      <ul>
        {found.map((entry) => (
          <li key={entry.term}>
            <details>
              <summary>{entry.term}</summary>
              <p dangerouslySetInnerHTML={{ __html: noteHtml(entry.convention).html }} />
              {entry.differs_from_paper && (
                <p className="phrase-card__differs">
                  <strong>Differs from the paper:</strong> <span dangerouslySetInnerHTML={{ __html: noteHtml(entry.differs_from_paper).html }} />
                </p>
              )}
            </details>
          </li>
        ))}
      </ul>
    </div>
  );
}

/**
 * What stands between a phrase's title and its Lean, in the order a reader asks: the exact words,
 * how the Lean compares with them and every qualification of that, the reading note, then the
 * conventions the statement relies on. The topic's colour marks nothing here: the amber rule
 * beside the quotation is the same mark the selected words carry in the paper.
 */
const MATTERS_KIND: Record<string, string> = {
  scope: "a difference of scope",
  granularity: "a difference of granularity",
  convention: "a difference of convention",
  "genuine-gap": "a genuine gap",
};

/** The verdict's last line: whether the difference bears on the paper's main result, and why. */
function Matters({ matters, mainResult }: { matters: ComparisonMatters; mainResult?: string }) {
  const answer = matters.affects_main_result === "yes" ? "Yes" : matters.affects_main_result === "no" ? "No" : "Not settled";
  return (
    <p className="phrase-card__matters" data-affects={matters.affects_main_result}>
      <span className="phrase-card__ask">Does this affect {mainResult ? <span dangerouslySetInnerHTML={{ __html: noteHtml(mainResult).html }} /> : "the main result"}?</span>{" "}
      <strong>{answer}.</strong>
      {MATTERS_KIND[matters.kind] ? ` This is ${MATTERS_KIND[matters.kind]}.` : ""}
      {matters.line && (
        <>
          {" "}
          <span dangerouslySetInnerHTML={{ __html: noteHtml(matters.line).html }} />
        </>
      )}
    </p>
  );
}

/** What the quoted words say, in the paper's notation, with its sources; and what is not settled from them. */
function Explanation({ explanation }: { explanation: PhraseExplanation }) {
  const sources = explanation.citations ?? [];
  return (
    <div className="phrase-card__explanation">
      <p className="phrase-card__label">
        What these words say <span>AI-drafted</span>
      </p>
      <p className="phrase-card__text" dangerouslySetInnerHTML={{ __html: noteHtml(explanation.text).html }} />
      {explanation.grounded === false && explanation.open && <p className="phrase-card__open" dangerouslySetInnerHTML={{ __html: noteHtml(explanation.open).html }} />}
      {sources.length > 0 && (
        <details className="phrase-card__sources">
          <summary>{sources.length === 1 ? "The source this rests on" : `The ${sources.length} sources this rests on`}</summary>
          <ul>
            {sources.map((source) => (
              <li key={`${source.ref}:${source.where ?? ""}`}>
                {source.url ? <a href={source.url}>{source.title}</a> : source.title}
                {source.where && <>, {source.where}</>}
                {source.supports && (
                  <>
                    : <span dangerouslySetInnerHTML={{ __html: noteHtml(source.supports).html }} />
                  </>
                )}
              </li>
            ))}
          </ul>
        </details>
      )}
    </div>
  );
}

export function PhraseCard({ row, note, quote, merged, phrase, names, explanation, mainResult }: { row: PhraseLean; topic?: PhraseTopic | null; note: string | undefined; quote?: string | null; merged?: readonly MergedPhrase[]; phrase?: string | null; names?: readonly string[]; explanation?: PhraseExplanation; mainResult?: string }) {
  const shown = assessmentsOf(row, merged);
  const leanNote = useLeanNote(row.name);
  const keys = useMemo(() => cardKeys(phrase, names ?? [row.name]), [phrase, names, row.name]);
  return (
    <section className="phrase-card" aria-label="These words and how the Lean compares with them">
      {quote && <blockquote className="phrase-card__quote" aria-label="The words in the paper" dangerouslySetInnerHTML={{ __html: quote }} />}
      {explanation?.text && <Explanation explanation={explanation} />}
      <div className="phrase-card__compare">
        <p className="phrase-card__label">
          Comparison with these words
        </p>
        {merged && merged.length > 1 && (
          <p className="phrase-card__merged" data-merged={merged.length}>
            These words hold {merged.length} overlapping phrases of the source, merged into one link. Each comparison below names the phrase it was made for.
          </p>
        )}
        {shown.map(({ assessment, words }, i) => (
          <Verdict key={i} assessment={assessment} words={words} />
        ))}
        {row.matters && <Matters matters={row.matters} mainResult={mainResult} />}
        <ComparisonLegend />
      </div>
      {note && (
        <div className="phrase-card__note">
          <p className="phrase-card__label">
            Reading note <span>AI-drafted</span>
          </p>
          <NoteBody text={note} summary={leanNote && leanNote.text.trim() === note.trim() ? leanNote.summary : undefined} />
        </div>
      )}
      <Conventions keys={keys} />
    </section>
  );
}

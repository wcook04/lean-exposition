// What a phrase's declaration card adds to its Lean: the topic the phrase belongs to, how the
// Lean compares with the phrase in words, and a reading note. The comparison, the note and the
// topic were all drafted by an AI agent, and the card says so; nothing here rests on colour.
// The note's mathematics is typeset with KaTeX, and its `names` are set as code.

import { useEffect, useMemo, useState } from "react";
import { loadPhraseNotes, type PhraseLean, type PhraseNotes, type PhraseTopic } from "../../api/lean";
import type { Stage } from "../../api/types";
import { isFidelity, type Fidelity } from "../../compare/fidelityWords";
import { cardKeys, conventionsFor, useAids } from "../aids";
import { renderTex } from "../math";
import site from "@instance/site";
import { Signal } from "./signal";
import { useLeanNote } from "../../lean/noteSummaries";

const cache = new Map<Stage, Promise<PhraseNotes | null>>();

/** Each part's titles and notes for one paper, loaded once; null for a paper without them. */
export function usePhraseNotes(stage: Stage, wanted: boolean): PhraseNotes | null {
  const [notes, setNotes] = useState<PhraseNotes | null>(null);
  useEffect(() => {
    if (!wanted) return;
    let live = true;
    let pending = cache.get(stage);
    if (!pending) {
      pending = loadPhraseNotes(stage).catch(() => null);
      cache.set(stage, pending);
    }
    void pending.then((found) => live && setNotes(found));
    return () => {
      live = false;
    };
  }, [stage, wanted]);
  return notes;
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

/** Each comparison word in one sentence, in mathematical terms (docs/reader-design.md, "The legend"). */
export const COMPARISON_LEGEND: readonly (readonly [string, string])[] = [
  ["Same", "The formal statement asserts what the quoted words assert, after the translation the note states."],
  ["Stronger", "The formal statement has fewer hypotheses, more conclusions or a sharper bound; the note names the difference."],
  ["Weaker", "The formal statement has more hypotheses, fewer conclusions or a looser bound; the note names the difference."],
  ["Different", "Neither implies the other as stated: for example, a definition linked to a sentence about a construction."],
  ["Not assessed", "No comparison has been recorded for this pair. That says nothing about whether they agree."],
  ["Withheld", "A comparison was drafted and is not shown, for the reason given beside it."],
];

const VERDICT: Record<Fidelity, readonly [string, string]> = {
  same: ["Same", "the Lean states what these words state."],
  stronger: ["Stronger", "the Lean states more than these words."],
  weaker: ["Weaker", "the Lean states less than these words."],
  different: ["Different", "the Lean states something these words neither imply nor are implied by."],
};

/** The legend under every comparison: closed until asked for, and the same words wherever it stands. */
export function ComparisonLegend() {
  return (
    <details className="phrase-card__legend">
      <summary>What do these words mean?</summary>
      <dl>
        {COMPARISON_LEGEND.map(([word, meaning]) => (
          <div key={word}>
            <dt>{word}</dt>
            <dd>{meaning}</dd>
          </div>
        ))}
      </dl>
      <p>A comparison concerns the quoted words only. A shared name or number is not evidence that two statements agree, and a check of the Lean by its kernel is not a check of this comparison.</p>
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
export function PhraseCard({ row, note, quote, phrase, names }: { row: PhraseLean; topic?: PhraseTopic | null; note: string | undefined; quote?: string | null; phrase?: string | null; names?: readonly string[] }) {
  const state = row.fidelity as string | undefined;
  const verdict = isFidelity(row.fidelity) ? VERDICT[row.fidelity] : null;
  const leanNote = useLeanNote(row.name);
  const keys = useMemo(() => cardKeys(phrase, names ?? [row.name]), [phrase, names, row.name]);
  return (
    <section className="phrase-card" aria-label="These words and how the Lean compares with them">
      {quote && <blockquote className="phrase-card__quote" aria-label="The words in the paper" dangerouslySetInnerHTML={{ __html: quote }} />}
      <div className="phrase-card__compare">
        <p className="phrase-card__label">
          Comparison with these words {verdict && <span>AI-assessed</span>}
        </p>
        {verdict ? (
          <p className="phrase-card__fidelity" data-fidelity={row.fidelity}>
            <strong>{verdict[0]}:</strong> {verdict[1]}
            {row.fidelity_note && (
              <>
                {" "}
                <span dangerouslySetInnerHTML={{ __html: noteHtml(row.fidelity_note).html }} />
              </>
            )}
          </p>
        ) : state === "held" ? (
          <p className="phrase-card__fidelity" data-fidelity="held">
            <strong>Withheld:</strong> {site.comparisonsHeld ?? "a comparison was drafted and is not shown."}
          </p>
        ) : (
          <p className="phrase-card__fidelity" data-fidelity="none">
            No comparison is recorded for this passage and formal statement.
          </p>
        )}
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

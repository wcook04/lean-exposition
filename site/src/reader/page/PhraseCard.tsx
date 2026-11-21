// What a phrase's declaration card adds to its Lean: the topic the phrase belongs to, how the
// Lean compares with the phrase in words, and a reading note. The comparison, the note and the
// topic were all drafted by an AI agent, and the card says so; nothing here rests on colour.
// The note's mathematics is typeset with KaTeX, and its `names` are set as code.

import { useEffect, useState } from "react";
import { loadPhraseNotes, type MergedPhrase, type PhraseAssessment, type PhraseLean, type PhraseNotes, type PhraseTopic } from "../../api/lean";
import type { Stage } from "../../api/types";
import { isFidelity, NOT_ASSESSED, NOT_ASSESSED_DETAIL, phraseVerdict } from "../../compare/fidelityWords";
import { renderTex } from "../math";
import { Signal } from "./signal";

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
 * source wrote, or "Not assessed" where none is recorded. A note is shown
 * whatever the verdict, "same" included: a qualification is never hidden behind agreement.
 */
export function Verdict({ assessment, words }: { assessment: Pick<PhraseAssessment, "fidelity" | "fidelity_note">; words?: string | null }) {
  const { fidelity, fidelity_note: note } = assessment;
  const lead = words ? <span className="phrase-card__for">For “<span dangerouslySetInnerHTML={{ __html: noteHtml(words).html }} />”: </span> : null;
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

export function PhraseCard({ row, topic, note, quote, merged }: { row: PhraseLean; topic: PhraseTopic | null; note: string | undefined; quote?: string | null; merged?: readonly MergedPhrase[] }) {
  const shown = assessmentsOf(row, merged);
  return (
    <section className="phrase-card" data-tone={topic ? topic.colour * 2 : undefined} aria-label="About this phrase and its Lean">
      {topic && (
        <p className="phrase-card__topic" title={topic.description || undefined}>
          <span className="phrase-card__swatch" aria-hidden="true" />
          Topic: {topic.name}
        </p>
      )}
      {quote && (
        <blockquote className="phrase-card__quote" aria-label="The phrase in the paper" dangerouslySetInnerHTML={{ __html: quote }} />
      )}
      {merged && merged.length > 1 && (
        <p className="phrase-card__merged" data-merged={merged.length}>
          These words hold {merged.length} overlapping phrases of the source, merged into one link. Each comparison below names the phrase it was made for.
        </p>
      )}
      {shown.map(({ assessment, words }, i) => (
        <Verdict key={i} assessment={assessment} words={words} />
      ))}
      {note && (
        <div className="phrase-card__note">
          <p className="phrase-card__label">
            Reading note <span>· AI-drafted</span>
          </p>
          <p className="phrase-card__text" dangerouslySetInnerHTML={{ __html: noteHtml(note).html }} />
        </div>
      )}
    </section>
  );
}

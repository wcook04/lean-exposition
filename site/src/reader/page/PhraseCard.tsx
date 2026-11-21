// What a phrase's declaration card adds to its Lean: the topic the phrase belongs to, how the
// Lean compares with the phrase in words, and a reading note. The comparison, the note and the
// topic were all drafted by an AI agent, and the card says so; nothing here rests on colour.
// The note's mathematics is typeset with KaTeX, and its `names` are set as code.

import { useEffect, useState } from "react";
import { loadPhraseNotes, type PhraseLean, type PhraseNotes, type PhraseTopic } from "../../api/lean";
import type { Stage } from "../../api/types";
import { isFidelity, phraseVerdict } from "../../compare/fidelityWords";
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

export function PhraseCard({ row, topic, note, quote }: { row: PhraseLean; topic: PhraseTopic | null; note: string | undefined; quote?: string | null }) {
  const verdict = isFidelity(row.fidelity) ? phraseVerdict(row.fidelity) : null;
  const leanNote = useLeanNote(row.name);
  return (
    <section className="phrase-card" data-tone={topic ? topic.tone : undefined} aria-label="About this phrase and its Lean">
      {topic && (
        <p className="phrase-card__topic" title={topic.description || undefined}>
          <span className="phrase-card__swatch" aria-hidden="true" />
          Topic: {topic.name}
        </p>
      )}
      {quote && (
        <blockquote className="phrase-card__quote" aria-label="The phrase in the paper" dangerouslySetInnerHTML={{ __html: quote }} />
      )}
      {verdict && (
        <p className="phrase-card__fidelity" data-fidelity={row.fidelity}>
          <strong>{verdict}</strong>
          {row.fidelity !== "same" && row.fidelity_note ? (
            <>
              : <span dangerouslySetInnerHTML={{ __html: noteHtml(row.fidelity_note).html }} />
            </>
          ) : (
            "."
          )}{" "}
          <span className="phrase-card__who">AI-assessed</span>
        </p>
      )}
      {(row.fidelity as string) === "held" && site.comparisonsHeld && <p className="phrase-card__fidelity">{site.comparisonsHeld}</p>}
      {note && (
        <div className="phrase-card__note">
          <p className="phrase-card__label">
            Reading note <span>· AI-drafted</span>
          </p>
          <NoteBody text={note} summary={leanNote && leanNote.text.trim() === note.trim() ? leanNote.summary : undefined} />
        </div>
      )}
    </section>
  );
}

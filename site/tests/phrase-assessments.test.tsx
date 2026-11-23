// A comparison is in one of three states, and the card says which: a verdict with every
// qualification the source wrote ("same" included), "Not assessed" where none is recorded, or
// the held text. A tie that holds several overlapping phrases shows each phrase's own
// comparison with that phrase's words, so one phrase's verdict is never read as another's.
import { renderToStaticMarkup } from "react-dom/server";
import { describe, expect, it } from "vitest";
import type { MergedPhrase, PhraseLean } from "../src/api/lean";
import { FidelityLine } from "../src/compare/Fidelity";
import { assessmentsOf, BriefPhraseCard, PhraseCard, phraseOpening } from "../src/reader/page/PhraseCard";

const row = (over: Partial<PhraseLean>): PhraseLean => ({
  name: "Demo.widget_round", module: "Demo.Basic", line: 4, end_line: 4, lines: [4, 4], relation: "states", note: "", ...over,
});

const text = (html: string) => html.replace(/<[^>]+>/g, "").replace(/&quot;/g, '"').replace(/&amp;/g, "&");

describe("the phrase card's comparison", () => {
  it("shows the note of a 'same' verdict, not only of the others", () => {
    const html = renderToStaticMarkup(<PhraseCard row={row({ fidelity: "same", fidelity_note: "Only for round widgets." })} topic={null} note={undefined} />);
    expect(text(html)).toContain("Lean states the same as this phrase: Only for round widgets.");
  });

  it("says 'Not assessed' where no comparison is recorded, and never 'same'", () => {
    for (const fidelity of ["unassessed", undefined] as const) {
      const html = renderToStaticMarkup(<PhraseCard row={row({ fidelity })} topic={null} note={undefined} />);
      expect(text(html)).toContain("Not assessed");
      expect(text(html)).not.toMatch(/same/i);
      expect(html).toContain('data-fidelity="unassessed"');
    }
  });

  it("gives a source-only mention the same link note in every card", () => {
    const mention = row({ relation: null, note: "The paper names `widget_round` here." });
    const cards = [
      <BriefPhraseCard row={mention} role="mention" />,
      <PhraseCard row={mention} role="mention" note={undefined} />,
      <PhraseCard row={mention} role="mention" note="A separate reading note." inLean />,
    ];
    for (const card of cards) {
      const html = renderToStaticMarkup(card);
      expect(html).toContain("The paper names <code>widget_round</code> here.");
      expect(html).not.toMatch(/Not assessed|States this result|Comparison terms|How the Lean compares/i);
    }
    expect(renderToStaticMarkup(cards[2])).toContain("A separate reading note.");
  });

  it("keeps a theorem statement's missing comparison and an assessed mention's verdict", () => {
    const statement = row({ relation: null, note: "The source binding covers only the first clause." });
    const assessed = { ...statement, fidelity: "different" as const, fidelity_note: "The theorem is about the diagonal." };
    const statementHtml = renderToStaticMarkup(<PhraseCard row={statement} role="statement" note={undefined} inLean />);
    expect(statementHtml).toContain("Not assessed");
    expect(statementHtml).toContain(statement.note);
    for (const role of ["mention", "statement"] as const) {
      expect(renderToStaticMarkup(<BriefPhraseCard row={assessed} role={role} />)).toContain(assessed.fidelity_note);
      expect(renderToStaticMarkup(<PhraseCard row={assessed} role={role} note={undefined} inLean />)).toContain(assessed.fidelity_note);
    }
  });

  it.each([
    ["statement", null, "`VWin` allows the window to depend on the prime pair."],
    ["derivation", "part", "The Lean argument supplies a separately proved `countZ` input."],
  ] as const)("uses a reviewed %s's scoped note in brief and expanded cards", (role, relation, note) => {
    const reviewed = row({ relation, note, source_review: true });
    const unassessed = row({ relation, note });
    const brief = renderToStaticMarkup(<BriefPhraseCard row={reviewed} role={role} />);
    const expanded = renderToStaticMarkup(<PhraseCard row={reviewed} role={role} note={undefined} inLean />);
    for (const card of [brief, expanded]) {
      expect(text(card)).toContain(note.replaceAll("`", ""));
      expect(card).not.toMatch(/Not assessed|No comparison|Comparison terms/);
    }
    expect(renderToStaticMarkup(<BriefPhraseCard row={unassessed} role={role} />)).toContain("Not assessed");
    expect(renderToStaticMarkup(<PhraseCard row={unassessed} role={role} note={undefined} inLean />)).toContain("Not assessed");
  });

  it("shows every phrase's own comparison in a merged tie, each with its words", () => {
    const merged: MergedPhrase[] = [
      { id: "p.outer", quote: "**Theorem 1.1.** Every widget is round and every gadget is square" },
      { id: "p.inner", quote: "every gadget is square" },
    ];
    const lean = row({
      fidelity: "same",
      assessments: [
        { phrase: "p.outer", fidelity: "same" },
        { phrase: "p.inner", fidelity: "stronger", fidelity_note: "Says more." },
      ],
    });
    const html = renderToStaticMarkup(<PhraseCard row={lean} topic={null} note={undefined} merged={merged} />);
    const words = text(html);
    expect(words).toContain("hold 2 overlapping phrases");
    expect(words).toContain("For “Theorem 1.1. Every widget is round and every gadget is square”: Lean states the same as this phrase.");
    expect(words).toContain("For “every gadget is square”: Lean states more: Says more.");
    expect(html.match(/phrase-card__fidelity/g)).toHaveLength(2);
  });

  it("a tie of one phrase shows its single comparison", () => {
    expect(assessmentsOf(row({ fidelity: "weaker", fidelity_note: "Less." }), undefined)).toEqual([
      { assessment: { fidelity: "weaker", fidelity_note: "Less." }, words: null },
    ]);
  });

  it("opens a long merged phrase between words and outside any formula", () => {
    const quote = "There is an odd divergence-free $u_0\\in C^\\infty(\\mathbb T^3;\\mathbb R^3)$ whose maximal classical solution $u$ of (1.1) is smooth $$\\int_0^T f$$ and odd";
    const opening = phraseOpening(quote, 6);
    expect(opening.replace(/\\\$/g, "").split("$").length % 2).toBe(1);
    expect(opening.startsWith("There is an odd divergence-free $u_0")).toBe(true);
    expect(phraseOpening("See \\[[45](#cite-W)\\] for $$x$$ more")).toBe("See [45] for … more");
  });
});

describe("a record's comparison line", () => {
  it("says 'Not assessed' for an unassessed row and shows a 'same' note", () => {
    expect(text(renderToStaticMarkup(<FidelityLine row={{ fidelity: "unassessed" }} />))).toContain("Not assessed.");
    expect(text(renderToStaticMarkup(<FidelityLine row={{ fidelity: "same", fidelity_note: "With one caveat." }} />))).toContain("With one caveat.");
  });
});

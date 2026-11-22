// The reader design (docs/reader-design.md): section aids set under their heads, the pane's
// remembered choices, the subject band, the inspector's order and words, the conventions that bear
// on a card, and the "Start here" guide.
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import type { PhraseLean } from "../src/api/lean";

vi.mock("@instance/site", async (importOriginal) => {
  const original = (await importOriginal()) as { default: Record<string, unknown> };
  return { default: { ...original.default, library: true, comparisonsHeld: undefined } };
});

const AIDS = {
  glossary: [
    { term: "Natural subtraction", convention: "$a - b = 0$ when $b > a$.", cards: ["declaration:Euler.first"] },
    { term: "Unrelated", convention: "Nothing here.", cards: ["tie:other"] },
    { term: "Real division", convention: "$x / 0 = 0$.", cards: ["tie:p1", "result:Euler.second"] },
  ],
  showcase: [
    { card: "p1", why: "The main estimate, stated as the paper states it.", text: "x" },
    { card: "p2", why: "A definition that differs from the paper's.", text: "y" },
  ],
};

beforeEach(() => {
  vi.stubGlobal(
    "fetch",
    vi.fn(async (url: string) => {
      const body = String(url).endsWith("aids.json") ? AIDS : String(url).endsWith("lean-notes.json") ? { notes: {} } : null;
      return { ok: body !== null, json: async () => body } as Response;
    }),
  );
});
afterEach(() => {
  vi.unstubAllGlobals();
});

// ---------------------------------------------------------------- section aids

describe("section aids", async () => {
  const { sectionAidFor, sectionAidHtml, prepareDocument } = await import("../src/reader/engine");

  const aids = {
    "5.6": "By number.",
    "Whole Title Here": "By whole title.",
    "Background": "By title without number.",
    A: "By appendix letter.",
  };

  it("finds an aid by section number, whole title, title without its number, or appendix letter", () => {
    expect(sectionAidFor(aids, "5.6 Anything at all")).toBe("By number.");
    expect(sectionAidFor(aids, "5.6. Anything at all")).toBe("By number.");
    expect(sectionAidFor(aids, "Whole Title Here")).toBe("By whole title.");
    expect(sectionAidFor(aids, "2 Background")).toBe("By title without number.");
    expect(sectionAidFor(aids, "A Proof of the lemma")).toBe("By appendix letter.");
    expect(sectionAidFor(aids, "7 Something else")).toBeNull();
    expect(sectionAidFor(aids, "Introduction")).toBeNull();
  });

  it("sets a one-sentence aid as a paragraph, escaped", () => {
    const html = sectionAidHtml("This section defines <b> & proves nothing.");
    const el = document.createElement("div");
    el.innerHTML = html;
    expect(el.children).toHaveLength(1);
    expect(el.firstElementChild!.tagName).toBe("P");
    expect(el.firstElementChild!.classList.contains("section-aid")).toBe(true);
    expect(el.querySelector("details")).toBeNull();
    expect(html).toContain("&lt;b&gt; &amp; proves");
    expect(html).not.toContain("<b>");
  });

  it("sets a longer aid as a disclosure: the first sentence in the summary, the rest in the body", () => {
    const first = "The formal development proves the bound $|x| \\le 1.5$ for every admissible flow.";
    const rest = "It then extends it to the closure. Nothing else is formalised.";
    const el = document.createElement("div");
    el.innerHTML = sectionAidHtml(`${first} ${rest}`);
    const details = el.querySelector("details.section-aid")!;
    expect(details).not.toBeNull();
    const summary = details.querySelector("summary")!;
    // The formula is typeset, and its full stop did not end the sentence.
    expect(summary.querySelector(".katex")).not.toBeNull();
    const label = summary.querySelector(".section-aid__label")!.textContent!;
    const summaryText = summary.textContent!.replace(label, "").trim();
    expect(summaryText.endsWith("for every admissible flow.")).toBe(true);
    expect(summaryText).not.toContain("closure");
    const body = details.querySelector(":scope > p")!.textContent!;
    expect(body).toContain("It then extends it to the closure. Nothing else is formalised.");
    expect(body).not.toContain("admissible flow");
  });

  const source = [
    "# 5.6 The paper's title",
    "",
    "Authors.",
    "",
    "## 5.6 Main estimate",
    "",
    "We prove it.",
    "",
    "### A. Appendix part",
    "",
    "More text.",
    "",
    "## 9 Unaided",
    "",
    "End.",
    "",
  ].join("\n");
  const prepare = (sectionAids?: Record<string, string>) =>
    prepareDocument({ stage: "t", bytes: new TextEncoder().encode(source), documentPath: "t/paper.md", documentPaths: { t: "t/paper.md" }, ...(sectionAids ? { sectionAids } : {}) });

  it("inserts the aid directly after its h2 or h3, and never after an h1", () => {
    const html = prepare({ "5.6": "Aid for five six.", A: "Aid for the appendix." }).renderAll().map((p) => p.html).join("");
    const el = document.createElement("div");
    el.innerHTML = html;
    const h1 = el.querySelector("h1")!;
    const h2 = el.querySelector("h2")!;
    const h3 = el.querySelector("h3")!;
    expect(h1.nextElementSibling?.classList.contains("section-aid")).toBe(false);
    expect(h2.nextElementSibling?.classList.contains("section-aid")).toBe(true);
    expect(h2.nextElementSibling!.textContent).toContain("Aid for five six.");
    expect(h3.nextElementSibling?.classList.contains("section-aid")).toBe(true);
    expect(h3.nextElementSibling!.textContent).toContain("Aid for the appendix.");
    expect(el.querySelectorAll(".section-aid")).toHaveLength(2);
  });

  it("renders byte-identical HTML without section aids", () => {
    const plain = prepare().renderAll().map((p) => p.html);
    const again = prepare().renderAll().map((p) => p.html);
    const unmatched = prepare({ "42": "Matches nothing." }).renderAll().map((p) => p.html);
    expect(again).toEqual(plain);
    expect(unmatched).toEqual(plain);
    expect(plain.join("")).not.toContain("section-aid");
  });
});

// ---------------------------------------------------------------- pane preferences

describe("the pane's remembered choices", async () => {
  const prefs = await import("../src/reader/page/panePrefs");
  beforeEach(() => {
    localStorage.clear();
    document.documentElement.removeAttribute("data-tones");
  });

  it("reads no view when nothing is stored, the stored view, and Lean from the legacy key", () => {
    expect(prefs.readView()).toBeNull();
    prefs.saveView("graph");
    expect(prefs.readView()).toBe("graph");
    prefs.saveView("lean");
    expect(prefs.readView()).toBe("lean");
    localStorage.clear();
    localStorage.setItem("lx-reader-keep-lean", "open");
    expect(prefs.readView()).toBe("lean");
    localStorage.setItem("lx-reader-view", "graph");
    expect(prefs.readView()).toBe("graph");
  });

  it("remembers the tone switch and sets it on the root", () => {
    expect(prefs.readTones()).toBe(true);
    prefs.saveTones(false);
    expect(prefs.readTones()).toBe(false);
    expect(document.documentElement.getAttribute("data-tones")).toBe("off");
    prefs.saveTones(true);
    expect(prefs.readTones()).toBe(true);
    expect(document.documentElement.hasAttribute("data-tones")).toBe(false);
    prefs.applyTones(false);
    expect(document.documentElement.getAttribute("data-tones")).toBe("off");
    prefs.applyTones(true);
    expect(document.documentElement.hasAttribute("data-tones")).toBe(false);
  });
});

// ---------------------------------------------------------------- mounting helpers

let container: HTMLDivElement;
let root: Root;
beforeEach(() => {
  (globalThis as { IS_REACT_ACT_ENVIRONMENT?: boolean }).IS_REACT_ACT_ENVIRONMENT = true;
  container = document.createElement("div");
  document.body.appendChild(container);
  root = createRoot(container);
});
afterEach(() => {
  act(() => root.unmount());
  container.remove();
});
const flush = async () => {
  for (let i = 0; i < 5; i++) await act(async () => await Promise.resolve());
};

// ---------------------------------------------------------------- subject band

describe("the subject band", async () => {
  const { SubjectBand } = await import("../src/reader/page/SubjectBand");
  const words = () => container.querySelector(".subject-band__words")!.textContent;
  const live = () => container.querySelector('[aria-live="polite"]')!.textContent;
  const acts = () => [...container.querySelectorAll<HTMLButtonElement>(".subject-band__act")];

  it("says each state in words", () => {
    const expected = { following: "Following the paper", preview: "Preview", words: "Selected words", paragraph: "Selected paragraph", declaration: "Selected declaration" } as const;
    for (const [state, text] of Object.entries(expected)) {
      act(() => root.render(<SubjectBand state={state as keyof typeof expected} place="§5.6" />));
      expect(words()).toBe(text);
      expect(container.querySelector(".subject-band")!.getAttribute("data-state")).toBe(state);
    }
  });

  it("offers Return only for a selection, and Auto and Manual as one switch", () => {
    const onResume = vi.fn();
    const onReturn = vi.fn();
    const onManual = vi.fn();
    const side = (name: string) => [...container.querySelectorAll<HTMLButtonElement>(".mode-switch__side")].find((b) => b.textContent === name)!;
    for (const state of ["following", "preview"] as const) {
      act(() => root.render(<SubjectBand state={state} place="§5.6" onResume={onResume} onReturn={onReturn} onManual={onManual} />));
      expect(acts()).toHaveLength(0);
      expect(side("Auto").getAttribute("aria-pressed")).toBe("true");
      expect(side("Manual").getAttribute("aria-pressed")).toBe("false");
    }
    act(() => side("Manual").click());
    expect(onManual).toHaveBeenCalledTimes(1);
    act(() => root.render(<SubjectBand state="following" place="§5.6" />));
    expect(side("Manual").disabled).toBe(true);
    act(() => root.render(<SubjectBand state="words" place="§5.6" onResume={onResume} onReturn={onReturn} />));
    const [back] = acts();
    expect(acts()).toHaveLength(1);
    expect(back.textContent).toBe("Return to selected words");
    expect(side("Manual").getAttribute("aria-pressed")).toBe("true");
    expect(side("Auto").title).toBe("Auto: the pane follows the passage you are reading");
    expect(side("Manual").title).toBe("Manual: the pane stays on what you selected");
    act(() => side("Auto").click());
    expect(onResume).toHaveBeenCalledTimes(1);
    expect(onReturn).not.toHaveBeenCalled();
    act(() => back.click());
    expect(onReturn).toHaveBeenCalledTimes(1);
  });

  it("makes the place a button only when it can return to it", () => {
    act(() => root.render(<SubjectBand state="words" place="§5.6" onResume={() => {}} />));
    expect(container.querySelector("button.subject-band__place")).toBeNull();
    expect(container.textContent).toContain("in §5.6");
    const onReturn = vi.fn();
    act(() => root.render(<SubjectBand state="words" place="§5.6" onResume={() => {}} onReturn={onReturn} />));
    const place = container.querySelector<HTMLButtonElement>("button.subject-band__place")!;
    expect(place.textContent).toBe("in §5.6");
    act(() => place.click());
    expect(onReturn).toHaveBeenCalledTimes(1);
  });

  it("announces a change of state, not the first state nor a new title within one state", () => {
    act(() => root.render(<SubjectBand state="following" title="One" />));
    expect(live()).toBe("");
    act(() => root.render(<SubjectBand state="following" title="Two" />));
    expect(live()).toBe("");
    act(() => root.render(<SubjectBand state="words" title="Theorem 1.1" place="§1" />));
    expect(live()).toBe("Selected words: Theorem 1.1");
    act(() => root.render(<SubjectBand state="words" title="Lemma 2.3" place="§2" />));
    expect(live()).toBe("Selected words: Theorem 1.1");
    act(() => root.render(<SubjectBand state="following" title="Lemma 2.3" />));
    expect(live()).toBe("Following the paper");
  });
});

// ---------------------------------------------------------------- phrase card

describe("the inspector's phrase card", async () => {
  const { PhraseCard } = await import("../src/reader/page/PhraseCard");
  const row = (over: Partial<PhraseLean>): PhraseLean => ({ name: "Euler.first", module: "Euler", ...over }) as PhraseLean;
  const fidelityText = () => container.querySelector(".phrase-card__fidelity")!.textContent!;

  it("orders the quotation, the comparison, the reading note and the conventions", async () => {
    act(() => root.render(<PhraseCard row={row({ fidelity: "stronger", fidelity_note: "It drops a hypothesis." })} note="The Lean says $x = 1$." quote="the words <em>as set</em>" phrase="p1" names={["Euler.first"]} />));
    await flush();
    const card = container.querySelector(".phrase-card")!;
    const order = [...card.children].map((el) => el.className.split(" ")[0]);
    expect(order).toEqual(["phrase-card__quote", "phrase-card__compare", "phrase-card__note", "phrase-card__conventions"]);
    // Both conventions that bear on this card, in the glossary's order.
    expect([...card.querySelectorAll(".phrase-card__conventions summary")].map((s) => s.textContent)).toEqual(["Natural subtraction", "Real division"]);
  });

  it("shows a same verdict's note and says AI-assessed", () => {
    act(() => root.render(<PhraseCard row={row({ fidelity: "same", fidelity_note: "After reading $n$ as a natural number." })} note={undefined} />));
    expect(fidelityText()).toContain("Lean states the same as this phrase:");
    expect(fidelityText()).toContain("After reading");
    expect(container.querySelector(".phrase-card__fidelity .katex")).not.toBeNull();
    // The verdict says who assessed it; the block's label does not say it a second time.
    expect(fidelityText()).toContain("AI-assessed");
    expect(container.querySelector(".phrase-card__compare .phrase-card__label")!.textContent).toBe("Comparison with these words");
  });

  it("says when no comparison is recorded, and does not call it AI-assessed", () => {
    act(() => root.render(<PhraseCard row={row({})} note={undefined} />));
    expect(fidelityText()).toBe("Not assessed. No comparison of these words with this Lean is recorded.");
    expect(container.querySelector(".phrase-card__fidelity")!.getAttribute("data-fidelity")).toBe("unassessed");
    expect(container.textContent).not.toContain("AI-assessed");
    expect(container.textContent).not.toMatch(/same/i);
  });

  it("says a withheld comparison is withheld", () => {
    act(() => root.render(<PhraseCard row={row({ fidelity: "held" as never })} note={undefined} />));
    expect(container.querySelector(".phrase-card__fidelity")!.getAttribute("data-fidelity")).toBe("held");
    expect(fidelityText()).not.toMatch(/same|not assessed/i);
    expect(container.textContent).not.toContain("AI-assessed");
  });

  it("gives the legend's six words, in the card's own words, once it is opened", () => {
    act(() => root.render(<PhraseCard row={row({ fidelity: "weaker" })} note={undefined} />));
    const legend = container.querySelector<HTMLDetailsElement>(".phrase-card__legend")!;
    // Closed, it names no verdict, so no verdict's name stands beside a different comparison.
    expect(legend.querySelectorAll("dt")).toHaveLength(0);
    act(() => {
      legend.open = true;
      legend.dispatchEvent(new Event("toggle"));
    });
    const words = [...legend.querySelectorAll("dt")].map((dt) => dt.textContent);
    expect(words).toEqual(["Lean states the same as this phrase", "Lean states more", "Lean states less", "Lean states something different", "Not assessed", "Withheld"]);
  });
});

// ---------------------------------------------------------------- conventions

describe("the conventions that bear on a card", async () => {
  const { cardKeys, cardTarget, conventionsFor } = await import("../src/reader/aids");
  const aids = { glossary: AIDS.glossary, showcase: [] };

  it("names a card by its phrase and each declaration, as a declaration, a result and bare", () => {
    expect(cardKeys("p1", ["A.b", "C.d"])).toEqual(["tie:p1", "p1", "declaration:A.b", "result:A.b", "A.b", "declaration:C.d", "result:C.d", "C.d"]);
    expect(cardKeys(null, ["A.b"])).toEqual(["declaration:A.b", "result:A.b", "A.b"]);
    expect(cardKeys(undefined, [])).toEqual([]);
    // Navier–Stokes names a showcase card by its bare phrase id; Euler by kind and id.
    expect(cardTarget("p::s1-theorem-premise")).toEqual({ kind: "bare", id: "p::s1-theorem-premise" });
    expect(cardTarget("result:TorusEuler.Paper.lemma_1_3")).toEqual({ kind: "result", id: "TorusEuler.Paper.lemma_1_3" });
  });

  it("matches by tie, declaration and result keys, in the glossary's order", () => {
    expect(conventionsFor(aids, ["tie:p1"]).map((c) => c.term)).toEqual(["Real division"]);
    expect(conventionsFor(aids, ["declaration:Euler.first"]).map((c) => c.term)).toEqual(["Natural subtraction"]);
    expect(conventionsFor(aids, ["result:Euler.second"]).map((c) => c.term)).toEqual(["Real division"]);
    expect(conventionsFor(aids, ["result:Euler.second", "declaration:Euler.first", "tie:other"]).map((c) => c.term)).toEqual(["Natural subtraction", "Unrelated", "Real division"]);
    expect(conventionsFor(aids, [])).toEqual([]);
    expect(conventionsFor(aids, ["tie:nothing"])).toEqual([]);
    expect(conventionsFor({ glossary: [], showcase: [] }, ["tie:p1"])).toEqual([]);
  });
});

// ---------------------------------------------------------------- start here

describe("Start here", async () => {
  const { StartHere } = await import("../src/reader/page/Guides");
  const titles: Record<string, string> = { p1: "Theorem 1.1", p2: "Definition 2.1" };

  it("lists every card with its title and why, and opens the one chosen", () => {
    const onOpen = vi.fn();
    act(() => root.render(<StartHere cards={AIDS.showcase} titleOf={(c) => titles[c]} onOpen={onOpen} />));
    const items = [...container.querySelectorAll<HTMLButtonElement>(".guide-panel__cards button")];
    expect(items).toHaveLength(2);
    expect(items.map((b) => b.querySelector(".guide-panel__title")!.textContent)).toEqual(["Theorem 1.1", "Definition 2.1"]);
    expect(items.map((b) => b.querySelector(".guide-panel__why")!.textContent)).toEqual(AIDS.showcase.map((c) => c.why));
    act(() => items[1].click());
    expect(onOpen).toHaveBeenCalledWith("p2");
  });

  it("has a Close button only when it can close", () => {
    act(() => root.render(<StartHere cards={AIDS.showcase} titleOf={(c) => titles[c]} onOpen={() => {}} />));
    expect([...container.querySelectorAll("button")].some((b) => b.textContent === "Close")).toBe(false);
    const onClose = vi.fn();
    act(() => root.render(<StartHere cards={AIDS.showcase} titleOf={(c) => titles[c]} onOpen={() => {}} onClose={onClose} />));
    const close = [...container.querySelectorAll<HTMLButtonElement>("button")].find((b) => b.textContent === "Close")!;
    expect(close).toBeTruthy();
    act(() => close.click());
    expect(onClose).toHaveBeenCalledTimes(1);
  });
});

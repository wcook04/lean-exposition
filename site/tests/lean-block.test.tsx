// @vitest-environment jsdom
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, describe, expect, it, vi } from "vitest";
import type { LeanDeclaration, LeanModule, LeanModules } from "../src/api/lean";
import type { LeanShell } from "../src/lean/data";
import { signatureText } from "../src/lean/data";
import { DeclView, LeanFacts } from "../src/lean/LeanBlock";
import { AnnotationSources, PassageAnnotation } from "../src/reader/page/PhraseCard";
import { buildIndex } from "../src/lean/resolve";
import { hasLeanHost, hostLean, showInHost } from "../src/lean/walk";
import { paperBlocks, orderStatements, statementRows } from "../src/search/corpus";

const source = ["theorem main (x : Thing) : Good x := by", "  have h := helper x", "  exact h", "", "def Thing : Type := Nat", "theorem helper (x : Thing) : Good x := sorry"].join("\n");
const decl = (over: Partial<LeanDeclaration>): LeanDeclaration => ({ name: "OAI.main", short: "main", kind: "theorem", namespace: "OAI", line: 1, signature_end_line: 1, end_line: 3, doc: null, private: false, uses: ["OAI.Thing", "OAI.helper"], used_by: [], ...over });
const main = decl({});
const helper = decl({ name: "OAI.helper", short: "helper", line: 6, signature_end_line: 6, end_line: 6, uses: ["OAI.Thing"], used_by: ["OAI.main"] });
const module: LeanModule = { module: "OAI.M", path: "OAI/M.lean", sha256: "", imports: [], source, declarations: [main, helper] };
const shell: LeanShell = {
  plain: new Map(),
  modules: { base_url: "https://github.com/o/r/blob/abc/lean/", revision: "abcdef1234", dependency_source: "source_text" } as LeanModules,
  index: buildIndex({ modules: ["OAI.M"], names: [["OAI.main", "theorem", 0, 1, 3], ["OAI.Thing", "def", 0, 5, 5], ["OAI.helper", "theorem", 0, 6, 6]] }),
  paths: new Map([["OAI.M", { module: "OAI.M", path: "OAI/M.lean", lines: 6, declarations: 3, sha256: "" }]]),
  terms: new Map(),
  linked: new Map(),
};

let root: Root | undefined;
let host: HTMLDivElement | undefined;
afterEach(async () => {
  if (root) await act(async () => root!.unmount());
  host?.remove();
  root = undefined;
});

async function render(node: React.ReactNode): Promise<HTMLDivElement> {
  host = document.createElement("div");
  document.body.append(host);
  root = createRoot(host);
  await act(async () => root!.render(node));
  return host;
}

const nameLink = (view: HTMLElement, text: string) => [...view.querySelectorAll<HTMLElement>("a[data-t]")].find((a) => a.textContent === text)!;

describe("LeanBlock's props", () => {
  it("lights exact lines, and opens the proof when they lie in it", async () => {
    const view = await render(<DeclView decl={main} module={module} shell={shell} lines={[2, 2]} noTerms noDependencies noPapers />);
    expect([...view.querySelectorAll(".lean-line.is-lit")].map((line) => (line as HTMLElement).dataset.line)).toEqual(["2"]);
    expect(view.querySelector(".lean-block__proof")).not.toBeNull();
  });

  it("keeps a passage's proof folded and its one annotated reading directly below", async () => {
    const view = await render(
      <DeclView decl={main} module={module} shell={shell} lines={[2, 2]}
        passageNote={<PassageAnnotation text="In `main`, $x$ is the input to `helper`." creditInSources />}
        noTerms noDependencies noPapers />
    );
    const code = view.querySelector(".lean-code")!;
    const fold = view.querySelector<HTMLButtonElement>(".lean-fold")!;
    const annotation = view.querySelector<HTMLElement>(".passage-annotation")!;
    const details = view.querySelector<HTMLDetailsElement>(".lean-block__details")!;
    expect(code.nextElementSibling).toBe(fold);
    expect(fold.getAttribute("aria-expanded")).toBe("false");
    expect(fold.nextElementSibling).toBe(annotation);
    const note = annotation.textContent?.trim() ?? "";
    expect(note).toMatch(/^In main,/);
    expect(note).not.toContain("AI-written");
    expect(annotation.querySelector(".phrase-card__label")).toBeNull();
    expect([...annotation.querySelectorAll("code")].map(el => el.textContent)).toEqual(["main", "helper"]);
    expect(annotation.querySelector(".katex")).not.toBeNull();
    expect(annotation.nextElementSibling).toBe(details);
    expect(details.querySelector(":scope > summary > small.lean-block__credit")?.textContent).toBe("AI-written annotation");
    expect(view.querySelectorAll(".lean-block__credit")).toHaveLength(1);
    expect(details.open).toBe(false);
    expect(details.querySelector(".lean-block__actions")).not.toBeNull();
    await act(async () => fold.click());
    expect(view.querySelector(".lean-block__proof .lean-line.is-lit")).not.toBeNull();
    expect(view.querySelectorAll(".passage-annotation")).toHaveLength(1);
    await act(async () => fold.click());
  });

  it("credits a standalone graph annotation below its mathematical text", async () => {
    const view = await render(<PassageAnnotation text="Apply `helper` to $x$." />);
    const annotation = view.querySelector(".passage-annotation")!;
    const text = annotation.firstElementChild!;
    expect(text.classList.contains("passage-annotation__text")).toBe(true);
    expect(text.textContent).toMatch(/^Apply helper/);
    expect(annotation.querySelector(".phrase-card__label")).toBeNull();
    expect(text.nextElementSibling).toBe(annotation.lastElementChild);
    expect(annotation.lastElementChild?.textContent).toBe("AI-written annotation");
    expect(annotation.querySelectorAll(".lean-block__credit")).toHaveLength(1);
  });

  it("links resolvable equation lists, numbered statements and sections in annotation prose", async () => {
    const onPaperReference = vi.fn();
    const first = { line: 18, page: 2, y: 0.3, tone: 0 };
    const view = await render(<PassageAnnotation
      text={"Equations (1.1), (1.2)–(1.3) use Theorem 2.4, Lemmas 3.1 and 3.2, and §4. Compare (1.1–1.3), not 1.1 or (9.9). Code `(1.1)` and math $(1.1)$."}
      referenceTargets={{
        "equation:1.1": first, "equation:1.2": { line: 19 }, "equation:1.3": { line: 20 },
        "theorem:2.4": { line: 32 }, "lemma:3.1": { line: 46 }, "lemma:3.2": { line: 52 },
        "section:4": { line: 60 },
      }}
      paperReferenceHref={({ line }) => `/adapted/?l=${line}`}
      onPaperReference={onPaperReference}
    />);
    const links = [...view.querySelectorAll<HTMLAnchorElement>("a")];
    expect(links.map((link) => link.textContent)).toEqual([
      "Equations (1.1)", "(1.2)", "(1.3)", "Theorem 2.4", "Lemmas 3.1", "3.2", "§4", "1.1", "1.3",
    ]);
    expect(links[0].getAttribute("href")).toBe("/adapted/?l=18");
    expect(links[0].dataset.tone).toBe("0");
    expect(links[1].dataset.tone).toBeUndefined();
    expect(view.querySelector("code a, .katex a")).toBeNull();
    const click = new MouseEvent("click", { bubbles: true, cancelable: true });
    await act(async () => void links[0].dispatchEvent(click));
    expect(click.defaultPrevented).toBe(true);
    expect(onPaperReference).toHaveBeenCalledExactlyOnceWith(first, "equation:1.1");

    links[0].href = "#equation";
    const modifiedClick = new MouseEvent("click", { bubbles: true, cancelable: true, metaKey: true });
    await act(async () => void links[0].dispatchEvent(modifiedClick));
    expect(modifiedClick.defaultPrevented).toBe(false);
    expect(onPaperReference).toHaveBeenCalledTimes(1);
  });

  it("links the local source locator and preserves an external citation's own destination", async () => {
    const view = await render(<AnnotationSources
      explanation={{ text: "", citations: [
        { ref: "paper", title: "This paper", where: "Theorem 2.4" },
        { ref: "external", title: "Other paper", where: "Theorem 2.4", url: "https://example.com/" },
      ] }}
      referenceTargets={{ "theorem:2.4": { line: 32 } }}
    />);
    expect([...view.querySelectorAll("a")].map((link) => [link.textContent, link.getAttribute("href")])).toEqual([
      ["Theorem 2.4", "?l=32"], ["Other paper", "https://example.com/"],
    ]);
  });

  it("links only the reviewed occurrence and uses the other edition's palette", async () => {
    const source = "Step (2) precedes Equation (2). See `extE` in the long edition.";
    const local = { line: 27, tone: 1 };
    const other = { line: 93, stage: "long", tone: 3, colours: { light: "oklch(0.485 0.190 359.0)", dark: "oklch(0.660 0.190 359.0)" } };
    const onPaperReference = vi.fn();
    const span = (text: string, key: string) => ({ start: source.indexOf(text), end: source.indexOf(text) + text.length, key });
    const view = await render(<PassageAnnotation
      text={source}
      reviewed={[span("Equation (2)", "equation:2"), span("`extE`", "long/definition:exte")]}
      referenceTargets={{ "equation:2": local, "long/definition:exte": other }}
      paperReferenceHref={({ stage, line }) => `/read/${stage ?? "short"}/?l=${line}`}
      onPaperReference={onPaperReference}
    />);
    const links = [...view.querySelectorAll("a")];
    expect(links.map((link) => link.textContent)).toEqual(["Equation (2)", "extE"]);
    expect(links[1].querySelector("code")?.textContent).toBe("extE");
    expect(links[1].target).toBe("_blank");
    expect(links[1].getAttribute("href")).toBe("/read/long/?l=93");
    expect(links[1].style.getPropertyValue("--tone")).toBe("light-dark(oklch(0.485 0.190 359.0), oklch(0.660 0.190 359.0))");
    const click = new MouseEvent("click", { bubbles: true, cancelable: true });
    await act(async () => void links[0].dispatchEvent(click));
    expect(onPaperReference).toHaveBeenCalledExactlyOnceWith(local, "equation:2");
  });

  it("links printed reference abbreviations and lettered targets", async () => {
    const view = await render(<PassageAnnotation
      text="See Eq. (18)/(20), Appendix G.4, Fig. S11, Propositions 8.1–8.2, Lemma A.2, §2.2.1, and Equation (B.30)."
      referenceTargets={{
        "equation:18": { line: 18 }, "equation:20": { line: 20 }, "appendix:g.4": { line: 41 },
        "figure:s11": { line: 52 }, "proposition:8.1": { line: 61 }, "proposition:8.2": { line: 62 },
        "lemma:a.2": { line: 72 }, "section:2.2.1": { line: 82 }, "equation:b.30": { line: 91 },
      }}
    />);
    expect([...view.querySelectorAll("a")].map((link) => link.textContent)).toEqual([
      "Eq. (18)", "(20)", "Appendix G.4", "Fig. S11", "Propositions 8.1", "8.2", "Lemma A.2", "§2.2.1", "Equation (B.30)",
    ]);
  });

  it("takes several ranges, and leaves the proof folded for lines in the statement", async () => {
    const view = await render(<DeclView decl={main} module={module} shell={shell} lines={[[1, 1]]} noTerms noDependencies noPapers />);
    expect(view.querySelectorAll(".lean-line.is-lit").length).toBe(1);
    expect(view.querySelector(".lean-block__proof")).toBeNull();
    expect(view.querySelector(".lean-fold")?.textContent).toContain("Proof");
  });

  it("moves the nearest scroller to lit lines, unless told to stay quiet", async () => {
    const tall = { ...module, source: `${"-- filler\n".repeat(40)}theorem far : True := trivial` };
    const far = decl({ name: "OAI.far", short: "far", line: 41, signature_end_line: 41, end_line: 41 });
    const mount = async (quiet: boolean) => {
      const box = document.createElement("div");
      box.style.overflowY = "auto";
      document.body.append(box);
      Object.defineProperty(box, "scrollHeight", { value: 900 });
      Object.defineProperty(box, "clientHeight", { value: 200 });
      box.getBoundingClientRect = () => ({ top: 0, bottom: 200, height: 200 }) as DOMRect;
      const inner = createRoot(box);
      Element.prototype.getBoundingClientRect = function () { return this === box ? ({ top: 0, bottom: 200, height: 200 } as DOMRect) : ({ top: 600, bottom: 620, height: 20 } as DOMRect); };
      await act(async () => inner.render(<DeclView decl={far} module={tall} shell={shell} lines={[41, 41]} quietLines={quiet} noTerms noDependencies noPapers />));
      const top = box.scrollTop;
      await act(async () => inner.unmount());
      box.remove();
      return top;
    };
    const original = Element.prototype.getBoundingClientRect;
    // The column moves only in answer to the reader: the lines are shown after a press.
    window.dispatchEvent(new Event("pointerdown"));
    expect(await mount(true)).toBe(0);
    expect(await mount(false)).toBeGreaterThan(0);
    Element.prototype.getBoundingClientRect = original;
  });

  it("reports a name to onName and stays on the page", async () => {
    const onName = vi.fn();
    const view = await render(<DeclView decl={main} module={module} shell={shell} onName={onName} noTerms noDependencies noPapers />);
    const click = new MouseEvent("click", { bubbles: true, cancelable: true });
    await act(async () => void nameLink(view, "Thing").dispatchEvent(click));
    expect(onName).toHaveBeenCalledWith({ name: "OAI.Thing", module: "OAI.M", short: "Thing", from: "OAI.main" });
    expect(click.defaultPrevented).toBe(true);
  });

  it("leaves a name a real link without onName", async () => {
    const view = await render(<DeclView decl={main} module={module} shell={shell} noTerms noDependencies noPapers />);
    const click = new MouseEvent("click", { bubbles: true, cancelable: true });
    await act(async () => void nameLink(view, "Thing").dispatchEvent(click));
    expect(click.defaultPrevented).toBe(false);
    expect(nameLink(view, "Thing").getAttribute("href")).toContain("/lean/?m=OAI.M&d=OAI.Thing");
  });

  it("offers the whole file here first, and GitHub's pinned line range second", async () => {
    const view = await render(<DeclView decl={main} module={module} shell={shell} noTerms noDependencies noPapers />);
    const actions = [...view.querySelectorAll<HTMLAnchorElement>(".lean-block__actions a")];
    expect(actions.map((a) => a.textContent)).toEqual(["Whole file", "On GitHub"]);
    expect(actions[0].getAttribute("href")).toBe("/lean/?m=OAI.M&file=1-3");
    expect(actions[1].getAttribute("href")).toBe("https://github.com/o/r/blob/abc/lean/OAI/M.lean#L1-L3");
  });

  it("opens an archived source at its DOI while keeping the exact local lines", async () => {
    const doi = "https://doi.org/10.5281/zenodo.19081887";
    const archived = { ...shell, modules: { ...shell.modules, revision: doi, base_url: `${doi}/blob/${doi}/` } };
    const view = await render(<DeclView decl={main} module={module} shell={archived} compact noTerms noDependencies noPapers />);
    const actions = Array.from(view.querySelectorAll<HTMLAnchorElement>("a.lean-action"));
    expect(actions.map((a) => a.textContent)).toEqual(["Whole file", "Source archive"]);
    expect(actions.map((a) => a.getAttribute("href"))).toEqual(["/lean/?m=OAI.M&file=1-3", doi]);
  });

  it("puts the head and reading line around a scrolling middle when filling", async () => {
    const view = await render(<DeclView decl={main} module={module} shell={shell} compact fill noTerms noDependencies noPapers />);
    expect(view.querySelector(".lean-block.is-compact.is-fill > .lean-block__head")).not.toBeNull();
    expect(view.querySelector(".lean-block__scroll .lean-code")).not.toBeNull();
    expect(view.querySelector(".lean-block.is-fill > .lean-slot")).not.toBeNull();
  });

  it("reads a name into the host's slot, and leaves none of its own", async () => {
    const slot = document.createElement("div");
    document.body.append(slot);
    const view = await render(<DeclView decl={main} module={module} shell={shell} previewSlot={slot} noTerms noDependencies noPapers />);
    expect(view.querySelector(".lean-slot")).toBeNull();
    await act(async () => void nameLink(view, "Thing").focus());
    expect(slot.textContent).toContain("Thing");
    expect(slot.textContent).toContain("Definition in M.lean, line 5");
    slot.remove();
  });

  it("drops the head for a host that has its own", async () => {
    const view = await render(<DeclView decl={main} module={module} shell={shell} noHead noTerms noDependencies noPapers />);
    expect(view.querySelector(".lean-block__head")).toBeNull();
  });

  it("gives the statement as one line of source", () => {
    expect(signatureText(module, helper)).toBe("theorem helper (x : Thing) : Good x := sorry");
    expect(signatureText(module, main)).toBe("theorem main (x : Thing) : Good x");
  });
});

describe("axioms and sorry", () => {
  it("says a text scan is a text scan", async () => {
    const clean = await render(<LeanFacts decl={main} module={module} />);
    expect(clean.textContent).toContain("A text scan finds no sorry");
    expect(clean.textContent).toContain("no report from Lean");
  });

  it("finds sorry by scanning, and never in a comment", async () => {
    const view = await render(<LeanFacts decl={helper} module={module} />);
    expect(view.textContent).toContain("A text scan finds sorry");
    const commented: LeanModule = { ...module, source: "theorem a : True := trivial -- not sorry" };
    const quiet = await render(<LeanFacts decl={decl({ line: 1, end_line: 1 })} module={commented} />);
    expect(quiet.textContent).toContain("finds no sorry");
  });

  it("gives Lean's report when the edition has one", async () => {
    const reported = { ...main, axioms: ["propext", "Classical.choice", "Quot.sound"] } as LeanDeclaration;
    const view = await render(<LeanFacts decl={reported} module={module} />);
    expect(view.textContent).toBe("Lean reports that it depends on the axioms propext, Classical.choice and Quot.sound.");
  });
});

describe("the host seam", () => {
  it("shows a declaration in the page that offers, and otherwise says no", () => {
    const show = vi.fn();
    expect(showInHost({ name: "a", module: "m", short: "a" })).toBe(false);
    const stop = hostLean(show);
    expect(hasLeanHost()).toBe(true);
    expect(showInHost({ name: "a", module: "m", short: "a" })).toBe(true);
    stop();
    expect(hasLeanHost()).toBe(false);
  });
});

describe("what search reads from the papers", () => {
  const paper = "# Title\n\nFirst paragraph with $x$.\nStill first.\n\n## 1. A section\n\nA display:\n$$\na\n\nb\n$$\nafter.\n\n## References\n\nSomeone (2020). See https://example.test/a-b.\n";

  it("cuts at blank lines with exact bytes, keeps a display whole and skips the references", () => {
    const rows = paperBlocks("short", paper);
    expect(rows.map((row) => row.section)).toEqual(["Title", "1. A section"]);
    const bytes = new TextEncoder().encode(paper);
    const [start, end] = /b(\d+)-(\d+)/.exec(decodeURIComponent(rows[1].href))!.slice(1).map(Number);
    expect(new TextDecoder().decode(bytes.slice(start, end))).toBe("A display:\n$$\na\n\nb\n$$\nafter.");
  });

  it("counts bytes, not characters, past a multi-byte letter", () => {
    const rows = paperBlocks("short", "𝔼 and é\n\nSecond block.\n");
    const [start] = /b(\d+)-/.exec(rows[1].href)!.slice(1).map(Number);
    expect(start).toBe(new TextEncoder().encode("𝔼 and é\n\n").length);
  });

  it("holds each slice once and leaves bare mentions out", () => {
    const statement = { paper: "short", role: "statement", markdown: "S", start_byte: 1, end_byte: 2, anchor: "a", section: "1. X", heading_id: null };
    const rows = statementRows({ dictionary: [], records: { a: { short: "A", lean: [], statements: [statement, { ...statement, role: "mention", start_byte: 9 }] }, b: { short: "B", lean: [], statements: [statement] } } } as never);
    expect(rows.map((row) => row.label)).toEqual(["A"]);
    expect(rows[0].href).toContain("l=b1-2");
  });

  it("puts a statement of the thing before a passage that uses the word", () => {
    const items = [{ ref: "1", table: "statements", label: "Other", role: "explanation" }, { ref: "2", table: "statements", label: "Other", role: "statement" }, { ref: "3", table: "statements", label: "Parisi value", role: "derivation" }];
    expect(orderStatements(items, "parisi").map((item) => item.ref)).toEqual(["3", "2", "1"]);
  });
});

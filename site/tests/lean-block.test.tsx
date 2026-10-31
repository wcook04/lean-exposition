// @vitest-environment jsdom
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, describe, expect, it, vi } from "vitest";
import type { LeanDeclaration, LeanModule, LeanModules } from "../src/api/lean";
import type { LeanShell } from "../src/lean/data";
import { signatureText } from "../src/lean/data";
import { DeclView, LeanFacts } from "../src/lean/LeanBlock";
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

  it("links source to the commit-pinned line range", async () => {
    const view = await render(<DeclView decl={main} module={module} shell={shell} noTerms noDependencies noPapers />);
    const source = [...view.querySelectorAll("a")].find((a) => a.textContent === "source")!;
    expect(source.getAttribute("href")).toBe("https://github.com/o/r/blob/abc/lean/OAI/M.lean#L1-L3");
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
    expect(view.textContent).toBe("Lean reports that it rests on the axioms propext, Classical.choice and Quot.sound.");
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

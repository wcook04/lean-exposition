// @vitest-environment jsdom
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, describe, expect, it } from "vitest";
import type { LeanModules } from "../src/api/lean";
import type { LeanShell } from "../src/lean/data";
import { LINK_CAVEAT, RELATION_WORDS, dependencyWords, kindWord } from "../src/lean/data";
import { ReadingStrip } from "../src/lean/ReadingStrip";
import { buildIndex, type DeclRow } from "../src/lean/resolve";

const row: DeclRow = { name: "OAI.X.OrderParameter", short: "OrderParameter", kind: "structure", module: "OAI.X.Model", line: 17, endLine: 22 };
const shell: LeanShell = {
  modules: {} as LeanModules,
  index: buildIndex({ modules: [], names: [] }),
  paths: new Map([["OAI.X.Model", { module: "OAI.X.Model", path: "OAI/X/Model.lean", lines: 90, declarations: 29, sha256: "" }]]),
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

describe("the reading strip", () => {
  it("says how to use it before a name is read", async () => {
    const view = await render(<ReadingStrip target={null} shell={shell} />);
    expect(view.querySelector('[role="status"]')?.textContent).toMatch(/Point at a name/);
  });

  it("gives a dictionary term as notation, words, kind and place", async () => {
    const term = { name: row.name, module: row.module, line: 17, tex: "\\mathcal U", words: "The admissible class." };
    const container = await render(<ReadingStrip target={{ kind: "decl", row, term }} shell={shell} />);
    expect(container.querySelector(".katex")).not.toBeNull();
    expect(container.textContent).toContain("The admissible class.");
    expect(container.textContent).toContain("Structure in OAI/X/Model.lean, line 17");
  });

  it("says From Mathlib and links the search", async () => {
    const view = await render(<ReadingStrip target={{ kind: "mathlib", name: "Set.Ico" }} shell={shell} />);
    expect(view.textContent).toContain("From Mathlib");
    expect(view.querySelector("a")?.getAttribute("href")).toBe("https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Set.Ico");
  });
});

describe("the wording", () => {
  it("names each relation and never claims equivalence", () => {
    expect(RELATION_WORDS.part).toBe("States one part of this result");
    expect(LINK_CAVEAT).toBe("Linked by reading the source. Not checked as equivalent.");
    expect(dependencyWords("source_text")).toBe("Names found in the source text");
    expect(kindWord("def")).toBe("Definition");
  });
});

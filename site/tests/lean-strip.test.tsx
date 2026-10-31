// @vitest-environment jsdom
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, describe, expect, it } from "vitest";
import type { LeanModules } from "../src/api/lean";
import type { LeanShell } from "../src/lean/data";
import { LINK_CAVEAT, RELATION_WORDS, dependencyWords, kindWord } from "../src/lean/data";
import { barPlace, ReadingLine } from "../src/lean/ReadingStrip";
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

describe("the reading line", () => {
  it("gives a dictionary term as notation and words", async () => {
    const term = { name: row.name, module: row.module, line: 17, tex: "\\mathcal U", words: "The admissible class." };
    const container = await render(<ReadingLine target={{ kind: "decl", row, term }} shell={shell} />);
    expect(container.querySelector(".katex")).not.toBeNull();
    expect(container.textContent).toContain("The admissible class.");
  });

  it("gives a name with no words its kind and place", async () => {
    const container = await render(<ReadingLine target={{ kind: "decl", row }} shell={shell} />);
    expect(container.textContent).toContain("Structure in Model.lean, line 17");
  });

  it("says From Mathlib and leaves the link to the name itself", async () => {
    const view = await render(<ReadingLine target={{ kind: "mathlib", name: "Set.Ico" }} shell={shell} />);
    expect(view.textContent).toContain("From Mathlib");
    expect(view.querySelector("a")).toBeNull();
  });

  it("keeps a long name whole in its text while allowing breaks only at its parts", async () => {
    const long = { ...row, short: "contactPotential_hasDerivAt" };
    const view = await render(<ReadingLine target={{ kind: "decl", row: long }} shell={shell} />);
    const name = view.querySelector(".lean-break")!;
    expect(name.textContent).toBe("contactPotential_hasDerivAt");
    expect([...name.querySelectorAll(":scope > span")].map((part) => part.textContent)).toEqual(["contactPotential_", "hasDerivAt"]);
  });

  it("sits at the column's foot, and moves to its head rather than cover the name", () => {
    const column = { left: 300, top: 52, width: 700, bottom: 790 };
    expect(barPlace(column, { bottom: 400 }, 31)).toEqual({ left: 300, width: 700, top: 759, edge: "bottom" });
    expect(barPlace(column, { bottom: 757 }, 31)).toEqual({ left: 300, width: 700, top: 52, edge: "top" });
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

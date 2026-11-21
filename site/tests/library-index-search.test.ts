// The library index's search (scripts/build_library_index_assets/index.js) says what it covers and
// matches a result's number exactly: "Lemma 2.1" never finds Lemma 2.5 through "(2.12)", and a
// paper whose contents could not be loaded is named rather than left "loading".
// @vitest-environment jsdom
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { beforeEach, describe, expect, it, vi } from "vitest";

const SCRIPT = readFileSync(resolve(__dirname, "../../scripts/build_library_index_assets/index.js"), "utf8");

const SHARD = {
  schema: "library-search/1", paper: "euler", lean_base: "/library/euler/lean/",
  statements: [
    ["Lemma 2.1", "For every $x$ the bound holds.", "/library/euler/lemma-2.1/"],
    ["Lemma 2.5", "By (2.12) and Lemma 2.4 the estimate follows.", "/library/euler/lemma-2.5/"],
    ["Bounded velocity", "The velocity is bounded, see (2.1).", "/library/euler/@p"],
  ],
  lean: [["TorusEuler.lemma_2_1"]],
};

const PAPERS = [
  { id: "euler", title: "Euler singularity", authors: "A, B and C", sentence: "", href: "/library/euler/", here: true, shard: "/library/_index/search/euler.json", pages: [] },
  { id: "ns", title: "Navier–Stokes blow-up", authors: "A and B", sentence: "", href: "/library/ns/", here: true, shard: "/library/_index/search/ns.json", pages: [] },
  { id: "sk", title: "QAOA on the SK model", authors: "D", sentence: "Lemma 2.1 and more", href: "https://example.org/sk/", here: false, pages: [] },
];

async function boot(failing: string[] = []) {
  document.body.innerHTML = `
    <input id="q"><p id="search-status"></p><div id="search-results" hidden></div>
    <script id="library-data" type="application/json">${JSON.stringify({ papers: PAPERS })}</script>`;
  vi.stubGlobal("matchMedia", () => ({ matches: false, addEventListener() {}, removeEventListener() {} }));
  vi.stubGlobal("fetch", vi.fn(async (url: string) => {
    if (failing.some((f) => url.includes(f))) return { ok: false, json: async () => ({}) };
    return { ok: true, json: async () => SHARD };
  }));
  // Run the module's body afresh against this document.
  new Function(SCRIPT)();
  const input = document.getElementById("q") as HTMLInputElement;
  return async (query: string) => {
    input.value = query;
    input.dispatchEvent(new Event("input"));
    await new Promise((r) => setTimeout(r, 0));
    await new Promise((r) => setTimeout(r, 0));
    return {
      status: document.getElementById("search-status")!.textContent ?? "",
      links: [...document.querySelectorAll("#search-results a")].map((a) => a.getAttribute("href")),
    };
  };
}

describe("library index search", () => {
  beforeEach(() => vi.unstubAllGlobals());

  it("a numbered query matches that result exactly, not a number inside another", async () => {
    const search = await boot(["ns.json"]);
    const { links } = await search("Lemma 2.1");
    expect(links).toContain("/library/euler/lemma-2.1/");
    expect(links).not.toContain("/library/euler/lemma-2.5/");
    expect(links).not.toContain("/library/euler/@p");
  });

  it("a bare number matches only as a whole number", async () => {
    const search = await boot();
    const { links } = await search("2.1");
    expect(links).toContain("/library/euler/lemma-2.1/");
    expect(links).toContain("/library/euler/@p");
    expect(links).not.toContain("/library/euler/lemma-2.5/");
  });

  it("says how many papers' contents were searched, and names a paper whose contents failed", async () => {
    const search = await boot(["ns.json"]);
    const { status } = await search("bound");
    expect(status).toMatch(/Matches in 1 paper of 3\./);
    expect(status).toContain("Searched the contents of 1 paper and the titles of 1 paper more.");
    expect(status).toContain("The contents of Navier–Stokes blow-up could not be loaded");
    expect(status).not.toMatch(/Loading/);
  });
});

// A library paper's addresses (docs/library-architecture.md, "URL scheme"): each kind opens the
// reader on what it names, and the address the reader writes for that state (Copy link) is the
// same address. Runs under every instance: the library settings are passed in.
import { describe, expect, it } from "vitest";
import { libraryHref, movedLibraryPath, parseLibraryPath, retiredLink, setLibraryAddresses } from "../src/app/libraryAddress";

const lib = { paper: "euler", main: "short" as const, pages: { "how-the-lean-encodes-it": "expository" as const, "part-2": "long" as const } };
const BASE = "/library/euler";
setLibraryAddresses({
  "e01.abstract.bounded-velocity": { record: null, at: "b536-564" },
  "r2.prop54.endpoint-citation": { record: "euler.proposition-5.4", at: "b9000-9050" },
  "old.merged-phrase": { record: null, at: "b536-564", host: "e01.abstract.bounded-velocity" },
}, { "r2-s7-pressure-input": { retired: "2026-11-21", nearest: "r2.prop54.endpoint-citation" } },
{ "theorem-1.1": ["b4441-5169", "b4441-5200"] },
{ accounts: { to: "how-the-lean-encodes-it", phrases: { "p2.coercive": "part-2" } } },
{ "part-2": { "p2.coercive": { record: null, at: "b1-2" } }, "how-the-lean-encodes-it": { "e01.digest-phrase": { record: null, at: "b3-4" } } });

function roundTrip(address: string) {
  const url = new URL(address, "https://wcook04.github.io");
  const path = url.pathname.slice(BASE.length).replace(/\/$/, "") || "/";
  const route = parseLibraryPath(path, url.searchParams, url.hash ? decodeURIComponent(url.hash.slice(1)) : undefined, lib);
  expect(route, address).not.toBeNull();
  return { route: route!, href: libraryHref(route!, BASE, lib) };
}

describe("library addresses", () => {
  it("the paper's top opens the main document", () => {
    const { route, href } = roundTrip(`${BASE}/`);
    expect(route).toMatchObject({ view: "read", stage: "short", node: undefined });
    expect(href).toBe(`${BASE}/`);
  });

  it("a section is a fragment of the paper's top", () => {
    const { route, href } = roundTrip(`${BASE}/#5.6`);
    expect(route.anchor).toBe("5.6");
    expect(href).toBe(`${BASE}/#5.6`);
  });

  it("a numbered result selects its record at its canonical target, the statement block", () => {
    const { route, href } = roundTrip(`${BASE}/theorem-1.1/`);
    expect(route.node).toBe("euler.theorem-1.1");
    expect(route.at).toBe("b4441-5169");
    expect(href).toBe(`${BASE}/theorem-1.1/`);
  });

  it("Copy link, search and Compare name a result at its statement block by the result's address", () => {
    const read = { view: "read" as const, stage: "short" as const, node: "euler.theorem-1.1" };
    expect(libraryHref({ ...read, at: "b4441-5169" }, BASE, lib)).toBe(`${BASE}/theorem-1.1/`);
    expect(libraryHref({ ...read, at: "b4441-5200" }, BASE, lib)).toBe(`${BASE}/theorem-1.1/`);
    expect(libraryHref({ ...read, at: "b4441-5200", lean: true }, BASE, lib)).toBe(`${BASE}/theorem-1.1/?v=lean`);
    // Another place of the same record is not the result's address.
    expect(libraryHref({ ...read, at: "b100-200" }, BASE, lib)).not.toBe(`${BASE}/theorem-1.1/`);
  });

  it("a phrase off the map selects the phrase and its place", () => {
    const { route, href } = roundTrip(`${BASE}/@e01.abstract.bounded-velocity?v=graph`);
    expect(route).toMatchObject({ node: "phrase:e01.abstract.bounded-velocity", at: "b536-564", graph: true });
    expect(href).toBe(`${BASE}/@e01.abstract.bounded-velocity?v=graph`);
  });

  it("a phrase on the map selects its record at the phrase's place", () => {
    const { route, href } = roundTrip(`${BASE}/@r2.prop54.endpoint-citation?v=lean`);
    expect(route).toMatchObject({ node: "euler.proposition-5.4", at: "b9000-9050", lean: true });
    expect(href).toBe(`${BASE}/@r2.prop54.endpoint-citation?v=lean`);
  });

  it("a retired phrase link opens a notice, never its neighbour", () => {
    const { route, href } = roundTrip(`${BASE}/@r2-s7-pressure-input`);
    expect(route).toMatchObject({ view: "read", stage: "short", retired: "r2-s7-pressure-input" });
    expect(route.node).toBeUndefined();
    expect(route.at).toBeUndefined();
    expect(href).toBe(`${BASE}/@r2-s7-pressure-input`);
    expect(retiredLink("r2-s7-pressure-input")).toEqual({ retired: "2026-11-21", nearest: "r2.prop54.endpoint-citation" });
  });

  it("a phrase on the map, with no view named, selects its record at the phrase's place", () => {
    // The reader opens it in its default pane with the same card and Lean as a click on the phrase;
    // main.tsx parses the address again once this table has loaded (reparseCurrentRoute).
    const { route, href } = roundTrip(`${BASE}/@r2.prop54.endpoint-citation`);
    expect(route).toMatchObject({ node: "euler.proposition-5.4", at: "b9000-9050" });
    expect(route.lean).toBeUndefined();
    expect(href).toBe(`${BASE}/@r2.prop54.endpoint-citation`);
  });

  it("an old phrase id opens the phrase that now holds it, and Copy link names that phrase", () => {
    const { route, href } = roundTrip(`${BASE}/@old.merged-phrase?v=lean`);
    expect(route).toMatchObject({ node: "phrase:e01.abstract.bounded-velocity", at: "b536-564", lean: true });
    expect(href).toBe(`${BASE}/@e01.abstract.bounded-velocity?v=lean`);
  });

  it("a Lean declaration opens its card", () => {
    const { route, href } = roundTrip(`${BASE}/lean/TorusEuler.EulerSingularityWitness`);
    expect(route).toMatchObject({ decl: "TorusEuler.EulerSingularityWitness", lean: true });
    expect(route.node).toBeUndefined();
    expect(href).toBe(`${BASE}/lean/TorusEuler.EulerSingularityWitness`);
  });

  it("the PDF view and its page travel with any address", () => {
    const { route, href } = roundTrip(`${BASE}/@r2.prop54.endpoint-citation?v=lean&view=pdf&page=32`);
    expect(route).toMatchObject({ pdf: true, page: 32, lean: true, node: "euler.proposition-5.4" });
    expect(href).toBe(`${BASE}/@r2.prop54.endpoint-citation?v=lean&view=pdf&page=32`);
    expect(roundTrip(`${BASE}/theorem-1.1/?view=pdf&page=3`).href).toBe(`${BASE}/theorem-1.1/?view=pdf&page=3`);
  });

  it("a companion page opens its own document", () => {
    const { route, href } = roundTrip(`${BASE}/how-the-lean-encodes-it/`);
    expect(route.stage).toBe("expository");
    expect(href).toBe(`${BASE}/how-the-lean-encodes-it/`);
  });

  it("a page that moved opens its new page, and each of its phrases on the page that now holds it", () => {
    expect(movedLibraryPath("/accounts")).toBe("/how-the-lean-encodes-it");
    expect(movedLibraryPath("/accounts/@p2.coercive")).toBe("/part-2/@p2.coercive");
    expect(movedLibraryPath("/accounts/@e01.digest-phrase")).toBe("/how-the-lean-encodes-it/@e01.digest-phrase");
    expect(movedLibraryPath("/accounts/lean/Foo.bar")).toBe("/how-the-lean-encodes-it/lean/Foo.bar");
    expect(movedLibraryPath("/how-the-lean-encodes-it")).toBeNull();
    expect(roundTrip(`${BASE}/accounts/`).href).toBe(`${BASE}/how-the-lean-encodes-it/`);
    expect(roundTrip(`${BASE}/accounts/@p2.coercive`).href).toBe(`${BASE}/part-2/@p2.coercive`);
    expect(roundTrip(`${BASE}/accounts/lean/Foo.bar`).href).toBe(`${BASE}/how-the-lean-encodes-it/lean/Foo.bar`);
  });

  it("any other reading state keeps the reader's own parameters at the paper's top", () => {
    const route = { view: "read" as const, stage: "short" as const, at: "120-134" };
    expect(libraryHref(route, BASE, lib)).toBe(`${BASE}/?l=120-134`);
    expect(parseLibraryPath("/", new URLSearchParams("l=120-134"), undefined, lib)).toMatchObject({ at: "120-134" });
  });

  it("an address that names no phrase opens the paper with its notice, at no phrase", () => {
    const { route, href } = roundTrip(`${BASE}/@no-such-phrase`);
    expect(route).toMatchObject({ stage: "short", missing: "no-such-phrase" });
    expect(route.node).toBeUndefined();
    expect(href).toBe(`${BASE}/@no-such-phrase`);
  });

  it("a companion page's phrase and declaration have their own addresses", () => {
    setLibraryAddresses({}, {}, {}, {}, { "how-the-lean-encodes-it": { "g.first": { record: null, at: "b10-40" } } });
    const phrase = roundTrip(`${BASE}/how-the-lean-encodes-it/@g.first?v=lean`);
    expect(phrase.route).toMatchObject({ stage: "expository", node: "phrase:g.first", at: "b10-40", lean: true });
    expect(phrase.href).toBe(`${BASE}/how-the-lean-encodes-it/@g.first?v=lean`);
    const decl = roundTrip(`${BASE}/how-the-lean-encodes-it/lean/TorusEuler.theorem11`);
    expect(decl.route).toMatchObject({ stage: "expository", decl: "TorusEuler.theorem11", lean: true });
    expect(decl.href).toBe(`${BASE}/how-the-lean-encodes-it/lean/TorusEuler.theorem11`);
    const gone = roundTrip(`${BASE}/how-the-lean-encodes-it/@nothing-here`);
    expect(gone.route).toMatchObject({ stage: "expository", missing: "nothing-here" });
    expect(gone.href).toBe(`${BASE}/how-the-lean-encodes-it/@nothing-here`);
  });

  it("a result the paper states without a number keeps its claim id as its address", () => {
    expect(parseLibraryPath("/claim-source-13", new URLSearchParams(), undefined, lib)).toMatchObject({ node: "euler.claim-source-13" });
  });

  it("leaves every path to the reader when the instance is not a library paper", () => {
    expect(parseLibraryPath("/theorem-1.1", new URLSearchParams(), undefined, null)).toBeNull();
    expect(parseLibraryPath("/map", new URLSearchParams(), undefined, lib)).toBeNull();
  });
});

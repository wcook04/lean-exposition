// A library paper's addresses (docs/library-architecture.md, "URL scheme"): each kind opens the
// reader on what it names, and the address the reader writes for that state (Copy link) is the
// same address. Runs under every instance: the library settings are passed in.
import { describe, expect, it } from "vitest";
import { libraryHref, parseLibraryPath, setLibraryAddresses } from "../src/app/libraryAddress";

const lib = { paper: "euler", main: "short" as const, pages: { "how-the-lean-encodes-it": "expository" as const } };
const BASE = "/library/euler";
setLibraryAddresses({
  "e01.abstract.bounded-velocity": { record: null, at: "b536-564" },
  "r2.prop54.endpoint-citation": { record: "euler.proposition-5.4", at: "b9000-9050" },
});

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

  it("a numbered result selects its record", () => {
    const { route, href } = roundTrip(`${BASE}/theorem-1.1/`);
    expect(route.node).toBe("euler.theorem-1.1");
    expect(href).toBe(`${BASE}/theorem-1.1/`);
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

  it("any other reading state keeps the reader's own parameters at the paper's top", () => {
    const route = { view: "read" as const, stage: "short" as const, at: "120-134" };
    expect(libraryHref(route, BASE, lib)).toBe(`${BASE}/?l=120-134`);
    expect(parseLibraryPath("/", new URLSearchParams("l=120-134"), undefined, lib)).toMatchObject({ at: "120-134" });
  });

  it("leaves every path to the reader when the instance is not a library paper", () => {
    expect(parseLibraryPath("/theorem-1.1", new URLSearchParams(), undefined, null)).toBeNull();
    expect(parseLibraryPath("/map", new URLSearchParams(), undefined, lib)).toBeNull();
  });
});

import { describe, expect, it } from "vitest";
import { parseRoute, routeHref } from "../src/app/router";
import { citationText, editionLink, linkedEdition, sameEdition } from "../src/app/cite";

const snapshot = {
  bundle_id: "qaoa-sk-public-intake",
  bundle_version: "0.1.0",
  cache_key: "c",
  graph_sha256: "g",
  manifest_sha256: "79bf16ac8ab3a2adf5741ab97b2e4bd813e1c0a1940efbbdf9e35523f00de8bb",
  ref: "r",
};

describe("search route", () => {
  it("keeps the exact query, kind and page through a round trip", () => {
    const route = { view: "search", q: "strict curvature: μ", type: "passages", page: 3 } as const;
    expect(parseRoute(new URL(routeHref(route), "https://example.test"))).toEqual(route);
  });

  it("drops page 1, unknown kinds and nonsense pages", () => {
    expect(routeHref({ view: "search", q: "gap", page: 1 })).toBe("/search?q=gap");
    expect(parseRoute(new URL("https://example.test/search?q=gap&type=nope&p=-2"))).toEqual({ view: "search", q: "gap", type: undefined, page: undefined });
  });
});

describe("edition-pinned links and citations", () => {
  it("names the edition by manifest prefix and recognises it again", () => {
    const href = editionLink({ view: "read", stage: "short", anchor: "density" }, snapshot, "https://example.test");
    expect(href).toBe("https://example.test/read/short?edition=79bf16ac8ab3a2ad#density");
    const linked = linkedEdition(href)!;
    expect(sameEdition(linked, snapshot)).toBe(true);
    expect(sameEdition("0000000000000000", snapshot)).toBe(false);
    expect(linkedEdition("https://example.test/?edition=not-hex")).toBeNull();
  });

  it("cites the account, the place and the full manifest hash", () => {
    const text = citationText({ stage: "long", place: "§9.2" }, { view: "read", stage: "long", anchor: "density-positive" }, snapshot, "https://example.test");
    expect(text).toContain("Long record, §9.2");
    expect(text).toContain(snapshot.manifest_sha256);
    expect(text).toContain("qaoa-sk-public-intake 0.1.0");
  });
});

import { describe, expect, it } from "vitest";
import { parseRoute, routeHref } from "../src/app/router";

const at = (path: string) => parseRoute(new URL(path, "https://example.test"));

describe("the front page and the map's address", () => {
  it("opens the front page at /", () => {
    expect(at("/")).toEqual({ view: "home" });
    expect(routeHref({ view: "home" })).toBe("/");
  });

  it("opens the map at /map", () => {
    expect(at("/map")).toMatchObject({ view: "map", goal: undefined, node: undefined });
    expect(routeHref({ view: "map" })).toBe("/map");
    expect(routeHref({ view: "map", goal: "scalar_value", node: "a" })).toBe("/map?g=scalar_value&n=a");
  });

  it.each(["/?g=scalar_value", "/?n=support.diffusion", "/?n=x&t=rests", "/?lens=long", "/?e=a~b~supports"])(
    "keeps an old map link %s on the map",
    (path) => {
      expect(at(path).view).toBe("map");
    },
  );

  it("reads an old map link's parameters as before", () => {
    expect(at("/?g=scalar_value&n=a&lens=short")).toMatchObject({ view: "map", goal: "scalar_value", node: "a", lens: "short" });
  });

  it("round-trips a map route through /map", () => {
    const route = { view: "map" as const, goal: "g", node: "n", trace: "uses" as const, lens: "long" as const, edge: "a→b→supports" };
    expect(parseRoute(new URL(routeHref(route), "https://example.test"))).toEqual(route);
  });
});

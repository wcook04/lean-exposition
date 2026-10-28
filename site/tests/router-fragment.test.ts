import { afterEach, describe, expect, it, vi } from "vitest";
import { isAppPath, parseRoute, routeHref } from "../src/app/router";

describe("shared reader fragments", () => {
  it.each(["%", "%E0%A4%A", "a%GGb"])("keeps malformed fragment %s without stopping navigation", (anchor) => {
    const route = parseRoute(new URL(`https://example.test/read/short#${anchor}`));
    expect(route).toMatchObject({ view: "read", stage: "short", anchor });
  });

  it("preserves encoded mathematical and punctuation characters", () => {
    const anchor = "μ: a/b + 100%";
    const href = routeHref({ view: "read", stage: "expository", anchor });
    expect(parseRoute(new URL(href, "https://example.test"))).toMatchObject({
      view: "read", stage: "expository", anchor,
    });
  });

  it("treats an empty fragment as no anchor", () => {
    expect(parseRoute(new URL("https://example.test/read/long#"))).toMatchObject({
      view: "read", stage: "long", anchor: undefined,
    });
  });
});

describe("addresses the site opens itself", () => {
  afterEach(() => {
    vi.unstubAllEnvs();
    vi.resetModules();
  });

  it("names a band of the front page", () => {
    expect(routeHref({ view: "home", anchor: "papers" })).toBe("/#papers");
    expect(parseRoute(new URL("https://example.test/#papers"))).toEqual({ view: "home", anchor: "papers" });
  });

  it("leaves files, the API and other hosts to the browser", () => {
    const origin = "https://example.test";
    const at = (p: string) => new URL(p, origin);
    expect(isAppPath(at("/map?n=a.b"), origin)).toBe(true);
    expect(isAppPath(at("/read/short#model-and-result"), origin)).toBe(true);
    expect(isAppPath(at("/pdf/long-record.pdf"), origin)).toBe(false);
    expect(isAppPath(at("/verification/observation.json"), origin)).toBe(false);
    expect(isAppPath(at("/api/v1/overview"), origin)).toBe(false);
    expect(isAppPath(new URL("https://elsewhere.test/map"), origin)).toBe(false);
  });

  it("on GitHub Pages leaves the sister sites on the same host to the browser", async () => {
    vi.stubEnv("BASE_URL", "/lean-exposition-site/");
    vi.resetModules();
    const router = await import("../src/app/router");
    const origin = "https://wcook04.github.io";
    const at = (p: string) => new URL(p, origin);
    expect(router.isAppPath(at("/lean-exposition-site/"), origin)).toBe(true);
    expect(router.isAppPath(at("/lean-exposition-site"), origin)).toBe(true);
    expect(router.isAppPath(at("/lean-exposition-site/checks"), origin)).toBe(true);
    expect(router.isAppPath(at("/"), origin)).toBe(false);
    expect(router.isAppPath(at("/practical-formal-verification/maths/"), origin)).toBe(false);
    expect(router.isAppPath(at("/lean-exposition-site-other/"), origin)).toBe(false);
    expect(router.isAppPath(at("/lean-exposition-site/pdf/exposition.pdf"), origin)).toBe(false);
    expect(router.routeHref({ view: "home", anchor: "papers" })).toBe("/lean-exposition-site/#papers");
  });
});

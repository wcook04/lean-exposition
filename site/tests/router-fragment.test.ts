import { describe, expect, it } from "vitest";
import { parseRoute, routeHref } from "../src/app/router";

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

import { afterEach, describe, expect, it, vi } from "vitest";
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { PageTitle } from "../src/app/PageTitle";
import type { Route } from "../src/app/router";

vi.mock("../src/app/data", () => ({
  useEdition: () => ({ graph: { nodes: new Map([["full_support", { label: "Full support" }]]) } }),
}));

let root: Root | undefined;
let host: HTMLDivElement | undefined;
afterEach(async () => {
  if (root) await act(async () => root!.unmount());
  host?.remove();
  root = undefined;
  host = undefined;
});

describe("page title after navigation", () => {
  it("replaces the previous page or selected record title on every route", async () => {
    (globalThis as { IS_REACT_ACT_ENVIRONMENT?: boolean }).IS_REACT_ACT_ENVIRONMENT = true;
    host = document.createElement("div");
    document.body.append(host);
    root = createRoot(host);
    const cases: [Route, string][] = [
      [{ view: "checks" }, "What ran"],
      [{ view: "read", stage: "short" }, "Short paper"],
      [{ view: "about" }, "About"],
      [{ view: "map", node: "full_support" }, "Full support"],
      [{ view: "map" }, "Argument map"],
      [{ view: "checks", node: "full_support" }, "What ran on Full support"],
      [{ view: "read", stage: "expository", node: "full_support" }, "Exposition"],
      [{ view: "missing", path: "/missing" }, "Page not found"],
    ];
    for (const [route, title] of cases) {
      await act(async () => root!.render(<PageTitle route={route} />));
      expect(document.title).toBe(`${title} · Lean Exposition`);
    }
    await act(async () => root!.render(<PageTitle route={{ view: "home" }} />));
    expect(document.title).toBe("Why the Sherrington–Kirkpatrick order parameter has no gaps");
  });
});

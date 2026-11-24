// The header uses a disclosure with ordinary links and buttons.
import { afterEach, describe, expect, it, vi } from "vitest";
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";

vi.mock("../src/app/data", () => ({
  useMaybeEdition: () => ({ overview: { papers: [{ stage: "long", state: "draft" }, { stage: "short", state: "final" }] } }),
}));
window.matchMedia ??= ((query: string) => ({ matches: false, media: query, addEventListener() {}, removeEventListener() {} })) as never;

const { TopBar } = await import("../src/app/TopBar");

let root: Root | undefined;
let host: HTMLDivElement | undefined;
afterEach(async () => {
  if (root) await act(async () => root!.unmount());
  host?.remove();
});

function key(target: Element, k: string) {
  target.dispatchEvent(new KeyboardEvent("keydown", { key: k, bubbles: true }));
}

describe("site menu", () => {
  it("keeps the public routes behind one disclosure, and Escape restores focus", async () => {
    (globalThis as { IS_REACT_ACT_ENVIRONMENT?: boolean }).IS_REACT_ACT_ENVIRONMENT = true;
    host = document.createElement("div");
    document.body.append(host);
    root = createRoot(host);
    await act(async () => root!.render(<TopBar route={{ view: "read", stage: "short" }} onSearch={() => undefined} />));

    const button = host.querySelector<HTMLButtonElement>(".menu-toggle")!;
    const panel = document.getElementById(button.getAttribute("aria-controls")!)!;
    expect(button.textContent?.trim()).toBe("Menu");
    expect(button.getAttribute("aria-expanded")).toBe("false");
    expect(panel.hidden).toBe(true);

    button.focus();
    await act(async () => button.click());
    const links = [...panel.querySelectorAll("a")];
    expect(button.getAttribute("aria-expanded")).toBe("true");
    expect(panel.hidden).toBe(false);
    expect(links.map((link) => link.textContent)).toEqual(["Exposition", "Short paper", "Long record (draft)", "All papers and PDFs", "Map", "Compare", "Lean index"]);
    expect(links[1].getAttribute("aria-current")).toBe("page");

    links[0].focus();
    await act(async () => key(links[0], "Escape"));
    expect(panel.hidden).toBe(true);
    expect(document.activeElement).toBe(button);
  });

  it("opens search from the disclosure and closes it", async () => {
    host = document.createElement("div");
    document.body.append(host);
    root = createRoot(host);
    const onSearch = vi.fn();
    await act(async () => root!.render(<TopBar route={{ view: "map" }} onSearch={onSearch} />));
    const menu = host.querySelector<HTMLButtonElement>(".menu-toggle")!;
    await act(async () => menu.click());
    expect(host.querySelector('a[aria-current="page"]')!.textContent).toBe("Map");
    await act(async () => host!.querySelector<HTMLButtonElement>(".search-trigger")!.click());
    expect(onSearch).toHaveBeenCalledOnce();
    expect(menu.getAttribute("aria-expanded")).toBe("false");
  });
});

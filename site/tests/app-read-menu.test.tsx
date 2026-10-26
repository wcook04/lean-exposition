// The Read menu is a keyboard-complete menu button.
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

describe("Read menu", () => {
  it("opens, moves, jumps by letter, and closes back to its button", async () => {
    (globalThis as { IS_REACT_ACT_ENVIRONMENT?: boolean }).IS_REACT_ACT_ENVIRONMENT = true;
    host = document.createElement("div");
    document.body.append(host);
    root = createRoot(host);
    await act(async () => root!.render(<TopBar route={{ view: "read", stage: "short" }} onSearch={() => undefined} />));
    const button = host.querySelector<HTMLButtonElement>('button[aria-haspopup="menu"]')!;
    expect(button.getAttribute("aria-current")).toBe("page");
    expect(button.getAttribute("aria-expanded")).toBe("false");

    button.focus();
    await act(async () => key(button, "ArrowDown"));
    const items = [...host.querySelectorAll<HTMLAnchorElement>('[role="menuitem"]')];
    expect(button.getAttribute("aria-expanded")).toBe("true");
    expect(items.map((i) => i.querySelector(".readmenu__name")!.textContent)).toEqual(["Exposition", "Short paper", "Long recordDraft"]);
    expect(items[1].getAttribute("aria-current")).toBe("page");
    expect(document.activeElement).toBe(items[0]);

    await act(async () => key(items[0], "ArrowDown"));
    expect(document.activeElement).toBe(items[1]);
    await act(async () => key(items[1], "ArrowUp"));
    await act(async () => key(items[0], "ArrowUp"));
    expect(document.activeElement).toBe(items[2]);
    await act(async () => key(items[2], "e"));
    expect(document.activeElement).toBe(items[0]);
    await act(async () => key(items[0], "End"));
    expect(document.activeElement).toBe(items[2]);

    await act(async () => key(items[2], "Escape"));
    expect(button.getAttribute("aria-expanded")).toBe("false");
    expect(document.activeElement).toBe(button);
  });

  it("gives search and the phone menu names that do not depend on visible text", async () => {
    host = document.createElement("div");
    document.body.append(host);
    root = createRoot(host);
    await act(async () => root!.render(<TopBar route={{ view: "map" }} onSearch={() => undefined} />));
    expect(host.querySelector('[aria-label="Search records and passages"]')).not.toBeNull();
    expect(host.querySelector('button[aria-label="Menu"]')).not.toBeNull();
    expect(host.querySelector('a[aria-current="page"]')!.textContent).toBe("Argument map");
  });
});

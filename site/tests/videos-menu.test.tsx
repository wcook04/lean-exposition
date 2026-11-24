import { afterEach, describe, expect, it, vi } from "vitest";
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { heroHtml, heroLinks, VIDEOS_ANCHOR } from "../src/instances/qaoa-sk/hero";

vi.mock("../src/app/data", () => ({ useMaybeEdition: () => null }));
window.matchMedia ??= ((query: string) => ({ matches: false, media: query, addEventListener() {}, removeEventListener() {} })) as never;

const { TopBar } = await import("../src/app/TopBar");

let root: Root | undefined;
let host: HTMLDivElement | undefined;
afterEach(async () => {
  if (root) await act(async () => root!.unmount());
  host?.remove();
});

describe("reader videos", () => {
  it("keeps films outside the header and its Menu", async () => {
    (globalThis as { IS_REACT_ACT_ENVIRONMENT?: boolean }).IS_REACT_ACT_ENVIRONMENT = true;
    host = document.createElement("div");
    document.body.append(host);
    root = createRoot(host);
    await act(async () => root!.render(<TopBar route={{ view: "read", stage: "short" }} onSearch={() => undefined} />));

    const button = host.querySelector<HTMLButtonElement>(".menu-toggle")!;
    await act(async () => button.click());
    const menu = document.getElementById(button.getAttribute("aria-controls")!)!;
    expect(menu.hidden).toBe(false);
    expect(menu.querySelector("nav a")).not.toBeNull();
    expect([...host.querySelectorAll("button")].map((item) => item.textContent?.trim())).not.toContain("Videos");
    expect([...host.querySelectorAll("a")].some((link) => link.hostname === "www.youtube.com" || link.hash === "#videos")).toBe(false);
  });

  it("opens each film from the home page with one keyboard stop and a spoken duration", () => {
    const links = heroLinks("/");
    const home = document.createElement("div");
    home.innerHTML = heroHtml(links, (tex) => tex);
    const slots = [...home.querySelectorAll(`#${VIDEOS_ANCHOR} .film-slot`)];
    expect(slots).toHaveLength(3);
    expect(slots[0].classList.contains("front__lead")).toBe(true);

    for (const [index, slot] of slots.entries()) {
      const film = links.films[index];
      const frame = slot.querySelector<HTMLAnchorElement>(".film-slot__frame")!;
      const title = slot.querySelector<HTMLAnchorElement>(".film-slot__title a")!;
      expect(frame.tabIndex).toBe(-1);
      expect(frame.getAttribute("aria-hidden")).toBe("true");
      expect(title.tabIndex).toBe(0);
      expect(title.firstChild?.textContent).toBe(film.title);
      expect(title.querySelector(".sr-only")?.textContent).toBe(`, video on YouTube, ${film.spoken}`);
      for (const link of [frame, title]) {
        expect(link.href).toBe(film.href);
        expect(link.target).toBe("_blank");
        expect(link.rel).toBe("noopener noreferrer");
      }
    }
  });
});

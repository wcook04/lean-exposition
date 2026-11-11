// The bar's Videos button is a disclosure of the site's three videos.
import { afterEach, describe, expect, it, vi } from "vitest";
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { siteFilms } from "../src/app/siteFilms";

vi.mock("../src/app/data", () => ({ useMaybeEdition: () => null }));
window.matchMedia ??= ((query: string) => ({ matches: false, media: query, addEventListener() {}, removeEventListener() {} })) as never;

const { TopBar } = await import("../src/app/TopBar");

let root: Root | undefined;
let host: HTMLDivElement | undefined;
afterEach(async () => {
  if (root) await act(async () => root!.unmount());
  host?.remove();
});

async function render() {
  (globalThis as { IS_REACT_ACT_ENVIRONMENT?: boolean }).IS_REACT_ACT_ENVIRONMENT = true;
  host = document.createElement("div");
  document.body.append(host);
  root = createRoot(host);
  await act(async () => root!.render(<TopBar route={{ view: "read", stage: "short" }} onSearch={() => undefined} />));
  const button = host.querySelector<HTMLButtonElement>(".videos__button")!;
  const pop = document.getElementById(button.getAttribute("aria-controls")!)!;
  return { button, pop };
}

describe("Videos menu", () => {
  it("toggles its popover and closes on Escape back to the button", async () => {
    const { button, pop } = await render();
    expect(button.textContent).toBe("Videos");
    expect(button.hasAttribute("aria-haspopup")).toBe(false);
    expect(button.getAttribute("aria-expanded")).toBe("false");
    expect(pop.hidden).toBe(true);

    await act(async () => button.click());
    expect(button.getAttribute("aria-expanded")).toBe("true");
    expect(pop.hidden).toBe(false);
    await act(async () => button.click());
    expect(button.getAttribute("aria-expanded")).toBe("false");
    expect(pop.hidden).toBe(true);

    await act(async () => button.click());
    const link = pop.querySelector<HTMLAnchorElement>(".videos__link")!;
    link.focus();
    await act(async () => link.dispatchEvent(new KeyboardEvent("keydown", { key: "Escape", bubbles: true })));
    expect(button.getAttribute("aria-expanded")).toBe("false");
    expect(pop.hidden).toBe(true);
    expect(document.activeElement).toBe(button);
  });

  it("lists the three films in order, lead first, each opening YouTube in a new tab", async () => {
    const { pop } = await render();
    const films = siteFilms("/");
    expect(films).toHaveLength(3);
    const shown = [...pop.querySelectorAll<HTMLElement>("[data-film]")];
    expect(shown.map((el) => el.dataset.film)).toEqual(films.map((f) => f.id));
    expect(shown[0].classList.contains("videos__lead")).toBe(true);
    expect(shown[0].querySelector(".videos__kicker")!.textContent).toBe(films[0].kicker);

    const links = [...pop.querySelectorAll<HTMLAnchorElement>("a")];
    expect(links).toHaveLength(6);
    for (const a of links) {
      expect(a.href.startsWith("https://www.youtube.com/watch?v=")).toBe(true);
      expect(a.target).toBe("_blank");
      expect(a.rel).toBe("noopener noreferrer");
    }
    const titles = [...pop.querySelectorAll<HTMLAnchorElement>(".videos__link")];
    expect(titles.map((a) => a.firstChild!.textContent)).toEqual(films.map((f) => f.title));
    expect(titles[0].querySelector(".sr-only")!.textContent).toBe(`, video on YouTube, ${films[0].spoken}`);
  });

  it("keeps only the titles in the Tab order", async () => {
    const { pop } = await render();
    const frames = [...pop.querySelectorAll<HTMLAnchorElement>("a.film-slot__frame")];
    expect(frames).toHaveLength(3);
    for (const f of frames) {
      expect(f.getAttribute("tabindex")).toBe("-1");
      expect(f.getAttribute("aria-hidden")).toBe("true");
    }
    const tabbable = [...pop.querySelectorAll<HTMLAnchorElement>("a")].filter((a) => a.tabIndex >= 0);
    expect(tabbable.every((a) => a.classList.contains("videos__link"))).toBe(true);
    expect(tabbable).toHaveLength(3);
  });

  it("gives the phone menu a Videos group of the same three films", async () => {
    await render();
    const group = host!.querySelector<HTMLUListElement>(".phonemenu .videos__rows--phone")!;
    const head = document.getElementById(group.getAttribute("aria-labelledby")!)!;
    expect(head.textContent).toBe("Videos");
    expect([...group.querySelectorAll<HTMLElement>("[data-film]")].map((el) => el.dataset.film)).toEqual(siteFilms("/").map((f) => f.id));
  });
});

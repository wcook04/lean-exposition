// The family's shared parts (docs/family.md in wcook04.github.io): the film slot in both
// of its states, the sister sites, the header's lockup, and the copy of the registry and
// stylesheet they are rendered from.
import { afterEach, describe, expect, it, vi } from "vitest";
import { mkdirSync, writeFileSync } from "node:fs";
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { renderToStaticMarkup } from "react-dom/server";
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { FAMILY, THIS_SITE_ID, clockTime, familyFilm, familySite, isReleased, spokenTime, stillSources, type FamilyFilm } from "../src/app/family";
import { FilmSlot } from "../src/app/FilmSlot";
import { SisterSites } from "../src/app/SisterSites";

vi.mock("../src/app/data", () => ({ useMaybeEdition: () => null }));
window.matchMedia ??= ((query: string) => ({ matches: false, media: query, addEventListener() {}, removeEventListener() {} })) as never;

const site = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");

function render(element: React.ReactElement): HTMLElement {
  const host = document.createElement("div");
  host.innerHTML = renderToStaticMarkup(element);
  return host;
}

/** A released film as the registry would list it, with a still that exists in the hub's set. */
const RELEASED: FamilyFilm = {
  id: "fixture",
  title: "Plectis Atlas: compare maths papers with the reports that check them",
  short: "Plectis Atlas",
  description: "One or two sentences from the film’s description.",
  youtube: "https://www.youtube.com/watch?v=ugUObM3qpmM",
  duration_seconds: 327,
  still: "assets/films/atlas",
};

describe("the registry copy", () => {
  it("lists this site and its two films, each in preparation until it has a YouTube address", () => {
    const own = familySite(THIS_SITE_ID);
    expect(own.films).toEqual(expect.arrayContaining(["interfaces", "sk-no-gap"]));
    for (const id of own.films) {
      const film = familyFilm(id);
      expect(isReleased(film)).toBe(Boolean(film.youtube));
    }
  });

  // The front page and the About page name these films; a registry copy without one would fail to render them.
  it.each(["interfaces", "sk-no-gap", "mathematics", "mathematics-overview", "atlas", "introduction"])(
    "lists the film %s that the pages show",
    (id) => {
      expect(() => familyFilm(id)).not.toThrow();
    },
  );

  it("gives every released film a YouTube watch address, never another host", () => {
    for (const film of FAMILY.films) {
      if (film.youtube === null) continue;
      expect(film.youtube).toMatch(/^https:\/\/(www\.youtube\.com\/watch\?v=|youtu\.be\/)[\w-]+$/);
      expect(isReleased(film)).toBe(true);
    }
  });

  it("has both stills in public/films for every released film this site shows", () => {
    for (const id of familySite(THIS_SITE_ID).films) {
      const film = familyFilm(id);
      if (!isReleased(film) || !film.still) continue;
      const name = film.still.split("/").pop()!;
      for (const width of [640, 1280]) {
        expect(existsSync(path.join(site, "public/films", `${name}-${width}.webp`)), `${name}-${width}.webp`).toBe(true);
      }
    }
  });

  it("maps every name the shared stylesheet reads onto this site's tokens", () => {
    const tokens = readFileSync(path.join(site, "src/styles/tokens.css"), "utf8");
    for (const name of ["page", "surface", "ink", "ink-soft", "muted", "faint", "rule", "rule-strong", "accent", "serif", "sans"]) {
      expect(tokens).toMatch(new RegExp(`--fam-${name}:\\s*var\\(--`));
    }
  });
});

describe("running times", () => {
  it.each([
    [327, "5:27", "5 minutes 27 seconds"],
    [1800, "30:00", "30 minutes"],
    [61, "1:01", "1 minute 1 second"],
    [3725, "1:02:05", "1 hour 2 minutes 5 seconds"],
  ])("%i seconds is %s, said as %s", (seconds, clock, words) => {
    expect(clockTime(seconds)).toBe(clock);
    expect(spokenTime(seconds)).toBe(words);
  });
});

describe("a film slot", () => {
  it("holds a film in preparation with the registration-mark frame and no link", () => {
    const film: FamilyFilm = { ...familyFilm("sk-no-gap"), youtube: null, duration_seconds: null, still: null };
    const host = render(<FilmSlot film={film} size="small" />);
    const figure = host.querySelector("figure")!;
    expect(figure.className).toBe("film-slot film-slot--small film-slot--pending");
    const frame = figure.querySelector(".film-slot__frame")!;
    expect(frame.tagName).toBe("DIV");
    expect(frame.className).toBe("film-slot__frame film-slot__frame--pending");
    expect(frame.getAttribute("aria-hidden")).toBe("true");
    expect([...frame.children].map((c) => [c.className, c.textContent])).toEqual([
      ["film-slot__series", "Lean Exposition"],
      ["film-slot__name", film.short],
      ["film-slot__status", "In preparation"],
    ]);
    const caption = figure.querySelector("figcaption.film-slot__caption")!;
    expect([...caption.children].map((c) => [c.className, c.textContent])).toEqual([
      ["film-slot__title", film.title],
      ["film-slot__meta", "Video in preparation"],
      ["film-slot__text", film.description],
    ]);
    expect(host.querySelector("a")).toBeNull();
  });

  it("shows a released film's still, play chip and time, with the title as the one link in the Tab order", () => {
    const host = render(<FilmSlot film={RELEASED} sizes="200px" />);
    const figure = host.querySelector("figure")!;
    expect(figure.className).toBe("film-slot");
    const frame = figure.querySelector<HTMLAnchorElement>("a.film-slot__frame")!;
    expect(frame.getAttribute("href")).toBe(RELEASED.youtube);
    expect(frame.getAttribute("target")).toBe("_blank");
    expect(frame.getAttribute("rel")).toBe("noopener noreferrer");
    expect(frame.getAttribute("aria-hidden")).toBe("true");
    expect(frame.getAttribute("tabindex")).toBe("-1");
    const img = frame.querySelector("img")!;
    expect(img.getAttribute("src")).toBe("/films/atlas-640.webp");
    expect(img.getAttribute("srcset")).toBe("/films/atlas-640.webp 640w, /films/atlas-1280.webp 1280w");
    expect(img.getAttribute("sizes")).toBe("200px");
    expect(img.getAttribute("alt")).toBe("");
    expect([img.getAttribute("width"), img.getAttribute("height")]).toEqual(["1280", "720"]);
    expect([img.getAttribute("loading"), img.getAttribute("decoding")]).toEqual(["lazy", "async"]);
    expect(frame.querySelector(".film-slot__play")).not.toBeNull();
    expect(frame.querySelector(".film-slot__time")!.textContent).toBe("5:27");
    const title = figure.querySelector<HTMLAnchorElement>(".film-slot__title a")!;
    expect(title.getAttribute("href")).toBe(RELEASED.youtube);
    expect(title.getAttribute("target")).toBe("_blank");
    expect(title.getAttribute("tabindex")).toBeNull();
    expect(title.textContent).toBe(`${RELEASED.title}, video on YouTube, 5 minutes 27 seconds`);
    expect(title.querySelector(".sr-only")!.textContent).toBe(", video on YouTube, 5 minutes 27 seconds");
    expect(figure.querySelector(".film-slot__meta")).toBeNull();
    expect(figure.querySelector(".film-slot__text")!.textContent).toBe(RELEASED.description);
  });

  it("switches by itself once the registry gives the film's address and still", () => {
    const held: FamilyFilm = { ...familyFilm("interfaces"), youtube: null, duration_seconds: null, still: null };
    expect(render(<FilmSlot film={held} />).querySelector(".film-slot--pending")).not.toBeNull();
    const released = { ...held, youtube: "https://www.youtube.com/watch?v=abc_123-XY", duration_seconds: 300, still: "assets/films/interfaces" };
    const host = render(<FilmSlot film={released} />);
    expect(host.querySelector(".film-slot--pending")).toBeNull();
    expect(host.querySelector("img")!.getAttribute("src")).toBe("/films/interfaces-640.webp");
    expect(host.querySelector(".film-slot__title a")!.getAttribute("href")).toBe(released.youtube);
  });

  it("never links an address that is not a YouTube watch page", () => {
    const film = { ...RELEASED, youtube: "https://example.com/video" };
    expect(isReleased(film)).toBe(false);
    expect(render(<FilmSlot film={film} />).querySelector("a")).toBeNull();
  });

  it("serves the stills from public/films under the site's base path", () => {
    expect(stillSources(RELEASED, "/lean-exposition-site/")).toEqual({
      src: "/lean-exposition-site/films/atlas-640.webp",
      srcSet: "/lean-exposition-site/films/atlas-640.webp 640w, /lean-exposition-site/films/atlas-1280.webp 1280w",
    });
  });
});

describe("the sister sites", () => {
  it("lists every website in the registry's order, marks this one, then the home page", () => {
    const host = render(<SisterSites />);
    const nav = host.querySelector("nav.fam-sites")!;
    expect(nav.getAttribute("aria-label")).toBe("Will Cook's websites");
    expect(nav.querySelector(".fam-sites__title")!.textContent).toBe("More from Will Cook");
    const links = [...nav.querySelectorAll<HTMLAnchorElement>(".fam-sites__list a")];
    expect(links.map((a) => [a.textContent, a.getAttribute("href")])).toEqual([
      ...FAMILY.sites.map((s) => [s.short, s.url]),
      ["All websites and films", "https://wcook04.github.io/"],
    ]);
    expect(links.filter((a) => a.getAttribute("aria-current") === "page").map((a) => a.textContent)).toEqual([familySite(THIS_SITE_ID).short]);
  });
});

describe("the header's lockup", () => {
  let root: Root | undefined;
  let host: HTMLDivElement | undefined;
  afterEach(async () => {
    if (root) await act(async () => root!.unmount());
    host?.remove();
  });

  it("opens with the Plectis plait to the home page, a rule, then this site's mark and name, and lists the five jobs", async () => {
    (globalThis as { IS_REACT_ACT_ENVIRONMENT?: boolean }).IS_REACT_ACT_ENVIRONMENT = true;
    const { TopBar } = await import("../src/app/TopBar");
    host = document.createElement("div");
    document.body.append(host);
    root = createRoot(host);
    await act(async () => root!.render(<TopBar route={{ view: "map" }} onSearch={() => undefined} />));
    const lockup = host.querySelector(".topbar > .fam-lockup")!;
    expect([...lockup.children].map((el) => el.className)).toEqual(["fam-lockup__home", "fam-lockup__rule", "fam-lockup__site"]);
    const home = lockup.querySelector<HTMLAnchorElement>("a.fam-lockup__home")!;
    expect(home.getAttribute("href")).toBe("https://wcook04.github.io/");
    expect(home.getAttribute("rel")).toBe("author");
    const plait = home.querySelector("img")!;
    expect(plait.getAttribute("alt")).toBe("Will Cook: all websites and films");
    expect(plait.getAttribute("src")).toMatch(/^\/(lean-exposition-site\/)?plectis\.svg$/);
    expect(lockup.querySelector(".fam-lockup__rule")!.getAttribute("aria-hidden")).toBe("true");
    const own = lockup.querySelector<HTMLAnchorElement>("a.fam-lockup__site")!;
    expect(own.getAttribute("href")).toBe("/");
    expect(own.querySelector("svg.wordmark__mark")!.getAttribute("aria-hidden")).toBe("true");
    expect(own.querySelector(".fam-lockup__name")!.textContent).toBe("Lean Exposition");
    expect(host.querySelector(".fam-ladder")).toBeNull();
    const jobs = [...host.querySelectorAll(".topnav > a, .topnav > .readmenu > button")].map((el) => el.textContent?.trim());
    expect(jobs).toEqual(["Read", "Map", "Compare", "Checks", "Lean index"]);
    expect(host.querySelector<HTMLAnchorElement>(".readmenu a[href='/#papers']")!.textContent).toContain("All papers and PDFs");
  });

  it("serves the plait from beside the site, with nothing from another host", () => {
    const svg = readFileSync(path.join(site, "public/plectis.svg"), "utf8");
    expect(svg).toMatch(/^<svg|^<\?xml/);
    expect(svg).not.toMatch(/(href|src)=["'](https?:)?\/\//);
    expect(svg).not.toMatch(/url\(["']?(https?:)?\/\//);
  });
});

// FILM_PREVIEW_DIR=<dir> npx vitest run tests/family.test.tsx writes one page per scheme with a
// released fixture and the two held films, styled by the site's own stylesheets, to look at in a
// browser (serve <dir> with the two stills of the fixture in <dir>/films/).
const previewDir = process.env.FILM_PREVIEW_DIR;
describe.runIf(previewDir)("preview of the film slots", () => {
  it("writes one page per scheme", () => {
    const dir = path.resolve(previewDir!);
    mkdirSync(dir, { recursive: true });
    const nm = path.join(site, "node_modules");
    const face = (family: string, weight: string, file: string) =>
      `@font-face{font-family:"${family}";font-weight:${weight};src:url(data:font/woff2;base64,${readFileSync(path.join(nm, file)).toString("base64")}) format("woff2")}`;
    const css = [
      face("STIX Two Text", "400", "@fontsource/stix-two-text/files/stix-two-text-latin-400-normal.woff2"),
      face("STIX Two Text", "500", "@fontsource/stix-two-text/files/stix-two-text-latin-500-normal.woff2"),
      face("Source Sans 3 Variable", "200 900", "@fontsource-variable/source-sans-3/files/source-sans-3-latin-wght-normal.woff2"),
      ...["src/styles/tokens.css", "src/styles/base.css", "src/styles/family.css"].map((f) => readFileSync(path.join(site, f), "utf8")),
      "body{height:auto;padding:32px}.row{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:32px;max-width:1200px;margin-bottom:40px}",
    ].join("\n");
    const slots = renderToStaticMarkup(
      <>
        <div className="row">
          <FilmSlot film={RELEASED} size="small" sizes="360px" />
          <FilmSlot film={RELEASED} sizes="360px" />
          <FilmSlot film={RELEASED} size="large" sizes="360px" />
        </div>
        <div className="row">
          <FilmSlot film={familyFilm("interfaces")} size="small" />
          <FilmSlot film={familyFilm("sk-no-gap")} />
          <FilmSlot film={familyFilm("sk-no-gap")} size="large" />
        </div>
      </>,
    );
    for (const theme of ["light", "dark"]) {
      writeFileSync(
        path.join(dir, `film-slots-${theme}.html`),
        `<!doctype html><html lang="en" data-theme="${theme}"><head><meta charset="utf-8"><title>Film slots</title><style>${css}</style></head><body>${slots}</body></html>`,
      );
    }
  });
});

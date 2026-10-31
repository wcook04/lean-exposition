import { existsSync, readFileSync } from "node:fs";
import { resolve } from "node:path";
import { act, type ReactNode } from "react";
import { createRoot } from "react-dom/client";
import { beforeEach, describe, expect, it, vi } from "vitest";
import { firstScreen } from "../src/reader/firstScreen";
import { openedFirstScreen, readerFirstScreenHtml, readerSkeletonHtml } from "../src/reader/skeleton";

const edition = resolve(__dirname, "../public/edition");

(globalThis as { IS_REACT_ACT_ENVIRONMENT?: boolean }).IS_REACT_ACT_ENVIRONMENT = true;

function render(node: ReactNode) {
  const container = document.createElement("div");
  const root = createRoot(container);
  act(() => root.render(node));
  return { container, unmount: () => act(() => root.unmount()) };
}

function open(html: string) {
  document.body.innerHTML = html;
  // innerHTML does not run scripts; the browser runs this one where it stands.
  new Function(document.querySelector("script")!.textContent!)();
}

describe("a paper's first screen in its HTML", () => {
  // The site's own modules stamp the history entry as they load.
  beforeEach(() => {
    window.history.replaceState(null, "", "/");
    document.body.innerHTML = "";
  });

  it("stays for a reader who opens the paper at the top", () => {
    open(readerFirstScreenHtml("<p class='account-line'>Line</p>", "<section class='part'><div class='part__text'><h1>Title</h1></div></section>"));
    expect(document.querySelector(".prose h1")?.textContent).toBe("Title");
    expect(openedFirstScreen(document)).toContain("Title");
  });

  it.each([["#theorem-1"], ["?l=b1-2"]])("gives way to the empty shape at %s, which opens further down", (address) => {
    window.history.replaceState(null, "", address);
    open(readerFirstScreenHtml("", "<section class='part'><div class='part__text'><h1>Title</h1></div></section>"));
    expect(document.querySelector(".prose")).toBeNull();
    expect(document.querySelector(".reader-shape__text")).not.toBeNull();
    expect(openedFirstScreen(document)).toBeNull();
  });

  it("gives way on a reload or Back, which restores a place from the history entry", () => {
    window.history.replaceState({ key: "kept" }, "", "/read/short");
    open(readerFirstScreenHtml("", "<section class='part'><div class='part__text'><h1>Title</h1></div></section>"));
    expect(document.querySelector(".prose")).toBeNull();
  });

  it("is what React keeps showing, and only until the page has taken over", async () => {
    vi.resetModules();
    window.history.replaceState(null, "", "/read/short");
    document.body.innerHTML = readerFirstScreenHtml("", "<section class='part'><div class='part__text'><h1>Title</h1></div></section>");
    const { ReaderSkeleton, useFirstScreenDone } = await import("../src/reader/skeletonView");
    const shown = render(<ReaderSkeleton />);
    expect(shown.container.querySelector(".prose h1")?.textContent).toBe("Title");
    shown.unmount();
    const Done = () => {
      useFirstScreenDone();
      return null;
    };
    render(<Done />).unmount();
    expect(render(<ReaderSkeleton />).container.querySelector(".prose")).toBeNull();
  });

  it("has the same words for the column as the empty shape has", () => {
    expect(readerFirstScreenHtml("", "")).toContain(readerSkeletonHtml());
  });

  it.runIf(existsSync(resolve(edition, "index.json"))).each(["short", "long", "expository"] as const)("draws the opening of the %s account with the page's engine", (stage) => {
    const index = JSON.parse(readFileSync(resolve(edition, "index.json"), "utf8"));
    const json = (name: string) => JSON.parse(readFileSync(resolve(edition, name), "utf8"));
    const bytes = new Uint8Array(readFileSync(resolve(edition, index.documents[stage])));
    const { account, parts } = firstScreen(stage, bytes, json(index.responses[`/papers/${stage}/structure?representation=reader`]), json(index.responses[`/ties/${stage}`]), null);
    const box = document.createElement("div");
    box.innerHTML = parts;
    expect(box.querySelector("h1")).not.toBeNull();
    expect(box.querySelector("[data-figure-slot]")).toBeNull();
    expect((box.textContent ?? "").length).toBeGreaterThan(1500);
    expect(parts.length).toBeLessThan(160_000);
    expect(account).toContain("Open PDF,");
  });
});

import { act } from "react";
import { createRoot } from "react-dom/client";
import { beforeEach, describe, expect, it, vi } from "vitest";
import { canonicalPath, navigate, parseRoute, routeHref, walkEntry } from "../src/app/router";
import { snapshotScroll, restoreScroll, SCROLLERS } from "../src/app/restore";
import { useKeptCamera } from "../src/map/scene";
import { arrive, arrivedBy, entryKey, leaveAs, namePlace, onLeave, pushEntry, readEntry, readEntryOf, replaceEntry, useBack, useEntryState, writeEntry } from "../src/app/trail";

(globalThis as { IS_REACT_ACT_ENVIRONMENT?: boolean }).IS_REACT_ACT_ENVIRONMENT = true;

const url = (path: string) => new URL(path, window.location.href);

/** jsdom's history moves asynchronously; this does what the browser does, in order. */
function popTo(state: unknown, path: string) {
  window.history.replaceState(state, "", path);
  arrive();
}

beforeEach(() => {
  sessionStorage.clear();
  window.history.replaceState(null, "", "/");
});

describe("an entry", () => {
  it("has a key and keeps values in history.state and in sessionStorage", () => {
    vi.useFakeTimers();
    const key = entryKey();
    writeEntry("tab", "papers");
    expect(readEntry("tab")).toBe("papers");
    expect(window.history.state.lxEntry).toBeUndefined();
    vi.advanceTimersByTime(250);
    vi.useRealTimers();
    expect(window.history.state.lxEntry).toEqual({ tab: "papers" });
    expect(JSON.parse(sessionStorage.getItem(`lx-entry:${key}`)!)).toEqual({ tab: "papers" });
  });

  it("does not call replaceState for each write", () => {
    vi.useFakeTimers();
    entryKey();
    const spy = vi.spyOn(window.history, "replaceState");
    for (let i = 0; i < 20; i++) writeEntry("scroll", i);
    expect(spy).not.toHaveBeenCalled();
    vi.advanceTimersByTime(250);
    expect(spy).toHaveBeenCalledTimes(1);
    spy.mockRestore();
    vi.useRealTimers();
  });

  it("forgets a value written as undefined", () => {
    writeEntry("tab", "papers");
    writeEntry("tab", undefined);
    expect(readEntry("tab")).toBeUndefined();
  });

  it("merges what other owners keep in history.state", () => {
    window.history.replaceState({ lxVisit: { key: "k" } }, "", "/");
    vi.useFakeTimers();
    writeEntry("tab", "papers");
    vi.advanceTimersByTime(250);
    vi.useRealTimers();
    expect(window.history.state.lxVisit).toEqual({ key: "k" });
  });
});

describe("leaving", () => {
  it("runs the hooks on a push, writing into the entry being left", () => {
    const left = entryKey();
    const off = onLeave(() => writeEntry("y", 100));
    pushEntry(url("/about"));
    off();
    expect(readEntryOf(left, "y")).toBe(100);
    expect(readEntry("y")).toBeUndefined();
    expect(arrivedBy()).toBe("push");
  });

  it("on a pop the hooks still write into the entry on screen, whose state history has already left", () => {
    const first = entryKey();
    const firstState = window.history.state;
    pushEntry(url("/about"));
    const second = entryKey();
    const off = onLeave(() => writeEntry("y", 200));
    popTo(firstState, "/");
    off();
    expect(entryKey()).toBe(first);
    expect(arrivedBy()).toBe("pop");
    expect(readEntryOf(second, "y")).toBe(200);
    expect(readEntry("y")).toBeUndefined();
  });

  it("after a reload reads from the mirror what history.state could not be given", async () => {
    const first = window.history.state;
    pushEntry(url("/about"));
    const second = JSON.parse(JSON.stringify(window.history.state));
    const off = onLeave(() => writeEntry("y", 300));
    popTo(first, "/");
    off();
    expect(second.lxEntry?.y).toBeUndefined();
    window.history.replaceState(second, "", "/about");
    vi.resetModules();
    const reloaded = await import("../src/app/trail");
    expect(reloaded.readEntry("y")).toBe(300);
    expect(reloaded.arrivedBy()).toBe("load");
  });

  it("does not run the hooks on a replace", () => {
    const hook = vi.fn();
    const off = onLeave(hook);
    replaceEntry(url("/?x=1"));
    off();
    expect(hook).not.toHaveBeenCalled();
  });

  it("survives a throwing hook", () => {
    const quiet = vi.spyOn(console, "error").mockImplementation(() => undefined);
    const off = onLeave(() => {
      throw new Error("nope");
    });
    expect(() => pushEntry(url("/about"))).not.toThrow();
    off();
    quiet.mockRestore();
  });
});

describe("the push and replace policy", () => {
  it("pushes a change of what is looked at and replaces a refinement", () => {
    const length = window.history.length;
    const key = entryKey();
    navigate({ view: "map" });
    expect(window.history.length).toBe(length + 1);
    expect(entryKey()).not.toBe(key);
    const mapKey = entryKey();
    writeEntry("mapScene", { camera: 1 });
    navigate({ view: "map", lens: "long" }, { replace: true });
    expect(window.history.length).toBe(length + 1);
    expect(entryKey()).toBe(mapKey);
    expect(readEntry("mapScene")).toEqual({ camera: 1 });
  });

  it("ignores a navigation to the address already shown", () => {
    navigate({ view: "map" });
    const length = window.history.length;
    const key = entryKey();
    navigate({ view: "map" });
    expect(window.history.length).toBe(length);
    expect(entryKey()).toBe(key);
  });

  it("a replace onto another page keeps the depth but starts the entry clean", () => {
    navigate({ view: "map" });
    const depth = window.history.state.lxDepth;
    writeEntry("mapScene", { camera: 1 });
    const key = entryKey();
    navigate({ view: "about" }, { replace: true });
    expect(entryKey()).not.toBe(key);
    expect(readEntry("mapScene")).toBeUndefined();
    expect(window.history.state.lxDepth).toBe(depth);
  });

  it("stamps a fragment link the browser followed itself, one step on", () => {
    const left = entryKey();
    const depth = window.history.state.lxDepth;
    popTo(null, "/about#x");
    expect(entryKey()).not.toBe(left);
    expect(window.history.state).toMatchObject({ lxDepth: depth + 1, lxPrevious: left });
    expect(arrivedBy()).toBe("push");
  });
});

describe("a walk between Lean names", () => {
  const seen = { current: null as ReturnType<typeof useBack> };

  it("on the reader is one entry with an address, named for where it came from", () => {
    mount(<Control seen={seen} />);
    navigate({ view: "read", stage: "short", node: "a.b", at: "12" });
    const length = window.history.length;
    act(() => walkEntry({ name: "OAI.SK.first", module: "OAI.SK", from: "OAI.SK.start" }));
    expect(window.history.length).toBe(length + 1);
    expect(parseRoute(new URL(window.location.href))).toMatchObject({ view: "read", stage: "short", node: "a.b", at: "12", decl: "OAI.SK.first", declModule: "OAI.SK" });
    expect(seen.current?.label).toBe("start");
  });

  it("walks again, dropping a module the next name does not need", () => {
    navigate({ view: "read", stage: "short", decl: "OAI.SK.first", declModule: "OAI.SK" });
    const length = window.history.length;
    walkEntry({ name: "OAI.SK.second" });
    expect(window.history.length).toBe(length + 1);
    const route = parseRoute(new URL(window.location.href));
    expect(route).toMatchObject({ decl: "OAI.SK.second" });
    expect(route).not.toHaveProperty("declModule", "OAI.SK");
  });

  it("does not stack a walk to the name already open", () => {
    navigate({ view: "read", stage: "short", decl: "OAI.SK.first" });
    const length = window.history.length;
    walkEntry({ name: "OAI.SK.first" });
    expect(window.history.length).toBe(length);
  });

  it("gives a selected step way to the declaration on the map", () => {
    navigate({ view: "map", node: "a.b", edge: "a→b→uses" });
    walkEntry({ name: "OAI.SK.first" });
    const params = new URL(window.location.href).searchParams;
    expect(params.get("n")).toBe("a.b");
    expect(params.get("d")).toBe("OAI.SK.first");
    expect(params.has("e")).toBe(false);
  });

  it("goes to the declaration on /lean and from a page that cannot show it", () => {
    navigate({ view: "lean", module: "A", decl: "A.x" });
    walkEntry({ name: "B.y", module: "B" });
    expect(parseRoute(new URL(window.location.href))).toEqual({ view: "lean", module: "B", decl: "B.y" });
    navigate({ view: "compare" });
    walkEntry({ name: "A.x", module: "A" });
    expect(parseRoute(new URL(window.location.href))).toEqual({ view: "lean", module: "A", decl: "A.x" });
  });
});

describe("a load that has lost history.state", () => {
  /** What the page left behind, then a new page load at `path` with no state. */
  async function reload(path: string, options: { type?: string; ago?: number } = {}) {
    if (options.ago !== undefined) {
      const live = JSON.parse(sessionStorage.getItem("lx-live")!);
      sessionStorage.setItem("lx-live", JSON.stringify({ ...live, at: Date.now() - options.ago }));
    }
    window.history.replaceState(null, "", path);
    vi.resetModules();
    const timing = vi.spyOn(performance, "getEntriesByType").mockReturnValue(options.type ? [{ type: options.type } as unknown as PerformanceEntry] : []);
    const trail = await import("../src/app/trail");
    timing.mockRestore();
    return trail;
  }

  // The mirror's debounce. A synthetic pagehide would also reach the trail of each earlier
  // simulated load, which a real page never has.
  const settled = () => new Promise((resolve) => setTimeout(resolve, 260));

  function leaveAPage() {
    navigate({ view: "read", stage: "short" });
    navigate({ view: "read", stage: "long", node: "a.b" });
    writeEntry("reading", { part: 3 });
    pushEntry(url(window.location.href));
    return window.location.pathname + window.location.search;
  }

  it("is the same entry after a reload, with its depth, its way back and its values", async () => {
    const path = leaveAPage();
    const { key, depth, previous } = { key: entryKey(), depth: window.history.state.lxDepth, previous: window.history.state.lxPrevious };
    writeEntry("reading", { part: 7 });
    await settled();
    const trail = await reload(path, { type: "reload" });
    expect(trail.entryKey()).toBe(key);
    expect(window.history.state).toMatchObject({ lxKey: key, lxDepth: depth, lxPrevious: previous });
    expect(trail.readEntry("reading")).toEqual({ part: 7 });
    expect(trail.arrivedBy()).toBe("load");
  });

  it("does the same when the browser calls the reload a new navigation, as Firefox does", async () => {
    const path = leaveAPage();
    const key = entryKey();
    await settled();
    const trail = await reload(path, { type: "navigate" });
    expect(trail.entryKey()).toBe(key);
  });

  it("does not take a much later visit to the same address for a reload", async () => {
    const path = leaveAPage();
    const key = entryKey();
    await settled();
    const trail = await reload(path, { type: "navigate", ago: 60_000 });
    expect(trail.entryKey()).not.toBe(key);
    expect(window.history.state.lxDepth).toBe(0);
  });

  it("does not take another address for this entry", async () => {
    leaveAPage();
    const key = entryKey();
    await settled();
    const trail = await reload("/about/", { type: "reload" });
    expect(trail.entryKey()).not.toBe(key);
  });

  it("treats the host's slash as the same place", async () => {
    navigate("/read/short?l=12");
    const key = entryKey();
    await settled();
    const trail = await reload("/read/short/?l=12", { type: "reload" });
    expect(trail.entryKey()).toBe(key);
  });

  it("finds a Back or Forward entry by its address", async () => {
    navigate({ view: "compare" });
    const key = entryKey();
    navigate({ view: "about" });
    await settled();
    const trail = await reload("/compare/", { type: "back_forward" });
    expect(trail.entryKey()).toBe(key);
  });

  it("restores what else stood in history.state, a visit's origin", async () => {
    navigate({ view: "read", stage: "short" });
    window.history.replaceState({ ...window.history.state, lxVisit: { key: "k", label: "§4" } }, "");
    const path = window.location.pathname;
    writeEntry("tab", "papers");
    await settled();
    await reload(path, { type: "reload" });
    expect(window.history.state.lxVisit).toEqual({ key: "k", label: "§4" });
  });

  it("works with sessionStorage unusable, and starts a new entry", async () => {
    navigate({ view: "compare" });
    const path = window.location.pathname;
    const read = vi.spyOn(Storage.prototype, "getItem").mockImplementation(() => {
      throw new Error("denied");
    });
    const write = vi.spyOn(Storage.prototype, "setItem").mockImplementation(() => {
      throw new Error("denied");
    });
    const trail = await reload(path, { type: "reload" });
    expect(typeof trail.entryKey()).toBe("string");
    trail.writeEntry("tab", "papers");
    expect(trail.readEntry("tab")).toBe("papers");
    expect(() => window.dispatchEvent(new Event("pagehide"))).not.toThrow();
    read.mockRestore();
    write.mockRestore();
  });

  it("names an unkeyed Back by its address, and a fragment link as one step on", () => {
    navigate({ view: "compare" });
    const compare = entryKey();
    navigate({ view: "about" });
    const depth = window.history.state.lxDepth;
    popTo(null, "/compare/");
    expect(entryKey()).toBe(compare);
    expect(arrivedBy()).toBe("pop");
    popTo(null, "/compare/#x");
    expect(entryKey()).not.toBe(compare);
    expect(arrivedBy()).toBe("push");
    expect(window.history.state.lxDepth).toBe(depth);
  });
});

describe("addresses in the host's exact form", () => {
  it("writes each page as the directory it is", () => {
    expect(routeHref({ view: "map", node: "a" })).toBe("/map/?n=a");
    expect(routeHref({ view: "read", stage: "short", anchor: "x" })).toBe("/read/short/#x");
    expect(routeHref({ view: "lean", decl: "A.b" })).toBe("/lean/?d=A.b");
    expect(routeHref({ view: "about" })).toBe("/about/");
    expect(routeHref({ view: "home" })).toBe("/");
  });

  it("turns any address it is given into that form, and leaves the rest alone", () => {
    expect(canonicalPath("/read/short")).toBe("/read/short/");
    expect(canonicalPath("/read/short/")).toBe("/read/short/");
    expect(canonicalPath("/compare")).toBe("/compare/");
    expect(canonicalPath("/")).toBe("/");
    expect(canonicalPath("/read/nothing")).toBe("/read/nothing");
    expect(canonicalPath("/pdf/short.pdf")).toBe("/pdf/short.pdf");
    navigate("/compare?n=a#x");
    expect(window.location.pathname + window.location.search + window.location.hash).toBe("/compare/?n=a#x");
  });

  it("parses the slashed form as the same route", () => {
    expect(parseRoute(new URL("https://example.test/read/short/?l=1#a"))).toMatchObject({ view: "read", stage: "short", at: "1", anchor: "a" });
  });
});

function Control({ seen }: { seen: { current: ReturnType<typeof useBack> } }) {
  seen.current = useBack();
  return null;
}

function mount(element: React.ReactElement) {
  const root = createRoot(document.createElement("div"));
  act(() => root.render(element));
  return root;
}

describe("the visible Back", () => {
  it("is absent at the start of the visit", () => {
    const seen = { current: null as ReturnType<typeof useBack> };
    mount(<Control seen={seen} />);
    expect(seen.current).toBeNull();
  });

  it("names the place left, however it was named", () => {
    const seen = { current: null as ReturnType<typeof useBack> };
    mount(<Control seen={seen} />);
    act(() => navigate({ view: "map" }));
    expect(seen.current?.label).toBe("the front page");
    act(() => {
      leaveAs("Short paper §2.3");
      navigate({ view: "compare" });
    });
    expect(seen.current?.label).toBe("Short paper §2.3");
    const off = namePlace(() => "Compare, step 4");
    act(() => navigate({ view: "about" }));
    off();
    expect(seen.current?.label).toBe("Compare, step 4");
  });

  it("uses the browser's Back", () => {
    const seen = { current: null as ReturnType<typeof useBack> };
    mount(<Control seen={seen} />);
    act(() => navigate({ view: "map" }));
    const back = vi.spyOn(window.history, "back").mockImplementation(() => undefined);
    seen.current?.back();
    expect(back).toHaveBeenCalledTimes(1);
    back.mockRestore();
  });

  it("refreshes the name when the place changed on a later visit", () => {
    const seen = { current: null as ReturnType<typeof useBack> };
    mount(<Control seen={seen} />);
    const first = window.history.state;
    leaveAs("Short paper §1");
    act(() => navigate({ view: "map" }));
    const second = window.history.state;
    expect(seen.current?.label).toBe("Short paper §1");
    act(() => popTo(first, "/"));
    act(() => {
      leaveAs("Short paper §4");
      window.history.replaceState(second, "", "/map");
      arrive();
    });
    expect(seen.current?.label).toBe("Short paper §4");
  });
});

describe("state the entry owns", () => {
  it("follows the entry through Back and Forward", () => {
    const seen = { current: ["", (_: string) => undefined] as [string, (v: string) => void] };
    function Tab() {
      seen.current = useEntryState("tab", "lean");
      return null;
    }
    mount(<Tab />);
    const first = window.history.state;
    act(() => seen.current[1]("papers"));
    expect(seen.current[0]).toBe("papers");
    act(() => navigate({ view: "map" }));
    expect(seen.current[0]).toBe("lean");
    act(() => popTo(first, "/"));
    expect(seen.current[0]).toBe("papers");
  });
});

describe("a map shown in a pane", () => {
  const scene = { camera: { x: 4, y: 8, k: 1 }, expanded: [], mode: "overview" as const };
  const has = () => true;

  function Pane({ tree }: { tree: { current: { getScene(): typeof scene; restoreScene(s: typeof scene): void } } }) {
    useKeptCamera(tree, has);
    return null;
  }

  it("keeps its camera on leaving and returns to it, without writing as it follows", () => {
    vi.useFakeTimers();
    const tree = { current: { getScene: vi.fn(() => scene), restoreScene: vi.fn() } };
    mount(<Pane tree={tree} />);
    expect(tree.current.getScene).not.toHaveBeenCalled();
    const first = window.history.state;
    act(() => navigate({ view: "map" }));
    expect(tree.current.getScene).toHaveBeenCalledTimes(1);
    expect(tree.current.restoreScene).not.toHaveBeenCalled();
    act(() => popTo(first, "/"));
    expect(tree.current.restoreScene).toHaveBeenCalledWith(scene);
    act(() => void vi.advanceTimersByTime(800));
    expect(tree.current.restoreScene).toHaveBeenCalledTimes(2);
    vi.useRealTimers();
  });
});

describe("restoreScroll", () => {
  function scroller(max: number) {
    const el = document.createElement("div");
    el.className = "panel__body";
    Object.defineProperty(el, "scrollHeight", { configurable: true, get: () => max + 100 });
    Object.defineProperty(el, "clientHeight", { configurable: true, get: () => 100 });
    el.scrollTo = ((options: ScrollToOptions) => {
      el.scrollTop = Math.min(options.top ?? 0, max);
    }) as typeof el.scrollTo;
    document.body.append(el);
    return el;
  }

  it("lists its scrollers once each", () => {
    expect(new Set(SCROLLERS).size).toBe(SCROLLERS.length);
  });

  it("saves inner scrollers by name", () => {
    const el = scroller(500);
    el.scrollTop = 240;
    expect(snapshotScroll(false).inner).toEqual({ ".panel__body@0": [240, 0] });
    expect(snapshotScroll(false).window).toBeUndefined();
    el.remove();
  });

  it("waits for content that arrives late and stops when it holds", async () => {
    const el = scroller(100);
    const done = vi.fn();
    restoreScroll({ inner: { ".panel__body@0": [400, 0] } }, { onDone: done, settle: 30, limit: 800 });
    expect(el.scrollTop).toBe(100);
    Object.defineProperty(el, "scrollHeight", { configurable: true, get: () => 900 });
    el.scrollTo = ((options: ScrollToOptions) => {
      el.scrollTop = options.top ?? 0;
    }) as typeof el.scrollTo;
    await vi.waitFor(() => expect(done).toHaveBeenCalled());
    expect(el.scrollTop).toBe(400);
    el.remove();
  });

  it("puts the place back when late fonts arrive, and never after the reader has moved", async () => {
    const listeners = new Set<() => void>();
    const fonts = {
      addEventListener: (_: string, fn: () => void) => listeners.add(fn),
      removeEventListener: (_: string, fn: () => void) => listeners.delete(fn),
    };
    const had = Object.getOwnPropertyDescriptor(document, "fonts");
    Object.defineProperty(document, "fonts", { configurable: true, value: fonts });
    const el = scroller(900);
    const done = vi.fn();
    const stop = restoreScroll({ inner: { ".panel__body@0": [400, 0] } }, { onDone: done, settle: 20, limit: 400, refit: true });
    await vi.waitFor(() => expect(done).toHaveBeenCalledTimes(1));
    el.scrollTop = 410;
    [...listeners].forEach((fn) => fn());
    expect(el.scrollTop).toBe(400);
    await vi.waitFor(() => expect(done).toHaveBeenCalledTimes(2));
    window.dispatchEvent(new Event("wheel"));
    expect(listeners.size).toBe(0);
    el.scrollTop = 700;
    [...listeners].forEach((fn) => fn());
    expect(el.scrollTop).toBe(700);
    stop();
    el.remove();
    if (had) Object.defineProperty(document, "fonts", had);
    else delete (document as { fonts?: unknown }).fonts;
  });

  it("gives way the moment the reader scrolls", async () => {
    const el = scroller(100);
    const done = vi.fn();
    restoreScroll({ inner: { ".panel__body@0": [400, 0] } }, { onDone: done, settle: 20, limit: 200 });
    window.dispatchEvent(new Event("wheel"));
    await new Promise((r) => setTimeout(r, 260));
    expect(done).not.toHaveBeenCalled();
    el.remove();
  });
});

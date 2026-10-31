// Code that has arrived shows at once: no fallback, so React has no reveal to hold back.
import { Suspense, act } from "react";
import { createRoot } from "react-dom/client";
import { describe, expect, it, vi } from "vitest";
import { code, lazyCode } from "../src/app/code";

describe("code loaded on demand", () => {
  it("fetches once, however often it is asked for", async () => {
    const fetchIt = vi.fn(() => Promise.resolve("module"));
    const source = code(fetchIt);
    source.start();
    source.start();
    await source.load();
    await source.load();
    expect(fetchIt).toHaveBeenCalledTimes(1);
  });

  it("answers at once when the module has arrived", async () => {
    const source = code(() => Promise.resolve({ value: 1 }));
    await source.load();
    let seen = 0;
    source.load().then((module) => {
      seen = module.value;
    });
    expect(seen).toBe(1);
  });

  it("carries a value through a chain at once", async () => {
    const source = code(() => Promise.resolve(1));
    await source.load();
    let seen = 0;
    source
      .load()
      .then((n) => n + 1)
      .then((n) => {
        seen = n;
      });
    expect(seen).toBe(2);
  });

  it("tries again after a failed fetch", async () => {
    const fetchIt = vi.fn<() => Promise<string>>().mockRejectedValueOnce(new Error("offline")).mockResolvedValue("module");
    const source = code(fetchIt);
    await expect(source.load()).rejects.toThrow("offline");
    await expect(source.load()).resolves.toBe("module");
    expect(fetchIt).toHaveBeenCalledTimes(2);
  });

  it("does not throw from start when a fetch fails", async () => {
    const source = code(() => Promise.reject(new Error("offline")));
    source.start();
    await expect(source.load()).rejects.toThrow("offline");
  });
});

describe("a component from code that has arrived", () => {
  it("renders without showing the fallback", async () => {
    (globalThis as Record<string, unknown>).IS_REACT_ACT_ENVIRONMENT = true;
    const source = code(() => Promise.resolve({ Page: () => <p>the page</p> }));
    await source.load();
    const Page = lazyCode(source, (m) => m.Page);
    const fallback = vi.fn(() => <p>waiting</p>);
    function Waiting() {
      return fallback();
    }
    const container = document.createElement("div");
    const root = createRoot(container);
    act(() =>
      root.render(
        <Suspense fallback={<Waiting />}>
          <Page />
        </Suspense>,
      ),
    );
    expect(container.textContent).toBe("the page");
    expect(fallback).not.toHaveBeenCalled();
    act(() => root.unmount());
  });
});

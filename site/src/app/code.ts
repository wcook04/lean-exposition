// Code loaded on demand that can answer at once. lazy() suspends for at least a tick even
// when the import has finished, and after showing a Suspense fallback React holds the next
// reveal back for about 300ms, so a page whose code had already arrived still waited.
// Finished code here resolves through a thenable that calls back immediately, which lazy()
// reads without suspending.

import { lazy, type ComponentType } from "react";

export interface Code<T> {
  /** Start fetching, if nothing has. */
  start(): void;
  /** The module: at once if it has arrived, otherwise when it does. */
  load(): PromiseLike<T>;
}

function atOnce<T>(value: T): PromiseLike<T> {
  return { then: (done) => atOnce(done ? done(value) : value) } as PromiseLike<T>;
}

export function code<T>(fetchIt: () => Promise<T>): Code<T> {
  let arrived: { module: T } | null = null;
  let pending: Promise<T> | null = null;
  const fetchOnce = () =>
    (pending ??= fetchIt().then(
      (module) => {
        arrived = { module };
        return module;
      },
      (error: unknown) => {
        pending = null;
        throw error;
      },
    ));
  return {
    start: () => void fetchOnce().catch(() => undefined),
    load: () => (arrived ? atOnce(arrived.module) : fetchOnce()),
  };
}

/** A component from code loaded on demand. */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export function lazyCode<T, C extends ComponentType<any>>(source: Code<T>, pick: (module: T) => C) {
  return lazy(() => source.load().then((module) => ({ default: pick(module) })) as Promise<{ default: C }>);
}

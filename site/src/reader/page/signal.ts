// A value several small components watch. The scroll path writes these, never React
// state on the page: only the few leaves that show a value re-render when it changes.

import { startTransition, useEffect, useState, useSyncExternalStore } from "react";

export class Signal<T> {
  private listeners = new Set<() => void>();
  constructor(
    private value: T,
    private same: (a: T, b: T) => boolean = Object.is,
  ) {}
  get = () => this.value;
  set(next: T) {
    if (this.same(next, this.value)) return;
    this.value = next;
    this.listeners.forEach((listener) => listener());
  }
  subscribe = (listener: () => void) => {
    this.listeners.add(listener);
    return () => {
      this.listeners.delete(listener);
    };
  };
}

export function useSignal<T>(signal: Signal<T>): T {
  return useSyncExternalStore(signal.subscribe, signal.get);
}

/** As useSignal, for something costly to draw: React may set the update aside for scrolling and input. */
export function useSlowSignal<T>(signal: Signal<T>): T {
  const [value, setValue] = useState(signal.get);
  useEffect(() => {
    const update = () => startTransition(() => setValue(signal.get()));
    update();
    return signal.subscribe(update);
  }, [signal]);
  return value;
}

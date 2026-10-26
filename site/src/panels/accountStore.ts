// The account the reader last chose in the record panel. It persists across
// selections, so clicking around the map keeps showing each result in the
// same account, and across reloads within the browser session.

import { useSyncExternalStore } from "react";
import type { Stage } from "../api/types";

const KEY = "lx-panel-account";
const STAGES = new Set<string>(["expository", "short", "long"]);
const listeners = new Set<() => void>();

function read(): Stage | null {
  try {
    const value = sessionStorage.getItem(KEY);
    return value && STAGES.has(value) ? (value as Stage) : null;
  } catch {
    return null;
  }
}

let current: Stage | null = typeof window === "undefined" ? null : read();

export function chosenAccount(): Stage | null {
  return current;
}

export function chooseAccount(stage: Stage | null): void {
  if (stage === current) return;
  current = stage;
  try {
    if (stage) sessionStorage.setItem(KEY, stage);
    else sessionStorage.removeItem(KEY);
  } catch {
    /* storage unavailable: the choice lasts for this page */
  }
  listeners.forEach((l) => l());
}

function subscribe(listener: () => void): () => void {
  listeners.add(listener);
  return () => listeners.delete(listener);
}

export function useChosenAccount(): Stage | null {
  return useSyncExternalStore(subscribe, chosenAccount, () => null);
}

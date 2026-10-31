// The map's remembered scene, kept per history entry so Back returns the reader
// to the camera, unfolded branches and representation they left. The URL holds
// what is selected; the history entry's state holds how it was being looked at.
//
// Pan and zoom only ever write to the current entry (never push); app/trail.ts
// holds the entry.

import { useEffect, type RefObject } from "react";
import { arrivedBy, entryKey, onLeave, readEntry, useEntryKey, writeEntry } from "../app/trail";
import type { MapScene } from "./ArgumentTree";

export type { MapScene };
type TreeHandle = { getScene(): MapScene; restoreScene(scene: MapScene): void };

const KEY = "mapScene";
const PANE_KEY = "paneScene";
const DELAY = 200;
/** A pane opens with a fit of its own after a moment; the restored camera lands after it. */
const PANE_SETTLE = 700;

const finite = (v: unknown): v is number => typeof v === "number" && Number.isFinite(v);

/** A scene as stored, if it is well formed and every record it names is in this edition. */
export function validScene(value: unknown, has: (id: string) => boolean): MapScene | null {
  if (!value || typeof value !== "object") return null;
  const v = value as Partial<MapScene>;
  const c = v.camera;
  if (!c || !finite(c.x) || !finite(c.y) || !finite(c.k) || c.k <= 0) return null;
  if (!Array.isArray(v.expanded) || !v.expanded.every((id) => typeof id === "string" && has(id))) return null;
  if (v.mode !== "steps" && v.mode !== "overview") return null;
  const a = v.anchor;
  const anchor = a && typeof a.id === "string" && has(a.id) && finite(a.x) && finite(a.y) ? { id: a.id, x: a.x, y: a.y } : undefined;
  return { camera: { x: c.x, y: c.y, k: c.k }, expanded: [...v.expanded], mode: v.mode, ...(anchor ? { anchor } : {}) };
}

/** The scene remembered for the current history entry, or null. */
export function readScene(has: (id: string) => boolean): MapScene | null {
  return validScene(readEntry(KEY), has);
}

/** Debounced writes of the settled scene into the entry it settled in. */
export function sceneWriter() {
  let timer: ReturnType<typeof setTimeout> | null = null;
  let pending: { scene: MapScene; entry: string } | null = null;
  const cancel = () => {
    if (timer) clearTimeout(timer);
    timer = null;
    pending = null;
  };
  const write = (p: { scene: MapScene; entry: string }) => {
    // The entry may have changed since the scene settled; never write into another's.
    if (p.entry === entryKey()) writeEntry(KEY, p.scene);
  };
  return {
    /** Remember this scene for the current entry after a short quiet period. */
    save(scene: MapScene) {
      if (timer) clearTimeout(timer);
      pending = { scene, entry: entryKey() };
      timer = setTimeout(() => {
        const p = pending;
        cancel();
        if (p) write(p);
      }, DELAY);
    },
    /** Write now (before leaving the entry), preferring a fresh scene when one is given. */
    flush(scene?: MapScene | null) {
      const p = pending;
      cancel();
      if (scene) write({ scene, entry: entryKey() });
      else if (p) write(p);
    },
    cancel,
  };
}

/**
 * The camera of a map shown beside something else, kept per history entry. The
 * pane follows the reader, so it writes only on leaving, and on coming back it
 * returns to the view that was left before following resumes.
 */
export function useKeptCamera(tree: RefObject<Pick<TreeHandle, "getScene" | "restoreScene"> | null>, has: (id: string) => boolean): void {
  const key = useEntryKey();
  useEffect(
    () =>
      onLeave(() => {
        const scene = tree.current?.getScene();
        if (scene) writeEntry(PANE_KEY, scene);
      }),
    [tree],
  );
  useEffect(() => {
    if (arrivedBy() === "push") return;
    const scene = validScene(readEntry(PANE_KEY), has);
    if (!scene) return;
    const put = () => tree.current?.restoreScene(scene);
    put();
    const again = window.setTimeout(put, PANE_SETTLE);
    return () => window.clearTimeout(again);
  }, [key, tree, has]);
}

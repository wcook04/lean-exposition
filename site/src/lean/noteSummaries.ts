// A library paper's reading notes on Lean declarations, by full name (lean-notes.json, written by
// its build from the instance's generated/lean-notes.json). A note may carry a summary of at most a
// few lines, written from the note; cards show the summary first and the whole note on request.

import { useEffect, useState } from "react";
import site from "@instance/site";

export interface LeanNote { text: string; summary?: string }
type Notes = Record<string, LeanNote>;
let loading: Promise<Notes> | null = null;

export function loadLeanNotes(): Promise<Notes> {
  if (!site.library) return Promise.resolve({});
  loading ??= fetch(`${import.meta.env.BASE_URL}lean-notes.json`)
    .then((r) => (r.ok ? r.json() : {}))
    .then((data: { notes?: Notes }) => data.notes ?? {})
    .catch(() => ({}));
  return loading;
}

/** The reading note on one declaration, or null when there is none (or not yet loaded). */
export function useLeanNote(name: string | undefined): LeanNote | null {
  const [note, setNote] = useState<LeanNote | null>(null);
  useEffect(() => {
    let live = true;
    setNote(null);
    if (name) void loadLeanNotes().then((notes) => live && setNote(notes[name] ?? null));
    return () => {
      live = false;
    };
  }, [name]);
  return note;
}

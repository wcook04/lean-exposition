// Reading notes on Lean declarations that no phrase names (a library paper's lean-notes.json,
// written by its build from the instance's generated/lean-notes.json). A phrase's own card keeps
// its note; this shows the note on any other declaration's Lean card, marked AI-drafted.

import { useEffect, useState } from "react";
import site from "@instance/site";
import { Prose } from "./ReadingStrip";

type Notes = Record<string, { text: string; summary?: string }>;
let loading: Promise<Notes> | null = null;

function loadNotes(): Promise<Notes> {
  if (!site.library) return Promise.resolve({});
  loading ??= fetch(`${import.meta.env.BASE_URL}lean-notes.json`)
    .then((r) => (r.ok ? r.json() : {}))
    .then((data: { notes?: Notes }) => data.notes ?? {})
    .catch(() => ({}));
  return loading;
}

export function LeanReadingNote({ name }: { name: string }) {
  const [note, setNote] = useState<{ text: string; summary?: string } | null>(null);
  useEffect(() => {
    let live = true;
    void loadNotes().then((notes) => live && setNote(notes[name] ?? null));
    return () => {
      live = false;
    };
  }, [name]);
  if (!note) return null;
  return (
    <div className="lean-block__link lean-reading-note">
      <p className="lean-block__relation">
        <strong>Reading note</strong> <span className="lean-reading-note__who">· AI-drafted</span>
      </p>
      {note.summary ? <p className="lean-reading-note__summary">{note.summary}</p> : null}
      <p><Prose text={note.text} /></p>
    </div>
  );
}

// Reading notes on Lean declarations that no phrase names (a library paper's lean-notes.json,
// written by its build from the instance's generated/lean-notes.json). A phrase's own card keeps
// its note; this shows the note on any other declaration's Lean card, marked AI-drafted: its
// summary first when it has one, with "more" for the whole note.

import { NoteBody } from "../reader/page/PhraseCard";
import { useLeanNote } from "./noteSummaries";

export function LeanReadingNote({ name }: { name: string }) {
  const note = useLeanNote(name);
  if (!note) return null;
  return (
    <div className="lean-block__link lean-reading-note">
      <p className="lean-block__relation">
        <strong>Reading note</strong> <span className="lean-reading-note__who">· AI-drafted</span>
      </p>
      <NoteBody text={note.text} summary={note.summary} className="lean-reading-note__text" />
    </div>
  );
}

// The subject band: one strip at the head of the right pane, the same in both views and outside
// the graph's canvas. It says which state the reader is in (following the paper, a preview, or a
// selection) and where in the paper the subject is, and it holds the two acts that end or revisit
// a selection. They are different acts: "Resume here" lets go and never moves the paper; "Return to
// selected words" moves the paper and keeps the selection. docs/reader-design.md specifies it.

import { useEffect, useRef, useState } from "react";

export type SubjectState = "following" | "preview" | "words" | "paragraph" | "declaration" | "step";

const WORDS: Record<SubjectState, string> = {
  following: "Following the paper",
  preview: "Preview",
  words: "Selected words",
  paragraph: "Selected paragraph",
  declaration: "Selected declaration",
  step: "Selected step",
};

const RETURN: Partial<Record<SubjectState, string>> = {
  words: "Return to selected words",
  paragraph: "Return to selected paragraph",
};

interface Props {
  state: SubjectState;
  /** Where in the paper: "§5.6", a heading, "the opening". Empty when the subject has no place here. */
  place?: string;
  /** What the preview or selection is, in a few plain words, for the announcement. */
  title?: string;
  onResume?(): void;
  onReturn?(): void;
}

export function SubjectBand({ state, place, title, onResume, onReturn }: Props) {
  const selected = state !== "following" && state !== "preview";
  // A change of state is said once to assistive technology; a new subject within one state is not,
  // so scrolling does not read every passage aloud.
  const [said, setSaid] = useState("");
  const last = useRef<SubjectState | null>(null);
  useEffect(() => {
    if (last.current === state) return;
    const first = last.current === null;
    last.current = state;
    if (first) return;
    setSaid(`${WORDS[state]}${selected && title ? `: ${title}` : ""}`);
  }, [state, selected, title]);
  return (
    <div className="subject-band" data-state={state}>
      <p className="subject-band__state">
        <span className="subject-band__words">{WORDS[state]}</span>
        {state === "following" && <span className="subject-band__hint">Changes as you scroll</span>}
        {state === "preview" && <span className="subject-band__hint">Not selected</span>}
        {selected &&
          place &&
          (onReturn ? (
            <button type="button" className="subject-band__place" onClick={onReturn} title={RETURN[state] ?? "Return to it in the paper"}>
              in {place}
            </button>
          ) : (
            <span className="subject-band__hint">in {place}</span>
          ))}
      </p>
      {selected && (
        <div className="subject-band__acts">
          {onReturn && (
            <button type="button" className="subject-band__act" onClick={onReturn}>
              {RETURN[state] ?? "Return to it in the paper"}
            </button>
          )}
          {onResume && (
            <button type="button" className="subject-band__act subject-band__act--resume" aria-keyshortcuts="Escape" onClick={onResume}>
              Resume here
            </button>
          )}
        </div>
      )}
      <span className="visually-hidden" role="status" aria-live="polite">
        {said}
      </span>
    </div>
  );
}

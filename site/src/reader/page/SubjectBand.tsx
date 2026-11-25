// The pane’s subject and whether it follows the paper or holds a selection.

import { useEffect, useRef, useState } from "react";
import { ModeSwitch } from "./ModeSwitch";

export type SubjectState = "following" | "preview" | "words" | "paragraph" | "declaration" | "step";

const WORDS: Record<SubjectState, string> = {
  following: "Following the paper",
  preview: "Preview",
  words: "Selected words",
  paragraph: "Selected paragraph",
  declaration: "Selected declaration",
  step: "Selected step",
};

interface Props {
  state: SubjectState;
  /** Where in the paper: "§5.6", a heading, "the opening". Empty when the subject has no place here. */
  place?: string;
  /** What the preview or selection is, in a few plain words, for the announcement. */
  title?: string;
  /** Auto: let the selection go and follow the paper from where the reader is. */
  onResume?(): void;
  /** Manual, while following: keep what the pane shows now. Absent when it shows nothing to keep. */
  onManual?(): void;
}

export function SubjectBand({ state, place, title, onResume, onManual }: Props) {
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
      <ModeSwitch manual={selected} onAuto={onResume} onManual={onManual} />
      <p className="subject-band__state">
        <span className="subject-band__words">{WORDS[state]}</span>
        {state === "following" && (
          <span className="subject-band__hint">
            {onManual ? <>Select <span className="subject-band__sample">underlined text</span> to keep its annotation open</> : "Changes as you scroll"}
          </span>
        )}
        {state === "preview" && <span className="subject-band__hint">Not selected</span>}
        {selected && place && <span className="subject-band__hint">in {place}</span>}
      </p>
      <span className="visually-hidden" role="status" aria-live="polite">
        {said}
      </span>
    </div>
  );
}

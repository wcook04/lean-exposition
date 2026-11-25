// The pane’s subject and whether it follows the paper or holds a selection.

import { useEffect, useRef, useState } from "react";
import type { PhraseTopic } from "../../api/lean";
import { ModeSwitch } from "./ModeSwitch";

/** "next" and "last": no link is at the reading line, and the pane shows the one Next lands on, or the last one passed. */
export type SubjectState = "following" | "preview" | "next" | "last" | "words" | "paragraph" | "declaration" | "step";

const WORDS: Record<SubjectState, string> = {
  following: "Following the paper",
  preview: "Preview",
  next: "Next link",
  last: "Last link",
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
  /** The topic of the annotation the pane shows, named and coloured as in the sidebar's key. */
  topic?: PhraseTopic | null;
}

export function SubjectBand({ state, place, title, onResume, onManual, topic }: Props) {
  const selected = state !== "following" && state !== "preview" && state !== "next" && state !== "last";
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
        {/* The band names the annotation's topic; the state stays in words for assistive technology,
            and is shown only where there is no topic to name and it says more than the switch. */}
        {topic ? (
          <>
            <span className="visually-hidden">{WORDS[state]}: </span>
            <span className="subject-band__topic" data-tone={topic.tone} title={topic.description || undefined}>
              <span className="phrase-key__swatch" aria-hidden="true" />
              <span className="subject-band__name">{topic.name}</span>
            </span>
          </>
        ) : state === "following" ? (
          <span className="visually-hidden">{WORDS[state]}</span>
        ) : (
          <span className="subject-band__words">{WORDS[state]}</span>
        )}
        {state === "preview" && <span className="subject-band__hint">{topic ? "Preview, not selected" : "Not selected"}</span>}
        {state === "next" && <span className="subject-band__hint">Not reached yet · Next goes here</span>}
        {state === "last" && <span className="subject-band__hint">Nothing linked further on · the last link before here</span>}
        {selected && place && <span className="subject-band__hint">in {place}</span>}
      </p>
      <span className="visually-hidden" role="status" aria-live="polite">
        {said}
      </span>
    </div>
  );
}

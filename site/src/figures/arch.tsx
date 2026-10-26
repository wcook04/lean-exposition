// Shared parts for the two architecture-paper diagrams, translating the
// paper's TikZ styles: archbox (hairline frame), archrecord (the shared
// record, blue frame and faint blue fill), archview (dashed frame),
// archflow (Stealth arrow, black!65) and archnote (label on a ground patch).
import { Fragment } from "react";
import { Rich } from "./tex";

export type BoxKind = "box" | "record" | "view";

export function Box({ kind, title, lines }: { kind: BoxKind; title?: string; lines: string[] }) {
  return (
    <div className={`arch-box arch-box--${kind}`}>
      {title && <Rich className="arch-box__title" src={title} />}
      <span className="arch-box__body">
        {lines.map((line, i) => (
          <Fragment key={line}>
            {i > 0 && " "}
            <Rich className="arch-box__line" src={line} />
          </Fragment>
        ))}
      </span>
    </div>
  );
}

/**
 * A vertical archflow arrow with its archnote: a stem, the note on its own
 * clear band (lines never cross it), then the shaft and a Stealth head that
 * meets the target frame perpendicularly.
 */
export function Flow({ note }: { note: string[] }) {
  return (
    <div className="arch-flow">
      <span className="arch-flow__stem" />
      <span className="arch-flow__note">
        {note.map((line) => (
          <Rich key={line} className="arch-flow__line" src={line} />
        ))}
      </span>
      <span className="arch-flow__shaft" />
      <svg className="arch-flow__head" viewBox="0 0 10 10" aria-hidden="true" focusable="false">
        <path d="M0 0 L5 2.2 L10 0 L5 10 Z" />
      </svg>
    </div>
  );
}

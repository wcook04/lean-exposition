// "Why three papers need only one shared record" (architecture paper, Section 2).
// Adapted from its TikZ block: three dashed archview boxes at x = -4.7, 0, 4.7,
// each with an archflow arrow down to one archrecord box spanning the row.
// The arrows denote authored correspondence, so they carry the same note.
import { Box, Flow } from "./arch";
import "./figures.css";

const NOTE = ["maps its passages", "to recorded support"];

const PAPERS: { title: string; lines: string[] }[] = [
  { title: "Long record", lines: ["Recover the derivation", "and its separate cases"] },
  { title: "Short paper", lines: ["Read the result", "and decisive proof"] },
  { title: "Exposition", lines: ["Learn the objects", "and the proof idea"] },
];

const LABEL =
  "Three paper boxes, Long record, Short paper and Exposition, each with an arrow labelled " +
  "'maps its passages to recorded support' pointing down to a single box, the Shared record of the mathematics: " +
  "claims and assumptions, supporting arguments, source editions and checks.";

export function AccountsFigure() {
  return (
    <div className="fig arch arch--accounts" role="img" aria-label={LABEL}>
      <div className="arch-row arch-row--3">
        {PAPERS.map((p) => (
          <div className="arch-col" key={p.title}>
            <Box kind="view" title={p.title} lines={p.lines} />
            <Flow note={NOTE} />
          </div>
        ))}
      </div>
      <Box
        kind="record"
        title="Shared record of the mathematics"
        lines={["Claims and assumptions, supporting arguments, source editions and checks"]}
      />
    </div>
  );
}

export default AccountsFigure;

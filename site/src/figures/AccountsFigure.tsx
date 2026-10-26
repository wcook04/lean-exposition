// Figure fig:shared-claim (architecture paper, Section 2), retaining the
// existing three-account composition with its actual selected passage maps.
// Adapted from its TikZ block: three dashed archview boxes at x = -4.7, 0, 4.7,
// each with an archflow arrow down to one archrecord box spanning the row.
// The arrows denote authored correspondence, so they carry the same note.
import { Box, Flow } from "./arch";
import "./figures.css";

const NOTE = ["maps this passage", "to the claim"];

const PAPERS: { title: string; lines: string[] }[] = [
  { title: "Long record, §5", lines: ["The separate gap cases"] },
  { title: "Short paper, §1", lines: ["Theorem 1 and its scope"] },
  { title: "Exposition, §4", lines: ["The prepared theorem"] },
];

const LABEL =
  "The separate gap cases in long record section 5, Theorem 1 in short paper section 1, and the prepared theorem " +
  "in exposition section 4 each map to the same ordinary claim: no gaps for an admissible SK minimiser. " +
  "These authored passage mappings do not assert equivalent passages or automatic generation.";

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
        title="One selected claim in the shared record"
        lines={["No gaps for an admissible SK minimiser"]}
      />
    </div>
  );
}

export default AccountsFigure;

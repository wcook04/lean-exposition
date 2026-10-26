// Figure fig:excursion-return of the architectural companion. Adapts its
// two-expansion TikZ composition and the existing Accounts/GapIngredients
// HTML compositions. The short passage remains above two fuller treatments;
// the citation chain stacks below the claim so labels reflow on a phone.
// Arrow direction and direct mappings follow the manuscript's actual records.
import { Box, Flow } from "./arch";
import "./figures.css";

const LABEL =
  "Start and return at the integrated estimate in short paper section 3. Two long passages expand it: " +
  "sections 4.1 to 4.4 supply the finite-step calculation and integrated positivity; section 4.5 transfers " +
  "the estimate and proves strictness for the limit. Dashed expansion arrows point towards the short passage; " +
  "a reader follows them backwards. Only the short passage and the transfer passage map directly to the " +
  "strict-curvature claim. Dotted references lead from that claim to its citation and original Proposition 5.1. " +
  "These are reading and source relations, not proof edges.";

export function ReadingJourneyFigure() {
  return (
    <div className="fig arch arch--journey" role="img" aria-label={LABEL}>
      <div className="arch-journey__short" data-passage="short:curvature">
        <Box kind="record" title="Start and return: short §3" lines={["The integrated estimate"]} />
      </div>
      <div className="arch-journey__branches">
        <div className="arch-journey__expand-analytic" data-relation="expands" data-from="long:curvature" data-to="short:curvature">
          <Flow direction="up" line="dashed" note={["expands"]} />
        </div>
        <div className="arch-journey__expand-limit" data-relation="expands" data-from="long:fixed-time-coercivity" data-to="short:curvature">
          <Flow direction="up" line="dashed" note={["expands"]} />
        </div>
        <div className="arch-journey__analytic" data-passage="long:curvature">
          <Box kind="box" title="Long §§4.1–4.4" lines={["Finite-step calculation", "and integrated positivity"]} />
        </div>
        <div className="arch-journey__limit" data-passage="long:fixed-time-coercivity">
          <Box kind="box" title="Long §4.5" lines={["Transfer of the estimate", "and strictness for the limit"]} />
        </div>
        <div className="arch-journey__direct" data-relation="maps" data-from="short:curvature" data-to="support.positive_curvature">
          <Flow note={["maps", "to claim"]} />
        </div>
        <div className="arch-journey__limit-map" data-relation="maps" data-from="long:fixed-time-coercivity" data-to="support.positive_curvature">
          <Flow note={["maps to claim"]} />
        </div>
      </div>
      <Box kind="box" title="Strict curvature on a positive plateau" lines={["The claim used in the gap proof"]} />
      <div data-relation="citation_ids" data-from="support.positive_curvature" data-to="support_curvature_source">
        <Flow line="dotted" note={["citation reference"]} />
      </div>
      <div className="arch-journey__source">
        <Box kind="box" title="Original-proposition citation" lines={["The supplier of the estimate"]} />
      </div>
      <div data-relation="source_id" data-from="support_curvature_source" data-to="support_tex_curvature">
        <Flow line="dotted" note={["identifies the source"]} />
      </div>
      <div className="arch-journey__source">
        <Box kind="box" title="Original Proposition 5.1" lines={["The retained source edition"]} />
      </div>
    </div>
  );
}

export default ReadingJourneyFigure;

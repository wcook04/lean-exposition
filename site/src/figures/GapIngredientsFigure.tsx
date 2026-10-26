// "Which ingredients does the contradiction use?" (architecture paper, Section 3).
// Adapted from its TikZ block: an archrecord conclusion on top, two solid
// archbox ingredients at x = -3.55 and 3.55, each resting on a dashed
// archview premise. Arrows point from a conclusion to its inputs.
import { Box, Flow } from "./arch";
import "./figures.css";

const LABEL =
  "A dependency diagram. The conclusion 'A bounded positive gap is impossible' uses endpoint data from Endpoint contact " +
  "and the strict estimate from Strict curvature. Endpoint contact requires minimality and support endpoints; " +
  "strict curvature requires admissibility, a positive constant interval and the analytic regularity. " +
  "Both inputs concern the same moment curve q on the same closed interval.";

export function GapIngredientsFigure() {
  return (
    <div className="fig arch arch--ingredients" role="img" aria-label={LABEL}>
      <div className="arch-inset">
        <Box
          kind="record"
          title="A bounded positive gap is impossible"
          lines={["The required change in $q$ is $r-\\ell$; the integral of $q'$ is smaller."]}
        />
      </div>
      <Flow note={["Both inputs concern the same", "$q$ on $[\\ell,r]$."]} arrow={false} />
      <div className="arch-junction" aria-hidden="true" />
      <div className="arch-row arch-row--2">
        <div className="arch-col">
          <Flow note={["uses endpoint data"]} />
          <Box kind="box" title="Endpoint contact" lines={["$q(r)-q(\\ell)=r-\\ell$", "$q'(\\ell),q'(r)\\leq1$"]} />
          <Flow note={["requires"]} />
          <Box kind="view" lines={["Minimality and", "support endpoints"]} />
        </div>
        <div className="arch-col">
          <Flow note={["uses the strict estimate"]} />
          <Box
            kind="box"
            title="Strict curvature"
            lines={["$q'''(t)>0$ inside the interval,", "so $q'$ is strictly convex."]}
          />
          <Flow note={["requires"]} />
          <Box kind="view" lines={["Admissibility; a positive constant", "interval; analytic regularity"]} />
        </div>
      </div>
    </div>
  );
}

export default GapIngredientsFigure;

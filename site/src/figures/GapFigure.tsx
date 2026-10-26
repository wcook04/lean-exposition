// Figure "fig:support-increments" of the QAOA-SK exposition (Section 2).
// Adapted from the paper's TikZ block, coordinate for coordinate: x=1cm,
// y=.8cm, the lower plot shifted down by 3.45cm. Only the drawing is here;
// the page renders the paper's caption.
import { AxisTip, frame, Label } from "./tex";
import "./figures.css";

const F = frame(-1.0, 9.0, -4.05, 3.0);
const third = 2.666667;
const twoThirds = 5.333333;
/** Upper plot: TikZ y=.8cm. */
const ux = (x: number) => F.X(x);
const uy = (y: number) => F.Y(0.8 * y);
const uAt = (x: number, y: number) => F.at(x, 0.8 * y);
/** Lower plot: yshift=-3.45cm, then y=.8cm. */
const ly = (y: number) => F.Y(-3.45 + 0.8 * y);
const lAt = (x: number, y: number) => F.at(x, -3.45 + 0.8 * y);

const ticks: [number, string][] = [
  [third, "$1/3$"],
  [twoThirds, "$2/3$"],
  [8, "$1$"],
];

const LABEL =
  "Two plots of the example candidate gamma on [0, 1). Above, gamma rises linearly to 1/3 at t = 1/3, " +
  "stays flat at the positive value 1/3 until t = 2/3, then rises towards 2/3 at the excluded endpoint 1. " +
  "Below, the density of its measure is 1 outside the gap (1/3, 2/3) and 0 inside it: no mass there.";

function Axes({ y }: { y: (v: number) => number }) {
  return (
    <>
      <line className="fig-axis" x1={ux(-0.45)} y1={y(0)} x2={ux(8.5)} y2={y(0)} />
      <AxisTip x={ux(8.5)} y={y(0)} dir="right" />
      {ticks.map(([x]) => (
        <line key={x} className="fig-axis" x1={ux(x)} y1={y(0)} x2={ux(x)} y2={y(0) + 8} />
      ))}
    </>
  );
}

export function GapFigure() {
  return (
    <div className="fig fig-plot" role="img" aria-label={LABEL}>
      <svg viewBox={`0 0 ${F.W} ${F.H}`} aria-hidden="true" focusable="false">
        {/* Upper plot: the cumulative function gamma. */}
        <rect className="fig-subject" x={ux(third)} y={uy(2.9)} width={ux(twoThirds) - ux(third)} height={uy(0) - uy(2.9)} />
        <Axes y={uy} />
        <line className="fig-axis" x1={ux(0)} y1={uy(-0.05)} x2={ux(0)} y2={uy(3.15)} />
        <AxisTip x={ux(0)} y={uy(3.15)} dir="up" />
        <line className="fig-guide fig-guide--dashed" x1={ux(0)} y1={uy(1.333333)} x2={ux(twoThirds)} y2={uy(1.333333)} />
        <polyline
          className="fig-curve"
          points={[
            [0, 0],
            [third, 1.333333],
            [twoThirds, 1.333333],
            [8, 2.666667],
          ]
            .map(([x, y]) => `${ux(x)},${uy(y)}`)
            .join(" ")}
        />
        <circle className="fig-open" cx={ux(8)} cy={uy(2.666667)} r={5.5} />

        {/* Lower plot: the density of the measure. */}
        <rect className="fig-subject" x={ux(third)} y={ly(1.85)} width={ux(twoThirds) - ux(third)} height={ly(0) - ly(1.85)} />
        <rect className="fig-mass" x={ux(0)} y={ly(1.35)} width={ux(third) - ux(0)} height={ly(0) - ly(1.35)} />
        <rect className="fig-mass" x={ux(twoThirds)} y={ly(1.35)} width={ux(8) - ux(twoThirds)} height={ly(0) - ly(1.35)} />
        <Axes y={ly} />
        <line className="fig-axis" x1={ux(0)} y1={ly(-0.05)} x2={ux(0)} y2={ly(1.95)} />
        <AxisTip x={ux(0)} y={ly(1.95)} dir="up" />
        <line className="fig-guide fig-guide--dotted" x1={ux(third)} y1={ly(0)} x2={ux(third)} y2={ly(1.35)} />
        <line className="fig-guide fig-guide--dotted" x1={ux(twoThirds)} y1={ly(0)} x2={ux(twoThirds)} y2={ly(1.35)} />
        <line className="fig-curve" x1={ux(0)} y1={ly(1.35)} x2={ux(third)} y2={ly(1.35)} />
        <line className="fig-curve" x1={ux(third)} y1={ly(0)} x2={ux(twoThirds)} y2={ly(0)} />
        <line className="fig-curve" x1={ux(twoThirds)} y1={ly(1.35)} x2={ux(8)} y2={ly(1.35)} />
        <circle className="fig-open" cx={ux(8)} cy={ly(1.35)} r={5.5} />
      </svg>

      <Label at={uAt(8.5, 0)} anchor="right" src="$t$" />
      <Label at={uAt(0, 3.15)} anchor="above" src="$\gamma(t)$" />
      <Label at={uAt(0, 1.333333)} anchor="left" src="$1/3$" />
      <Label at={uAt(0, 2.666667)} anchor="left" src="$2/3$" />
      <Label at={uAt(4, 2.2)} className="fig-words" src="positive but flat" />
      <Label at={uAt(0, 0)} anchor="below-left" src="$0$" />
      {ticks.map(([x, s]) => (
        <Label key={`u${x}`} at={uAt(x, 0)} anchor="below" className="fig-tick" src={s} />
      ))}

      <Label at={lAt(8.5, 0)} anchor="right" src="$t$" />
      <Label at={lAt(0, 1.95)} anchor="above" className="fig-words" src="density of $\mu_\gamma$" />
      <Label at={lAt(0, 1.35)} anchor="left" src="$1$" />
      <Label at={lAt(4, 0.8)} className="fig-words" src="no mass here" />
      <Label at={lAt(0, 0)} anchor="below-left" src="$0$" />
      {ticks.map(([x, s]) => (
        <Label key={`l${x}`} at={lAt(x, 0)} anchor="below" className="fig-tick" src={s} />
      ))}
    </div>
  );
}

export default GapFigure;

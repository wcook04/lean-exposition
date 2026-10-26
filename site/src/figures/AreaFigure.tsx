// The "missing area" figure of the QAOA-SK exposition (Section 5.3).
// Adapted from the paper's TikZ block (x=1cm, y=1cm; height 3.1cm is the
// value one). The default view is the paper's picture: the Bezier curve
// (0,3.1) .. (2.667,2.067) and (5.333,2.067) .. (8,3.1) is exactly
// 1 - x(1 - x) with x = (t - r)/(s - r). An optional Explore mode varies the
// endpoint slopes and the strictness of the same calculus model.
import { useId, useState } from "react";
import { AxisTip, frame, Label, Rich } from "./tex";
import "./figures.css";

const ONE = 3.1; // TikZ height of the value one
const PAPER = frame(-2.55, 9.7, -0.7, 4.35);

/** Lowest value of the model on [r, s], sampled. */
function modelMin(m: Model): number {
  let lo = Infinity;
  for (let i = 0; i <= 96; i++) lo = Math.min(lo, modelValue(m, i / 96));
  return lo;
}

const PAPER_LABEL =
  "A plot of q'(t) between the gap endpoints r and s. Both endpoint values equal 1, so the endpoint chord is the " +
  "horizontal line at height 1; the strictly convex curve q' sags below it, and the shaded missing area between them is positive.";

export interface Model {
  /** q'(r), between 0 and 1. */
  a: number;
  /** q'(s), between 0 and 1. */
  b: number;
  /** Strictness: q' = chord - k * 4x(1 - x). */
  k: number;
}

export const PAPER_MODEL: Model = { a: 1, b: 1, k: 0.25 };

/** Model value of q' at x = (t - r)/(s - r). */
export function modelValue(m: Model, x: number): number {
  return (1 - x) * m.a + x * m.b - m.k * 4 * x * (1 - x);
}

/** Mean of q' over (r, s): the chord's mean minus k times the mean 2/3 of 4x(1 - x). */
export function modelMean(m: Model): number {
  return (m.a + m.b) / 2 - (2 * m.k) / 3;
}

function fmt(v: number): string {
  const r = Math.round(v * 1000) / 1000;
  if (Math.abs(r) < 0.0005) return "0";
  return r.toFixed(3).replace(/0+$/, "").replace(/\.$/, "");
}

function Art({ model, explore }: { model: Model; explore: boolean }) {
  // Explore keeps the paper's frame unless the curve dips below the axis.
  const F = explore ? frame(-2.55, 9.7, Math.min(-0.7, modelMin(model) * ONE - 0.7), 4.35) : PAPER;
  const { X, Y } = F;
  const v = (val: number) => Y(val * ONE);
  const t = (x: number) => X(8 * x);
  const isPaper = !explore;
  const chordIsOne = model.a === 1 && model.b === 1;

  // The curve: the paper's exact Bezier, or the model sampled finely.
  const curve = isPaper
    ? `M${X(0)} ${Y(ONE)} C${X(2.666667)} ${Y(2.066667)} ${X(5.333333)} ${Y(2.066667)} ${X(8)} ${Y(ONE)}`
    : Array.from({ length: 97 }, (_, i) => {
        const x = i / 96;
        return `${i === 0 ? "M" : "L"}${t(x).toFixed(2)} ${v(modelValue(model, x)).toFixed(2)}`;
      }).join(" ");
  // The shaded region: between the level one and q'.
  const shade = isPaper
    ? `M${X(0)} ${Y(ONE)} L${X(8)} ${Y(ONE)} C${X(5.333333)} ${Y(2.066667)} ${X(2.666667)} ${Y(2.066667)} ${X(0)} ${Y(ONE)} Z`
    : `M${X(0)} ${Y(ONE)} L${X(8)} ${Y(ONE)} ` +
      Array.from({ length: 97 }, (_, i) => {
        const x = 1 - i / 96;
        return `L${t(x).toFixed(2)} ${v(modelValue(model, x)).toFixed(2)}`;
      }).join(" ") +
      " Z";

  const mid = modelValue(model, 0.5);
  const chordMid = (model.a + model.b) / 2;
  // Put "missing area" in the widest clear band at the midpoint: between the
  // level one and the chord, or between the chord and the curve.
  const upper = (1 - chordMid) * ONE;
  const lower = (chordMid - mid) * ONE;
  const areaAt: number | null = isPaper
    ? 2.8
    : chordIsOne || lower >= upper
      ? lower >= 0.5 ? (chordMid + mid) / 2 * ONE : null
      : upper >= 0.5 ? (1 + chordMid) / 2 * ONE : null;
  const label = isPaper
    ? PAPER_LABEL
    : `Calculus model of q'(t) between r and s with q'(r) = ${fmt(model.a)}, q'(s) = ${fmt(model.b)} and strictness ${fmt(model.k)}. ` +
      `The shaded area between height 1 and the curve is ${fmt(1 - modelMean(model))} times s minus r.`;

  return (
    <div className={`fig fig-plot${explore ? " fig-plot--explore" : ""}`} role="img" aria-label={label}>
      <svg viewBox={`0 0 ${F.W} ${F.H}`} aria-hidden="true" focusable="false">
        <path className="fig-subject" d={shade} />
        <line className="fig-axis" x1={X(-1.9)} y1={Y(0)} x2={X(8.7)} y2={Y(0)} />
        <AxisTip x={X(8.7)} y={Y(0)} dir="right" />
        <line className="fig-axis" x1={X(-1.9)} y1={Y(0)} x2={X(-1.9)} y2={Y(3.8)} />
        <AxisTip x={X(-1.9)} y={Y(3.8)} dir="up" />
        <line className="fig-guide" x1={X(-1.9)} y1={Y(ONE)} x2={X(0)} y2={Y(ONE)} />
        {/* The endpoint chord (dashed, as in TikZ). Off the paper's case, the level one stays dashed too. */}
        {!chordIsOne && <line className="fig-guide fig-guide--dashed" x1={X(0)} y1={Y(ONE)} x2={X(8)} y2={Y(ONE)} />}
        <line
          className={chordIsOne ? "fig-guide fig-guide--dashed" : "fig-chord"}
          x1={X(0)}
          y1={v(model.a)}
          x2={X(8)}
          y2={v(model.b)}
        />
        <path className="fig-curve" d={curve} />
        <line className="fig-guide fig-guide--dotted" x1={X(0)} y1={Y(0)} x2={X(0)} y2={v(model.a)} />
        <line className="fig-guide fig-guide--dotted" x1={X(8)} y1={Y(0)} x2={X(8)} y2={v(model.b)} />
        <circle className="fig-dot" cx={X(0)} cy={v(model.a)} r={5.5} />
        <circle className="fig-dot" cx={X(8)} cy={v(model.b)} r={5.5} />
      </svg>

      <Label at={F.at(8.7, 0)} anchor="right" src="$t$" />
      <Label at={F.at(-1.9, 3.8)} anchor="above" src="$q'(t)$" />
      <Label at={F.at(-1.9, ONE)} anchor="left" src="$1$" />
      {chordIsOne && <Label at={F.at(4, ONE)} anchor="above" className="fig-words fig-masked" src="endpoint chord $=1$" />}
      <Label at={F.at(0, 0)} anchor="below" src="$r$" />
      <Label at={F.at(8, 0)} anchor="below" src="$s$" />
      {model.a === 1 && <Label at={F.at(0, ONE)} anchor="above-left" className="fig-endpoint" src="$q'(r)=1$" />}
      {model.b === 1 && <Label at={F.at(8, ONE)} anchor="above-right" className="fig-endpoint" src="$q'(s)=1$" />}
      {model.k > 0 ? (
        <Label at={F.at(4, isPaper ? 2.12 : mid * ONE - 0.205)} anchor="below" className="fig-words" src="strictly convex $q'$" />
      ) : (
        <Label at={F.at(4, mid * ONE - 0.205)} anchor="below" className="fig-words" src="affine $q'$, not strictly convex" />
      )}
      {areaAt !== null && <Label at={F.at(4, areaAt)} className="fig-words" src="missing area" />}
    </div>
  );
}

function Slider({
  label,
  value,
  min,
  max,
  onChange,
}: {
  label: string;
  value: number;
  min: number;
  max: number;
  onChange: (v: number) => void;
}) {
  const id = useId();
  return (
    <div className="fig-explore__control">
      <label htmlFor={id}>
        <Rich src={label} /> <output htmlFor={id}>{fmt(value)}</output>
      </label>
      <input
        id={id}
        type="range"
        min={min}
        max={max}
        step={0.01}
        value={value}
        onChange={(e) => onChange(Number(e.currentTarget.value))}
      />
    </div>
  );
}

/** The paper's picture, with an optional Explore mode below it. */
export function AreaFigure({ explorable = true, initialOpen = false }: { explorable?: boolean; initialOpen?: boolean }) {
  const [open, setOpen] = useState(initialOpen);
  const [model, setModel] = useState<Model>(PAPER_MODEL);
  const panelId = useId();
  if (!explorable) return <Art model={PAPER_MODEL} explore={false} />;

  const mean = modelMean(model);
  const shortfall = 1 - mean;
  const set = (patch: Partial<Model>) => setModel((m) => ({ ...m, ...patch }));

  return (
    <div className="fig-explorable">
      <Art model={open ? model : PAPER_MODEL} explore={open} />
      <div className="fig-explore__bar">
        <button
          type="button"
          className="control control--plain fig-explore__toggle"
          aria-expanded={open}
          aria-controls={panelId}
          onClick={() => setOpen((o) => !o)}
        >
          {open ? "Back to the paper’s picture" : "Explore this picture"}
        </button>
      </div>
      {open && (
        <div className="fig-explore" id={panelId}>
          <p className="fig-explore__note">
            <Rich src="Calculus model, not an SK moment curve: $q'(t)=\text{chord}(t)-k\cdot 4x(1-x)$ with $x=(t-r)/(s-r)$." />
          </p>
          <Slider label="Endpoint slope $q'(r)$" value={model.a} min={0} max={1} onChange={(a) => set({ a })} />
          <Slider label="Endpoint slope $q'(s)$" value={model.b} min={0} max={1} onChange={(b) => set({ b })} />
          <Slider label="Strictness $k$" value={model.k} min={0} max={0.5} onChange={(k) => set({ k })} />
          <p className="fig-explore__readout" aria-live="polite">
            <Rich src={`Mean of $q'$ on $(r,s)$: ${fmt(mean)}. Contact requires $1$; shortfall ${fmt(shortfall)}.`} />
            {shortfall < 0.0005 && " With no strictness and both slopes at 1, nothing is lost: strict curvature is what removes area."}
          </p>
          <button type="button" className="control" onClick={() => setModel(PAPER_MODEL)}>
            Reset to the paper’s values
          </button>
        </div>
      )}
    </div>
  );
}

export default AreaFigure;

/** One state of the picture, for previews and tests. */
export function AreaModelView({ model, explore = true }: { model: Model; explore?: boolean }) {
  return <Art model={model} explore={explore} />;
}

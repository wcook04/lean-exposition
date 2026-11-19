// What a Lean statement says against the paper, in words, with its note and who compared
// them; and who made a tie. Shown by Compare, the step view and the Lean panel a tick opens,
// only where the data carries the fields: an edition without them looks as before.

import type { FidelityFields, TieOrigin } from "../api/lean";
import { fidelitySentence, fidelitySourceWords, isFidelity, originWords } from "./fidelityWords";

export function FidelityLine({ row }: { row: FidelityFields | null | undefined }) {
  if (!row || !isFidelity(row.fidelity)) return null;
  return (
    <p className={`fidelity fidelity--${row.fidelity}`} data-fidelity={row.fidelity}>
      <strong className="fidelity__verdict">{fidelitySentence(row.fidelity)}</strong>
      {row.fidelity_note ? <> {row.fidelity_note}</> : null}{" "}
      <span className="fidelity__who" data-source={row.fidelity_source ?? "unrecorded"}>
        {fidelitySourceWords(row.fidelity_source)}
      </span>
    </p>
  );
}

export function OriginLine({ origin }: { origin: TieOrigin | null | undefined }) {
  const words = originWords(origin);
  if (!words) return null;
  return (
    <p className={`tie-origin tie-origin--${origin}`} data-origin={origin}>
      {words}
    </p>
  );
}

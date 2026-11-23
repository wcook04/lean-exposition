// What a Lean statement says against the paper, in words, with its note and who compared
// them; and who made a tie. Shown by Compare, the step view and the Lean panel a tick opens,
// only where the data carries the fields: an edition without them looks as before.

import type { FidelityFields, TieOrigin } from "../api/lean";
import type { ReactNode } from "react";
import site from "@instance/site";
import { noteHtml } from "../reader/math";
import { fidelitySentence, fidelitySourceWords, isFidelity, NOT_ASSESSED, NOT_ASSESSED_DETAIL, originWords } from "./fidelityWords";

export function FidelityLine({ row, renderNote }: { row: FidelityFields | null | undefined; renderNote?: (note: string) => ReactNode }) {
  if (!row?.fidelity) return null;
  // A comparison held back, or none recorded: said as such, never as a verdict.
  if (row.fidelity === "held") {
    return (
      <p className="fidelity fidelity--held" data-fidelity="held">
        <span dangerouslySetInnerHTML={{ __html: noteHtml(site.comparisonsHeld ?? row.fidelity_note ?? "This comparison is held.").html }} />
      </p>
    );
  }
  if (row.fidelity === "unassessed") {
    return (
      <p className="fidelity fidelity--unassessed" data-fidelity="unassessed">
        <strong className="fidelity__verdict">{NOT_ASSESSED}.</strong> {NOT_ASSESSED_DETAIL}
      </p>
    );
  }
  if (!isFidelity(row.fidelity)) return null;
  return (
    <p className={`fidelity fidelity--${row.fidelity}`} data-fidelity={row.fidelity}>
      <strong className="fidelity__verdict">{fidelitySentence(row.fidelity)}</strong>
      {row.fidelity_note && <> {renderNote ? renderNote(row.fidelity_note) : <span dangerouslySetInnerHTML={{ __html: noteHtml(row.fidelity_note).html }} />}</>}{" "}
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

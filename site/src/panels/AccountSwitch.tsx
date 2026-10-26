// The map bar's account switch: all accounts, or the records one account
// covers. Below it, one caption states the denominator and counts the three
// roles a record can have in that account, each with its shape (● ○ ⊟) and
// word; each count opens the list of its records.

import { useEffect, useMemo, useRef, useState } from "react";
import type { Stage } from "../api/types";
import { useEdition } from "../app/data";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { COVERAGE_WORDS, accountName, coverageOf, coverageScope, type Coverage } from "./model";
import "./panel.css";

interface Props {
  lens?: Stage;
  onLens(stage: Stage | undefined): void;
  /** Open a record from one of the role lists. */
  onSelect?(id: string): void;
}

const ROLES: { role: keyof Coverage; mark: string }[] = [
  { role: "own", mark: "own" },
  { role: "relied", mark: "relied" },
  { role: "out", mark: "outside" },
];

const LIST_TITLE: Record<keyof Coverage, (stage: Stage) => string> = {
  own: (s) => `Records with a passage of their own in ${accountName(s)}`,
  relied: (s) => `Records ${accountName(s)} uses without a passage of their own`,
  out: (s) => `Records ${accountName(s)} does not use`,
};

/** The accessible name of a count button: the whole sentence the short label abbreviates. */
const COUNT_SENTENCE: Record<keyof Coverage, (n: number, total: number, stage: Stage) => string> = {
  own: (n, total, s) => `${n} of the ${total} records have a passage of their own in ${accountName(s)}. Show their names`,
  relied: (n, total, s) => `${n} of the ${total} records are used by ${accountName(s)} without a passage of their own. Show their names`,
  out: (n, total, s) => `${n} of the ${total} records are not among the records ${accountName(s)} uses. Show their names`,
};

export function AccountSwitch({ lens, onLens, onSelect }: Props) {
  const edition = useEdition();
  const { graph } = edition;
  const [open, setOpen] = useState<keyof Coverage | null>(null);
  const popRef = useRef<HTMLDivElement>(null);
  const coverage = useMemo(() => (lens ? coverageOf(graph, lens) : null), [graph, lens]);
  const total = graph.order.length;

  useEffect(() => setOpen(null), [lens]);
  useEffect(() => {
    if (!open) return;
    const onDown = (event: PointerEvent) => {
      if (!popRef.current?.contains(event.target as Node)) setOpen(null);
    };
    const onKey = (event: KeyboardEvent) => {
      if (event.key === "Escape") {
        event.preventDefault();
        setOpen(null);
      }
    };
    document.addEventListener("pointerdown", onDown);
    document.addEventListener("keydown", onKey, true);
    return () => {
      document.removeEventListener("pointerdown", onDown);
      document.removeEventListener("keydown", onKey, true);
    };
  }, [open]);

  const options: (Stage | undefined)[] = [undefined, ...STAGE_ORDER];
  return (
    <div className="acct-switch">
      <div className="acct-switch__group" role="radiogroup" aria-label="Records used by">
        {options.map((s) => (
          <button key={s ?? "all"} type="button" role="radio" aria-checked={lens === s} className="acct-switch__item" onClick={() => onLens(s)}>
            {s ? PAPER_NAMES[s].short : "All accounts"}
          </button>
        ))}
      </div>
      {lens && coverage && (
        <div className="acct-switch__caption cov-line" ref={popRef}>
          <span className="cov-line__scope">{coverageScope(total)}:</span>
          {ROLES.map(({ role, mark }) => (
            <span key={role} className="cov-line__item">
              <button
                type="button"
                className="cov-line__count"
                aria-expanded={open === role}
                aria-label={COUNT_SENTENCE[role](coverage[role].length, total, lens)}
                onClick={() => setOpen(open === role ? null : role)}
              >
                <span className={`cov-mark cov-mark--${mark}`} aria-hidden="true" />
                <span className="num">{coverage[role].length}</span> {COVERAGE_WORDS[role]}
              </button>
            </span>
          ))}
          {open && (
            <div className="acct-switch__pop" role="dialog" aria-label={LIST_TITLE[open](lens)}>
              <p className="cov-line__title">{LIST_TITLE[open](lens)}</p>
              <ul>
                {coverage[open].map((id) => {
                  const n = graph.nodes.get(id)!;
                  return (
                    <li key={id}>
                      {onSelect ? (
                        <button
                          type="button"
                          className="linklike acct-switch__name"
                          onClick={() => {
                            setOpen(null);
                            onSelect(id);
                          }}
                        >
                          {n.label}
                        </button>
                      ) : (
                        <span className="acct-switch__name">{n.label}</span>
                      )}
                    </li>
                  );
                })}
              </ul>
            </div>
          )}
        </div>
      )}
    </div>
  );
}

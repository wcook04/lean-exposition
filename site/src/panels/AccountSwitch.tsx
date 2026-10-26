// The map bar's account switch: all records, or the records one account
// covers. Below it, one caption line counts how that account covers them,
// and "left out" opens the records outside it with the reason for each.

import { useEffect, useMemo, useRef, useState } from "react";
import type { Stage } from "../api/types";
import { useEdition } from "../app/data";
import { PAPER_NAMES, STAGE_ORDER } from "../app/papers";
import { accountName, coverageOf, unusedBy } from "./model";

interface Props {
  lens?: Stage;
  onLens(stage: Stage | undefined): void;
  /** Open a record from the "left out" list. */
  onSelect?(id: string): void;
}

export function AccountSwitch({ lens, onLens, onSelect }: Props) {
  const edition = useEdition();
  const { graph } = edition;
  const [open, setOpen] = useState(false);
  const popRef = useRef<HTMLDivElement>(null);
  const coverage = useMemo(() => (lens ? coverageOf(graph, lens) : null), [graph, lens]);
  const goals = edition.overview.papers.find((p) => p.stage === lens)?.paper_scope.selected_goal_ids ?? [];

  useEffect(() => setOpen(false), [lens]);
  useEffect(() => {
    if (!open) return;
    const onDown = (event: PointerEvent) => {
      if (!popRef.current?.contains(event.target as Node)) setOpen(false);
    };
    const onKey = (event: KeyboardEvent) => {
      if (event.key === "Escape") {
        event.preventDefault();
        setOpen(false);
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
      <div className="acct-switch__group" role="radiogroup" aria-label="Records shown">
        {options.map((s) => (
          <button
            key={s ?? "all"}
            type="button"
            role="radio"
            aria-checked={lens === s}
            className="acct-switch__item"
            onClick={() => onLens(s)}
          >
            {s ? PAPER_NAMES[s].short : "All records"}
          </button>
        ))}
      </div>
      {lens && coverage && (
        <div className="acct-switch__caption" ref={popRef}>
          <span>
            {PAPER_NAMES[lens].short}: <span className="num">{coverage.own.length}</span> with passages of their own ·{" "}
            <span className="num">{coverage.relied.length}</span> relied on ·{" "}
          </span>
          <button type="button" className="linklike" aria-expanded={open} onClick={() => setOpen((o) => !o)}>
            <span className="num">{coverage.out.length}</span> left out
          </button>
          {open && (
            <div className="acct-switch__pop" role="dialog" aria-label={`Records left out of ${accountName(lens)}`}>
              <ul>
                {coverage.out.map((id) => {
                  const n = graph.nodes.get(id)!;
                  return (
                    <li key={id}>
                      {onSelect ? (
                        <button
                          type="button"
                          className="linklike acct-switch__name"
                          onClick={() => {
                            setOpen(false);
                            onSelect(id);
                          }}
                        >
                          {n.label}
                        </button>
                      ) : (
                        <span className="acct-switch__name">{n.label}</span>
                      )}
                      <span className="acct-switch__why">
                        {unusedBy(graph, id, goals)
                          ? `No result ${accountName(lens)} proves uses it.`
                          : `Outside ${accountName(lens)}'s selection.`}
                      </span>
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

// "Passages linked to this one": where the passage being read is treated elsewhere, with
// the promise of each destination stated before it is chosen. Authored
// reading links come first, worded in their recorded direction ("Expanded
// by", "Illustrates"); passages that map one of the same claims follow,
// named by that claim; every account can also be read from its beginning.

import type { Stage } from "../../api/types";
import { routeHref } from "../../app/router";
import { PAPER_NAMES } from "../../app/papers";
import { sectionLabel } from "../../map/TheoremPlate";
import type { ArgGraph } from "../../model/graph";
import { Modal } from "./Modal";
import { placeName, sameTopic, sectionTitleIn, type Destination, type Structures } from "./model";

interface Props {
  here: { stage: Stage; anchor: string };
  structures: Structures;
  graph: ArgGraph;
  placement: "centre" | "sheet";
  beside(stage: Stage, anchor: string): string;
  onChoose(destination: Destination): void;
  onBegin(stage: Stage): void;
  onClose(): void;
}

export function Chooser({ here, structures, graph, placement, beside, onChoose, onBegin, onClose }: Props) {
  const groups = sameTopic(structures, here);
  const from = `${PAPER_NAMES[here.stage].short}, ${placeName(structures, here.stage, here.stage, here.anchor)}`;
  const plain = (e: React.MouseEvent) => e.button !== 0 || e.metaKey || e.ctrlKey || e.shiftKey || e.altKey;
  const row = (d: Destination) => {
    const title = sectionTitleIn(structures[d.stage], d.anchor);
    return (
      <li key={`${d.stage}:${d.anchor}`}>
        <a
          className="destination"
          href={beside(d.stage, d.anchor)}
          onClick={(event) => {
            if (plain(event)) return;
            event.preventDefault();
            onChoose(d);
          }}
        >
          {d.relation && <span className="caps destination__relation">{d.relation}</span>}
          <span className="destination__title">{title ? sectionLabel(title) : `The passage “${d.anchor.replace(/-/g, " ")}”`}</span>
          <span className="destination__account">
            {PAPER_NAMES[d.stage].short}
            {d.rationale && <span className="destination__why"> · {d.rationale}</span>}
          </span>
        </a>
      </li>
    );
  };
  return (
    <Modal title="Passages linked to this one" placement={placement} className="chooser" onClose={onClose}>
      <p className="chooser__from">From {from}</p>
      {groups.map((g) => {
        const empty = !g.authored.length && !g.shared.length;
        const own = g.stage === here.stage;
        return (
          <section key={g.stage} className="chooser__account" aria-labelledby={`chooser-${g.stage}`}>
            <header className="chooser__head">
              <h3 id={`chooser-${g.stage}`} className="chooser__name">
                {own ? "Elsewhere in this account" : PAPER_NAMES[g.stage].short}
              </h3>
              {!own && (
                <a
                  className="chooser__begin"
                  href={routeHref({ view: "read", stage: g.stage })}
                  onClick={(event) => {
                    if (plain(event)) return;
                    event.preventDefault();
                    onBegin(g.stage);
                  }}
                >
                  Read from the beginning
                </a>
              )}
            </header>
            {!g.ready && <p className="chooser__none faint">Loading the passages…</p>}
            {g.ready && empty && <p className="chooser__none">No passage in this account is linked to this one.</p>}
            {g.authored.length > 0 && <ul className="destinations">{g.authored.map(row)}</ul>}
            {g.shared.map((s) => (
              <div key={s.record} className="chooser__shared">
                <h4 className="chooser__via">
                  Passages also linked to <em>{graph.nodes.get(s.record)?.label ?? s.record}</em>
                </h4>
                <ul className="destinations">{s.places.map(row)}</ul>
              </div>
            ))}
          </section>
        );
      })}
    </Modal>
  );
}

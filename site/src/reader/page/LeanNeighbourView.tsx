// A declaration that is no step of the argument map, with its Lean neighbours, laid out to use
// the room it has: the declaration itself first, so it is always in view, then the declarations
// of the project it uses and those that use it, each group in as many rows and columns as the
// width allows. Every card carries its full plain title, wrapped, never cut, in the map's card
// styling. Past the height of the half, the view scrolls.

import { useLayoutEffect, useRef, useState } from "react";
import type { Neighbourhood } from "./leanNeighbours";

export function LeanNeighbourView({ hood, name, kicker = "This declaration", usesWord = "It uses", usersWord = "Used by", kind = "declaration", onPick }: { hood: Neighbourhood; name: string; kicker?: string; usesWord?: string; usersWord?: string; kind?: string; onPick?(id: string): void }) {
  const root = hood.graph.nodes.get(name)!;
  // A card the view cannot show whole is not shown in part: it is counted in "+N more" below.
  const box = useRef<HTMLDivElement>(null);
  const [cut, setCut] = useState(0);
  useLayoutEffect(() => {
    const view = box.current;
    if (!view) return;
    const mark = () => {
      const box = view.getBoundingClientRect();
      // Past the height, the foot of the view holds the "+N more" line: no card sits under it.
      const over = view.scrollHeight > view.clientHeight + 1;
      view.toggleAttribute("data-more", over);
      const edge = { top: box.top, bottom: box.bottom - (over ? 44 : 0) };
      let n = 0;
      for (const card of view.querySelectorAll<HTMLElement>(".nb-card:not(.nb-card--root)")) {
        const r = card.getBoundingClientRect();
        const off = r.bottom > edge.bottom + 0.5 || r.top < edge.top - 0.5;
        card.toggleAttribute("data-cut", off);
        if (off) n++;
      }
      setCut(n);
    };
    mark();
    const observer = typeof ResizeObserver !== "undefined" ? new ResizeObserver(mark) : null;
    observer?.observe(view);
    view.addEventListener("scroll", mark, { passive: true });
    return () => {
      observer?.disconnect();
      view.removeEventListener("scroll", mark);
    };
  }, [hood]);
  const plainOf = (id: string) => hood.graph.nodes.get(id)?.tilePlain !== false;
  const uses = (hood.graph.out.get(name) ?? []).map((edge) => ({ edge, node: hood.graph.nodes.get(edge.to)! }));
  return (
    <div ref={box} className="nb-view">
      <div className="nb-card nb-card--root" data-record={name} title={name}>
        <span className="nb-card__kicker">{kicker}</span>
        <span className="nb-card__title">{root.label}</span>
        {root.leanNote && <span className="nb-card__note">{root.leanNote}</span>}
      </div>
      <section className="nb-view__group" aria-label="Declarations of the project it uses">
        <h4 className="nb-view__label">{uses.length ? usesWord : kind === "step" ? "It uses no other step drawn here" : "It uses no other declaration of the project by name"}</h4>
        {uses.length > 0 && (
          <ul className="nb-view__cards">
            {uses.map(({ edge, node }) =>
              node.id.endsWith("#more") ? (
                <li key={node.id} className="nb-view__more">
                  {node.label}
                </li>
              ) : (
                <li key={node.id} className="nb-card" data-record={node.id} title={`${node.id}. ${edge.note}.`} onClick={onPick ? () => onPick(node.id) : undefined}>
                  <span className={`nb-card__title${plainOf(node.id) ? "" : " nb-card__title--name"}`}>{node.label}</span>
                  {kind === "declaration" && <span className="nb-card__note">{edge.kind === "lean_type_dependency" ? "In its statement" : "In its proof"}</span>}
                </li>
              ),
            )}
          </ul>
        )}
      </section>
      <section className="nb-view__group" aria-label="Declarations of the project that use it">
        <h4 className="nb-view__label">{hood.users.length ? usersWord : kind === "step" ? "No step drawn here uses it" : "No declaration of the project uses it by name"}</h4>
        {hood.users.length > 0 && (
          <ul className="nb-view__cards">
            {hood.users.map((user) => (
              <li key={user.name} className="nb-card" data-record={user.name} title={user.name} onClick={onPick ? () => onPick(user.name) : undefined}>
                <span className={`nb-card__title${user.plain ? "" : " nb-card__title--name"}`}>{user.title}</span>
              </li>
            ))}
            {hood.moreUsers > 0 && <li className="nb-view__more">and {hood.moreUsers} more</li>}
          </ul>
        )}
      </section>
      {cut > 0 && (
        <p className="nb-view__cut" aria-live="polite" style={{ position: "sticky", bottom: 8, marginTop: 8 }}>
          +{cut} more {cut === 1 ? "card" : "cards"}, scroll to see {cut === 1 ? "it" : "them"}
        </p>
      )}
    </div>
  );
}

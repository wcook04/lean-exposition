// A declaration that is no step of the argument map, with its Lean neighbours, laid out to use
// the room it has: the declaration itself first, so it is always in view, then the declarations
// of the project it uses and those that use it, each group in as many rows and columns as the
// width allows. Every card carries its full plain title, wrapped, never cut, in the map's card
// styling. Past the height of the half, the view scrolls.

import type { Neighbourhood } from "./leanNeighbours";

export function LeanNeighbourView({ hood, name }: { hood: Neighbourhood; name: string }) {
  const root = hood.graph.nodes.get(name)!;
  const uses = (hood.graph.out.get(name) ?? []).map((edge) => ({ edge, node: hood.graph.nodes.get(edge.to)! }));
  return (
    <div className="nb-view">
      <div className="nb-card nb-card--root" data-record={name} title={name}>
        <span className="nb-card__kicker">This declaration</span>
        <span className="nb-card__title">{root.label}</span>
        {root.leanNote && <span className="nb-card__note">{root.leanNote}</span>}
      </div>
      <section className="nb-view__group" aria-label="Declarations of the project it uses">
        <h4 className="nb-view__label">{uses.length ? "It uses" : "It uses no other declaration of the project by name"}</h4>
        {uses.length > 0 && (
          <ul className="nb-view__cards">
            {uses.map(({ edge, node }) =>
              node.id.endsWith("#more") ? (
                <li key={node.id} className="nb-view__more">
                  {node.label}
                </li>
              ) : (
                <li key={node.id} className="nb-card" data-record={node.id} title={`${node.id}. ${edge.note}.`}>
                  <span className="nb-card__title">{node.label}</span>
                  <span className="nb-card__note">{edge.kind === "lean_type_dependency" ? "In its statement" : "In its proof"}</span>
                </li>
              ),
            )}
          </ul>
        )}
      </section>
      <section className="nb-view__group" aria-label="Declarations of the project that use it">
        <h4 className="nb-view__label">{hood.users.length ? "Used by" : "No declaration of the project uses it by name"}</h4>
        {hood.users.length > 0 && (
          <ul className="nb-view__cards">
            {hood.users.map((user) => (
              <li key={user.name} className="nb-card" data-record={user.name} title={user.name}>
                <span className="nb-card__title">{user.title}</span>
              </li>
            ))}
            {hood.moreUsers > 0 && <li className="nb-view__more">and {hood.moreUsers} more</li>}
          </ul>
        )}
      </section>
    </div>
  );
}

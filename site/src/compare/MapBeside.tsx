// The argument map beside two papers: it follows the row under the reading line.

import { useEffect, useMemo, useRef, useState } from "react";
import { useEdition } from "../app/data";
import { navigate } from "../app/router";
import { ArgumentTree, type Insets, type MapViewHandle } from "../map/ArgumentTree";
import { StatementExcerpt, TheoremBody, mainGoal, startingGoals } from "../map/TheoremPlate";
import { chooseGoal, reach } from "../map/treeModel";

const INSETS: Insets = { top: 12, right: 12, bottom: 12, left: 12 };

export function MapBeside({ records }: { records: readonly string[] }) {
  const edition = useEdition();
  const { graph } = edition;
  const tree = useRef<MapViewHandle>(null);
  const main = useMemo(() => mainGoal(edition), [edition]);
  // The main result wins a tie, so the map changes argument only when the text does.
  const candidates = useMemo(() => startingGoals(edition).map((g) => ({ id: g.id, own: g.id === main })), [edition, main]);
  const [held, setHeld] = useState(main);
  const goal = useMemo(() => chooseGoal(records, candidates, (id) => reach(graph, id), held) ?? held, [records, candidates, graph, held]);
  if (goal !== held) setHeld(goal);
  const lit = useMemo(() => new Set(records), [records]);
  useEffect(() => {
    if (records.length) tree.current?.focusIds(records, { exclusive: true });
  }, [records, goal]);
  return (
    <ArgumentTree
      key={goal}
      ref={tree}
      graph={graph}
      goal={goal}
      insets={INSETS}
      compact
      persist={false}
      mode="steps"
      echo={lit}
      litIds={lit}
      rootContent={<TheoremBody goal={goal} />}
      rootExcerpt={<StatementExcerpt goal={goal} />}
      onSelect={(id) => id && navigate({ view: "compare", node: id })}
      onTrace={(id) => navigate({ view: "map", goal, node: id, trace: "rests" })}
    />
  );
}

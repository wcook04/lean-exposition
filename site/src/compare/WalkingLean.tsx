// The Lean of one step, where a name in the code walks in place. The cell shows the new
// declaration with a named way back, the page stays where it is, and the walk is kept with
// the history entry, so Back and Forward find the cell as it was left.

import type { ReactNode } from "react";
import type { AlignedLean } from "../api/lean";
import { useEntryState } from "../app/trail";
import { LazyLeanBlock } from "../lean/lazy";
import type { LeanWalk } from "../lean/walk";
import { useAlignment } from "./useAlignment";

interface Props {
  row: AlignedLean;
  /** Names this cell in the history entry's state. */
  place: string;
  bare?: boolean;
  foot?(here: { name: string; module: string }): ReactNode;
}

const NO_WALK: LeanWalk[] = [];
const lastName = (name: string) => name.slice(name.lastIndexOf(".") + 1);

export function WalkingLean({ row, place, bare, foot }: Props) {
  const [path, setPath] = useEntryState<LeanWalk[]>(`compare-walk:${place}`, NO_WALK);
  const alignment = useAlignment();
  const title = (name: string) => alignment?.names?.[name] ?? lastName(name);
  const here = path[path.length - 1];
  const before = path[path.length - 2]?.name ?? row.name;
  const walk = (next: LeanWalk) => setPath([...path, next]);
  return (
    <>
      {here && (
        <button type="button" className="walk-back" onClick={() => setPath(path.slice(0, -1))}>
          <span aria-hidden="true">← </span>Back to {title(before)}
        </button>
      )}
      {here ? (
        <LazyLeanBlock key={here.name} name={here.name} module={here.module} compact bare={bare} onName={walk} />
      ) : (
        <LazyLeanBlock name={row.name} module={row.module} relation={row.relation} note={row.note} clause={row.clause} lines={row.lines} quietLines compact bare={bare} onName={walk} />
      )}
      {foot?.(here ?? row)}
    </>
  );
}

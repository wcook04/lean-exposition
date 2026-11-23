// The topic colour of each record on the argument map, as the reader colours its phrases: the
// colours of one account (the lens if one is chosen, else the first account whose phrases carry
// topics), with that account's colour variables installed while the map is shown.

import { useEffect, useState } from "react";
import type { Stage } from "../api/types";
import type { PhraseTopic } from "../api/lean";
import { STAGE_ORDER } from "../app/papers";
import { loadTies, tieModel } from "../reader/ties";
import { paperPlaces } from "../reader/page/focusModel";
import { useTopicColours } from "../reader/topicColours";

interface Tones {
  of: Map<string, string>;
  topics?: readonly PhraseTopic[];
}

const cache = new Map<string, Promise<Tones | null>>();

function tonesFor(stage: Stage): Promise<Tones | null> {
  let p = cache.get(stage);
  if (!p) {
    p = loadTies(stage).then((index) => {
      if (!index?.topics?.length) return null;
      return { of: paperPlaces(tieModel(index)).recordTone, topics: index.topics };
    });
    cache.set(stage, p);
  }
  return p;
}

/** A record's topic colour (`var(--tone-N)`), or undefined; null until loaded. */
export function useRecordTones(lens: Stage | undefined): ((id: string) => string | undefined) | undefined {
  const [tones, setTones] = useState<Tones | null>(null);
  useEffect(() => {
    let live = true;
    (async () => {
      for (const stage of lens ? [lens] : STAGE_ORDER) {
        const t = await tonesFor(stage).catch(() => null);
        if (t) {
          if (live) setTones(t);
          return;
        }
      }
      if (live) setTones(null);
    })();
    return () => {
      live = false;
    };
  }, [lens]);
  useTopicColours(tones?.topics);
  const [of] = [tones?.of];
  return of ? (id: string) => of.get(id) : undefined;
}

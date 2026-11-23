// The topic colour of each record on the argument map, as the reader colours its phrases: the
// colours of one account (the lens if one is chosen, else the first account whose phrases carry
// topics), with that account's colour variables installed while the map is shown.

import { useEffect, useMemo, useState } from "react";
import type { Stage } from "../api/types";
import type { PhraseTopic } from "../api/lean";
import type { ArgGraph } from "../model/graph";
import { STAGE_ORDER } from "../app/papers";
import { loadTies, tieModel } from "../reader/ties";
import { paperPlaces } from "../reader/page/focusModel";
import { useTopicColours } from "../reader/topicColours";

interface Tones {
  of: Map<string, string>;
  topic: Map<string, string>;
  declTone: Map<string, string>;
  declTopic: Map<string, string>;
  topics?: readonly PhraseTopic[];
}

const cache = new Map<string, Promise<Tones | null>>();

function tonesFor(stage: Stage): Promise<Tones | null> {
  let p = cache.get(stage);
  if (!p) {
    p = loadTies(stage).then((index) => {
      if (!index?.topics?.length) return null;
      const places = paperPlaces(tieModel(index));
      return { of: places.recordTone, topic: places.recordTopic, declTone: places.declTone, declTopic: places.declTopic, topics: index.topics };
    });
    cache.set(stage, p);
  }
  return p;
}

type Lookup = ((id: string) => string | undefined) | undefined;

/** A record's topic colour (`var(--tone-N)`) and topic name; undefined until loaded. */
export function useRecordTones(lens: Stage | undefined, graph: ArgGraph): { toneOf: Lookup; topicOf: Lookup } {
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
  return useMemo(() => {
    if (!tones) return { toneOf: undefined, topicOf: undefined };
    const nameOf = (id: string) => graph.nodes.get(id)?.declaration ?? id;
    return {
      toneOf: (id: string) => tones.of.get(id) ?? tones.declTone.get(nameOf(id)),
      topicOf: (id: string) => tones.topic.get(id) ?? tones.declTopic.get(nameOf(id)),
    };
  }, [tones, graph]);
}

// The argument map beside the paper, on wide screens. It opens with every branch
// drawn: records this paper discusses at full strength, the rest faded. It follows
// what the reader is reading: as a passage settles under the reading line, the map
// frames that passage's records and outlines them in amber. The reader stays in
// charge: panning, zooming or unfolding pauses following, and choosing a card
// scrolls the text to the first passage linked to it, or, for a record this paper
// does not discuss, says which paper does.

import { useCallback, useEffect, useMemo, useRef, useState, type ReactNode } from "react";
import type { Stage } from "../../api/types";
import { useEdition } from "../../app/data";
import { navigate, routeHref } from "../../app/router";
import { PAPER_NAMES, STAGE_ORDER } from "../../app/papers";
import { ArgumentTree, type Insets, type MapViewHandle } from "../../map/ArgumentTree";
import { StatementExcerpt, TheoremBody, mainGoal, startingGoals } from "../../map/TheoremPlate";
import { chooseGoal, reach, scopedGraph } from "../../map/treeModel";
import { useReducedMotion } from "../../map/canvas/useReducedMotion";
import { firstPassageFor, type Structures } from "./model";
import "./map-pane.css";

/** The inspector's width when it slides in over the pane (--reader-inspector). */
const INSPECTOR_W = 336;
/** --t-state: the canvas crossfades when the main result changes. */
const CROSSFADE_MS = 160;

interface Props {
  stage: Stage;
  structures: Structures;
  /** The passage being followed (already settled under the reading line), or null before any. */
  anchor: string | null;
  /** Its directly linked records, as the inspector lists them. */
  records: readonly string[];
  /** The passage inspector, drawn over the right of the pane. */
  overlay?: ReactNode;
  inert?: boolean;
  onHide(): void;
  /** Scroll the text to this passage of the paper. */
  onJump(anchor: string): void;
}

export function MapPane({ stage, structures, anchor, records, overlay, inert, onHide, onJump }: Props) {
  const edition = useEdition();
  const { graph } = edition;
  const reduced = useReducedMotion();
  const treeRef = useRef<MapViewHandle>(null);

  // ---- Which main result -------------------------------------------------------------

  const candidates = useMemo(
    () => startingGoals(edition).map((g) => ({ id: g.id, title: g.title, own: g.stages.includes(stage) })),
    [edition, stage],
  );
  const reaches = useMemo(() => new Map<string, Set<string>>(), [graph]);
  // As the map draws it: the goal's scoped argument.
  const reachOf = useCallback(
    (goal: string) => {
      let r = reaches.get(goal);
      if (!r) {
        r = reach(scopedGraph(graph, goal), goal);
        reaches.set(goal, r);
      }
      return r;
    },
    [graph, reaches],
  );
  const [goal, setGoal] = useState(() => chooseGoal(records, candidates, reachOf, candidates.find((c) => c.own)?.id ?? mainGoal(edition)) ?? mainGoal(edition));
  const [fadeTo, setFadeTo] = useState<string | null>(null);
  const title = candidates.find((c) => c.id === goal)?.title ?? graph.nodes.get(goal)?.label ?? goal;

  // ---- Following ---------------------------------------------------------------------

  const [following, setFollowing] = useState(true);
  const [paused, setPaused] = useState(false);
  const [notice, setNotice] = useState<string | null>(null);
  const followingRef = useRef(following);
  followingRef.current = following;
  const recordsKey = records.join("|");
  const drawable = useMemo(() => records.filter((id) => reachOf(goal).has(id)), [records, reachOf, goal]);
  const litIds = useMemo(() => (drawable.length ? new Set(drawable) : null), [drawable]);
  // The records this paper links a passage to: everything else on the map is drawn faded.
  const coverage = useMemo(() => {
    const ids = new Set<string>();
    for (const p of structures[stage]?.paper.passages ?? []) for (const id of [...p.claim_ids, ...p.assumption_ids]) ids.add(id);
    return ids;
  }, [structures, stage]);
  const overlayOpen = !!overlay;
  const insets: Insets = useMemo(() => ({ top: 20, left: 20, bottom: 20, right: overlayOpen ? INSPECTOR_W + 20 : 20 }), [overlayOpen]);

  useEffect(() => setNotice(null), [anchor]);

  useEffect(() => {
    if (!following || !records.length || fadeTo) return;
    const want = chooseGoal(records, candidates, reachOf, goal);
    if (want && want !== goal) {
      // Another main result: a deliberate crossfade, never a jump mid-motion.
      setFadeTo(want);
      return;
    }
    treeRef.current?.focusIds(records);
    // Refocus when the passage, the main result or following changes (the map re-centres itself when its room changes).
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [recordsKey, goal, following, fadeTo]);

  useEffect(() => {
    if (!fadeTo) return;
    const t = window.setTimeout(
      () => {
        setGoal(fadeTo);
        setFadeTo(null);
      },
      reduced ? 0 : CROSSFADE_MS,
    );
    return () => window.clearTimeout(t);
  }, [fadeTo, reduced]);

  // Every branch is drawn from the start, so following only frames; it never folds.
  const recordsRef = useRef(records);
  recordsRef.current = records;
  useEffect(() => {
    const open = window.setTimeout(() => treeRef.current?.expandAll(), 0);
    // Then frame the passage being read, once the whole map is laid out.
    const frame = window.setTimeout(() => {
      if (followingRef.current && recordsRef.current.length) treeRef.current?.focusIds(recordsRef.current);
    }, 80);
    return () => {
      window.clearTimeout(open);
      window.clearTimeout(frame);
    };
  }, [goal]);

  const onUserMove = useCallback(() => {
    if (!followingRef.current) return;
    followingRef.current = false;
    setFollowing(false);
    setPaused(true);
  }, []);

  const toggleFollowing = () => {
    setPaused(false);
    setFollowing((v) => !v);
  };

  // ---- Back into the text ------------------------------------------------------------

  const onSelect = useCallback(
    (id: string | null) => {
      if (!id) return;
      const at = firstPassageFor(structures[stage], [id]);
      if (at) {
        setNotice(null);
        onJump(at);
      } else setNotice(id);
    },
    [structures, stage, onJump],
  );

  const mapHref = routeHref({ view: "map", goal, node: drawable[0] });
  const noticeLabel = notice ? (graph.nodes.get(notice)?.label ?? notice) : "";
  // Where a record this paper does not discuss is read instead.
  const elsewhere = notice
    ? STAGE_ORDER.filter((s) => s !== stage)
        .map((s) => ({ stage: s, anchor: firstPassageFor(structures[s], [notice]) }))
        .filter((r): r is { stage: Stage; anchor: string } => !!r.anchor)
    : [];

  return (
    <section className="map-pane" aria-label="Argument map beside the text" inert={inert ? true : undefined}>
      <header className="map-pane__head">
        <span className="caps map-pane__kind">Argument map</span>
        <span className="map-pane__goal" title={title}>
          {title}
        </span>
        <span className="map-pane__state" role="status">
          {paused && !following ? "Paused while you move the map" : anchor && !records.length ? "No record is linked to this passage." : ""}
        </span>
        <button type="button" className="map-pane__follow" aria-pressed={following} onClick={toggleFollowing}>
          <span className="map-pane__dot" aria-hidden="true" />
          Follow the text
        </button>
        <a className="map-pane__open" href={mapHref} onClick={(event) => {
          if (event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
          event.preventDefault();
          navigate({ view: "map", goal, node: drawable[0] });
        }}>
          Open the full map
        </a>
        <button type="button" className="map-pane__hide" aria-label="Hide the map beside the text" onClick={onHide}>
          <svg viewBox="0 0 12 12" width="12" height="12" aria-hidden="true">
            <path d="M2.5 2.5l7 7M9.5 2.5l-7 7" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" />
          </svg>
        </button>
      </header>
      <div className="map-pane__body">
      <p className="map-pane__legend">
        <span className="map-pane__swatch map-pane__swatch--lit" aria-hidden="true" />
        In the passage you are reading
        <span className="map-pane__swatch map-pane__swatch--faded" aria-hidden="true" />
        Not discussed in the {PAPER_NAMES[stage].short.toLowerCase()}
      </p>
      {notice && (
        <p className="map-pane__notice" role="status">
          <span>
            <strong>{noticeLabel}</strong>: this paper does not discuss it.
          </span>
          {elsewhere.map((r) => (
            <a key={r.stage} href={routeHref({ view: "read", stage: r.stage, anchor: r.anchor })}>
              Read it in the {PAPER_NAMES[r.stage].short.toLowerCase()}
            </a>
          ))}
          <a href={routeHref({ view: "map", goal, node: notice })}>Open it in the full map</a>
          <button type="button" className="map-pane__dismiss" aria-label="Dismiss" onClick={() => setNotice(null)}>
            ×
          </button>
        </p>
      )}
      <div className={`map-pane__canvas${fadeTo ? " is-fading" : ""}`}>
        <ArgumentTree
          key={goal}
          ref={treeRef}
          graph={graph}
          goal={goal}
          insets={insets}
          persist={false}
          mode="steps"
          litIds={litIds}
          coverage={coverage}
          rootContent={<TheoremBody goal={goal} />}
          rootExcerpt={<StatementExcerpt goal={goal} />}
          onSelect={onSelect}
          onTrace={(id) => navigate({ view: "map", goal, node: id, trace: "rests" })}
          onUserMove={onUserMove}
        />
      </div>
      {overlay}
      </div>
    </section>
  );
}

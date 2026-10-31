// A step from one Lean name to another, and the page that can show it in place. This
// file holds no Lean code, so any page can import it without loading the viewer.

export interface LeanWalk {
  /** Full declaration name. */
  name: string;
  module: string;
  /** The name after its namespaces. */
  short: string;
  /** The declaration the step was taken from, for "Back to it"; absent from search. */
  from?: string;
}

type Host = (walk: LeanWalk) => boolean | void;

let host: Host | null = null;

/**
 * A page that shows Lean beside what it is reading says so here. While it is registered, a
 * Lean result from search opens there, and the reader stays where they are.
 */
export function hostLean(show: Host): () => void {
  host = show;
  return () => {
    if (host === show) host = null;
  };
}

/** Show a declaration in the registered host. False when there is none or it declined. */
export function showInHost(walk: LeanWalk): boolean {
  return host ? host(walk) !== false : false;
}

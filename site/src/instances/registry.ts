// Every instance the build can select, by its LX_INSTANCE value. vite.config.ts and the
// build-time fact reader use this; browser code reads only the selected one, through the
// alias "@instance/site". No browser API and no import.meta.

import erdos257 from "./erdos257/site.ts";
import qaoaSk from "./qaoa-sk/site.ts";
import type { SiteInstance } from "./types.ts";

export const INSTANCES: Record<string, SiteInstance> = { "qaoa-sk": qaoaSk, erdos257 };

export const DEFAULT_INSTANCE = "qaoa-sk";

/** The instance LX_INSTANCE names (default qaoa-sk); an unknown name stops the build with the list of known ones. */
export function selectInstance(name: string | undefined = process.env.LX_INSTANCE): SiteInstance {
  const id = name || DEFAULT_INSTANCE;
  const site = INSTANCES[id];
  if (!site) throw new Error(`LX_INSTANCE=${id} is not an instance of this site. Known: ${Object.keys(INSTANCES).join(", ")}.`);
  return site;
}

/** Every slot of an instance's copy, by its dotted name, whose text still holds "TODO(copy)". */
export function copyTodos(value: unknown, at = ""): string[] {
  if (typeof value === "string") return value.includes("TODO(copy)") ? [at] : [];
  if (Array.isArray(value)) return value.flatMap((item, i) => copyTodos(item, `${at}.${i}`));
  if (value && typeof value === "object") return Object.entries(value).flatMap(([key, item]) => copyTodos(item, at ? `${at}.${key}` : key));
  return [];
}

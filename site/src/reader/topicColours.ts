// The stored topic colours of a paper as CSS: `--tone-N` on the root in each theme, and
// `[data-tone="N"]` setting `--tone` for the phrase, card, key and graph card that carry it.
// The colours come computed with the ties (site/scripts/topic-colours.ts, colours-<paper>.json);
// nothing is computed here.

import { useEffect } from "react";
import type { PhraseTopic } from "../api/lean";

const STYLE_ID = "topic-colours";
const LOCAL_REFERENCE = '.annotation-paper-reference:not([target="_blank"])';

/** The CSS for one paper's topics; empty when they carry no stored colours. */
export function topicColourCss(topics: readonly PhraseTopic[] | undefined): string {
  const coloured = (topics ?? []).filter((topic) => topic.light && topic.dark);
  if (!coloured.length) return "";
  const vars = (theme: "light" | "dark") => coloured.map((topic) => `--tone-${topic.tone}: ${topic[theme]};`).join(" ");
  const preview = (pointerHover: boolean) => coloured.map(({ tone }) => {
    const colour = `[data-tone="${tone}"]`;
    const reference = LOCAL_REFERENCE + colour;
    const source = pointerHover
      ? `:is(:has(${reference}:hover), :has(${reference}:focus-visible):not(:has(${LOCAL_REFERENCE}:hover)))`
      : `:has(${reference}:focus-visible)`;
    return `.reader${source} :is(.paper .tie, .pdf-view__mark)${colour} { --reference-preview-fill: 21%; --reference-preview-line: 55%; }`;
  }).join("\n");
  return [
    `:root { ${vars("light")} }`,
    `:root[data-theme="dark"] { ${vars("dark")} }`,
    `@media (prefers-color-scheme: dark) { :root:not([data-theme="light"]) { ${vars("dark")} } }`,
    ...coloured.map((topic) => `[data-tone="${topic.tone}"] { --tone: var(--tone-${topic.tone}); }`),
    `@media (hover: hover) { ${preview(true)} }`,
    `@media (hover: none) { ${preview(false)} }`,
  ].join("\n");
}

/** Install the paper's topic colours while it is read. */
export function useTopicColours(topics: readonly PhraseTopic[] | undefined): void {
  const css = topicColourCss(topics);
  useEffect(() => {
    if (typeof document === "undefined") return;
    let el = document.getElementById(STYLE_ID) as HTMLStyleElement | null;
    if (!css) {
      el?.remove();
      return;
    }
    if (!el) {
      el = document.createElement("style");
      el.id = STYLE_ID;
      document.head.appendChild(el);
    }
    if (el.textContent !== css) el.textContent = css;
  }, [css]);
}

// The site's keys, in one list, for the About page and the `?` key.

export const SITE_KEYS: readonly { keys: readonly string[]; does: string }[] = [
  { keys: ["j", "k"], does: "Next or previous statement in a paper, next or previous step in Compare" },
  { keys: ["Enter"], does: "Open the statement under the highlighter, with its Lean" },
  { keys: ["Escape"], does: "Let go of a pinned statement, or close what is open" },
  { keys: ["["], does: "Back, the same as the browser’s Back button" },
  { keys: ["/"], does: "Search the papers, the steps and the Lean" },
  { keys: ["?"], does: "Show this list" },
];

// The site's keys, in one list, for the About page and the `?` key.

export const SITE_KEYS: readonly { keys: readonly string[]; does: string }[] = [
  { keys: ["j", "k"], does: "Next or previous statement in a paper, next or previous step in Compare" },
  { keys: ["↑", "↓"], does: "On a statement, the same as j and k" },
  { keys: ["Enter"], does: "Open the statement, with its Lean" },
  { keys: ["g"], does: "In a paper, switch the right pane between Graph and Lean" },
  { keys: ["Escape"], does: "Close what is open: an opened statement, then the Lean" },
  { keys: ["["], does: "Back, the same as the browser’s Back button" },
  { keys: ["/"], does: "Search the papers, the steps and the Lean" },
  { keys: ["?"], does: "Show this list" },
];

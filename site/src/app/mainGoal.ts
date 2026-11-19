// The site's main result: the instance's own choice when the graph has it, else the first
// goal the long record names, else the graph's first. The SK site names the long record's
// first goal, so its choice is unchanged; the #257 site names Theorem A.1.

import site from "@instance/site";

export function mainGoalOf(longGoals: readonly string[] | undefined, goals: readonly string[], has: (id: string) => boolean): string | undefined {
  if (site.mainGoal && has(site.mainGoal)) return site.mainGoal;
  return (longGoals ?? goals).find(has);
}

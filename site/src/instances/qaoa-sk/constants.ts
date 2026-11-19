// The SK site's names and ids, kept apart from the rest of its instance so the first screen
// (hero.ts) and the instance object (site.ts) can both use them. No browser API and no
// import.meta: vite.config.ts reads this too.

/** This website's name, as the family registry gives it (family.json: "SK Reader", once "Lean Exposition"). */
export const SITE_NAME = "SK Reader";

export const EDITION_TITLE = "Why the Sherrington–Kirkpatrick order parameter has no gaps";

/** The step recording that no Lean theorem connects OpenAI's two models. */
export const MODELS_STEP = "scalar.formal_model_transport_open";

export const LINK_CAVEAT = "An AI agent read each statement and its Lean and linked them. No independent mathematician has reviewed these links, and no program tests whether the two say the same thing.";

/** The short video of this website first and largest, then the two about the mathematics. */
export const FILMS: { id: string; kicker: string }[] = [
  { id: "short-sk-website", kicker: "This website in use" },
  { id: "sk-no-gap", kicker: "The result explained" },
  { id: "short-sk-no-gap", kicker: "The result in brief" },
];

export const SITE_URL = "https://wcook04.github.io/lean-exposition-site/";

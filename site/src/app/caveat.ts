// Who linked a paper to the Lean, said one way everywhere, and the step recording a known gap
// in the Lean where the instance has one. Both are the selected instance's (src/instances/).
import site from "@instance/site";

/** The step recording that no Lean theorem connects two Lean models (SK); empty where there is none. */
export const MODELS_STEP = site.modelsStep ?? "";

export const LINK_CAVEAT = site.linkCaveat;

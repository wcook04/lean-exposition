// Each instance's browser modules, checked against the one interface the shared code uses
// (types.ui.ts) and its site object against SiteInstance. Nothing imports this file; the
// type checker reads it, so `npm run typecheck` checks every instance whichever one is selected.

import type { SiteInstance } from "./types";
import type { AboutPageComponent, ChecksIntroComponent, ChecksNoteComponent, FigureForKey, FrontPageComponent, LeanLandingComponent } from "./types.ui";
import skSite from "./qaoa-sk/site";
import * as skFront from "./qaoa-sk/FrontPage";
import * as skAbout from "./qaoa-sk/AboutPage";
import * as skLean from "./qaoa-sk/LeanLanding";
import * as skChecks from "./qaoa-sk/ChecksIntro";
import * as skFigures from "./qaoa-sk/figures";
import erdosSite from "./erdos257/site";
import * as erdosFront from "./erdos257/FrontPage";
import * as erdosAbout from "./erdos257/AboutPage";
import * as erdosLean from "./erdos257/LeanLanding";
import * as erdosChecks from "./erdos257/ChecksIntro";
import * as erdosFigures from "./erdos257/figures";

interface InstanceModules {
  site: SiteInstance;
  FrontPage: FrontPageComponent;
  AboutPage: AboutPageComponent;
  LeanLanding: LeanLandingComponent;
  ChecksIntro: ChecksIntroComponent;
  ChecksNote: ChecksNoteComponent;
  figureForKey: FigureForKey;
}

export const CONFORMS: Record<string, InstanceModules> = {
  "qaoa-sk": { site: skSite, ...skFront, ...skAbout, ...skLean, ...skChecks, ...skFigures },
  erdos257: { site: erdosSite, ...erdosFront, ...erdosAbout, ...erdosLean, ...erdosChecks, ...erdosFigures },
};

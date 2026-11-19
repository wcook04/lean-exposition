// The selected instance's modules. vite.config.ts points "@instance/" at
// src/instances/<LX_INSTANCE>/; for the type checker every instance exports the same names
// with these types, and src/instances/conformance.ts checks each one against them.

declare module "@instance/site" {
  const site: import("./types.ts").SiteInstance;
  export default site;
}

declare module "@instance/FrontPage" {
  export const FrontPage: import("./types.ui.ts").FrontPageComponent;
}

declare module "@instance/AboutPage" {
  export const AboutPage: import("./types.ui.ts").AboutPageComponent;
}

declare module "@instance/LeanLanding" {
  export const LeanLanding: import("./types.ui.ts").LeanLandingComponent;
}

declare module "@instance/ChecksIntro" {
  export const ChecksIntro: import("./types.ui.ts").ChecksIntroComponent;
  export const ChecksNote: import("./types.ui.ts").ChecksNoteComponent;
}

declare module "@instance/figures" {
  export const figureForKey: import("./types.ui.ts").FigureForKey;
}

declare module "@instance/theme" {}

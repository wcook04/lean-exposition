// The browser half of an instance: the pages and parts whose wording or structure is the
// example's own. Each instance folder has FrontPage.tsx, AboutPage.tsx, LeanLanding.tsx,
// ChecksIntro.tsx and figures.ts exporting these names (conformance.ts checks them).

import type { ComponentType, ReactNode } from "react";
import type { Route } from "../app/router";
import type { EvidenceCard, KindGroup } from "../checks/summary";
import type { LeanShell } from "../lean/data";

export type FrontPageComponent = () => ReactNode;
export type AboutPageComponent = (props: { route: Extract<Route, { view: "about" }> }) => ReactNode;
export type LeanLandingComponent = (props: { shell: LeanShell; slot: HTMLElement | null }) => ReactNode;
/** The first screen of What ran, above the table by kind: terms and what ran. */
export type ChecksIntroComponent = (props: { groups: KindGroup[] }) => ReactNode;
/** A note under the table by kind, about a published observation; null for none. */
export type ChecksNoteComponent = (props: { cards: readonly EvidenceCard[] }) => ReactNode;
/** A figure slot's component, by the figure's key and caption; null leaves the slot to a plain image or empty. */
export type FigureForKey = (key: string, caption: string) => ComponentType | null;

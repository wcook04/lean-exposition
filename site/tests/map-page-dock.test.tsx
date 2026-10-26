// The dock's links keep the browser's own meaning for modified clicks, and each
// passage has a real name.
import { describe, expect, it, vi } from "vitest";

vi.mock("../src/app/data", () => ({ useEdition: () => ({}), useRecord: () => ({ status: "loading" }) }));
vi.mock("../src/map/TheoremPlate", () => ({
  sectionLabel: (t: string) => {
    const m = t.match(/^(\d+(?:\.\d+)*)\.?\s+(.*)$/);
    return m ? `§${m[1]} ${m[2]}` : t;
  },
}));

import { isPlainClick, passageName } from "../src/ribbons/ReadingsDock";
import type { StripPassage } from "../src/ribbons/useReadings";

const click = { button: 0, metaKey: false, ctrlKey: false, shiftKey: false, altKey: false };

describe("dock links", () => {
  it("only intercepts a plain primary click", () => {
    expect(isPlainClick(click)).toBe(true);
    expect(isPlainClick({ ...click, metaKey: true })).toBe(false);
    expect(isPlainClick({ ...click, ctrlKey: true })).toBe(false);
    expect(isPlainClick({ ...click, shiftKey: true })).toBe(false);
    expect(isPlainClick({ ...click, button: 1 })).toBe(false);
  });

  it("names a passage by account, section and claim count", () => {
    const p = { stage: "expository", anchor: "contact", section: "4.2 Contact", claims: ["a", "b"] } as unknown as StripPassage;
    expect(passageName(p)).toBe("Exposition §4.2 Contact, linked to 2 records");
    expect(passageName({ ...p, claims: [] })).toBe("Exposition §4.2 Contact, linked to no record");
  });
});

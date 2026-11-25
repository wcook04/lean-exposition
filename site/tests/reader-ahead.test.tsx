// Between links the pane previews the link Next lands on, or the last one above, as following and not selected.
import { act } from "react";
import { createRoot, type Root } from "react-dom/client";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { SubjectBand } from "../src/reader/page/SubjectBand";

(globalThis as { IS_REACT_ACT_ENVIRONMENT?: boolean }).IS_REACT_ACT_ENVIRONMENT = true;

let container: HTMLDivElement;
let root: Root;
beforeEach(() => {
  container = document.createElement("div");
  document.body.append(container);
  root = createRoot(container);
});
afterEach(() => {
  act(() => root.unmount());
  container.remove();
});

describe("the band between links", () => {
  const side = (name: string) => [...container.querySelectorAll<HTMLButtonElement>(".mode-switch__side")].find((b) => b.textContent === name)!;

  it("names the next link and where it is, still in Auto", () => {
    act(() => root.render(<SubjectBand state="next" place="§3" onManual={() => undefined} />));
    expect(container.querySelector(".subject-band")!.getAttribute("data-state")).toBe("next");
    expect(container.querySelector(".subject-band__words")!.textContent).toBe("Next link");
    expect(container.querySelector(".subject-band__state")!.textContent).toContain("In §3, below");
    expect(side("Auto select").getAttribute("aria-pressed")).toBe("true");
  });

  it("says when nothing follows and the link shown is above", () => {
    act(() => root.render(<SubjectBand state="last" place="§9" />));
    expect(container.querySelector(".subject-band__words")!.textContent).toBe("Last link");
    expect(container.querySelector(".subject-band__state")!.textContent).toContain("No link below");
    expect(container.querySelector(".subject-band__state")!.textContent).toContain("above");
    expect(side("Auto select").getAttribute("aria-pressed")).toBe("true");
  });
});

// A library paper's front matter (the account line above its title) says each sentence once: the
// credit line and the review must not both say that the links were made with AI. Checked on every
// library paper's own instance.json.
import { readdirSync, readFileSync } from "node:fs";
import { resolve } from "node:path";
import { describe, expect, it } from "vitest";
import { creditWithoutReview } from "../src/instances/library/site";

const INSTANCES = resolve(__dirname, "../../instances");
const sentences = (text: string) => text.split(/(?<=[.!?])\s+(?=[A-Z])/).map((t) => t.trim()).filter(Boolean);

describe("front matter", () => {
  for (const id of readdirSync(INSTANCES)) {
    const inst = JSON.parse(readFileSync(resolve(INSTANCES, id, "instance.json"), "utf8"));
    it(`${id}: no sentence twice, one AI sentence, then "No mathematician has reviewed them."`, () => {
      const said = sentences(`${creditWithoutReview(inst.credit_lines ?? [], inst.review ?? "")} ${inst.review ?? ""}`);
      expect(said.length).toBe(new Set(said).size);
      const ai = said.filter((t) => /\bwith AI\b/i.test(t));
      expect(ai).toHaveLength(1);
      if (said.includes("No mathematician has reviewed them.")) expect(said[said.indexOf(ai[0]) + 1]).toBe("No mathematician has reviewed them.");
    });
  }

  it("drops the credit line's own AI sentence and keeps the rest", () => {
    const credit = ["Paper and Lean by A and B. The links from sentences to the Lean were made with AI and have not been reviewed by the authors. Our files are MIT-licensed"];
    const review = "The links from the text to the Lean were made with AI and have not been reviewed by the authors. No mathematician has reviewed them.";
    expect(creditWithoutReview(credit, review)).toBe("Paper and Lean by A and B. Our files are MIT-licensed.");
  });
});

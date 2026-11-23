// Compute colours for a reference-only paper using the normal reader palette.
import { readFileSync } from "node:fs";
import { palette, relatedness, type FamilyIn, type PhraseIn, type TopicIn } from "../site/src/reader/palette.ts";

const input = JSON.parse(readFileSync(0, "utf8")) as {
  families: FamilyIn[];
  topics: TopicIn[];
  phrases: PhraseIn[];
};
const result = palette({
  families: input.families,
  topics: input.topics,
  related: relatedness(input.topics.map((topic) => topic.id), input.phrases),
});
process.stdout.write(JSON.stringify(result));

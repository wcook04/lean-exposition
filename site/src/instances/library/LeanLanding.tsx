// The Lean index landing of a library paper: the shared reading guide and the folders.
import type { LeanShell } from "../../lean/data";
import { Folders, HowToRead } from "../../lean/LeanPage";
import { PAPER } from "./data";

export function LeanLanding({ shell }: { shell: LeanShell; slot: HTMLElement | null }) {
  return (
    <>
      <p className="lean-landing__lead">The Lean of {PAPER.title}, by {PAPER.authors.join(", ")}, as their repository has it.</p>
      <HowToRead />
      <Folders shell={shell} />
    </>
  );
}

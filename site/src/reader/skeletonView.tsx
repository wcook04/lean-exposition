// The shape of a paper, for React to show until the text is ready: the same markup the
// paper's HTML opened with, so handing over moves nothing.

import { useEffect } from "react";
import { openedFirstScreen, readerSkeletonHtml } from "./skeleton";

let opened = openedFirstScreen(document);
const openedAt = window.location.pathname;

export function ReaderSkeleton({ words }: { words?: string }) {
  const here = opened && window.location.pathname === openedAt ? opened : null;
  return <div style={{ display: "contents" }} dangerouslySetInnerHTML={{ __html: here ?? readerSkeletonHtml(words) }} />;
}

/** The page has taken over from the first screen, which from now on could only be out of place. */
export function useFirstScreenDone(): void {
  useEffect(() => {
    opened = null;
  }, []);
}

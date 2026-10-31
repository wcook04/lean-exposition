// The shape of a paper, for React to show until the text is ready: the same markup the
// paper's HTML opened with, so handing over moves nothing.

import { readerSkeletonHtml } from "./skeleton";

export function ReaderSkeleton({ words }: { words?: string }) {
  return <div style={{ display: "contents" }} dangerouslySetInnerHTML={{ __html: readerSkeletonHtml(words) }} />;
}

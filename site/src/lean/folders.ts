// One plain sentence on each folder of the instance's Lean source (SK: written from reading
// the module names and the theorems inside each folder at the pinned revision).
import site from "@instance/site";

export const FOLDER_WORDS: Record<string, string> = site.lean.folderWords;

/** The folder's name for a reader: its path below the instance's prefix (SK: `OAI/Probability`). */
export const folderLabel = (path: string) => (site.lean.folderPrefix && path.startsWith(site.lean.folderPrefix) ? path.slice(site.lean.folderPrefix.length) : path);

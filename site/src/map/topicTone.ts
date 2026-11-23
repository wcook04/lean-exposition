/** The topic number in a tone written as `var(--tone-N)`, for the reader's topic key (data-topic-tone). */
export function toneNumber(tone: string | undefined | null): string | undefined {
  return tone ? /--tone-([^)\s]+)/.exec(tone)?.[1] : undefined;
}

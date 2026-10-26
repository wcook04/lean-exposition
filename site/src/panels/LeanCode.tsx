// A recorded Lean statement in mono with light syntax colouring.

import { useMemo } from "react";
import { formatLeanSignature, tokenizeLean } from "./leanTokens";

export function LeanCode({ source }: { source: string }) {
  const tokens = useMemo(() => tokenizeLean(formatLeanSignature(source)), [source]);
  return (
    <pre className="panel__lean">
      <code className="lean">
        {tokens.map((t, i) =>
          t.kind === "space" || t.kind === "punct" ? (
            t.text
          ) : (
            <span key={i} className={`lk lk--${t.kind}`}>
              {t.text}
            </span>
          ),
        )}
      </code>
    </pre>
  );
}

// A recorded Lean statement in mono, coloured by the reading tokenizer.

import { useMemo } from "react";
import "../lean/lean.css";
import { tokenize } from "../lean/tokenize";
import { formatLeanSignature } from "./leanTokens";

export function LeanCode({ source }: { source: string }) {
  const tokens = useMemo(() => tokenize(formatLeanSignature(source)), [source]);
  return (
    <pre className="panel__lean">
      <code className="lean">
        {tokens.map((t, i) =>
          t.kind === "space" ? (
            t.text
          ) : (
            <span key={i} className={`lean-t lean-t--${t.kind}`}>
              {t.text}
            </span>
          ),
        )}
      </code>
    </pre>
  );
}

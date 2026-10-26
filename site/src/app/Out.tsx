// A link that leaves the site: it opens in a new tab and carries a small arrow (app.css, a.out).

import type { ReactNode } from "react";

export function Out({ href, children }: { href: string; children: ReactNode }) {
  return (
    <a className="out" href={href} target="_blank" rel="noopener noreferrer">
      {children}
    </a>
  );
}

// The quiet "Elsewhere" block of the front page and About: the problem, the Lean on GitHub,
// each paper's PDF and TeX source, the Maths Map and the overview page (elsewhereLinks.ts).

import { Out } from "../../app/Out";
import { ELSEWHERE } from "./elsewhereLinks";

export function Elsewhere({ id, className = "" }: { id: string; className?: string }) {
  return (
    <section className={`elsewhere ${className}`} aria-labelledby={id}>
      <h2 id={id} className="elsewhere__title">
        Elsewhere
      </h2>
      <dl className="elsewhere__list">
        {ELSEWHERE.map((row) => (
          <div key={row.label} className="elsewhere__row">
            <dt>{row.label}</dt>
            <dd>
              {row.links.map((link, i) => (
                <span key={link.href}>
                  {i > 0 && <span aria-hidden="true"> · </span>}
                  <Out href={link.href}>{link.label}</Out>
                </span>
              ))}
            </dd>
          </div>
        ))}
      </dl>
    </section>
  );
}

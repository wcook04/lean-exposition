// The footer's list of Will Cook's websites, the same on every site of the family
// (docs/family.md): each site by its short name in the registry's order, this one
// marked as the current page rather than removed, then the home page.

import { FAMILY, THIS_SITE_ID } from "./family";

export function SisterSites({ className }: { className?: string }) {
  return (
    <nav className={className ? `fam-sites ${className}` : "fam-sites"} aria-label={`${FAMILY.owner.name}'s websites`}>
      <p className="fam-sites__title">More from {FAMILY.owner.name}</p>
      <ul className="fam-sites__list">
        {FAMILY.sites.map((site) => (
          <li key={site.id}>
            <a href={site.url} aria-current={site.id === THIS_SITE_ID ? "page" : undefined}>
              {site.short}
            </a>
          </li>
        ))}
        <li>
          <a href={FAMILY.owner.home}>All websites and films</a>
        </li>
      </ul>
    </nav>
  );
}

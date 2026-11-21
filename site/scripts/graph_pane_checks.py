"""Browser checks every reader's graph pane must pass (docs/graph-pane.md).

The same file is kept in the Quartic Reader, lean-exposition and Proof Reader. A reader's own
script drives its pages (which paper, which phrase, which card) and calls `check_graph_pane`
in each state, and `check_groups` where the drawing has groups; each returns the list of
failures, empty when the pane is right.

    from graph_pane_checks import check_graph_pane, check_groups
    failures += check_graph_pane(page, "short paper, phrase 5 clicked", dock=".graph-dock")
"""
from __future__ import annotations

from playwright.sync_api import Page

MEASURE = r"""
(dockSel) => {
  const fg = document.querySelector('.fg');
  if (!fg) return {error: 'no focus graph (.fg) on the page'};
  const sc = fg.querySelector('.fg__scroll');
  const world = fg.querySelector('.fg__world');
  const view = sc.getBoundingClientRect();
  const zoom = parseFloat(getComputedStyle(world).zoom) || 1;
  const out = {subjects: 0, nodes: 0, groups: 0, grouped: 0, small: [], cut: [], blank: [], outside: [],
               users: +fg.dataset.users, uses: +fg.dataset.uses, opened: +fg.dataset.opened,
               lines: fg.querySelectorAll('.fg__lines path[data-edge]').length, tops: 0,
               extraX: sc.scrollWidth - sc.clientWidth, extraY: sc.scrollHeight - sc.clientHeight,
               view: [Math.round(view.width), Math.round(view.height)], none: !!fg.querySelector('.fg__none')};
  const inside = (r) => r.top >= view.top - 1 && r.bottom <= view.bottom + 1 && r.left >= view.left - 1 && r.right <= view.right + 1;
  const text = (el, id) => {
    const cs = getComputedStyle(el);
    const size = parseFloat(cs.fontSize) * zoom;
    if (size < 13) out.small.push(`${id} (${size.toFixed(1)}px)`);
    if (!el.innerText.trim()) out.blank.push(id);
    if (el.scrollWidth > el.clientWidth + 1 || el.scrollHeight > el.clientHeight + 1 || cs.textOverflow === 'ellipsis' || (cs.webkitLineClamp && cs.webkitLineClamp !== 'none')) out.cut.push(id);
  };
  for (const c of fg.querySelectorAll('.fg__card')) {
    const id = c.dataset.card;
    text(c.querySelector('.fg__title'), id);
    if (c.dataset.band === 'subject') out.subjects += 1; else out.nodes += 1;
    if (!inside(c.getBoundingClientRect())) out.outside.push(id);
  }
  // Every neighbour is a node on show or is counted by exactly one outermost group.
  for (const side of fg.querySelectorAll('.fg__side')) {
    for (const el of side.children) {
      if (el.matches('.fg__card')) out.tops += 1;
      if (el.matches('.fg__group')) { out.tops += 1; out.grouped += +el.querySelector(':scope > .fg__grouphead').dataset.count; }
    }
    out.loose = (out.loose || 0) + side.querySelectorAll(':scope > .fg__card').length;
  }
  for (const g of fg.querySelectorAll('.fg__grouphead')) {
    out.groups += 1;
    text(g.querySelector('.fg__groupname'), 'group ' + g.dataset.group);
    if (!inside(g.getBoundingClientRect())) out.outside.push('group ' + g.dataset.group);
  }
  const dock = dockSel ? document.querySelector(dockSel) : null;
  out.dock = dockSel ? (dock ? dock.innerText.replace(/\s+/g, ' ').trim().length : -1) : null;
  return out;
}
"""


def check_graph_pane(page: Page, label: str, dock: str | None = None, expect_subject: bool = True) -> list[str]:
    """The rules of docs/graph-pane.md that a browser can check, as the pane opens on a subject (no group opened by hand)."""
    m = page.evaluate(MEASURE, dock)
    if m.get("error"):
        return [f"{label}: {m['error']}"]
    bad: list[str] = []
    if expect_subject and not m["subjects"]:
        bad.append(f"{label}: no subject card is drawn")
    if m["small"]:
        bad.append(f"{label}: titles under 13px: {', '.join(m['small'][:5])}")
    if m["cut"]:
        bad.append(f"{label}: titles cut: {', '.join(m['cut'][:5])}")
    if m["blank"]:
        bad.append(f"{label}: nodes with no title: {', '.join(m['blank'][:5])}")
    if not m["opened"]:
        if m["extraY"] > 4 or m["extraX"] > 4:
            bad.append(f"{label}: the drawing does not fit its area on opening (over by {max(0, m['extraX'])}px across, {max(0, m['extraY'])}px down)")
        if m["outside"]:
            bad.append(f"{label}: not wholly in view on opening: {', '.join(m['outside'][:5])}")
        if m.get("loose", 0) + m["grouped"] != m["users"] + m["uses"]:
            bad.append(f"{label}: {m['users'] + m['uses']} neighbours, but the nodes and group counts on show come to {m.get('loose', 0) + m['grouped']}")
    if m["lines"] < m["tops"]:
        bad.append(f"{label}: {m['tops']} nodes and groups but only {m['lines']} lines")
    if m["view"][1] < 180:
        bad.append(f"{label}: the graph area is only {m['view'][1]}px tall")
    if dock is not None and (m["dock"] is None or m["dock"] < 20):
        bad.append(f"{label}: the part under the graph is empty")
    if not bad:
        print(f"ok  {label}: {m['subjects']} subject, {m['users']} users and {m['uses']} uses as {m['nodes']} nodes and {m['groups']} groups, {m['lines']} lines, graph {m['view'][0]}x{m['view'][1]}")
    return bad


def check_groups(page: Page, label: str) -> list[str]:
    """A group opens in place into all its members, the drawing then scrolls if it must, and Fit folds it back."""
    heads = page.locator(".fg__side > .fg__group > .fg__grouphead")
    if heads.count() == 0:
        return []
    bad: list[str] = []
    # The largest group is the hardest case.
    counts = heads.evaluate_all("(els) => els.map((e) => +e.dataset.count)")
    head = heads.nth(counts.index(max(counts)))
    name = head.get_attribute("data-group")
    head.click()
    page.wait_for_timeout(400)
    group = page.locator(".fg__side > .fg__group.is-open").first
    if group.count() == 0:
        return [f"{label}: clicking the group {name} did not open it"]
    inside = group.evaluate("(g) => [...g.querySelectorAll('.fg__members .fg__card')].length + [...g.querySelectorAll('.fg__members .fg__grouphead')].reduce((n, h) => n + (h.getAttribute('aria-expanded') === 'true' ? 0 : +h.dataset.count), 0)")
    if inside != max(counts):
        bad.append(f"{label}: the group {name} counts {max(counts)} but opens into {inside}")
    sc = page.locator(".fg__scroll")
    extra = sc.evaluate("(el) => el.scrollHeight - el.clientHeight")
    if extra > 4:
        before = sc.evaluate("(el) => el.scrollTop")
        box = sc.bounding_box()
        page.mouse.move(box["x"] + box["width"] / 2, box["y"] + box["height"] / 2)
        page.mouse.wheel(0, 240 if before < extra / 2 else -240)
        page.wait_for_timeout(200)
        if sc.evaluate("(el) => el.scrollTop") == before:
            bad.append(f"{label}: with the group {name} open the graph does not scroll under the wheel")
        if page.locator(".fg__mini").count() == 0 and page.viewport_size["width"] > 600:
            bad.append(f"{label}: the drawing overflows but there is no overview")
        hidden = page.evaluate(
            """() => { const sc = document.querySelector('.fg__scroll'); const v = sc.getBoundingClientRect(); const out = [];
            for (const c of sc.querySelectorAll('.fg__card')) { let r = c.getBoundingClientRect(); if (r.top < v.top) sc.scrollTop += r.top - v.top - 4; else if (r.bottom > v.bottom) sc.scrollTop += r.bottom - v.bottom + 4; if (r.left < v.left) sc.scrollLeft += r.left - v.left - 4; else if (r.right > v.right) sc.scrollLeft += r.right - v.right + 4; r = c.getBoundingClientRect();
              if (r.height <= v.height && (r.top < v.top - 1 || r.bottom > v.bottom + 1 || r.left < v.left - 1 || r.right > v.right + 1)) out.push(c.dataset.card); }
            return out; }"""
        )
        if hidden:
            bad.append(f"{label}: cards that scrolling cannot bring wholly into view: {', '.join(hidden[:5])}")
    page.locator(".fg__tools button", has_text="Fit").click()
    page.wait_for_timeout(400)
    if page.locator(".fg__group.is-open").count():
        bad.append(f"{label}: Fit did not fold the opened group")
    if not bad:
        print(f"ok  {label}: the group {name} opens into its {max(counts)}, scrolls {max(0, extra)}px, and Fit folds it")
    return bad

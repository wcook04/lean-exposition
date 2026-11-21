"""Browser checks every reader's graph pane must pass (docs/graph-pane.md).

The same file is kept in the Quartic Reader, lean-exposition and Proof Reader. A reader's own
script drives its pages (which paper, which phrase, which card) and calls `check_graph_pane`
in each state; it returns the list of failures, empty when the pane is right.

    from graph_pane_checks import check_graph_pane, dogfood_scroll
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
  const cards = [...fg.querySelectorAll('.fg__card')];
  const out = {cards: cards.length, subjects: 0, small: [], cut: [], unreachable: [], blankTitle: [], subjectHidden: [],
               lines: fg.querySelectorAll('.fg__lines path[data-edge]').length, neighbours: 0,
               overflowX: world.getBoundingClientRect().width - sc.clientWidth,
               scrollable: sc.scrollHeight - sc.clientHeight, view: [Math.round(view.width), Math.round(view.height)],
               none: !!fg.querySelector('.fg__none')};
  const w = world.getBoundingClientRect();
  for (const c of cards) {
    const id = c.dataset.card;
    const title = c.querySelector('.fg__title');
    const size = parseFloat(getComputedStyle(title).fontSize) * (parseFloat(getComputedStyle(world).zoom) || 1);
    if (size < 13) out.small.push(`${id} (${size.toFixed(1)}px)`);
    if (!title.innerText.trim()) out.blankTitle.push(id);
    const cs = getComputedStyle(title);
    if (title.scrollWidth > title.clientWidth + 1 || title.scrollHeight > title.clientHeight + 1 || cs.textOverflow === 'ellipsis' || cs.webkitLineClamp !== 'none') out.cut.push(id);
    const r = c.getBoundingClientRect();
    if (r.left < w.left - 1 || r.right > w.right + 1 || r.top < w.top - 1 || r.bottom > w.bottom + 1) out.unreachable.push(id);
    if (r.width > view.width) out.unreachable.push(id + ' (wider than the pane)');
    if (c.dataset.band === 'subject') {
      out.subjects += 1;
      // Several subjects in a frame taller than the area: the frame starts in view, so its first rank must be.
      const frame = c.closest('.fg__subjects');
      const firstRank = !frame || frame.getBoundingClientRect().height <= view.height - 8 || c.parentElement === frame.querySelector('.fg__rank');
      const fits = firstRank && r.height <= view.height - 8;
      if (fits && (r.top < view.top - 1 || r.bottom > view.bottom + 1 || r.left < view.left - 1 || r.right > view.right + 1)) out.subjectHidden.push(id);
    } else out.neighbours += 1;
  }
  const dock = dockSel ? document.querySelector(dockSel) : null;
  out.dock = dockSel ? (dock ? dock.innerText.replace(/\s+/g, ' ').trim().length : -1) : null;
  out.dockHeight = dock ? Math.round(dock.getBoundingClientRect().height) : null;
  return out;
}
"""


def check_graph_pane(page: Page, label: str, dock: str | None = None, expect_subject: bool = True) -> list[str]:
    """The rules of docs/graph-pane.md that a browser can check, in the pane's present state."""
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
    if m["blankTitle"]:
        bad.append(f"{label}: cards with no title: {', '.join(m['blankTitle'][:5])}")
    if m["unreachable"]:
        bad.append(f"{label}: cards outside the scrollable drawing: {', '.join(m['unreachable'][:5])}")
    if m["subjectHidden"]:
        bad.append(f"{label}: the subject is not wholly in view at rest: {', '.join(m['subjectHidden'][:5])}")
    if m["neighbours"] and m["lines"] < m["neighbours"]:
        bad.append(f"{label}: {m['neighbours']} neighbours but only {m['lines']} lines")
    if m["overflowX"] > 2:
        bad.append(f"{label}: the drawing is {m['overflowX']:.0f}px wider than the pane at rest")
    if m["view"][1] < 180:
        bad.append(f"{label}: the graph area is only {m['view'][1]}px tall")
    if dock is not None and (m["dock"] is None or m["dock"] < 20):
        bad.append(f"{label}: the part under the graph is empty")
    if not bad:
        print(f"ok  {label}: {m['subjects']} subject, {m['neighbours']} neighbours, {m['lines']} lines, graph {m['view'][0]}x{m['view'][1]}, scrolls {max(0, m['scrollable'])}px")
    return bad


def check_scrolls(page: Page, label: str) -> list[str]:
    """A drawing taller than its pane moves under the wheel, shows its overview, and every card can be brought into view."""
    sc = page.locator(".fg__scroll")
    extra = sc.evaluate("(el) => el.scrollHeight - el.clientHeight")
    if extra <= 4:
        return []
    bad: list[str] = []
    before = sc.evaluate("(el) => el.scrollTop")
    box = sc.bounding_box()
    page.mouse.move(box["x"] + box["width"] / 2, box["y"] + box["height"] / 2)
    page.mouse.wheel(0, 240 if before < extra / 2 else -240)
    page.wait_for_timeout(200)
    if sc.evaluate("(el) => el.scrollTop") == before:
        bad.append(f"{label}: the graph does not scroll under the wheel")
    if page.locator(".fg__mini").count() == 0:
        bad.append(f"{label}: the drawing overflows but there is no overview")
    hidden = page.evaluate(
        """() => { const sc = document.querySelector('.fg__scroll'); const v = sc.getBoundingClientRect(); const out = [];
        for (const c of sc.querySelectorAll('.fg__card')) { c.scrollIntoView({block: 'nearest', inline: 'nearest'}); const r = c.getBoundingClientRect();
          if (r.height <= v.height && (r.top < v.top - 1 || r.bottom > v.bottom + 1 || r.left < v.left - 1 || r.right > v.right + 1)) out.push(c.dataset.card); }
        return out; }"""
    )
    if hidden:
        bad.append(f"{label}: cards that scrolling cannot bring wholly into view: {', '.join(hidden[:5])}")
    page.locator(".fg__tools button", has_text="Centre").click()
    page.wait_for_timeout(200)
    if not bad:
        print(f"ok  {label}: scrolls {extra}px, overview shown, every card reachable")
    return bad

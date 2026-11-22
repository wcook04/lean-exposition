"""Browser checks every reader's graph pane must pass (docs/graph-pane.md).

The same file is kept in the Quartic Reader, lean-exposition and Proof Reader. A reader's own
script drives its pages (which paper, which phrase, which card) and calls `check_graph_pane`
in each state, and `check_groups` where the drawing has groups; each returns the list of
failures, empty when the pane is right. `check_groups` leaves the pane as it found it: the
list of a large group closed, a small group folded again.

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
  // The camera's scale: the drawing is moved and zoomed by a transform on the world.
  const t = getComputedStyle(world).transform;
  const zoom = t && t !== 'none' ? new DOMMatrixReadOnly(t).a : 1;
  const drawing = world.getBoundingClientRect();
  const out = {subjects: 0, nodes: 0, groups: 0, grouped: 0, small: [], cut: [], blank: [], outside: [],
               users: +fg.dataset.users, uses: +fg.dataset.uses, opened: +fg.dataset.opened,
               lines: fg.querySelectorAll('.fg__lines path[data-edge]').length, tops: 0,
               extraX: Math.round(Math.max(0, view.left - drawing.left, drawing.right - view.right)),
               extraY: Math.round(Math.max(0, view.top - drawing.top, drawing.bottom - view.bottom)),
               bars: sc.offsetWidth - sc.clientWidth + sc.offsetHeight - sc.clientHeight,
               view: [Math.round(view.width), Math.round(view.height)], none: !!fg.querySelector('.fg__none')};
  const inside = (r) => r.top >= view.top - 1 && r.bottom <= view.bottom + 1 && r.left >= view.left - 1 && r.right <= view.right + 1;
  const text = (el, id) => {
    const cs = getComputedStyle(el);
    const size = parseFloat(cs.fontSize) * zoom;
    if (size < 11) out.small.push(`${id} (${size.toFixed(1)}px)`);
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
        bad.append(f"{label}: titles under 11px at the fitted zoom: {', '.join(m['small'][:5])}")
    if m["bars"]:
        bad.append(f"{label}: the graph's area shows scroll bars")
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


LIST_ABOVE = 8

SUBJECT_BOX = "() => { const c = document.querySelector('.fg .fg__card[data-band=subject]'); if (!c) return null; const r = c.getBoundingClientRect(); return [r.left, r.top, r.width, r.height]; }"


def _moved(a: list[float] | None, b: list[float] | None) -> float:
    if a is None or b is None:
        return 0.0 if a == b else float("inf")
    return max(abs(x - y) for x, y in zip(a, b))


def _fit(page: Page) -> None:
    page.locator(".fg__tools button", has_text="Fit").click()
    page.wait_for_timeout(500)


def check_groups(page: Page, label: str) -> list[str]:
    """The largest group opens all its members: a group of more than eight as a list beside the drawing that
    leaves the drawing still, a smaller one in place. Fit only moves the camera and folds or closes nothing."""
    heads = page.locator(".fg__side > .fg__group > .fg__grouphead")
    if heads.count() == 0:
        return []
    # The largest group is the hardest case.
    counts = heads.evaluate_all("(els) => els.map((e) => +e.dataset.count)")
    count = max(counts)
    head = heads.nth(counts.index(count))
    name = head.get_attribute("data-group")
    if count > LIST_ABOVE:
        return _check_list(page, label, head, name, count)
    return _check_in_place(page, label, head, name, count)


def _check_list(page: Page, label: str, head, name: str, count: int) -> list[str]:
    bad: list[str] = []
    before = page.evaluate(SUBJECT_BOX)
    opened_before = page.evaluate("() => document.querySelector('.fg').dataset.opened")
    head.click()
    page.wait_for_timeout(400)
    panel = page.locator(".fg__list")
    if panel.count() == 0:
        return [f"{label}: clicking the group {name} of {count} did not list its members"]
    if head.get_attribute("aria-expanded") != "true":
        bad.append(f"{label}: the group {name} is listed but its button does not say it is expanded")
    if page.evaluate("() => document.querySelector('.fg').dataset.opened") != opened_before:
        bad.append(f"{label}: listing the group {name} opened groups in the drawing")
    moved = _moved(before, page.evaluate(SUBJECT_BOX))
    if moved > 1:
        bad.append(f"{label}: listing the group {name} moved the subject by {moved:.1f}px")
    status = page.locator(".fg__liststatus").inner_text().strip()
    total = status.split(" of ")[-1].split(" ")[0] if " of " in status else ""
    if total != str(count):
        bad.append(f"{label}: the group {name} counts {count} but its list says \"{status}\"")
    # Every member is reached by paging, and each is listed whole.
    seen: list[str] = []
    for _ in range(count + 1):
        seen += page.locator(".fg__list .fg__member").evaluate_all("(els) => els.map((e) => e.dataset.card)")
        cut = page.locator(".fg__list .fg__membertitle").evaluate_all(
            "(els) => els.filter((e) => { const cs = getComputedStyle(e); return e.scrollWidth > e.clientWidth + 1 || cs.textOverflow === 'ellipsis' || (cs.webkitLineClamp && cs.webkitLineClamp !== 'none') || parseFloat(cs.fontSize) < 13; }).length"
        )
        if cut:
            bad.append(f"{label}: {cut} member titles of {name} are cut or under 13px")
        nxt = page.locator(".fg__listpages button", has_text="Next")
        if nxt.is_disabled():
            break
        nxt.click()
        page.wait_for_timeout(80)
    if len(seen) != count or len(set(seen)) != count:
        bad.append(f"{label}: paging through {name} reaches {len(set(seen))} members of {count} ({len(seen)} rows)")
    # A search for the first member's first word finds at least that member, on any page.
    box = page.locator(".fg__listsearch")
    while not page.locator(".fg__listpages button", has_text="Previous").is_disabled():
        page.locator(".fg__listpages button", has_text="Previous").click()
        page.wait_for_timeout(40)
    first_el = page.locator(".fg__list .fg__member").first
    if first_el.count():
        first = first_el.get_attribute("data-card")
        text = first_el.locator(".fg__membertitle").inner_text().strip()
        # The first plain word: typeset mathematics in a title reads differently on the page and in its plain text.
        word = next((w for w in (x.strip(".,;:()") for x in text.split()) if len(w) >= 3 and w.isascii() and w.isalpha()), "")
        if word:
            box.fill(word)
            page.wait_for_timeout(150)
            found: list[str] = []
            for _ in range(count + 1):
                found += page.locator(".fg__list .fg__member").evaluate_all("(els) => els.map((e) => e.dataset.card)")
                nxt = page.locator(".fg__listpages button", has_text="Next")
                if nxt.is_disabled():
                    break
                nxt.click()
                page.wait_for_timeout(40)
            if first not in found:
                bad.append(f"{label}: searching {name} for \"{word}\" does not find its first member {first}")
            # Back to the whole list, as the reader found it.
            box.fill("")
            page.wait_for_timeout(100)
    covered = panel.evaluate("(el) => el.classList.contains('fg__list--narrow')")
    if covered:
        if not page.locator(".fg__tools[inert]").count():
            bad.append(f"{label}: the graph toolbar under the list of {name} still takes keyboard focus")
    else:
        _fit(page)
        if not panel.count():
            bad.append(f"{label}: Fit closed the list of {name}")
    before_close = page.evaluate(SUBJECT_BOX)
    back = page.locator(".fg__listback")
    if back.count():
        back.click()
        page.wait_for_timeout(300)
    if panel.count():
        bad.append(f"{label}: Back did not close the list of {name}")
    if not head.evaluate("(el) => el === document.activeElement"):
        bad.append(f"{label}: Back did not return focus to the group {name}")
    moved = _moved(before_close, page.evaluate(SUBJECT_BOX))
    if moved > 1:
        bad.append(f"{label}: closing the list of {name} moved the subject by {moved:.1f}px")
    if covered and not panel.count():
        _fit(page)
    if not bad:
        print(f"ok  {label}: the group {name} lists its {count} members, pages and searches them, and the subject stays still")
    return bad


def _check_in_place(page: Page, label: str, head, name: str, count: int) -> list[str]:
    bad: list[str] = []
    head.click()
    page.wait_for_timeout(400)
    group = page.locator(".fg__side > .fg__group.is-open").first
    if group.count() == 0:
        return [f"{label}: clicking the group {name} did not open it"]
    inside = group.evaluate("(g) => [...g.querySelectorAll('.fg__members .fg__card')].length + [...g.querySelectorAll('.fg__members .fg__grouphead')].reduce((n, h) => n + (h.getAttribute('aria-expanded') === 'true' ? 0 : +h.dataset.count), 0)")
    if inside != count:
        bad.append(f"{label}: the group {name} counts {count} but opens into {inside}")
    sc = page.locator(".fg__scroll")
    extra = sc.evaluate("(el) => { const v = el.getBoundingClientRect(), d = el.querySelector('.fg__world').getBoundingClientRect(); return Math.round(Math.max(0, v.top - d.top, d.bottom - v.bottom, v.left - d.left, d.right - v.right)); }")
    if extra > 4:
        before = sc.evaluate("(el) => el.querySelector('.fg__world').style.transform")
        box = sc.bounding_box()
        page.mouse.move(box["x"] + 12, box["y"] + box["height"] / 2)
        page.mouse.down()
        page.mouse.move(box["x"] + 12, box["y"] + box["height"] / 2 - 120, steps=6)
        page.mouse.up()
        page.wait_for_timeout(200)
        if sc.evaluate("(el) => el.querySelector('.fg__world').style.transform") == before:
            bad.append(f"{label}: with the group {name} open, dragging does not pan the graph")
        if page.locator(".fg__mini").count() == 0 and page.viewport_size["width"] > 600:
            bad.append(f"{label}: the drawing overflows but there is no overview")
        hidden = page.evaluate(
            """async () => { const sc = document.querySelector('.fg__scroll'); const v = sc.getBoundingClientRect(); const out = [];
            for (const c of sc.querySelectorAll('.fg__card')) { c.focus(); await new Promise((r) => requestAnimationFrame(() => requestAnimationFrame(r))); const r = c.getBoundingClientRect();
              if (r.height <= v.height && (r.top < v.top - 1 || r.bottom > v.bottom + 1 || r.left < v.left - 1 || r.right > v.right + 1)) out.push(c.dataset.card); }
            return out; }"""
        )
        if hidden:
            bad.append(f"{label}: cards that focusing cannot bring wholly into view: {', '.join(hidden[:5])}")
    # Fit only moves the camera: the group stays open, and folding it is the group's own button.
    _fit(page)
    if page.locator(".fg__side > .fg__group.is-open").count() == 0:
        bad.append(f"{label}: Fit folded the opened group {name}")
    head.click()
    page.wait_for_timeout(300)
    if not bad:
        print(f"ok  {label}: the group {name} opens into its {count}, pans {max(0, extra)}px, and Fit keeps it open")
    return bad

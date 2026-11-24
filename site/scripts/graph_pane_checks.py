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

from playwright.sync_api import Locator, Page


GRAPH_SETTLED = """async graph => {
  await document.fonts.ready;
  let previous = '';
  let since = performance.now();
  const deadline = since + 6000;
  while (performance.now() < deadline) {
    await new Promise(requestAnimationFrame);
    const world = graph.querySelector('.fg__world');
    const viewport = graph.querySelector('.fg__scroll');
    const bounds = viewport.getBoundingClientRect();
    const signature = JSON.stringify([
      bounds.left, bounds.top, bounds.width, bounds.height, world.style.transform,
      ...[...world.querySelectorAll('.fg__wire')].map(wire => wire.getAttribute('d')),
    ]);
    if (signature !== previous) {
      previous = signature;
      since = performance.now();
    } else if (performance.now() - since >= 250) {
      return true;
    }
  }
  return false;
}"""

PAIRED_GEOMETRY = """() => {
  const split = document.querySelector('.map-pane__paired');
  const box = (e) => {
    if (!e) return null;
    const r = e.getBoundingClientRect();
    return {top: r.top, bottom: r.bottom, left: r.left, right: r.right, width: r.width, height: r.height};
  };
  const lean = split?.querySelector(':scope > .lean-page');
  const scroll = lean?.querySelector(':scope > .lean-page__scroll');
  const leanBox = box(lean);
  let intrinsic = null;
  if (scroll && leanBox) {
    const r = scroll.getBoundingClientRect();
    const px = (value) => parseFloat(value) || 0;
    const contentEnd = Math.max(r.top, ...[...scroll.children].filter(e => e.getClientRects().length).map(e =>
      e.getBoundingClientRect().bottom + px(getComputedStyle(e).marginBottom)));
    const style = getComputedStyle(scroll);
    const content = contentEnd - r.top + scroll.scrollTop + px(style.paddingBottom) + px(style.borderBottomWidth);
    const leanStyle = getComputedStyle(lean);
    const children = [...lean.children].filter(e => e.getClientRects().length);
    const chrome = children.reduce((total, child) => {
      const childStyle = getComputedStyle(child);
      return total + (child === scroll ? 0 : child.getBoundingClientRect().height)
        + px(childStyle.marginTop) + px(childStyle.marginBottom);
    }, px(leanStyle.paddingTop) + px(leanStyle.paddingBottom) + px(leanStyle.borderTopWidth) + px(leanStyle.borderBottomWidth));
    intrinsic = chrome + content + Math.max(0, children.length - 1) * px(leanStyle.rowGap);
  }
  return {
    pane: box(split),
    lean: leanBox,
    graph: box(split?.querySelector(':scope > .map-pane__local')),
    canvas: box(split?.querySelector('.map-pane__local .fg__scroll')),
    intrinsic,
    subjects: split?.querySelectorAll('.map-pane__local .fg__card[data-band="subject"]').length ?? 0,
  };
}"""


def paired_geometry(page: Page) -> tuple[bool, dict]:
    """Lean has enough room for its content and the graph fills the remaining height."""
    page.wait_for_function("""() => document.querySelector('.map-pane__paired')
                          ?.style.getPropertyValue('--paired-graph-paint')""", timeout=15000)
    drawing = page.locator(".map-pane__paired .map-pane__local .fg").first
    settled = drawing.evaluate(GRAPH_SETTLED)
    layout = page.evaluate(PAIRED_GEOMETRY)
    pane, lean, graph, canvas = (layout[key] for key in ("pane", "lean", "graph", "canvas"))
    if not all((pane, lean, graph, canvas)):
        return False, layout
    fitted, shape = painted_fit(drawing)
    layout.update(settled=settled, painted=shape)
    if "error" in shape or not shape["scale"] or layout["intrinsic"] is None:
        return False, layout

    left, right, top, bottom = shape["gap"]
    world_width = (canvas["width"] - left - right) / shape["scale"]
    world_height = (canvas["height"] - top - bottom) / shape["scale"]
    if world_width <= 0 or world_height <= 0:
        return False, layout
    # Size from the physical paint and the width available before fitting in height.
    # The SVG marker and stroke bounds allow a few pixels of variation at either end.
    margin = 8
    width_scale = min(1.15, (canvas["width"] - 2 * margin) / world_width)
    fitted_height = world_height * width_scale + 2 * margin
    preferred_graph = fitted_height + graph["height"] - canvas["height"]
    minimum_graph = min(0.4 * pane["height"], preferred_graph)
    expected_lean = min(layout["intrinsic"], pane["height"] - minimum_graph)
    expected_graph = pane["height"] - expected_lean
    layout.update(expected_lean=expected_lean, expected_graph=expected_graph)
    fits = (abs(lean["height"] - expected_lean) <= 6 and abs(graph["height"] - expected_graph) <= 6
            and canvas["height"] > 0 and canvas["width"] > 0
            and abs(lean["top"] - pane["top"]) <= 2 and abs(lean["bottom"] - graph["top"]) <= 2
            and abs(graph["bottom"] - pane["bottom"]) <= 2
            and all(abs(row[edge] - pane[edge]) <= 2 for row in (lean, graph) for edge in ("left", "right"))
            and graph["left"] <= canvas["left"] < canvas["right"] <= graph["right"] + 2
            and graph["top"] <= canvas["top"] < canvas["bottom"] <= graph["bottom"] + 2)
    return settled and fitted and fits and layout["subjects"] == 1, layout


PAINTED_GRAPH = r"""fg => {
  const viewport = fg.querySelector('.fg__scroll').getBoundingClientRect();
  const world = fg.querySelector('.fg__world');
  const boxes = [];
  const detached = [];
  const subjects = [...world.querySelectorAll('.fg__card[data-band="subject"]')];
  const stacked = world.classList.contains('fg__world--narrow');
  const distanceToBorder = (point, card, edge) => {
    if (!card) return Infinity;
    const rect = card.getBoundingClientRect();
    return Math.hypot(point.x - rect[edge], Math.max(rect.top - point.y, point.y - rect.bottom, 0));
  };
  const put = (rect, kind, padX = 0, padY = padX) => {
    if (!rect.width && !rect.height) return;
    boxes.push({kind, left: rect.left - padX, top: rect.top - padY,
                right: rect.right + padX, bottom: rect.bottom + padY});
  };
  for (const card of world.querySelectorAll('.fg__card, .fg__grouphead, .fg__subjects--many')) {
    put(card.getBoundingClientRect(), 'card');
  }
  const range = document.createRange();
  for (const label of world.querySelectorAll('.fg__sidehead, .fg__sidekinds, .fg__edge-note')) {
    range.selectNodeContents(label);
    for (const rect of range.getClientRects()) put(rect, 'label');
  }
  for (const path of world.querySelectorAll('.fg__lines .fg__wire, .fg__lines .fg__hotline')) {
    const matrix = path.getScreenCTM();
    const halfStroke = (parseFloat(getComputedStyle(path).strokeWidth) || 0) / 2;
    put(path.getBoundingClientRect(), 'wire', Math.hypot(matrix.a, matrix.c) * halfStroke,
        Math.hypot(matrix.b, matrix.d) * halfStroke);
    const length = path.getTotalLength();
    if (subjects.length === 1 && path.dataset.edge) {
      // For one subject, resolve the neighbouring endpoint from its wire identity.
      const [from, to] = path.dataset.edge.split('>');
      const side = from ? 'users' : 'uses';
      const id = from || to;
      const column = world.querySelector('.fg__side[data-band="' + side + '"]');
      const grouped = id.startsWith('group:');
      const parts = column?.querySelectorAll(grouped ? ':scope > .fg__group > .fg__grouphead' : ':scope > .fg__card');
      const neighbour = [...(parts ?? [])].find(el => grouped ? el.dataset.group === id.slice(6) : el.dataset.card === id);
      const source = from ? subjects[0] : neighbour;
      const target = from ? neighbour : subjects[0];
      const start = path.getPointAtLength(0).matrixTransform(matrix);
      const end = path.getPointAtLength(length).matrixTransform(matrix);
      const tolerance = 1.5 * Math.hypot(matrix.a, matrix.b);
      if (!length || distanceToBorder(start, source, 'left') > tolerance
          || distanceToBorder(end, target, stacked ? 'left' : 'right') > tolerance) detached.push(path.dataset.edge);
    }
    // A marker is painted at the end of its curve, but is absent from the path's client rect.
    const marker = path.getAttribute('marker-end')?.match(/^url\(#([^)]+)\)$/)?.[1];
    const arrow = marker && path.ownerSVGElement.querySelector(`#${CSS.escape(marker)}`);
    const glyph = arrow?.querySelector('path');
    if (!arrow || !glyph || !length) continue;
    const end = path.getPointAtLength(length);
    const before = path.getPointAtLength(Math.max(0, length - 0.1));
    const angle = Math.atan2(end.y - before.y, end.x - before.x);
    const {x, y, width, height} = glyph.getBBox();
    const viewBox = arrow.viewBox.baseVal;
    const scale = Math.min(arrow.markerWidth.baseVal.value / viewBox.width,
                           arrow.markerHeight.baseVal.value / viewBox.height);
    const place = new DOMMatrix().translate(end.x, end.y).rotate(angle * 180 / Math.PI).scale(scale)
      .translate(-arrow.refX.baseVal.value, -arrow.refY.baseVal.value);
    const corners = [[x,y], [x+width,y], [x,y+height], [x+width,y+height]].map(([x,y]) =>
      new DOMPoint(x,y).matrixTransform(place).matrixTransform(matrix));
    const xs = corners.map(p => p.x), ys = corners.map(p => p.y);
    put(DOMRect.fromRect({x: Math.min(...xs), y: Math.min(...ys),
                         width: Math.max(...xs) - Math.min(...xs), height: Math.max(...ys) - Math.min(...ys)}), 'arrow');
  }
  if (!boxes.length) return {error: 'nothing painted in the local graph'};
  const left = Math.min(...boxes.map(r => r.left)), right = Math.max(...boxes.map(r => r.right));
  const top = Math.min(...boxes.map(r => r.top)), bottom = Math.max(...boxes.map(r => r.bottom));
  const gap = [left - viewport.left, viewport.right - right, top - viewport.top, viewport.bottom - bottom];
  const outside = boxes.filter(r => r.left < viewport.left - 1 || r.right > viewport.right + 1 ||
                                    r.top < viewport.top - 1 || r.bottom > viewport.bottom + 1);
  const transform = getComputedStyle(world).transform;
  const scale = transform === 'none' ? 1 : new DOMMatrixReadOnly(transform).a;
  return {view: [viewport.width, viewport.height], scale, gap, detached, outside: outside.map(r => r.kind),
          counts: Object.fromEntries(['card', 'wire', 'arrow', 'label'].map(kind =>
            [kind, boxes.filter(r => r.kind === kind).length])), sides: [+fg.dataset.users, +fg.dataset.uses],
          subjects: subjects.map(card => card.dataset.card)};
}"""


def painted_fit(graph: Locator) -> tuple[bool, dict]:
    """A fitted local camera shows and centres the painted content in both axes."""
    shape = graph.evaluate(PAINTED_GRAPH)
    if "error" in shape:
        return False, shape
    left, right, top, bottom = shape["gap"]
    # Include the actual wire strokes and arrowheads in the enclosure. Their small asymmetric
    # protrusions allow subpixel variation in the measured centre of the painted shape.
    return (not shape["outside"] and min(shape["gap"]) >= 2
            and max(abs(left - right), abs(top - bottom)) <= 6), shape


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
  const out = {subjects: 0, nodes: 0, groups: 0, grouped: 0, small: [], cut: [], blank: [], outside: [],
               users: +fg.dataset.users, uses: +fg.dataset.uses, opened: +fg.dataset.opened,
               lines: fg.querySelectorAll('.fg__lines path[data-edge]').length, tops: 0,
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
    if page.locator(".fg__mini").count():
        bad.append(f"{label}: the reader graph has a miniature overview")
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
        _, shape = painted_fit(page.locator(".fg").first)
        if "error" in shape:
            bad.append(f"{label}: {shape['error']}")
        elif shape["outside"]:
            outside = m["outside"] or shape["outside"]
            bad.append(f"{label}: outside the graph viewport on opening: {', '.join(outside[:5])}")
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

SUBJECT_BOX = """() => {
  const c = document.querySelector('.fg .fg__card[data-band=subject]');
  if (!c) return null;
  const r = c.getBoundingClientRect();
  const v = c.closest('.map-pane__paired') && c.closest('.fg__scroll').getBoundingClientRect();
  return [r.left - (v?.left ?? 0), r.top - (v?.top ?? 0), r.width, r.height];
}"""
CANVAS_HEIGHT = "() => document.querySelector('.fg__scroll')?.getBoundingClientRect().height ?? 0"


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
    paired = page.locator(".map-pane__paired .fg").count() > 0
    before = page.evaluate(SUBJECT_BOX)
    height_before = page.evaluate(CANVAS_HEIGHT)
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
    if paired and page.evaluate(CANVAS_HEIGHT) < height_before - 1:
        bad.append(f"{label}: listing the group {name} reduced the graph viewport")
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
    moved = _moved(before if paired else before_close, page.evaluate(SUBJECT_BOX))
    if moved > 1:
        bad.append(f"{label}: the subject moved by {moved:.1f}px after closing the list of {name}")
    if paired and abs(page.evaluate(CANVAS_HEIGHT) - height_before) > 2:
        bad.append(f"{label}: closing the list of {name} did not restore the fitted viewport height")
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
    _, shape = painted_fit(page.locator(".fg").first)
    extra = max(0, round(-min(shape.get("gap", [0]))))
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
        if page.locator(".fg__mini").count():
            bad.append(f"{label}: panning the opened group {name} shows a miniature overview")
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

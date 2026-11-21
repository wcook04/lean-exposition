// The library index: the scheme switch (the reader's own rule and storage key, so a choice made
// here holds in every paper) and one search across every paper. Papers read here search their
// built data (statements and Lean names, /library/_index/search/<paper>.json, fetched the first
// time the field is used); papers still on their current sites match by title, authors,
// sentence and page names.

const KEY = "lx-theme";
const root = document.documentElement;
const media = window.matchMedia("(prefers-color-scheme: dark)");

const systemScheme = () => (media.matches ? "dark" : "light");
const currentScheme = () => {
  const forced = root.getAttribute("data-theme");
  return forced === "light" || forced === "dark" ? forced : systemScheme();
};

function setScheme(next) {
  root.classList.add("no-transitions");
  if (next === systemScheme()) {
    root.removeAttribute("data-theme");
    try { localStorage.removeItem(KEY); } catch { /* storage unavailable */ }
  } else {
    root.setAttribute("data-theme", next);
    try { localStorage.setItem(KEY, next); } catch { /* storage unavailable */ }
  }
  labelToggle();
  requestAnimationFrame(() => requestAnimationFrame(() => root.classList.remove("no-transitions")));
}

const toggle = document.querySelector("[data-scheme-toggle]");
function labelToggle() {
  if (toggle) toggle.setAttribute("aria-label", currentScheme() === "dark" ? "Switch to light colours" : "Switch to dark colours");
}
labelToggle();
toggle?.addEventListener("click", () => setScheme(currentScheme() === "dark" ? "light" : "dark"));
media.addEventListener("change", labelToggle);

// ------------------------------------------------------------------ search

const DATA = JSON.parse(document.getElementById("library-data")?.textContent || "{\"papers\":[]}");
const input = document.getElementById("q");
const status = document.getElementById("search-status");
const results = document.getElementById("search-results");
const SHOWN = 4;

const fold = (text) => text.normalize("NFD").replace(/[̀-ͯ]/g, "").toLowerCase();
const words = (query) => fold(query).split(/[\s,]+/).filter(Boolean);
const holdsAll = (hay, terms) => terms.every((t) => hay.includes(t));
const fmt = (k) => k.toLocaleString("en-GB");

const shards = new Map(); // paper id -> {statements, lean} with folded text
let loading = null;

function loadShards() {
  loading ??= Promise.all(
    DATA.papers.filter((p) => p.shard).map(async (p) => {
      try {
        const response = await fetch(p.shard);
        if (!response.ok) return;
        const data = await response.json();
        shards.set(p.id, {
          statements: data.statements.map(([label, text, href]) => ({ label, text, href, hay: fold(`${label} ${text}`) })),
          lean: data.lean.map(([name, plain = ""]) => ({ name, plain, href: data.lean_base + name, hay: fold(`${name} ${name.replace(/[._]/g, " ")} ${plain}`) })),
        });
      } catch {
        /* this paper's statements stay unsearched; its title still matches */
      }
    }),
  ).then(() => run());
  return loading;
}

function el(tag, attrs = {}, ...children) {
  const node = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === "class") node.className = v;
    else node.setAttribute(k, v);
  }
  for (const child of children) if (child != null) node.append(child);
  return node;
}

/** The text with each search word marked, cut to a window around the first match. */
function marked(text, terms, room = 220) {
  const folded = fold(text);
  let start = 0;
  const first = Math.min(...terms.map((t) => folded.indexOf(t)).filter((i) => i >= 0));
  if (Number.isFinite(first) && first > room / 2 && text.length > room) start = Math.max(0, first - 60);
  let slice = text.slice(start, start + room);
  const lead = start > 0 ? "…" : "";
  const tail = start + room < text.length ? "…" : "";
  const frag = document.createDocumentFragment();
  frag.append(lead);
  const sliceFold = fold(slice);
  const spans = [];
  for (const t of terms) {
    let i = sliceFold.indexOf(t);
    while (i >= 0) {
      spans.push([i, i + t.length]);
      i = sliceFold.indexOf(t, i + t.length);
    }
  }
  spans.sort((a, b) => a[0] - b[0]);
  let at = 0;
  for (const [a, b] of spans) {
    if (a < at) continue;
    frag.append(slice.slice(at, a), el("mark", {}, slice.slice(a, b)));
    at = b;
  }
  frag.append(slice.slice(at), tail);
  return frag;
}

function rank(rows, terms, key) {
  return rows
    .filter((r) => holdsAll(r.hay, terms))
    .map((r) => ({ r, score: (fold(key(r)).includes(terms[0]) ? 0 : 1) * 1e6 + key(r).length }))
    .sort((a, b) => a.score - b.score)
    .map((x) => x.r);
}

function group(paper, terms, open) {
  const titleHay = fold(`${paper.title} ${paper.authors} ${paper.sentence} ${paper.pages.map((p) => p.title).join(" ")}`);
  const titleHit = holdsAll(titleHay, terms);
  const shard = shards.get(paper.id);
  const statements = shard ? rank(shard.statements, terms, (r) => r.label || r.text) : [];
  const lean = shard ? rank(shard.lean, terms, (r) => r.name) : [];
  const pages = paper.pages.filter((p) => holdsAll(fold(p.title), terms));
  if (!titleHit && !statements.length && !lean.length && !pages.length) return null;

  const box = el("section", { class: "results__paper", "aria-label": paper.title });
  const head = el("div", { class: "results__head" },
    el("a", { href: paper.href }, marked(paper.title, terms, 400)),
    el("span", { class: "results__where" }, paper.here ? `By ${paper.authors}` : `By ${paper.authors}, on its current site`));
  box.append(head);
  if (titleHit && paper.sentence) box.append(el("p", { class: "results__text" }, marked(paper.sentence, terms)));

  const list = (kind, rows, draw) => {
    if (!rows.length) return;
    const all = open.has(`${paper.id}:${kind}`);
    box.append(el("p", { class: "results__kind" }, `${kind === "statements" ? "Statements" : "Lean declarations"}: ${fmt(rows.length)}`));
    const ul = el("ul", { class: "results__list" });
    for (const row of all ? rows.slice(0, 200) : rows.slice(0, SHOWN)) ul.append(el("li", {}, draw(row)));
    box.append(ul);
    if (rows.length > SHOWN && !all) {
      const more = el("button", { type: "button", class: "results__more" }, `Show ${fmt(Math.min(rows.length, 200) - SHOWN)} more`);
      more.addEventListener("click", () => {
        open.add(`${paper.id}:${kind}`);
        run();
      });
      box.append(more);
    }
  };
  list("statements", statements, (r) =>
    el("a", { href: r.href }, r.label ? el("span", { class: "results__label" }, marked(r.label, terms, 200)) : null, el("span", { class: "results__text" }, marked(r.text, terms))));
  list("lean", lean, (r) =>
    el("a", { href: r.href }, el("span", { class: "results__lean", translate: "no" }, marked(r.name, terms, 300)), r.plain ? el("span", { class: "results__plain" }, marked(r.plain, terms, 200)) : null));
  if (pages.length) {
    const ul = el("ul", { class: "results__list" });
    for (const p of pages) ul.append(el("li", {}, el("a", { href: p.href }, el("span", { class: "results__label" }, marked(p.title, terms, 200)))));
    box.append(el("p", { class: "results__kind" }, "Pages"), ul);
  }
  return box;
}

const opened = new Set();
let last = "";

function run() {
  const query = input.value.trim();
  if (query !== last) opened.clear();
  last = query;
  const terms = words(query);
  results.replaceChildren();
  if (!terms.length) {
    results.hidden = true;
    status.textContent = "";
    return;
  }
  const groups = DATA.papers.map((p) => group(p, terms, opened)).filter(Boolean);
  results.append(...groups);
  results.hidden = groups.length === 0;
  const pending = loading && shards.size < DATA.papers.filter((p) => p.shard).length;
  status.textContent = groups.length
    ? `Matches in ${groups.length} ${groups.length === 1 ? "paper" : "papers"}.${pending ? " Still loading the statements and Lean names." : ""}`
    : pending ? "Loading the statements and Lean names…" : "No paper matches every word.";
}

if (input && results) {
  input.addEventListener("focus", loadShards, { once: true });
  input.addEventListener("input", () => {
    loadShards();
    run();
  });
  input.addEventListener("keydown", (event) => {
    if (event.key === "Escape" && input.value) {
      event.preventDefault();
      input.value = "";
      run();
    }
  });
  document.addEventListener("keydown", (event) => {
    if (event.key !== "/" || event.metaKey || event.ctrlKey || event.altKey) return;
    const target = event.target;
    if (target instanceof HTMLElement && (target.isContentEditable || /^(INPUT|TEXTAREA|SELECT)$/.test(target.tagName))) return;
    event.preventDefault();
    input.focus();
  });
  const initial = new URLSearchParams(location.search).get("q");
  if (initial) {
    input.value = initial;
    loadShards();
    run();
  }
}

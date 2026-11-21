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
// A number matches only as a whole number: "2.1" finds Lemma 2.1, never "(2.12)" or "2.1.3".
const NUMBER = /^\d+(?:\.\d+)*$/;
const escapeRe = (t) => t.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
const numberAt = new Map();
function numberRe(t) {
  if (!numberAt.has(t)) numberAt.set(t, new RegExp(`(?<![\\d.])${escapeRe(t)}(?![\\d]|\\.\\d)`));
  return numberAt.get(t);
}
const holds = (hay, t) => (NUMBER.test(t) ? numberRe(t).test(hay) : hay.includes(t));
const holdsAll = (hay, terms) => terms.every((t) => holds(hay, t));
// "Lemma 2.1": a kind of numbered result and its number. Such a query matches result labels exactly.
const KINDS = "theorem|proposition|lemma|corollary|definition|remark|conjecture|problem|example|assumption|claim|step";
const NUMBERED = new RegExp(`^(${KINDS})\\s+(\\d+(?:\\.\\d+)*[a-z]?)$`);
function numberedQuery(query) {
  const m = NUMBERED.exec(fold(query).trim().replace(/\s+/g, " "));
  return m ? new RegExp(`^\\W*${m[1]}\\s+${escapeRe(m[2])}(?![\\d]|\\.\\d)`) : null;
}
const fmt = (k) => k.toLocaleString("en-GB");

const shards = new Map(); // paper id -> {statements, lean} with folded text
const failed = new Set(); // paper ids whose contents could not be loaded
let loading = null;

function loadShards() {
  loading ??= Promise.all(
    DATA.papers.filter((p) => p.shard).map(async (p) => {
      try {
        const response = await fetch(p.shard);
        if (!response.ok) {
          failed.add(p.id);
          return;
        }
        const data = await response.json();
        shards.set(p.id, {
          statements: data.statements.map(([label, text, href]) => ({ label, text, href, hay: fold(`${label} ${text}`) })),
          lean: data.lean.map(([name, plain = ""]) => ({ name, plain, href: data.lean_base + name, hay: fold(`${name} ${name.replace(/[._]/g, " ")} ${plain}`) })),
        });
      } catch {
        // This paper's statements stay unsearched, and the status says so; its title still matches.
        failed.add(p.id);
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

function group(paper, terms, open, numbered) {
  const titleHay = fold(`${paper.title} ${paper.authors} ${paper.sentence} ${paper.pages.map((p) => p.title).join(" ")}`);
  const titleHit = !numbered && holdsAll(titleHay, terms);
  const shard = shards.get(paper.id);
  // A numbered query ("Lemma 2.1") lists the results with exactly that label, not every row that
  // holds the kind and the number somewhere.
  const statements = !shard ? [] : numbered ? shard.statements.filter((r) => r.label && numbered.test(fold(r.label)))
    : rank(shard.statements, terms, (r) => r.label || r.text);
  const lean = shard && !numbered ? rank(shard.lean, terms, (r) => r.name) : [];
  const pages = numbered ? [] : paper.pages.filter((p) => holdsAll(fold(p.title), terms));
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
  const numbered = numberedQuery(query);
  const groups = DATA.papers.map((p) => group(p, terms, opened, numbered)).filter(Boolean);
  results.append(...groups);
  results.hidden = groups.length === 0;
  status.textContent = statusLine(groups.length, !!numbered);
}

/** The result count with its denominators: how many papers were searched by contents, and how. */
function statusLine(matched, numbered) {
  const indexed = DATA.papers.filter((p) => p.shard);
  const loaded = indexed.filter((p) => shards.has(p.id)).length;
  const lost = indexed.filter((p) => failed.has(p.id));
  const pending = !!loading && loaded + lost.length < indexed.length;
  const titleOnly = DATA.papers.length - indexed.length;
  const paper = (k) => `${fmt(k)} ${k === 1 ? "paper" : "papers"}`;
  const searched = numbered
    ? `Searched the numbered results of ${paper(loaded)}; ${titleOnly ? `${paper(titleOnly)} ${titleOnly === 1 ? "is" : "are"} indexed by title only and not searched for results.` : ""}`
    : `Searched the contents of ${paper(loaded)}${titleOnly ? ` and the titles of ${paper(titleOnly)} more` : ""}.`;
  const failure = lost.length ? ` The contents of ${lost.map((p) => p.title).join(", ")} could not be loaded; ${lost.length === 1 ? "its title was" : "their titles were"} still searched.` : "";
  if (pending) return `${matched ? `Matches in ${paper(matched)} so far. ` : ""}Loading the statements and Lean names…`;
  const head = matched ? `Matches in ${paper(matched)} of ${fmt(DATA.papers.length)}.` : numbered ? "No result has that number." : "No paper matches every word.";
  return `${head} ${searched}${failure}`.replace(/\s+$/, "");
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

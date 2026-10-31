# Design system

The site is a reading instrument for one mathematical result. Its job is to let
someone see the goal, follow any step down to where it starts, read how each
account explains that step, and check what was recorded about it. This file
holds the rules every page follows. The values live in
[`src/styles/tokens.css`](src/styles/tokens.css); the shared classes live in
[`src/styles/base.css`](src/styles/base.css).

## Principles

1. **Reading size is fixed.** Prose a reader must read never renders below 13px on
   screen, and a card's title never below 14px. When there is more than fits,
   change the representation (a mark, a count, a list), never shrink the prose.
   The titles on the map's zoomed-out tiles are labels: they shrink to 10px
   before they are cut, and a tile with room for its title never stands empty.
2. **One channel per meaning.** Each visual variable answers one question:

   | Question | Channel |
   | --- | --- |
   | Where does this record come from? | A small square in its source colour beside the source's name. In overview, the fill of its mark. |
   | What kind of record is it? | A word in small capitals: CLAIM, ASSUMPTION, LEAN DECLARATION, MAIN RESULT. Assumptions alone get a dashed border. |
   | How does a step use it? | The line's colour and pattern together, with the relation named in words wherever it is inspected. |
   | How does an account treat it? | A shape and a word: ● own passage, ○ used without a passage of its own, ⊟ outside the account's selection. |
   | What am I looking at? | Amber. Selection, a lit support route and keyboard focus. Nothing else is amber. |
   | What did a check record? | The outcome in words: passed, failed, unavailable, not run. Only a recorded failure is coloured. |

3. **The page is quiet so the mathematics can be loud.** Statements are set large
   in STIX Two Text. Controls are small Source Sans. Lean is JetBrains Mono. Use
   rules and space before boxes; no gradients, glossy badges or decorative haze.
4. **Motion explains one change, then stops.** New records grow out of the one
   that was opened; the camera moves only as far as the change needs; nothing
   loops. With reduced motion the same end state appears at once.
5. **Say only what the records say.** The site adds layout and wording, not facts.
   See [Wording](#wording).

## Type

| Use | Face | Size / line height |
| --- | --- | --- |
| Goal title on the plate | STIX Two Text 500 | `--fs-plate` (28–36px) / 1.12 |
| Inspector title | STIX Two Text 500 | `--fs-title` (26px) / 1.15 |
| Card title | STIX Two Text | `--fs-card` (17px) / 1.3 |
| Paper prose | STIX Two Text | `--fs-read` (18px) / 1.62, measure `--reader-measure` |
| Excerpts in the inspector | STIX Two Text | 17px / 1.55 |
| Controls | Source Sans 3 | `--fs-ui` (14px) |
| Metadata | Source Sans 3 | `--fs-sm` (13px) |
| Kind words | Source Sans 3 600, `.caps` | `--fs-micro` (11px), tracked |
| Lean | JetBrains Mono | 13px |

Record statements that are recorded as plain text stay verbatim. Do not convert
them to TeX with patterns; show authored mathematics from the papers instead.

## Colour

The neutrals (ground, surfaces, rules and inks) follow the palette Will Cook's websites
share, warm paper and violet ink by day and a violet ground with bone ink at night
([the family contract](https://github.com/wcook04/wcook04.github.io/blob/main/docs/family.md));
the colours below that carry meaning keep their own hues on it, each checked again on
the new grounds.

- **Ground, surface, raised.** The page, reading surfaces, and cards.
- **Ink 1–3.** Text and marks, in falling emphasis. `--ink-3` still passes 4.5:1.
- **Source slots `--src-1…3`.** A validated colour-blind-safe set; slot 0 is
  neutral. Assigned by family, never by rank or position, so a filter never
  repaints a record.
- **Amber `--lit*`.** Attention only. In the dark scheme a selected card may carry
  a faint amber glow (`--lit-glow`); in the light scheme it does not.
- **`--fail`.** A recorded failed outcome. Never a mathematical verdict.
- **Edges `--edge-rest`, `--edge-strong`, `--edge-lit`.** Rest lines keep at least
  3:1 against the ground in both schemes.
- **`--rule-control`.** The hairline of a control that has no other edge (a ghost
  button, a field, a picker): 3:1 or more against every surface it sits on. Rules that
  only divide stay `--rule` and `--rule-strong`.

## The map

The map draws the recorded argument for one goal: the goal at the top, what it
uses beneath it, each line running from a result up into the result it helps
prove.

### Two scales, three representations

The camera never shrinks a card's prose below reading size. Instead each record
changes representation with the screen scale `k`:

| Scale | Representation | Shows |
| --- | --- | --- |
| `k ≥ 0.8` | **Card** | Kind word, source square and name, title, inputs control, account mark |
| `0.5 ≤ k < 0.8` | **Compact** | Title, up to 13px on screen, source square; the goal's plate also gives the theorem's first sentence |
| `k < 0.5` | **Mark** | A tile in its source colour, with its title whenever the tile can hold it at 10px or more |

In compact form each tile shows its title, centred, in as many lines as the
tile's height on screen holds. The goal's plate sets its title at up to 24px,
breaking between words only, and below it the theorem's first sentence, 360px
wide at 13px, whenever both fit: the plate never stands empty. A mark keeps its
title for as long as its own size on screen allows, so the plate keeps its title
long after the small tiles lose theirs; a title too long for a mark is cut after
a whole word, and only while at least half of it stays. The goal, the selected
record and the hovered record carry labels drawn at screen size when their marks
are too small to name them, so the reader always knows where they are.

**Navigation.** Scrolling up or down, with a wheel or two fingers on a trackpad,
zooms about the pointer, as a pinch does; a sideways swipe pans; dragging pans
from anywhere on the map, cards included. A press that moves less than 5px is a
click. In the map beside the paper, scrolling moves along the route instead.
**Steps** is the reading mode: it opens at `k = 1` and keeps the opened record
in view. **Overview** fits the whole goal and uses marks. Clicking a mark opens
its lineage like any card; a mark with nothing below it returns to Steps around it. When Steps cannot fit every input of the opened record,
chips at the canvas edge say how many records lie beyond it in each direction,
and clicking one brings them in.

### Relations

| Relation (backend) | Name in the interface | Line | Colour at rest → lit |
| --- | --- | --- | --- |
| `supports` | Recorded support | Solid | `--rel-supports` grey → amber |
| `assumes` | Explicit assumption | Dotted, round caps | `--rel-assumes` violet → bright violet |
| `formalizes` | Recorded Lean correspondence | Dashed | `--rel-formalizes` steel cyan → bright cyan |
| `cites` | Citation | Not drawn on the map; listed in the inspector | — |

Type is carried twice, by colour and by pattern, so it survives colour-blindness,
print and lighting. Lines are drawn 1.5px on screen whatever the zoom
(`vector-effect: non-scaling-stroke`). A lit line is 2.25px in its type's lit
colour, **keeps its pattern** (an assumption stays dotted and violet when lit,
also under reduced motion), and glows faintly in the dark scheme only. Draw-on
reveals use a mask over the typed stroke, never the stroke's own dash array.
Arrowheads take their line's colour.

**Lines never sit on top of each other.** Only lines of the same type into the
same consumer share a bus. Every other pair keeps its own lane, at least 8px apart
where they run in parallel; assumptions and correspondences enter a consumer at
their own ports, left of the support port and in the same order as their cards.
Each line is drawn over a thin casing in the ground colour, so where two lines
cross the lower one shows a gap: a crossing never reads as a junction. Lines run
in the channels between ranks and never pass under a card.

Supports sharing a consumer meet in one bus. The bus means "direct inputs", not
"together sufficient". The map draws a simplified skeleton: a direct relation is
omitted when another drawn route already reaches the same record. The map says
so ("Simplified map · 36 relations not drawn") and every selected record lists
all its direct relations, drawn or not.

### Shared records are drawn where they are used

A record that many steps use would otherwise pull long lines across the whole
map. Like a ground symbol on a circuit schematic, a premise written at each use
in a proof tree, or a cloned molecule in a pathway map, the map draws such a
record locally:

- **Assumptions are premise tags.** Each result shows the assumptions it
  explicitly makes as a row of violet, dotted-outline tags at the foot of its
  card ("Assumes · …"). No assumption line crosses the map. A tag selects the
  relation; every tag of the same assumption lights together.
- **Shared starting records are clones.** A record with no recorded inputs that
  several results use is drawn beside each of them. A band along a clone's foot
  marks the copies, and "Used by N" says how many there are. All copies select,
  hover and light as one record; counts count records, not copies.

Records that have inputs of their own are never copied.

### Cards

- Raised surface, `--card-border`, `--radius-card`, `--card-shadow`.
- Header row: kind word on the left, source square and short source name on the
  right. Title below in 17px STIX. Lean declarations set their name in mono.
- Assumptions: dashed border. No other record uses a dashed border.
- Selected: a 2px amber outline outside the border. The title does not move.
- Records outside the current lit route recede: their borders and fills fade
  toward the ground; their text keeps its contrast.
- **Text is cut short only when it cannot fit.** A tile first sets its title smaller, down
  to 10px on screen (a Lean name to 9.5px, breaking only after its dots and
  underscores, or in a tile also between the words of a camel-case name), before
  it shortens it. A box that has room shows the
  whole text; a box that grows with its content never shortens it. An ellipsis
  appears only when the text needs more room than the box can give at that
  moment, always after a whole word, and the full text is then one hover or
  focus away. Cards, tags and source names grow with their text; a tile shows as
  many lines as its height on screen holds. Whether a tile has room is judged
  from its own size on screen, never from the zoom level alone.
- **Resting the pointer on a card draws its whole lineage.** After about 300ms
  on a card (not while dragging and not while the map is moving), every record
  below it, down to the records with no recorded inputs, is drawn: records
  already on the map keep their places and the lines among them light in their
  type colours; records not yet drawn are placed where opening their branches
  would put them, at half strength, without a shadow, and cannot take keyboard
  focus. The card under the pointer stays where it is on screen, and the camera
  does not otherwise move. The lineage stays drawn while the pointer is on that
  card or on any card of the lineage, and folds back about 200ms after it leaves
  them. Keyboard focus and touch do not draw a lineage.
- **Clicking a card opens its whole lineage and frames it.** The card is
  selected, everything below it unfolds at full strength, and the camera zooms
  out or in and pans until the card and all of its lineage fill the canvas the
  inspector leaves. Clicking another card opens its lineage the same way. A click
  on the empty map, or closing the selection, puts back the unfolding and camera
  from before the first card was opened. The inputs control still opens one level.

### The map header

- **Title block.** "Argument for" in small sans over the main result's full title
  in serif, which opens the menu of main results, each with the accounts that
  state it. Below 1100px it shows the short name ("Full support").
- **On the right:** the view switch (Steps, Overview, Outline; pressing the
  current view frames it again), "Records used by" with its account menu, and
  Key. No control repeats a view: framing the whole argument is the Overview view.
- **Key row.** In the flow under the header, so the map yields the room: the
  source colours by name, each line type, the assumption tag, the band of a record
  drawn under each use, and "How the map is drawn" (About). It wraps onto more
  lines and never overlaps or cuts. Shown by default except on phones and windows
  under 760px tall, where it would push the first row of cards off the canvas; a
  reader's choice to show or hide it is remembered.
- **On the canvas.** "Show all branches" and "Collapse branches" sit bottom right
  in the grammar of the canvas notes (surface, hairline, short shadow). A button
  that would change nothing is disabled and says why. The room they take is part
  of the canvas insets, so framing never puts a card under them.
- The header never overlaps itself or scrolls sideways, from 320px to 2560px and
  at 125% text: parts compress first, then wrap onto a second row.

## Front page

"/" is for someone arriving for the first time. The map is at "/map"; "/" with map
parameters (`g`, `n`, `t`, `lens`, `e`) still opens the map, so old links work.

- **The site's whole idea, in its first screen.** The proof is a table: rows are the steps
  of the argument and columns are its levels. The hero shows one row of that table for the
  main theorem: each clause of OpenAI's Lean beside the same clause of Theorem 1, with one
  plain line matching them. It needs no interaction, and a reader who knows no Lean can
  still see what the site does. `src/home/heroMarkup.ts` owns it, and
  `tests/front-hero.test.ts` holds each Lean fragment to the exact statement in OpenAI's
  source.
- **The first screen is HTML.** The build types the hero and the bar into `index.html`
  (`firstScreen` in `vite.config.ts`), with the theorem already typeset, so it paints before
  any script or data, and reaches readers and crawlers that run no script. React takes over
  with the same markup, so nothing moves. Its stylesheet, `hero.css`, loads with the first
  CSS. Other routes get the bar only.
- **Then, in order:** the two films, side by side; **one argument at four levels**
  (`LevelsBand.tsx`): a rail of the levels from the Lean down to the exposition, each with
  its first page, who it is for, how much of the graph it keeps and its links, beside the
  main theorem's real argument. Pointing at a level closes the drawing up to the records
  that level discusses. A paper can skip a step, so two kept records stay joined through
  any skipped records between them; the drawing is that paper's own narrower graph. Every
  tile opens that step in Compare. The rail is sticky because the drawing runs longer.
  This band replaces three that said the same thing (the shelf of papers, the layers and
  a still drawing), and keeps the `papers` anchor. After it come what was asked and proved;
  the mathematics of the proof, in full, with the exposition's two figures; what follows;
  what has been checked, with the outcomes by kind in a table; and where the material
  comes from. The footer names Will Cook and Plectis, then lists his other websites.
- **The mathematical prose follows the papers.** Every claim, hypothesis and attribution on
  the page is one the papers state (see the comment at the top of `src/home/FrontPage.tsx`),
  and mathematical prose is set in the serif. Every number from the edition is computed.
- **Who made the site.** The About page ends with it: names and addresses come from his
  own pages (`src/app/author.ts`); websites and films come from the family registry
  (`src/app/family.json`), and a film without a YouTube address is shown in preparation,
  never linked.
- **The family's parts.** The header's lockup (the Plectis plait to the home page, a rule,
  then the rising-graph mark and "Lean Exposition"), the film slots and the footer's sister
  sites are the markup of the family contract, styled by `src/styles/family.css`, an
  unchanged copy, through the `--fam-*` names in `tokens.css`. Focus on them is amber, as
  everywhere here; under the pointer their links turn ink, like the site's own.
- The PDFs are served from the repository's own renders under `pdf/`, with page counts read
  from the files at build time (`vite.config.ts`), and open in a new tab. The rail's pictures
  are the PDFs' first pages (`scripts/render-paper-pages.py`); a picture that no longer
  matches its PDF is not shown.

## The levels and the data behind them

The build reads the authored alignment (`docs/record-alignment.md`) once and ships one line
per record, `virtual:record-index`, so tile titles and level marks are there at first paint.
The full alignment, the Lean index and the Lean modules are on-demand files: nothing about
Lean touches the startup path.

## Inspector

Selecting a record or a step opens the inspector: a full-height reading column
(`--panel-w`) on the right on desktop, a sheet on phones. Its first screen
answers the reader's question:

- **Record:** identity (kind, source, status) → title → section jumps
  (Explanation · Statement · Argument · Sources & checks) → an actual passage
  from the chosen account, with its authored treatment ("explains it", "states
  it") → the recorded statement, verbatim, with its scope → direct relations
  and traces → source and checks.
- **Step:** the relation in words ("*Consumer* uses *prerequisite*", with its
  type) → for an applied theorem, the objects held fixed, each premise and its
  recorded supplier, and what is still assumed → the recorded explanation →
  related passages in each account.

On phones the sheet peeks with the title and two actions; reading it opens a
full-screen view that holds focus until it is closed, and closing returns focus
to whatever opened it.

## Motion

| Change | Behaviour | Time |
| --- | --- | --- |
| Hover or focus | Colour and outline only | `--t-hover` 120ms |
| Inspector, popover, sheet | Fade and at most 8px travel; content present at once | `--t-reveal` 180ms |
| Account or treatment switch | Crossfade of the changed text only | `--t-state` 160ms |
| Unfold or fold | Staged so that two maps never show through each other: leaving records and lines fade where they are within 120ms; the records that stay and the camera move together; arriving records fade in at their final places over the last part of the move | `--t-unfold` 360ms |
| Drawing or folding a card's lineage (pointer resting on it) | As an unfold or fold, with the card under the pointer held still on screen; added records end at half strength. The camera does not move | `--t-unfold` 360ms |
| Opening a card (a click) | Its whole lineage unfolds at full strength, and the camera frames the card with all of it in the canvas the inspector leaves, zooming out or in as far as that needs; a click on the empty map, or closing the selection, puts back the unfolding and camera from before the first card was opened | As an unfold or fold, with the camera on a smooth-zoom path |
| Pointing at a passage mark or an inspector row on the map page (after 180ms) | Opens the routes to that passage's records and frames them with the passage outline; another mark moves straight to its records; 250ms after the pointer leaves, the unfolding and camera from before come back, unless the reader moved the map or opened something | As an unfold or fold |
| Following a passage (map beside the paper) | As an unfold or fold, with the camera on a smooth-zoom path whose time grows with its travel | 450–900ms |
| Camera correction | Only as far as needed; never after an unrelated reflow | `--t-camera` 320ms |
| Lighting a route | Spreads from the selected record, one rank after another, pattern kept | ≤ `--t-trace` 520ms |
| Card ↔ compact ↔ mark | Crossfade as the scale crosses a threshold | 160ms |
| Back to a remembered view | Restore at once | 0 |

Easing is `--ease-out` for things arriving and `--ease-move` for things moving.
No spring bounce, no parallax, no animated status. Hover and focus never change
the layout, the URL or anything saved.

## Wording

The interface names relations and states by what was recorded.

| Say | Not |
| --- | --- |
| Recorded support | helps prove |
| Explicit assumption | — |
| Recorded Lean correspondence | the same statement in Lean |
| Related passages; Both records linked; Linked to the conclusion only | Where the accounts make this step |
| No passage is linked directly to this record | the account does not discuss it |
| Not among the records this account uses (in full: no passage in this account is linked to this record, and the recorded argument for its main results does not use it) | no result in this account uses it; outside this account's recorded selection |
| Across all 129 records (the count computed from the edition) | (an unlabelled count) |
| No successful Comparator result is recorded | no Comparator run is recorded (when one failed) |
| Review record: passed | independently reviewed |
| One recorded route from Full support | (a breadcrumb that looks like history) |
| No recorded inputs | starting point, axiom (a record boundary is not a foundation) |
| Back to Exposition §5.3 | Back (when the origin is a graph path) |

Most recorded checks are "not run"; no warrant has been independently reviewed.
Never suggest otherwise with colour, icons or wording.

## Layout and breakpoints

| Width | Map | Inspector | Reader |
| --- | --- | --- | --- |
| ≥ 1360px | Canvas with bar; dock collapsed to a bar | Right column, full height | Outline, paper, optional inspector |
| 1100–1359px | Canvas | Right column | Outline or inspector beside the paper |
| 901–1099px | Canvas | Right column | Paper; sections and passage context as sheets |
| 701–900px | Canvas | Bottom sheet, full-screen reading | Paper; sections and passage context as sheets |
| ≤ 700px | Outline list by default; map on request | Bottom sheet, full-screen reading | Paper only, bottom bar |

Phones use 16px gutters and `--target` (44px) for primary touch targets. No
ordinary page scrolls sideways; a wide formula scrolls inside its own box with a
visible cue.

## Accessibility

- Every control has a name that does not depend on visible responsive text.
- Closing anything returns focus to what opened it.
- Desktop inspectors are not modal. A phone's full-screen view is a modal dialog
  with an inert background.
- Relation type, coverage and outcome are always in words as well as pattern,
  shape or colour.
- `prefers-reduced-motion` is read live, not once.

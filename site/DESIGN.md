# Design system

The site is a reading instrument for one mathematical result. Its job is to let
someone see the goal, follow any step down to where it starts, read how each
account explains that step, and check what was recorded about it. This file
holds the rules every page follows. The values live in
[`src/styles/tokens.css`](src/styles/tokens.css); the shared classes live in
[`src/styles/base.css`](src/styles/base.css).

## Principles

1. **Reading size is fixed.** Text a reader must read never renders below 13px on
   screen, and a record's title never below 14px. When there is more than fits,
   change the representation (a mark, a count, a list), never shrink the prose.
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
| `0.5 ≤ k < 0.8` | **Compact** | Title only, at a constant 13px on screen, source square |
| `k < 0.5` | **Mark** | A tile in its source colour, no text |

In compact and mark form, the goal, the selected record and the hovered record
carry labels drawn at screen size, so the reader always knows where they are.
**Steps** is the reading mode: it opens at `k = 1` and keeps the opened record
in view. **Overview** fits the whole goal and uses marks. Opening a mark returns
to Steps around it. When Steps cannot fit every input of the opened record,
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
| Unfold or fold | Records grow from the opened card; one synchronised move of cards, lines and camera | `--t-unfold` 360ms |
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

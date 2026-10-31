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
   The titles on the map's tiles are labels: they shrink to 11px before they are
   cut, the camera stops where a tile can still hold them, and no tile is ever empty.
2. **One channel per meaning.** Each visual variable answers one question:

   | Question | Channel |
   | --- | --- |
   | Where does this record come from? | A small square in its source colour, beside the source's name on a card and in the corner of a tile. |
   | What kind of record is it? | A word in small capitals: CLAIM, ASSUMPTION, LEAN DECLARATION, MAIN RESULT. Assumptions alone get a dashed border. |
   | How does a step use it? | The line's colour and pattern together, with the relation named in words wherever it is inspected. |
   | How does an account treat it? | A shape and a word: ● own passage, ○ used without a passage of its own, ⊟ outside the account's selection. |
   | What does the Lean hold of it? | The card's shape (a box for a definition, a rounded shape for a result) and a soft fill: green when it is in Lean, much paler for a part of it, plain for none. The sheet and the outline carry the same fill and say it in words, so nothing rests on the colour alone. |
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

### Two representations, and a floor

The camera never shrinks a card's prose below reading size, and every record
always shows words. There are no blank tiles and no marks without text.

| Scale | Representation | Shows |
| --- | --- | --- |
| `k ≥ 0.8` in Step by step | **Card** | Title, inputs control, the kind word where the record is not a claim |
| `k < 0.8` in Step by step | **Tile** | Title from 13px down to 11px on screen, and nothing else |
| Whole argument, at every scale | **Tile** in the dense layout | The same, 190×46 world pixels (60 tall under a paper's lens, for the section) |

A tile uses the record's short title (`shortTitle`, from the build-time record
index) and falls back to its label. A title that still cannot fit is cut after a
whole word. Under the pointer or keyboard focus, a tile's full title and its Lean mark in
words show in the strip under the canvas. A tile shows nothing of the card beneath it.

**The floor.** Step by step stops at `k = 0.5`, the side pane at `0.6`, and Whole argument at
`11/13`, the scale at which 13px world text is 11px on screen. If the drawing is
then taller or wider than the canvas it pans; it does not shrink further. The
dense layout is chosen so that the 30 records of the Full support argument fit a
1440×640 canvas at that floor.

**Whole argument** is the first view: every record named, with the main theorem
and its Lean open beside it, because that is what a reader came to see. **Step by
step** opens at `k = 1` with the plate and the first row and shows what is unfolded;
Whole argument draws every branch without changing what is unfolded, so Step by step
comes back exactly as it was.

**Lean fills** come from the alignment and from nothing else (`model/leanStatus.ts`), and read
as a blueprint does, with no key needed. `states` and `contains` give the green fill, and so does
`defines` on a definition, which takes a box and has nothing to prove. `part`, and `proof` alone
(a Lean proof carrying the step in a different form), give the much paler fill. A record with no
declaration stays the plain card. "Proved" means a theorem or lemma in OpenAI's source with no
`sorry` in its text, which all 162 rows keep today; whether a build ran stays in each record's
checks. The sheet says the status in a plain sentence for readers who cannot tell the greens
apart. `--lean-fill`, `--lean-fill-part` and `--lean-fill-line` are chosen per scheme: ink keeps
at least 7:1 on both fills, `--ink-3` at least 3.5:1, and the three states stay apart in OKLab.
A receding card keeps its fill, so it never reads as having no Lean. Amber still means what you
are looking at, and the reader pane's trail uses no tint. The relations ship in the record
index, so the fills are there at first paint.

**The strip** under the canvas is a row of its own: the key a newcomer needs, always on the
page, and Fit. What the pointer rests on is named there for that moment, in place of the key,
so a caption can never cover a target, and it goes when the pointer goes.

**The Lean graph** is a secondary view (`?v=lean`), a sidecar for those who want it; the argument
stays the default. It draws the results (theorems and lemmas) behind the argument's steps with the
same engine (`model/leanGraph.ts`, `map/useLeanGraph.ts`), one card each, 53 for Full support.
The 12 definitions nearly every result uses are a list of plain titles under the drawing, because
as cards they bury the shape of the proof. It loads on first use, about 120 modules of 349.

Nothing opens off screen. Where the whole graph can be read at once (a monitor), it opens whole.
Otherwise it opens on the part around the step you came from: that step's results, what uses them
and what they use. Clicking a card moves that part to it. Fit shows every result, and "Around this
step" returns. The sheet stays closed until a declaration is chosen, so the drawing has the width,
and the drawing refits while the reader has not moved it. A title has one size in the drawing and
zooms with it (`worldText`), so it is never cut; at Fit on a laptop the whole is a shape to read
closer in, with the title in the strip under the pointer.

A card shows plain words (`model/declTitle.ts`): the authored title, then the short title of the
step that links it most directly, then the dictionary's words, and the raw name only where none
exists. The raw name is small under the sheet's heading and in the code. A solid line is a use in
the proof, a dashed line a use in the statement, a thin dotted line a use reached only through
helpers no step links; the caption names them. Half the declarations are joined only through
helpers, so they stay collapsed rather than absent. The lines come from `uses` in the Lean index
and say so on the strip: a text scan today, and the compiler's report when `dependency_source`
says `elaborated`. Statement against proof is whether the name is written in the statement's
lines. A use a longer chain already says is not drawn, and the Key counts those. What nothing drawn
uses hangs from the goal by a dashed line, which says only that the argument links it. Under a paper's lens the
numbers count declarations, results and definitions together, and the line above the lens says so. A card opens the sheet at that
declaration. Helpers with no plain title stay collapsed behind their line, which says how many
there are.

**The goal's plate** is at most 200px tall: the title, one sentence of the theorem
and the ways on. The full theorem and its Lean are in the record sheet.

**Navigation.** Two fingers on a trackpad and a wheel pan. A pinch, or Ctrl or ⌘
with the wheel, zooms about the pointer; + and − zoom too. Shift with an arrow key pans, and
0 or Fit shows the whole drawing as large as it fits. Dragging pans from
anywhere, cards included, and nothing on the canvas selects as text; a press that
moves less than 5px is a click. The camera cannot lose the drawing (`clampView`): one larger
than the canvas always fills it but for 40% on one side, one that fits can move a little and
never more than half of it leaves, and a lens, a sheet or a smaller window that leaves the camera
past the new edge brings it back. ↑ goes to the result that uses the selected record, ↓ to its first input
(opening it if it is folded), ← and → among the inputs beside it; each move keeps
the selection on screen by the smallest pan. Enter opens the selected record's
inputs and Esc clears the selection. When a card cannot show every input,
chips at the canvas edge say how many records lie beyond it.

**The level lens.** Plain words: All, Long record, Short paper, Exposition, each with the
number of steps of this argument it uses, the chosen one underlined, counted from the records its own passages
discuss (`mapped_*` roles; every paper also lists the prerequisites of those
records, so bare membership would count all of them). A small line above the lens says
what its numbers count. The levels are not nested: the exposition uses records
the short paper does not, so nothing may say one contains another. Choosing a
level is the unfold motion: records outside it leave, and the rest close up. A
line then joins a record to the nearest records it uses in that paper, and may pass
over records the paper leaves out (`lensArgument`); such a line is a reading aid,
not a recorded relation, opens the record that uses rather than a step, and the
sentence says so. What is unfolded does not change.

**Paper walk.** Under a paper's lens each record carries the section where that
paper first discusses it, and the foot bar steps through the paper's passages on
this argument in reading order: ◀ ▶ or [ ], the section's name, and "Read here".
Each step lights that passage's records and pans only as far as they need.

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
  several results use is drawn beside each of them. "Used by N" says how many there
  are, and where Lean fills are off a band along a clone's foot marks the copies. All copies select,
  hover and light as one record; counts count records, not copies.

Records that have inputs of their own are never copied.

### Cards

- Raised surface, `--card-border`, `--radius-card`, `--card-shadow`.
- A card says what the record is and nothing else: its title, its inputs control and,
  for a record that is not a claim, the kind word. Source, level and Lean belong to the
  record's sheet. Marks repeated on nearly every card carry no information, so they
  do not appear. An assumption reads as a line of words with a dotted rule.
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
- **Pointing at a card lights its direct lines**, and nothing else: no ghost
  records, no camera, nothing that covers another card.
- **Clicking a card selects it.** The sheet opens, its direct inputs and one drawn
  route up to the goal light, everything else recedes, and the camera pans only as
  far as it takes to show the card and its direct neighbours at the current scale;
  when they do not fit, its inputs; when those do not, the card alone. A click never
  changes the scale and never unfolds. The inputs control opens one level. "Open
  everything below" is an action in the sheet, and holds the card still on screen.
  A click on the empty map clears the selection.

### The map header

- **Title block.** "Argument for" in small sans over the main result's full title
  in serif, which opens the menu of main results, each with the accounts that
  state it. Below 1100px it shows the short name ("Full support").
- **On the right:** the level lens, the view switch (Whole argument, Step by step, Outline,
  Lean graph; pressing the current view frames it again) and Key.
- **The line under the header.** Under a paper's lens, one sentence on how much of the
  argument the level uses and what a line means. The strip gives the key. Key says the rest
  in words, lists the links the map leaves out, gives the keys and "How the map is
  drawn".
- **The foot bar.** Only when it has something to do, in a row of its own under the
  canvas so nothing in it can cover a card: the paper walk on the left under a paper's
  lens, and in Step by step "Show all branches" and "Collapse branches" on the right.
  Show all keeps the view, the camera and the cards' order, and holds the selection
  still; Collapse returns exactly the unfolding, order and camera from before. A button
  that would change nothing is disabled and says why.
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
- **The first action is reading a paper.** The two buttons are "Read the short paper" and
  "Read the exposition". Below them, quieter, are Theorem 1 with its Lean open (an address
  built from the alignment, `heroLinks`), Compare and the map. The graph and the Lean come
  along beside the paper; they are never the way in.
- **A real still follows the films.** `public/stills/` holds a capture of Theorem 1 open on its
  Lean, in both schemes, taken from a production build at 1440x790. Retake it when the reader
  changes visibly (`loading="lazy"`, so the scheme not in use is never fetched).
- **Every count is read at build time.** `src/home/siteFacts.ts` reads the edition, the
  reference tables, the published observation and the vendored Lean, and hands the result to
  the pages as `virtual:site-facts` and to `llms.txt`. A file that is absent gives a null and
  the sentence is left out.
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

Selecting a record or a step opens the record sheet: a full-height reading column
(`--panel-w`) on the right on desktop, a sheet on phones. It is the drill-down from
a card, and its first screen answers "what is this, and how is it stated?":

- **Record:** kind, source and title, the Lean mark in words and "Compare"; then, under five
  short jumps (Statement, Lean, Papers, Uses, Checks), **the statement** quoted from the
  strongest slice with "Read in context"; **In Lean**, a `LeanBlock` for each linked
  declaration with its relation, exact lines and `Proof ▶`; **In the papers**,
  tabs for the long record, the short paper and the exposition, each with that
  paper's exact slices as the reader typesets them and "Read in context", then the
  plain recorded statement behind a quiet "As recorded" line; **Uses and used by**,
  rows that move the selection, with "Open everything below"; assumptions; sources
  and checks. The statement and the start of the Lean are on the first screen at 1280×690.
  Where the alignment has no slices, the record's passages stand in. It starts on the lens's
  paper. A record with no Lean says so and lists what it rests on, with each input's mark.
- **Declaration:** the same sheet at one Lean name. Every name in a sheet
  walks here in place, and each walk is one history entry (`?d=`).
- **Step:** the relation in words ("*Consumer* uses *prerequisite*", with its
  type) → the chain of Lean names between the two records, each a walk, or a plain sentence
  that none was found and what that does not show → for an applied theorem, the objects held fixed, each premise and its
  recorded supplier, and what is still assumed → the recorded explanation →
  related passages in each account.

On phones the sheet peeks with the title and two actions; reading it opens a
full-screen view that holds focus until it is closed, and closing returns focus
to whatever opened it.

## Compare

"/compare" is the table the site is built on. Rows are the steps of the argument and columns
are the levels, so the words side by side are always about the same thing. A cell is that
step's exact statement at that level, typeset as the reader typesets it, with "Read in
context" leading into the paper or the Lean. Whole passages are never paired: two passages
that share a record can be making different arguments, and side by side they look like
unrelated text.

- **All steps** is the first view. The levels are four pressable words, and the width sets
  how many start on: the Lean, the short paper and the exposition on a laptop, all four on a
  monitor. The rows are the steps every level shown has, so each row compares something, with
  the rest one link away. The main result comes first, then the first paper's reading order,
  so its column reads down as the paper does. A record for a Lean declaration is not a row,
  because the Lean has a column. Two steps whose cells start with the same words share a row.
  A cell shows the strongest thing that level says, and a bare mention does not count. A row's
  title stays in view while its cells are read; j and k move between rows. A Lean cell lights
  the exact lines, and a name in the code walks in place with a named way back
  (`WalkingLean.tsx`); the walk stays with the history entry. "Read in context" lands on the
  exact statement and pins the tie.
- **One step** is one row in full, reached from a row's title. The rail lists the steps of the
  argument. Each level gets a scrolling column with everything it says about the step, and
  "Uses" and "Used by" walk the argument in either direction. On a phone the levels stack,
  with tabs to jump between them.

Going between the two keeps the step. Pressing a level keeps the row in view. A formula that
is too wide shrinks, then breaks at a relation sign; a cases or aligned block never breaks,
because its rows and brace would come apart, so it keeps its shape and scrolls in its own box
with a cue and Expand.

## The Lean index

"/lean" is the index at the back of the book: OpenAI's Lean at a pinned commit, in two proof
trees, for anyone who wants the files and declarations themselves. It is quiet and last in the
top bar, and its first lines send a reader to a paper. A plain title comes first wherever the
alignment's `names` has one, as the heading of a declaration's page, in lists and on tiles, with
the Lean name small beside it. A pointed name is read in the top bar's free space, which is
empty at rest, so nothing on the page waits for a hover and pointing moves nothing. The first screen says what the tree is and what was checked, in the words of the Checks page, and
offers `full_support`, `IsMinimizer`, `value_consequences`, the Comparator challenge file and the
declarations the papers rest on, beside the main theorem itself. The folders stay on the left
with a find box: Enter opens the first result, which is the exact name, then names that start
with what was typed, then names that hold it (`lean/find.ts`).

Every declaration has its own address (`?m=&d=`). Its page says first where the papers state it,
quoted with "Read in context", then the Lean, facing it from 880px of column width; then what
uses it and what it uses, split into its statement and its proof. Eight or fewer neighbours are
drawn with lines; more are listed, because a fan of lines into one point says nothing. A module
page lists its declarations in source order and shows the way up; a folder has its own page.

**`LeanBlock`** is the one view of a declaration on every page: signature first, `Proof ▶` for the
rest, `source` to the commit-pinned line range, axioms and `sorry` said once with where the
statement comes from (Lean's report, or a text scan, by name). Every identifier is a link: to its
declaration's page, or to Mathlib's search page, because a name written after `open` is not a full
name and doc-gen's `find` address would give a 404. `onName` makes a click walk in place. `lines`
lights exact lines and may open the proof and move the nearest scroller; `pointed` lights without
moving anything; `quietLines` keeps `lines` from moving the scroller. `compact fill` works at
340px tall.

**The reading line.** Pointing at a name or focusing it shows its signature, its docstring and the
paper's notation in one row of fixed height, at the foot of the block or in the host's
`previewSlot`, so pointing moves nothing and covers nothing. A signature printed by Lean replaces
the source text when an edition has one.

The dependency edges come from the source text and say so (`dependency_source`,
`dependency_note`), because a text parser can miss or misattribute a use. A link from a record to
a declaration is a reading link, and the page never calls two statements equivalent.

## Search

"/" opens search everywhere. It is built on the first query, never at startup, from the names,
the alignment and the three papers' Markdown, cut at blank lines with exact bytes. An exact
declaration name comes before everything; Enter opens the first result. A result says what it
is and where it stands. A hit in a paper goes there as an ordinary entry, with Back; a Lean hit
opens in the page that registered with `hostLean` (`lean/walk.ts`), and otherwise on its own
page.

## The reader

A reader reads the paper, as they always have. The graph is a sidecar: full height on the
page facing the paper, it comes along as they scroll, and it can be closed. One line under
it names what is lit in plain words and says whether it has Lean. Clicking a statement or a
highlighted card opens the raw Lean, which rises from the card over the graph and leaves a band
of it above, or stands beside it from 860px of page. It is headed by the step's plain title
with the raw name small beside it, then a link to where each paper states it, and Compare. The
graph underneath keeps its size and camera; only a transform lifts the card clear, so closing
leaves it exactly as it was. A handle sets the height, and it is remembered.

The Lean closed is the default. A reader who wants it beside their reading can choose "Keep the
Lean open" or draw the handle up from the foot of the graph; it then follows the text, and that
is remembered in this browser. Below 1280px the same page is a sheet opened on demand. It is
never modal: the paper stays where it is and can still be scrolled.

Four verbs run the page.

- **Follow.** One reading line, 30% of the way down the paper, picks the statement under
  it, or the nearest within a third of the page, the one just read winning a near tie.
  Its tick in the margin lights at once, and nothing touches the words: the paper reads as a
  paper. Once it has held the line for 200ms, and the page is no longer flying past, its card
  lights and the line under the graph names it. The address keeps up by replacing the entry once the reader stops.
- **Point.** A statement under the pointer or focus takes a soft wash and its card lights
  at once; after a 150ms dwell the line under the graph names it, and a Lean kept open
  previews it. Moving away restores. A card does the same in the other direction. An untied
  paragraph names its passage's records in that line and moves nothing. Pointing never
  pushes history.
- **Open.** A click pins and raises the Lean, and only then does the statement take the full
  highlighter. A step with no Lean does not open: the line under the graph says so. A click is one history entry, `?n=<record>&l=<slice>`,
  and the paper does not move. A card pins too, and the paper goes to the statement while the
  graph stays. A name in the Lean walks in place, as its own entry. A pin ends when the reader
  scrolls the statement away, on Escape, or on Back. A drag or a double click that selects text
  never pins.
- **Back.** The browser's own, named in the strip.

`j` and `k` or the strip's arrows step between statements, Enter pins and Escape releases.
Where several statements open on the same words, a step stops there once, and the Lean
page lists the others under "The same words also tie to".

Scrolling writes attributes and signals, never React state on the page (`page/statements.ts`,
`page/signal.ts`). Marks reach the text as zero-width private-use characters put in before
parsing and turned into `.tie` spans once a part's HTML is whole (`ties.ts`); with every
segment marked, each paper's HTML is byte for byte the same once the spans are taken out,
and a test holds it there. A statement tick sits in the left margin, darker where the
step has Lean, drawn from where the words actually fell. The thread crosses only the empty
gutter and goes whenever an end leaves the screen.

The outline counts the statements with Lean in each section, and searches the paper's
text, including what has not rendered yet. Up to 1500px it stands on the right page, where it
covers no text. A passage's steps and links open from "This passage" under the graph, and the
first screen's one instruction sits in the strip. On a phone there is one row of chrome, which
goes while reading down and comes back going up, and a tapped statement moves above the sheet.

### References

Every reference in the three papers is a real link, 639 in all: 117 in the short paper, 442
in the long record and 80 in the exposition. What each one points to was decided by reading
its sentence and is kept as data, one table per paper, in
`examples/qaoa-sk/alignment/references-<paper>.json`, keyed by byte range. A pattern cannot
decide it. Most numbered results these papers name belong to OpenAI's manuscripts or to other
cited papers, whose numbers collide with the papers' own: "(6.1)" in the long record is its own
equation in one sentence and Basso et al.'s in another. The rows that stay plain (126, such as
the locators inside a reference-list entry) are in the table too, with the reason.

| Kind | Short | Long | Exposition | A click |
| --- | --- | --- | --- | --- |
| Citation, with its locator | 61 | 212 | 35 | Opens the list entry and the locator in place, with "Open source" |
| Result, equation or figure of this paper | 39 | 23 | 10 | Opens it in place, typeset as in the paper, with "Go to Lemma 2" and "See its Lean" where it has Lean |
| Result of another source | 9 | 53 | 1 | Opens in place, saying whose numbering it is, with "Open source" |
| Section of this paper | 7 | 154 | 34 | Jumps, with a Back |
| Section of the long record | 1 | 0 | 0 | Opens beside the paper |

Pointing or focusing shows the target on the right page after 150ms, in place of the Lean until
the pointer leaves. It covers no text and moves nothing in the paper. An inset is part of the page: it pushes only what is below it, the reader's line stays
where it is, and Escape, a second click or Close puts the page back. Opening one adds no history;
a jump does, and the Back on the strip names the place left, "Back to Short paper §2". A reference
inside a tied statement is a link of its own, and a click anywhere else in the statement pins it as
usual. Ids are stable: `thm-1`, `lem-2`, `prop-4.1`, `proof-thm-1`, `eq-4.1`, `fig-1`.

Text stays byte for byte: marks go in at render time, and `tests/references.test.ts` checks every
row against the paper's bytes and the rendered page, and fails on a candidate no row has decided. A
row whose words have moved gives no link at all, because a wrong link is worse than none.

## Checks

"/checks" opens with what a Lean reader asks first (`Standing.tsx`): what compiled, at which
commit and toolchain; the statement; the axioms; any `sorry`; what Comparator has and has not
done; where the dependency lines come from; and what people or agents read rather than a
machine. Each row sets what ran beside what that leaves open, and names the checker. When the
index's `dependency_source` becomes `elaborated`, the dependency row says so by itself. Then
comes a table by kind of check with the number passed, failed, unavailable and not run in
columns of their own. Outcomes are never merged across kinds. Only a recorded failure is coloured, and there is no percentage or
success badge. With a record chosen (`?n=`), the page starts with the checks attached to it.

## Going back

From anywhere on the site a reader can go back to exactly where they were: the
same page, scroll position, selected card, map camera and lens, open tab and panel
scroll. Back, Forward and reload all do this, and the visible control is the
browser's own Back, so the two cannot disagree.

The URL holds what is selected and can be shared. The history entry holds how it
was being looked at: scroll, tab, camera, a filter typed. `app/trail.ts` keeps one
record per entry, in `history.state` and mirrored in sessionStorage, because on a
pop `history.state` has already moved on and the entry being left can only be
written through the mirror.

| Action | History |
|---|---|
| The page, a pinned record, a passage, a Lean declaration or a search query changes | One new entry, with an address |
| A tab, the scroll, the camera or a filter changes | No entry; the current one is rewritten |
| Following and pointing | No entry |

`history.state` can be lost: a redirect drops it, and Firefox drops it on a plain
reload. So every address the site writes is the exact form the host serves, with
the slash after a page's directory, and a reload never redirects. And sessionStorage
keeps a copy of each entry under its key, with who it is and which entry the tab is
on, so a load that finds no state looks itself up and carries on as the same entry.
When the browser calls such a load a new navigation, it counts as a reload only
within 30 seconds of leaving and at the same address. Every read and write of
sessionStorage may fail, and the page then works from `history.state` and memory.

The control reads "Back to Short paper §1", "Back to the map" or "Back to
`minimizer_contact`". It sits in the top bar on every page but the reader, where it
is in the reader's strip, and takes the place of the site's name on a phone. It
appears only when there is somewhere in this site to go back to. The key is `[`;
Alt and Left is the browser's own. A page names itself once with `namePlace`, so no
link needs special handling.

A place in a paper names the part and the block under the reading line, and never a
raw page position, because placeholders above it change height as parts render. It
holds to within half a pixel, as rounding let a save and restore creep by one.
`restoreScroll` is the one way a place is put back, for the window and every inner
scroller: it keeps setting the place while content arrives, for up to five seconds,
and stops the moment the reader touches the wheel, the keyboard or the screen.

A step between Lean names is one entry through `walkEntry`, which adds `&d=` and
`&dm=` on a page that shows Lean in place and goes to the declaration's own page
otherwise.

## Motion

| Change | Behaviour | Time |
| --- | --- | --- |
| Hover or focus | Colour and outline only | `--t-hover` 120ms |
| Inspector, popover, sheet | Fade and at most 8px travel; content present at once | `--t-reveal` 180ms |
| Account or treatment switch | Crossfade of the changed text only | `--t-state` 160ms |
| Unfold or fold | Staged so that two maps never show through each other: leaving records and lines fade where they are within 120ms; the records that stay and the camera move together; arriving records fade in at their final places over the last part of the move | `--t-unfold` 360ms |
| Selecting a card (a click or an arrow key) | The smallest pan, at the same scale | `--t-camera` 320ms |
| Choosing a level | As an unfold or fold: leaving records fade, the rest close up, the whole argument refits | `--t-unfold` 360ms |
| Show all, collapse, open everything below | As an unfold or fold, with the selected card (else the goal) held still on screen | `--t-unfold` 360ms |
| Pointing at an inspector row | Tints that record if it is drawn; nothing unfolds or moves | `--t-hover` 120ms |
| Following a passage (map beside the paper) | As an unfold or fold, with the camera on a smooth-zoom path whose time grows with its travel | 450–900ms |
| Camera correction | Only as far as needed; never after an unrelated reflow | `--t-camera` 320ms |
| Lighting a route | Spreads from the selected record, one rank after another, pattern kept | ≤ `--t-trace` 520ms |
| Card ↔ tile | The tile's title fades in as the scale crosses the threshold; the card's text goes at once | 160ms |
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

## Loading

A page should appear as soon as its data has landed, and nothing should wait in line behind
something else.

- **Code and data start together.** Each route's HTML names its chunks, everything they
  import, their stylesheets and the edition files that route asks for first (`routeCode` and
  `routeData` in `vite.config.ts`). The file names are hashed, so the build reads them from the
  edition's own index. Without these links a page's code would start only after its data had
  arrived.
- **Code that has arrived shows at once.** `lazy()` suspends for a tick even for a finished
  import, and after a Suspense fallback React holds the next reveal back for about 300ms.
  That delay was most of the wait on every page. Pages, the Lean viewer, the typesetter and
  the reader's map pane go through `code()` (`src/app/code.ts`), which answers at once when the
  module is here, and `main.tsx` starts the opened page's code before anything renders.
- **Every preload must be used.** A link to a file nothing fetches is a wasted download, and a
  stylesheet preload needs `crossorigin` to match the request Vite makes for it. After
  changing what a route loads, check the console for preload warnings at laptop and phone width.

## Layout and breakpoints

| Width | Map | Inspector | Reader |
| --- | --- | --- | --- |
| ≥ 1501px | Canvas with foot bar | Right column, full height | Outline, paper, map |
| 1280–1500px | Canvas with foot bar | Right column | Paper and map; the outline as "Sections" |
| 1120–1279px | Canvas | Right column | Outline or inspector beside the paper; the right page as a sheet |
| 901–1119px | Canvas | Right column | Paper; sections and passage context as sheets; the right page as a side sheet |
| 701–900px | Canvas | Bottom sheet, full-screen reading | Paper; sections and passage context as sheets; the right page as a side sheet |
| ≤ 700px | Outline list by default; map on request | Bottom sheet, full-screen reading | Paper only, bottom bar; a tap opens the Lean in a bottom sheet |

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

# Reader design

This page is the design of the paper reader: what a reader sees, in what order, and why. It
merges five independent design reviews (cited below as packets 01 to 05) into one design, and
records each place they disagreed. The engine implements it for every paper; the Euler paper is
the first instance built to it. [The graph pane](graph-pane.md) remains the specification of the
drawing itself, and [the library architecture](library-architecture.md) of addresses and data.

## Who it is for

A mathematician who knows the theory, has the paper open, has never read Lean, and wants to
check the paper against its formalisation. Four jobs decide every choice below:

1. find which words of the paper the Lean states;
2. see what the Lean says about those words;
3. trust what the page claims, and see who is claiming it;
4. keep their place in the paper.

## Thesis

**The paper asks; the pane answers about exactly those words, and keeps answering until the
reader changes the question.** At every moment the page shows one subject: which words are
being examined, what they are linked to, and what that link establishes. Nothing else on the
page may compete with that sentence, and nothing may change it except an act of the reader.

Three rules follow, and the rest of this page applies them.

- **Scrolling changes what is followed. A click selects exact words. Only an explicit jump
  moves the paper.**
- **Each mark has one job.** Colour says topic. Amber says "you selected this". A line's style
  says which relation it records, and the key names it. No mark says whether a statement is proved, matched or
  reviewed; words say that, next to the name of who assessed it.
- **The page is still.** Nothing moves, fades or reflows unless the reader just did something,
  and then briefly.

## The order the eye takes

1. **The paper.** Serif text at its measure, the largest and calmest thing on the screen.
2. **The selected words.** A thick amber underline, an amber rule in the margin and a pale wash:
   the one loud mark on the paper.
3. **The subject band** at the head of the pane: the state ("Selected words", "Following the
   paper"), and the place in the paper. It stays put in both views and while the graph pans.
4. **The inspector**, in a fixed order (below): title and kind, the exact quotation, the
   comparison with its whole qualification, the reading note, the Lean statement, then the graph.
5. **Controls and navigation**, in the sans, at 14px, never amber.

## States

Four independent things describe the reader. Each has one owner in the code.

| Thing | Values | Changed by |
| --- | --- | --- |
| Reading place | the block under the reading line | scrolling; an explicit jump |
| Attention | Following, Selected | a click or Enter on linked words, a paragraph's margin control, a graph card or a Lean name selects; "Resume here" or Escape follows again |
| View | Lean, Graph | the two tabs; a control that names a view ("Open its Lean") |
| Presentation | open, collapsed | opening and closing the pane; on a phone, "Back to paper" |

### Following

The pane shows the linked passage under the reading line. The band says **Following the
paper** and "Changes as you scroll". The followed passage has a neutral ink tick in the margin
and no mark on its words. A paragraph with no link says so in words; the previous subject is
never left under a new heading without saying whose it is.

### Preview

Resting the pointer on linked words, or on a card in the graph, shows that item in the pane
under the label **Preview**. It changes nothing else: not the address, not the selection, not
the graph's centre, not the paper. Moving away restores what was there. While words are
selected, pointing at other words in the paper lights them and never replaces the selection's
quotation or comparison. Touch has no preview; a tap selects.

### Selected

A click, tap or Enter on linked words selects exactly those words. The band says **Selected
words** with their section, and the selection holds while the paper scrolls. Two actions sit in
the band, and they are different acts:

- **Resume here** lets go of the selection and follows the paper from where the reader now is.
  The paper does not move. Escape does the same.
- **Return to selected words** scrolls the paper back to the selection. The selection stays.

The browser's Back keeps its own meaning: the previous subject and place.

A graph card or a Lean name chosen in the pane is a **Selected declaration**. It has no words
in the paper unless the data records them, and the band says which.

### Selected paragraph

A reader can select by phrase and by paragraph. A paragraph is selected by its own control, never
by a click on its words. Each block of text that has links carries one small ring in the margin at
its first line, a real button named "Select this paragraph's links" (the same words show under the
pointer). A click on it, or Enter, selects the paragraph: the band says **Selected paragraph**, an
amber rule runs down the paragraph's whole height in the margin, and the pane lists every link in
the paragraph in the order of the text, each with its words whole and what they are linked to.
Choosing a row selects those words. A displayed formula that only continues a sentence is reached
through that sentence's paragraph and has no ring of its own.

A click on a paragraph's plain words does nothing but place the caret, as in any document. (The
earlier engine held the whole paragraph on such a click; packet 01 found that a click between two
lines could select something the reader never pointed at.)

### Deep links

An address that names a phrase (`/@id`), a numbered result or a declaration opens Selected,
with the paper at those words. Such an arrival is an explicit jump, so the paper may move.

## The subject band

One strip under the pane's tabs, in both views, outside the graph's canvas. 56px tall on one
line at pane widths from 520px; it may wrap to two lines below that, and its height then
depends on the pane's width alone, never on the state, so a change of state reflows nothing.

- Left: the state in the sans at 14px, semibold; then the place ("in §5.6", "in the opening")
  as a control that returns to it.
- Right: the state's actions as quiet buttons: "Return to selected words" and "Resume here" when
  Selected; nothing when Following or in a Preview.
- A selection puts the selection's amber rule on the band's left edge, the same mark the selected
  words carry in the paper's margin. The band is not coloured by topic and carries no verdict.
- The place control and both buttons show the amber focus ring when reached by keyboard.
- Each change of state (Following, Preview, Selected words, Selected paragraph, Selected
  declaration) is said once through a polite live region in the band. A new subject within one
  state is not announced, so scrolling does not read every passage aloud.

## The inspector

The same component fills the Lean view and sits under the drawing in the Graph view. Its order
is fixed, and is the order of the questions a reader asks.

1. **Title, kind and identity.** The plain title in the serif at 20px. Under it one quiet
   line: the kind in words ("Lean theorem", "Lean definition", "Paper result"), the exact Lean
   name in the mono, and the topic's name with its swatch. A definition is called a definition
   before anything is said about how it compares.
2. **The exact quotation.** The selected words as the paper sets them, in the serif at 17px,
   with an amber rule at their left: the same mark as in the paper's margin. Never clamped or
   elided; a long quotation scrolls with the inspector, not inside a box of its own.
3. **What these words say**, where the paper's data has it: three to five sentences in the
   paper's notation, labelled "AI-drafted", with the sources it rests on behind one disclosure.
   Where part of it is not settled from the sources, that part is said plainly under it ("Not
   settled from the sources: ..."), with an ink rule and never the colour of a failure.
4. **The comparison, with its whole qualification.** The verdict in words, then every sentence
   of qualification the data carries, whatever the verdict, then "AI-assessed". A verdict of
   *same* shows its note too. Where the data says whether the difference bears on the paper's
   main result, the verdict ends with that as a question and its answer: "Does this affect
   Theorem 1.1? No. This is a difference of convention." and the recorded line of why. An absent comparison says "Not assessed. No comparison of these
   words with this Lean is recorded."; a withheld one gives the recorded reason. A link that
   holds several overlapping phrases shows each phrase's own comparison, each headed by that
   phrase's opening words.
   Neither is drawn as agreement. One line under it opens the legend (below).
5. **The reading note**, labelled "AI-drafted": what the formal statement says, in the
   paper's notation. Sans, 16px on a 24px line, at most 38rem wide however wide the pane.
6. **Conventions used here**, where the paper has a glossary of formal conventions: each as a
   disclosure that states the convention as mathematics, and how it differs from the paper's
   where the glossary says.
7. **The formal statement**: the Lean, mono at 14px on a 21px line, with the tied lines lit by
   a narrow amber rule and a pale wash, and its Comparator line in the Comparator's own words.
8. **The graph**: in the Lean view a link at the foot, "See what this uses, and what uses it,
   in the graph"; in the Graph view the drawing itself, above.

Several declarations linked to the same words are a row of buttons between 1 and 2; choosing
one changes 4 to 8 and never the quotation or what the words say.

### The legend

A disclosure under every comparison, and at the foot of "How to read the Lean": "What do these
words mean?" It gives one sentence each, in mathematical terms, and writes them only once it
is opened, so a closed legend never sets a verdict's name beside a different comparison.

| Words on the card | Meaning |
| --- | --- |
| Lean states the same as this phrase | The formal statement asserts what the quoted words assert, after the translation the note states. |
| Lean states more | The formal statement has fewer hypotheses, more conclusions or a sharper bound; the note names the difference. |
| Lean states less | The formal statement has more hypotheses, fewer conclusions or a looser bound; the note names the difference. |
| Lean states something different | Neither implies the other as stated: for example a definition linked to a sentence about a construction. |
| Not assessed | No comparison has been recorded for this pair. This says nothing about whether they agree. |
| Withheld | A comparison was drafted and is not shown, for the reason given beside it. |

A comparison concerns the quoted words only. A shared name or number is not evidence that two
statements agree, and a kernel check of a declaration is not a check of the comparison.

## Marks on the paper

| State | Words | Margin |
| --- | --- | --- |
| Linked, at rest | 3px underline in the topic's colour at full strength over a faint wash of it, stopping 3px short of the phrase's end so neighbours read as two | thin tick |
| Pointed at | the same underline at 4px and a 14% wash of the topic's colour | tick in ink |
| Followed | no change to the words | tick in ink, 2px |
| Selected words | 5px amber underline, amber wash, on every fragment of the exact recorded range | 3px amber rule |
| Selected paragraph | no change to the words | 3px amber rule down the paragraph, and its ring filled amber |
| A paragraph with links | no change to the words | a 7px ring at its first line, between the ticks and the text; fills with ink under the pointer |
| Keyboard focus | 2px amber outline at 2px offset, on top of any of the above | none |
| Display formula | a rule at its left instead of an underline, in the same colours and weights | as above |

Amber appears on the paper for one reason only: the reader selected this. Following is neutral.
The curved thread that used to join a selection to the pane is gone: the quotation at the head
of the inspector now says which words are meant, and the thread was the one mark that moved
whenever the paper scrolled.

**Colour.** Underlines keep the colours of their topics, one hue per family of topics and one
shade per topic, computed and stored with the paper as before. The colour key is in Sections
and says, once: "Colours group topics within this paper. They do not say whether a statement
is proved or whether it matches the paper." A setting, "Colour underlines by topic", in the
key and in the page's guide, switches every underline to one neutral ink for a reader who
prefers it or cannot tell the hues apart; the choice is remembered. In forced-colours mode
underlines are real text decorations in the system's link colour and the selection is the
system's highlight.

## First visit

- The pane opens on the **Lean** view: the quotation, the comparison and the note, then the
  Lean. The graph is one tab away. A view named in the address wins; then a view the reader
  chose before (stored as an explicit choice of `graph` or `lean`); then Lean.
- One sentence, whole at every width including a phone, stands at the head of the paper above
  its title: "Underlined words are linked to a Lean statement. Select them to see the statement
  and how it compares." It is part of the page, so it wraps and scrolls away with the title, and
  it is in the first screen's own HTML, so nothing shifts when the page starts.
- Where the paper supplies them:
  - **Start here**: the paper's short list of places to start, each with the one line the
    paper's data gives for it (the reader adds no judgement of its own), under one paragraph on
    what the paper's main formal statement asserts. It stands in the pane before the paper's
    first link (beside the title and authors, where there is nothing yet to follow) and is one
    button away afterwards. Choosing an example selects its words and brings the paper to them.
  - **How to read the Lean**: the paper's own guide to its conventions, as a panel in the pane.
  - **At each section head**, one quiet note in the sans under the heading: what the formal
    development does in this section. Its first sentence shows and the rest opens in place. It
    is labelled "Reader annotation, AI-drafted", belongs to the annotation layer and never to
    the authors' text, and is not underlined or linked. It is set when the paper is prepared,
    in the first screen's HTML too, so it never arrives late and moves the text.
- The counter reads "Link 12 of 999". These are links, not theorems, and the number is never
  shown as a share of anything.

## The graph

The drawing is as specified in [the graph pane](graph-pane.md), with these changes.

- **The graph earns its space.** The Graph tab carries the number of neighbours the subject has
  in the recorded graph ("Graph · 19"). With four or more, the drawing takes about two thirds of
  the pane, fitted to that area and enlarged up to 1.3 times where the neighbourhood is small,
  and the dock under it is a short card: the title, the comparison's verdict and "Open its
  Lean", with "Show the whole card" to open the full inspector there. With one to three
  neighbours no canvas is drawn: one line names them ("Uses A, B. Used by C."), each name
  opening that declaration, and the inspector takes the rest of the pane. With none, the tab is
  dimmed but still opens, and one line says that nothing in the recorded graph uses this or is
  used by it.
- **The subject is named outside the canvas.** The subject band stays in place while the
  drawing pans and zooms, so a reader who has dragged the subject out of view still reads what
  the lines are about.
- **Relation types have names**, in the key under the drawing and in each line's tooltip:
  "A link the paper states" (heavy solid) where a paper has an authored argument, "A use the
  paper's proof states, with no Lean link" (heavy dashes; the line opens the sentence that states
  it), "A link between results, derived from the Lean" (heavy, longer dashes; never called the
  paper's argument), "An assumption" (heavy dots), "Used in a Lean proof or body" (solid), "Used
  in a Lean statement" (thin dashes) and "Used in the Lean, statement or proof not recorded"
  (thin dots). The key names only the kinds drawn and says which way arrows run: from a
  statement to what it uses. Each side's count says how many of its cards each relation joins.
  A count is a number on a badge; a line never grows heavier because a group is large.
- **A large group opens as a list, not in the drawing.** Choosing a group of more than eight
  shows its members in a panel beside the drawing: a search field over the whole group, twenty
  members to a page, each with its whole title and kind. The subject does not move and the
  drawing is not redrawn. "Back to the graph" closes the panel and keeps the search for next
  time. This is how 283 uses stay findable.
- **Fit only moves the camera.** It frames the drawing again. It folds nothing, closes nothing
  and forgets nothing.
- **Pointing is a preview.** A card under the pointer shows in the dock under the label
  "Preview". A click makes it the subject, as one step in the browser's history.
- The view the reader has arranged (zoom, place, an open list) is kept until the subject
  changes.

## What a paper can supply

All of this is optional data in a paper's instance. The reader draws each when it is there and
shows nothing in its place when it is not; no paper needs any of it to be read.

| Data | Where the reader looks | What the reader draws |
| --- | --- | --- |
| Section aids | `generated/section-aids.json`, or `reading_aids.json`: section number or heading to text, flat or under `paper` | the reader annotation under each section head |
| Glossary | `generated/glossary.json`: `{term, convention, differs_from_paper, cards}` | "Conventions used here" in the inspector |
| Showcase | `generated/showcase.json`: `{card, why}`; a card is `tie:<phrase>`, `result:<Lean name>`, `declaration:<Lean name>` or a bare phrase id | "Start here", and the line "Start here, example 3 of 10" with Previous and Next while one is open |
| Start summary | `generated/start-here-summary.md`, at most 150 words | the paragraph that opens "Start here" |
| Proof route | `generated/route.json`: steps `{step, result, statement, explanation, citations, lean[], verdict, why_needed}` | "Follow the proof" in the pane: the steps in order, each opening its result |
| Explanation | on a phrase's tie: `explanation {text, citations[{ref, title, url, where, supports}], grounded, open}` | "What these words say" in the inspector |
| Bearing on the main result | on a phrase's Lean row: `matters {kind, affects_main_result, line}`; `main_result` on the paper's ties | the verdict's "Does this affect the main result?" line |
| Guide | a document of kind `guide` | "How to read the Lean" in the pane |

Two longer pieces a paper may bring, a summary of differences (`differences-summary.md`) and a
long "Start here" (`start-here.md`), are pages: documents of the instance with their own
addresses, reached from the pane's "Start here" and from Read. They are not drawn in the pane.

## Adapted editions (planned, not built)

A paper may gain an adapted edition: a corrected, clearer version of the authors' text beside the
authors' own, with its own layer of Lean statements that are proved from the authors'
declarations. The reader shows either text, never a blend, and says at every moment which.

**One switch.** "Authors' paper" and "Adapted edition" stand in the strip beside "Text" and
"PDF", as a second pair of pressed buttons. The authors' paper is the default and every existing
address means the authors' paper. The switch keeps the reader's place by paragraph: the
alignment map gives, for the paragraph under the reading line, the paragraph on the other side.
A paragraph with no partner (a cut, an addition) lands on the nearest one before it and says so
in one line: "This paragraph has no counterpart in the authors' paper." The switch changes the
text and nothing else: the view and the pane stay, and a selection is let go, because its words
belong to the text being left.

**The states stay the same.** Following, Preview and Selected mean what they mean above. The
subject band names the text as well as the state while the adapted edition is open: "Selected
words in §5.6, adapted edition".

**A changes layer with its own mark.** Topic colour says topic and amber says selection, so a
change is marked by neither. Each changed passage of the adapted edition carries a mark in the
right margin, the one margin the other marks do not use: a short dotted rule in ink the height
of the passage, headed by a small open square. Dotted and on the right is the whole of the
encoding; the kind of change is said in words, never by a colour. The mark is a button named
"See what changed here". It opens the change in the pane as a **Selected change**: the authors'
text, the adapted text, the kind (correction, added justification, clarification, restatement,
or cut) and the reason with its source. A cut is marked where the text was. **Show changes**, a
button beside the switch, lists every change in the order of the text, each opening its passage.
The authors' paper carries no change marks; from it, a paragraph's margin control offers "See
this paragraph in the adapted edition" where the two differ.

**Links for both texts.** The adapted edition's words link to the adapted statements. The
inspector for such a link shows two formal statements in order: the adapted statement, then
"Proved from the authors' declaration" with that declaration, its Comparator line and the way to
its own card. The comparison is between the adapted words and the adapted statement; how the
adapted statement stands to the authors' is a second, separately labelled comparison.

**Credit.** The adapted edition's header and About say, whole: "An adapted edition of [authors]'
paper, prepared by Will Cook with AI assistance. The mathematics and the original text are the
authors'. Every change is marked, and no change has been reviewed by the authors." The authors'
paper keeps its own credit unchanged, and the two are never merged into one line.

**What the instance needs.**

| Field | Shape | Use |
| --- | --- | --- |
| `documents[].kind` | `"adapted"`, with `of: <document id>` | the second text and which text it adapts |
| `documents[].credit` | the sentence above, with the authors' names | the adapted edition's header and About |
| `alignment/changes.json` | `{authors, adapted, paragraphs: [{authors: <paragraph id or null>, adapted: <paragraph id or null>, change: null or {kind, reason, source: {ref, title, url, where}}}]}` | keeping the place across the switch, the margin marks and "Show changes" |
| paragraph ids | stable ids in both texts, with their byte ranges | the alignment map's two sides |
| `phrases-<adapted>.json` rows | each row may carry `proved_from: [{name, module}]` | the authors' declaration under the adapted statement |
| a second comparison | on those rows, `to_authors {fidelity, fidelity_note}` | how the adapted statement stands to the authors' |

## Layout

One composition at every desktop width: the paper at its measure on the left, the pane to its
right, nothing over the text. Widths are CSS pixels of the window.

| Window | Outline | Paper | Pane | Notes |
| --- | --- | --- | --- | --- |
| 390 | drawer | 350 | none beside | inspect and return, below |
| 1100 | drawer | 550 | 479 | two columns from 1024; the graph is folded to a line at this pane width |
| 1440 | drawer | 680 | 672 | |
| 2000 | 208 | 689 | to the edge, at least 600 | |
| 2560 | 208 | 755 | 1024, the pair centred | notes stay at 38rem; the Lean takes the rest |

- The pane is sticky under the top bar and has one vertical scroller per view. Its gutter is
  stable, so content arriving never changes a width.
- Under the drawing, the dock is a short card and the drawing has the rest, about two thirds
  of the pane or more. Opened with "Show the whole card", the dock takes 40% of the Graph view,
  never less than 240px while the drawing keeps 260px, and its height can be drawn with the
  handle; where both cannot fit, the drawing folds to one line.
- From 1024 to 1279 the paper's measure narrows so that both columns fit. Before this design
  the pane covered the paper there, which hid the words being checked.
- "Hide pane" leaves the paper alone at its measure and lets any selection go, since nothing
  would show it. Selecting words while the pane is hidden brings the pane back beside the paper;
  the reader's stored choice to hide it is not changed by that.

### A phone: inspect and return

1. **Read.** The paper alone. The hint and the reader-annotation notice are on the first screen.
2. **Tap linked words.** The inspector opens over the whole screen under the top bar, at once,
   with the quotation first. Its head is one row: "Back to paper" and the two tabs.
3. **Back to paper** (or Escape) closes it. The paper is exactly where it was. A bar stays at
   the foot: the selection's state and place, which returns to the words; "View", which
   reopens the inspector; and "Resume", which lets the selection go. The paper reserves the
   bar's height so it covers no last line.
4. Scrolling never reopens the inspector.

Nothing on a phone scrolls sideways except a formula or the Lean inside its own box.

## Type

| Role | Face | Size / line | Limit |
| --- | --- | --- | --- |
| Paper prose | STIX Two Text | 18 / 29; 20 / 32 by 2560 | 680px, 755px by 2560 |
| Inspector title | serif | 20 / 26 | whole, never elided |
| Quotation | serif | 17 / 25.5 | 38rem |
| Comparison and note | Source Sans 3 | 16 / 24 | 38rem |
| Lean | JetBrains Mono | 14 / 21 | scrolls in its own box |
| Controls | sans | 14 / 20 | 44px targets on a phone |
| Labels: state, "AI-assessed", kind | sans | 13 / 19.5 | never smaller, never for a sentence |
| Section aid | sans | 15 / 22.5, quiet ink | the paper's measure |

The inspector does not grow with the window. Past 1920 the paper's own type grows as it did;
the comparison stays at 16px, because a wider window is not a more distant reader. The mono is
for Lean and Lean names only.

## Tokens

All colours are the existing family tokens (`styles/tokens.css`); none is renamed. New names
are aliases, so each mark's job is written down once.

| Token | Value | Job |
| --- | --- | --- |
| `--tie-rule` | 3px | a linked phrase's underline at rest |
| `--tie-rule-strong` | 4px | the underline when pointed at |
| `--sel-rule` | 5px | the selection's underline |
| `--tie-end-gap` | 3px | where a phrase's underline stops short |
| `--tie-ink` | `var(--tone)`, or `var(--ink-3)` with colour off | the underline's colour |
| `--tie-hover-wash` | 12% of `--tie-ink` | under words the pointer is on |
| `--sel-ink` | `var(--lit)` | the selection's underline and rules (4.96:1 day, 9.75:1 night on the ground) |
| `--sel-wash` | `var(--lit-wash)` | under selected words; ink on it keeps 14.5:1 day, 11.2:1 night |
| `--sel-rail` | 3px | the selection's rule in the margin and beside its quotation |
| `--follow-ink` | `var(--ink-2)` | the followed passage's tick |
| `--evidence-fs`, `--evidence-lh` | 1rem, 1.5 | comparison and note |
| `--evidence-measure` | 38rem | the widest a note or quotation runs |
| `--quote-fs` | 1.0625rem | the quotation |
| `--code-fs` | 0.875rem | Lean |
| `--band-h` | 56px | the subject band |
| `--held-bar-h` | 56px | the phone's bar for a held selection |

The wash is reinforcement: against the ground it is only 1.1:1 by day. The selection is
carried by the 3px underline, the margin rule and the words "Selected words", each of which
passes 3:1 alone.

## Motion

Every change below is caused by the reader. Nothing else moves. Under
`prefers-reduced-motion: reduce` nothing animates: every transition is cut to the site's 1ms
(kept above zero so that code waiting on a transition's end still hears it) and no keyframe runs.

| Change | Duration, curve | What animates |
| --- | --- | --- |
| Pointer on a link or control | 120ms, ease-out `(0.2, 0.7, 0.2, 1)` | background and border colour |
| Press | 0 | colour |
| Selecting words | underline and rules at once; wash 120ms ease-out | background colour, once |
| The inspector's content for a new subject | 0 | replaced whole; no cross-fade between two statements |
| Lean to Graph and back | 0 | replaced whole, in the same box |
| The phone's inspector | opens over 180ms, closes at once | opacity; it has its final box from the first frame |
| A group's member list | 160ms ease-out | opacity |
| Fit, and the camera on a new subject | 320ms, ease-in-out `(0.45, 0, 0.2, 1)` | the drawing's transform; a new input cuts it short |
| Return to selected words | the browser's smooth scroll; instant under reduced motion | scroll |
| Following a new passage | 0, after the line has rested 200ms | replaced whole |
| Theme | 0, transitions suppressed | colour |

No entrance plays on load. Text never fades or rises into place. Nothing pulses, shimmers or
loops. Left alone, the page makes no change at all, and `check-idle.py` holds it to that.

## Where the reviews disagreed

| Question | Positions | Decision and reason |
| --- | --- | --- |
| Colour of underlines | 04: neutral underlines, topic only as a named swatch. 01: topic colour as a secondary cue. | Topic colours stay on the underlines, with a setting to turn them off. The colour coding is wanted and helps a reader see where a topic runs; the risk 04 names (colour read as a verdict) is met by the key's sentence and by giving amber and verdicts their own, separate marks. |
| How loud a selection is | 01: wash and margin rule, underline unchanged. 04: 3px amber underline as well. | The 3px amber underline, the margin rule and the wash. The exact extent of the selected words is the thing being checked; an underline shows the extent on every wrapped line, where a wash at 1.1:1 cannot. |
| The followed passage's mark | 04: keep the amber margin marker. 01: neutral. | Neutral ink. Amber then has one meaning on the paper. |
| Default view | 01, 02: the comparison first, unless the reader chose Graph. | Lean view on a first visit; an address or a stored choice of Graph wins. The stored choice is now an explicit value, since the old key could not tell "chose Graph" from "never chose". |
| The tab's name | 01: rename "Lean" to "Comparison". 02: keep "Lean". | "Lean". The sister readers, the addresses (`v=lean`), "Open its Lean" and the checks all use it, and the view is headed by the quotation and comparison whatever the tab is called. |
| A phone's inspector | 01: a sheet over 60% of the screen, paper usable above. 02: the whole screen, with a bar for the held selection. | The whole screen, with 02's bar and 01's "Resume". The comparison, the note and the Lean need the room, and the quotation at its head means the paper need not show behind it. |
| The pane at 1100 | 01: a sheet over the paper. 02: two true columns. | Two columns from 1024. A sheet covers the sentence the reader is checking. |
| Paper type past 1920 | 02: hold 680px and 18px. 01, 04: keep the existing growth to 755px and 20px. | Keep the growth. It is bounded, deliberate and already held still by the first-screen checks. The inspector does not grow (04). |
| Hover | 01: pointing never replaces the pane's content. 02, 03: a labelled preview that restores. | A labelled preview while following; while words are selected the paper's hover only lights. A card in the graph previews in the dock in both states. |
| Escape | The engine went back through the browser's history, which moved the paper. 01: release in place. | Escape is "Resume here": the paper stays. Back is Back. |
| A group in the graph | The engine opened it in the drawing. 03: a bounded member list. | The list, for groups over eight. Opening 36 cards in place pushed the subject off the canvas. |
| Fit | The engine and its check: Fit also folds opened groups. 03: camera only. | Camera only. Recovering the view must not cost the reader what they found. The check changes with it. |
| Focus colour in the graph | 03: a blue ring. Others: the site's amber ring. | Amber, one focus colour across the site. |
| A second graph projection | 03: tabs for "Paper argument" and "Lean references". | Not in this pass. Relation types are named in the key and on each line. Tabs wait until a paper's data carries both projections whole. |
| The dock's height | The engine: 30%. 02: 40% with floors. Review of the built page: the drawing was left too small. | A short card under a drawing that has about two thirds of the pane; 40% with floors of 240px and 260px once the reader opens the whole card. |
| The words for a selection | 01: "Selected words". 02: "Selected statement". 03: "Pinned to". | "Selected words" for words of the paper, "Selected declaration" for a card or a name. The reader selected words; the statement is what the pane then shows. |
| The library index | The engine: a strip of topic colours in proportion. 04, 05: remove it. | Removed. Counts stand in words, each with what it counts ("999 linked passages", "1,012 Lean declarations"), and none is a share of another. |

## Kept on purpose

- The paper as the authors set it: wording, formulas, numbering, the serif and its measure, the
  first screen's geometry before the fonts land.
- Every credit and every qualification, word for word: the authors and formalisers, the notice
  that the links, titles, notes and comparisons were made with AI and reviewed by no
  mathematician, "AI-assessed", "AI-drafted", and the Comparator's scope.
- Addresses: `/@phrase`, numbered results, `lean/Name`, `?l=`, and `v=lean` or `v=graph`.
- The graph's drawing, its cards as real buttons, the camera kept apart from the layout, the
  whole proof map one button away.
- The original PDF, white in both themes, beside the reading copy.
- Keyboard reading: one tab stop for the paper's links, arrows and `j`/`k` between them, Enter
  to select.
- Stillness: the idle check passes unchanged.

## Not in this pass

Named so that nobody takes their absence for a decision: adapted editions (planned above);
pages for a paper's summary of differences and its long "Start here"; zoom and one-stop-per-link marks in
the PDF view (packet 02); a recorded map between places in the reading copy and the PDF (02);
the whole map's opening as an argument overview (03); search scope and result rows (05); the
Compare page's columns for papers with other document kinds (05); one inventory of checks
across About and What ran (05).

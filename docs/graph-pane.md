# The graph pane

This page specifies the right-hand pane of three reading sites: the Quartic Reader, the SK and Erdős #257 readers built from lean-exposition, and Proof Reader. The same text is kept in each repository at `docs/graph-pane.md`. The drawing itself is one component, `FocusGraph.tsx` with `focus-graph.css` and the shared wheel gestures in `graphWheel.ts`, and the browser checks are one module, `graph_pane_checks.py`. A change to any of these files should be copied to the other two repositories.

## What the graph shows and why

The readers are mathematicians in the field of each paper: query complexity and Forrelation, the SK model and Parisi theory, irrationality of Lambert series, probabilistically checkable proofs, programming-language semantics. They read the paper on the left. They look right when the paragraph in front of them raises one of five questions.

| The reader asks | The pane answers with |
| --- | --- |
| What in the Lean corresponds to what I am reading? | The subject card in the middle of the graph: the step or declaration tied to the paragraph or to the clicked phrase, with its plain title and its Lean name. The dock under the graph shows its statement in Lean. |
| What does this step rest on? | The column on the right of the subject, each node joined to it by a line. |
| Where is this used later? | The column on the left of the subject, each node joined to it by a line. A node the paper states further on is set in paler ink. |
| Is this the paper's claim or a helper? | The look of each node: a numbered result carries its number ("Theorem 2.1") in bold on a filled node, a definition has square corners, a Lean helper lemma has a dashed outline. The paper's results and steps head each column. |
| How far is this from the main theorem? | One line over the drawing: the shortest chain of uses from the subject up to the main result, each link a button. |

Five consequences follow for the design.

**One subject, its whole neighbourhood, in one look.** A whole proof drawn at once answers none of the five questions at reading size: at 1440 pixels its type is 10 pixels tall and most of its cards are off the pane. A single card with its neighbours scrolled out of sight is no better. The drawing therefore shows one subject with everything that uses it and everything it uses, and it fits its area when it opens, at 12 neighbours, at 47 and at 283.

**Nodes are one compact line; the detail is in the dock.** A node carries the plain title and, for a numbered result, its number. The Lean name, the statement and the reading note are shown under the drawing for the node under the pointer. Small nodes are what lets a whole neighbourhood be seen at once.

**A crowded side is drawn as named groups, with every member one click away.** When a side has more neighbours than fit, they are gathered by the topic the paper already gives them (the same topics that colour its phrases), and by kind where a card has no topic. A group shows its name, its colour and its full count. When the column has room, related cards appear beneath the group heading. They still count toward the group total, and one line joins it to the subject; the line's weight says its kind of use and never grows with the count. The counts on show always add up to the whole neighbourhood. Clicking a small group opens it in place; a group of more than eight opens as a list of its members beside the drawing, so that the subject does not move and the drawing is not redrawn.

**Kinds and lines carry meaning.** A numbered result of the paper is set in bold on a filled node. A definition has square corners. A Lean helper lemma or library fact has a dashed outline, because it answers a question about the formalisation and says little about the mathematics. Every line says which relation it records, by name in the line's own tooltip. "A link the paper states" (heavy and solid) is a link of the paper's own argument. "A use the paper's proof states, with no Lean link" (heavy dashes) is a use the paper's text states and no Lean dependency joins; the line opens the sentence that states it. "A link between results, derived from the Lean" (heavy dashes, longer) is a `supports` link whose only evidence is `lean_dependencies`, and is never called the paper's argument. "An assumption" is a dotted heavy line. "Used in a Lean proof or body" (thin and solid) is a use in a Lean proof or definition body, "Used in a Lean statement" (thin dashes) a name used only in a Lean statement (Lean's own type dependencies where the edition has them, else the statement's text), and "Used in the Lean, statement or proof not recorded" (thin dots) a Lean use that no record splits into statement or proof. Each side's heading gives its neighbour total. Arrows point from an input to the card that uses it. The route over the drawing counts links, not cards, and says how many the paper states and how many were derived from the Lean; the correspondence between a declaration and the result it states is not counted as a link.

**The colours of the paper continue into the graph.** A node whose declaration belongs to a topic carries that topic's colour on its left edge, the same colour its phrases have in the paper.

## The three views

When a linked passage has both Lean and recorded neighbours, the reader opens the Lean statement and passage annotation above the local dependency graph. The annotation uses the paper’s reading size. A shallow drawing leaves more room for a long annotation. The graph fills the remaining pane, with its cards, labels and arrows centred in the available width and height. The AI-written credit follows the annotation, in the Sources and details summary when shown.

**Minimise graph** switches to separate Lean and Graph tabs. In that layout the Lean tab gives the statement the full pane and the Graph tab shows the drawing with its details dock. **Combine views** restores the automatic layout. Readers with a separate **Passage** view use it for the account of the paragraph across papers and the comparison of statement and Lean.

Switching between the views keeps the selected subject. In the automatic layout, choosing a passage can change what the pane shows according to its links.

The subject is set, in this order of precedence, by:

1. a phrase the reader clicked: the declaration tied to it;
2. a card the reader clicked;
3. a paragraph the reader clicked;
4. the paragraph under the reading line, as the reader scrolls.

A clicked subject holds until the reader clicks something else, presses Escape or chooses to follow the paper again. Escape returns the pane to following the paper.

For a passage with no linked Lean, the Lean view says "No Lean is linked to this paragraph." The whole proof map can still be read on its own, with no local step selected for that passage.

## The Graph view

### The drawing

- The subject is in the column labelled "Centre", with its kind, its whole title and its Lean name. A paragraph that states several steps has them all in the middle, inside one frame, each above the steps it uses, with the lines between them drawn.
- The cards that use a subject are in a column on the left under "These use the centre" with their number. The cards a subject uses are in a column on the right under "The centre uses these" with their number. A curved line with an arrowhead joins each to the subject. Its endpoints touch the card borders.
- Within a column the paper's results come first, then steps, definitions, cited results, open questions, Lean helper lemmas and library facts.
- A node is one line of plain words, wrapped onto a second line when the title is long. No title is truncated or clamped. Titles are 13.5 pixels at full size. When the available height would shrink the drawing below 0.85 of full size, the reader tries further grouping before fitting.
- On opening, the reader fits the cards, labels and connecting lines with a margin and centres the shape they draw. It enlarges a small neighbourhood up to 1.15 times its original size. Unused column space does not affect the fitted centre. A column can group its cards by topic or kind. A neighbour stands on its own or belongs to one group. Cards shown beneath a group heading count toward that group's total.
- Clicking a group of eight or fewer opens it in place: all its members stand under its name, joined by a bracket, and the group stays in view. Clicking the group's name again restores the shorter view.
- Clicking a group of more than eight lists its members in a panel over the side of the drawing the group is on (on the left for what uses the subject, on the right for what it uses), at most 360 pixels wide. The drawing holds its camera when the list opens. In the combined view the area can grow to make room for the list, then return to the fitted height when the list closes. The panel has the group's name and count, a button "Back to the graph", a field "Search these members" over the plain title, number and Lean name of every member of the group, a line such as "1–20 of 36 members" or "3 of 36 members match", twenty members to a page with Previous and Next, each with its whole title, its number and its kind. Pointing at a member previews it in the dock, as pointing at a node does; clicking it makes it the subject. Escape or "Back to the graph" closes the panel and returns the keyboard to the group's button. The search and the page of each group are kept until the subject changes. One panel is open at a time; it fades in over 160ms, at once under reduced motion.
- Lines between two neighbours are left out. Clicking a neighbour puts it in the middle with its own neighbourhood.

### Moving about

- The drawing's area is a canvas with no scroll bars: it never scrolls. Dragging or scrolling sideways pans the drawing. Scrolling up zooms in at the pointer and scrolling down zooms out, with a mouse or trackpad. A pinch, Ctrl or ⌘ with the wheel, and a double click also zoom at the pointer. A wheel over the paper or the member list scrolls that content. On the keyboard the arrows pan, + and − zoom and 0 fits. A pan always leaves part of the drawing in view, and focusing a card brings it into view.
- The buttons −, + and Fit change the zoom. Fit frames the drawing as it is and changes nothing else: an opened group stays open, and a panel of members stays open with its search and page.
- The drawing is fitted when it opens, when the subject changes, on Fit, and when the pane itself changes size while the view is still the fitted one. The camera never changes the layout and the layout never moves the camera except by such a fit, so the drawing is completely still while nobody touches it. After the reader pans, zooms or opens a small group, the view is kept until the subject changes or Fit is pressed. Opening or closing a panel of members never moves the view.
- Keyboard focus pans the drawing to bring a card into view. Pointing at or focusing a node lights its line to the subject and shows the node's detail in the dock. A member of an open group, or of a panel of members, lights the group's line. Clicking a node makes it the subject.
- Pointing at a phrase or a sentence in the paper lights its node if it is drawn.

### A declaration that is not on the paper's map

A phrase can be tied to a Lean declaration for which no paper-argument route is recorded. The line over the drawing then says exactly that ("No paper-argument route is recorded for this declaration"), which is a statement about the recorded data, not about the mathematics. The graph then draws that declaration in the middle with the declarations it uses and those that use it, from the Lean dependency data the site already holds. One line over the drawing says so and offers the way back to the paragraph's own steps.

### The dock

A strip under the drawing, about 30% of the pane's height, shows one card in detail. A handle between the two sets its height (15% to 70%), and the height is remembered. The dock scrolls by itself. It shows, in this order of precedence:

1. the node under the pointer or holding the keyboard focus, as a preview: its title, kind, Lean name, and the first lines of its Lean statement;
2. the clicked phrase: the quotation, its topic, the comparison of phrase and Lean, the AI-drafted reading note, and the Lean with the tied lines lit;
3. the subject's Lean statement;
4. "No Lean is linked to this paragraph."

The dock has a button to open the same declaration in the Lean view.

### The whole proof

Where a reader has a map of the whole argument, **Whole proof map** in the Graph tab opens it in the same area. **Neighbours of this step** returns to the local graph. The whole map pans and zooms, and its cards open as subjects.

### Small screens

Under 600 pixels of width the separate local Graph view can fold to one line that names the subject and counts what it uses and what uses it, with a button to unfold the drawing. The dock keeps the rest of the height.

## Checks

`graph_pane_checks.py` asserts in a real browser, at 1440×900 and 2560×1440, following the paper, after a phrase click and after a card click:

- a subject is drawn;
- on opening, the whole drawing lies inside its area, with nothing to scroll;
- the nodes on show and the counts of the groups on show add up to the number of neighbours;
- every title and group name is whole and, at the fitted zoom, at least 11 pixels;
- there is a line for every node and group beside the subject;
- the dock is never empty;
- the largest group opens all its members. A group of more than eight opens a panel whose line counts the group. The camera holds its position within the graph while the list is open. Paging reaches each member once, search finds a member by its title, Fit leaves the panel open, and "Back to the graph" closes it. A smaller group opens all its members in place. When it overflows, dragging pans the drawing and keyboard focus brings each card into view. Fit leaves the group open.

`check-graph-pane.py --painted-fit ADDRESS` checks the graph on a linked passage with one subject. It measures cards, labels, wires and arrowheads in the browser, checks the centre and margin on two cold desktop loads and after desktop and landscape resizes, and verifies that Fit restores the whole local graph after zooming and panning. It also checks that visible wire geometry meets the correct card borders throughout. Pass `--one-sided-cap` for a fixture whose neighbours all lie on one side and whose wide view reaches the 1.15 cap. The check also covers zooming in the combined view and the separate Graph tab and opening the whole proof map from that tab.

`check-idle.py` asserts that the page, the graph included, makes no change at all while it is left alone (no mutation, address change, layout shift or scroll), across window widths, with classic scroll bars that take room.

Each repository's own script drives its pages and calls these checks.

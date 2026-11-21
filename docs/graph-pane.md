# The graph pane

This page specifies the right-hand pane of three reading sites: the Quartic Reader, the SK and Erdős #257 readers built from lean-exposition, and Proof Reader. The same text is kept in each repository at `docs/graph-pane.md`. The drawing itself is one component, `FocusGraph.tsx` with `focus-graph.css`, and the browser checks are one module, `graph_pane_checks.py`. A change to any of the four files should be copied to the other two repositories.

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

**A crowded side is drawn as named groups, with every member one click away.** When a side has more neighbours than fit, they are gathered by the topic the paper already gives them (the same topics that colour its phrases), and by kind where a card has no topic. A group shows its name, its colour and its count, and one line whose weight grows with the count joins it to the subject. The counts on show always add up to the whole neighbourhood. Clicking a group opens it in place.

**Kinds and lines carry meaning.** A numbered result of the paper is set in bold on a filled node. A definition has square corners. A Lean helper lemma or library fact has a dashed outline, because it answers a question about the formalisation and says little about the mathematics. A heavy line is a step of the paper's own argument, a thin line is a use in a Lean proof or definition body, and a dashed line is a name that appears only in a statement, wherever the reader's data records the difference. Arrows run from a card to the card it uses, left to right.

**The colours of the paper continue into the graph.** A node whose declaration belongs to a topic carries that topic's colour on its left edge, the same colour its phrases have in the paper.

## The three views

The pane has the views each reader already names: Graph, Lean and, where the reader has one, Passage. Each view fills the pane and does one job.

- **Graph** is the drawing described below, with a dock under it.
- **Lean** is the Lean of the subject, the whole height of the pane.
- **Passage** is the reader's account of the paragraph: the same step in each paper and the comparison of statement and Lean.

All three views share one subject. Changing the view keeps the subject. A click on a paragraph, a phrase or a card changes the subject and never changes the view. Only the view buttons, and a control whose label names another view ("Open its Lean"), change the view.

The subject is set, in this order of precedence, by:

1. a phrase the reader clicked: the declaration tied to it;
2. a card the reader clicked;
3. a paragraph the reader clicked;
4. the paragraph under the reading line, as the reader scrolls.

A clicked subject holds until the reader clicks something else, presses Escape or chooses to follow the paper again. Escape returns the pane to following the paper.

No view is ever blank. A paragraph with nothing tied to it says "No Lean is linked to this paragraph." in the dock and in the Lean view, and the graph keeps the last subject with a line saying which paragraph it belongs to.

## The Graph view

### The drawing

- The subject is in the middle, with its kind, its whole title and its Lean name. A paragraph that states several steps has them all in the middle, inside one frame, each above the steps it uses, with the lines between them drawn.
- The cards that use a subject are in a column on the left under "Use this" with their number. The cards a subject uses are in a column on the right under "This uses" with their number. A curved line with an arrowhead joins each to the subject.
- Within a column the paper's results come first, then steps, definitions, cited results, open questions, Lean helper lemmas and library facts.
- A node is one line of plain words, wrapped onto a second line when the title is long. No title is truncated or clamped, no type is under 13 pixels at any zoom, and no type shrinks to make a drawing fit.
- The drawing fits its area when it opens. A column that would not fit is drawn as groups by topic, or by kind when the topics themselves would not fit; the smallest groups are then drawn out as their own nodes while there is room. Every neighbour is either a node on show or is counted by one group on show.
- Clicking a group opens it in place: its members stand under its name, joined by a bracket, and the group stays in view. A group of more than 18 members from several Lean files or sections opens into those first. Clicking the group's name again folds it.
- Lines between two neighbours are left out. Clicking a neighbour puts it in the middle with its own neighbourhood.
- A key under the drawing names the line styles and node styles in use.

### Moving about

- An opened group can make the drawing taller than its area. It then scrolls with the wheel, the trackpad, the arrow and page keys and a visible scrollbar, and dragging pans it. An overview beside the buttons shows the whole drawing and the part in view; clicking or dragging in it moves the view.
- The buttons −, + and Fit change the zoom; Fit also folds every opened group and brings the subject back to the middle. Ctrl or ⌘ with the wheel zooms.
- When the subject changes, the drawing is laid out afresh, fitted and centred. After that the reader's own scrolling and opened groups are kept until the subject changes again.
- Pointing at or focusing a node lights its line to the subject and shows the node's detail in the dock. A member of an open group lights the group's line. Clicking a node makes it the subject.
- Pointing at a phrase or a sentence in the paper lights its node if it is drawn.

### A declaration that is not on the paper's map

A phrase can be tied to a Lean declaration that is not a step of the paper's argument. The graph then draws that declaration in the middle with the declarations it uses and those that use it, from the Lean dependency data the site already holds. One line over the drawing says so and offers the way back to the paragraph's own steps.

### The dock

A strip under the drawing, about 30% of the pane's height, shows one card in detail. A handle between the two sets its height (15% to 70%), and the height is remembered. The dock scrolls by itself. It shows, in this order of precedence:

1. the node under the pointer or holding the keyboard focus, as a preview: its title, kind, Lean name, and the first lines of its Lean statement;
2. the clicked phrase: the quotation, its topic, the comparison of phrase and Lean, the AI-drafted reading note, and the Lean with the tied lines lit;
3. the subject's Lean statement;
4. "No Lean is linked to this paragraph."

The dock has a button to open the same declaration in the Lean view.

### The whole proof

Where a reader has a map of the whole argument, a button over the drawing opens it in the same area, and a button there returns to the subject. The whole map pans and zooms, and its cards open as subjects.

### Small screens

Under 600 pixels of width the graph folds to one line that names the subject and counts what it uses and what uses it, with a button to unfold the drawing. The dock keeps the rest of the height.

## Checks

`graph_pane_checks.py` asserts in a real browser, at 1440×900 and 2560×1440, following the paper, after a phrase click and after a card click:

- a subject is drawn;
- on opening, the whole drawing lies inside its area, with nothing to scroll;
- the nodes on show and the counts of the groups on show add up to the number of neighbours;
- every title and group name is whole and at least 13 pixels;
- there is a line for every node and group beside the subject;
- the dock is never empty;
- the largest group opens into exactly its count, the drawing then scrolls under the wheel and shows the overview, every card can be brought wholly into view, and Fit folds the group again.

Each repository's own script drives its pages and calls these checks.

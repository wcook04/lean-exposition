# The graph pane

This page specifies the right-hand pane of three reading sites: the Quartic Reader, the SK and Erdős #257 readers built from lean-exposition, and Proof Reader. The same text is kept in each repository at `docs/graph-pane.md`. The drawing itself is one component, `FocusGraph.tsx` with `focus-graph.css`, and the browser checks are one module, `graph_pane_checks.py`. A change to any of the four files should be copied to the other two repositories.

## What the graph shows and why

The readers are mathematicians in the field of each paper: query complexity and Forrelation, the SK model and Parisi theory, irrationality of Lambert series, probabilistically checkable proofs, programming-language semantics. They read the paper on the left. They look right when the paragraph in front of them raises one of five questions.

| The reader asks | The pane answers with |
| --- | --- |
| What in the Lean corresponds to what I am reading? | The subject card in the middle of the graph: the step or declaration tied to the paragraph or to the clicked phrase, with its plain title and its Lean name. The dock under the graph shows its statement in Lean. |
| What does this step rest on? | The cards below the subject, each joined to it by a line. |
| Where is this used later? | The cards above the subject, each joined to it by a line. A card the paper states further on is marked "stated later". |
| Is this the paper's claim or a helper? | Each card says what it is in a short line over its title: the paper's numbered result ("Theorem 2.1"), a step of the argument, a definition, a cited result, an open question, a Lean helper lemma, a library fact. Neighbours are grouped by these kinds, so "Results of the paper it uses" is read apart from "Lean helper lemmas it uses". |
| How far is this from the main theorem? | One line over the drawing: the shortest chain of uses from the subject up to the main result, each link a button. |

Three consequences follow for the design.

**One subject at a time.** A whole proof drawn at once answers none of the five questions at reading size: at 1440 pixels its cards are 10 pixels tall in type and most of them are off the pane. The default drawing is therefore the subject with every direct neighbour. The whole proof stays one click away where a reader has such a map.

**Kinds carry the meaning.** The paper's own results and steps come first in each direction. Definitions follow. Lean helper lemmas and library facts come last, in dashed cards, because they answer a question about the formalisation and say little about the mathematics. They are still drawn. A line is solid when a proof or a definition body uses the lower card and dashed when only a statement names it, wherever the reader's data records the difference.

**The colours of the paper continue into the graph.** A card whose declaration belongs to a topic carries that topic's colour on its left edge, the same colour its phrases have in the paper.

## The three views

The pane has the views each reader already names: Graph, Lean and, where the reader has one, Passage. Each view fills the pane and does one job.

- **Graph** is the drawing above with a dock under it.
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

- The subject is in the middle. A paragraph that states several steps has them all in the middle, inside one frame, ranked so that a step sits under the steps that use it, with the lines between them drawn.
- Every card that uses a subject is drawn above it and every card a subject uses is drawn below it. Nothing is replaced by a count.
- Neighbours are grouped by kind. Each group is a block with a heading that reads as a sentence about the subject ("Definitions it uses", 12) and its cards in rows. One line leaves the subject for each direction and branches to the groups; inside a group one rail runs along each row with a short line to each card. Thirty neighbours read as two or three blocks.
- Lines between two neighbours are left out. Clicking a neighbour puts it in the middle with its own lines.
- A card shows its kind, its whole title wrapped over as many lines as it needs, and its Lean name. Titles are at least 13 pixels at every zoom. No title is truncated or clamped, and no type shrinks to make a drawing fit.
- The rows wrap to the width of the pane, so the drawing is never wider than the pane at the default zoom.

### Moving about

- The drawing scrolls inside the graph area with the wheel, the trackpad, the arrow and page keys and a visible scrollbar. Dragging pans it.
- When the drawing is larger than the area, an overview in the corner shows the whole drawing and the part in view. Clicking or dragging in the overview moves the view.
- The buttons −, + and Centre change the zoom and bring the subject back to the middle. Ctrl or ⌘ with the wheel also zooms.
- When the subject changes, the subject comes to rest a little above the middle of the area, so that what uses it shows above and as much of what it uses as fits shows below. After that the reader's own scrolling is kept until the subject changes again.
- Pointing at or focusing a neighbour lights its line all the way to the subject and marks the subject. Clicking it makes it the subject.
- Pointing at a phrase or a sentence in the paper lights its card if it is drawn.

### A declaration that is not on the paper's map

A phrase can be tied to a Lean declaration that is not a step of the paper's argument. The graph then draws that declaration in the middle with the declarations it uses and those that use it, from the Lean dependency data the site already holds. One line over the drawing says so and offers the way back to the paragraph's own steps.

### The dock

A strip under the drawing, about 30% of the pane's height, shows one card in detail. A handle between the two sets its height (15% to 70%), and the height is remembered. The dock scrolls by itself. It shows, in this order of precedence:

1. the card under the pointer or holding the keyboard focus, as a preview: its title, kind, Lean name, and the first lines of its Lean statement;
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

- a subject is drawn and is wholly in view at rest;
- every card lies inside the scrollable drawing and can be brought wholly into view;
- every title is whole and at least 13 pixels;
- there is a line for every neighbour;
- the drawing is no wider than the pane at rest;
- the dock is never empty;
- a drawing taller than its area scrolls under the wheel and shows the overview.

Each repository's own script drives its pages and calls these checks.

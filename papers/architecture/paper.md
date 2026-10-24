---
title: "From a Lean source to a reviewable explanation"
subtitle: "An architectural companion to Lean Exposition"
date: "24 October 2026 · revised draft, not independently reviewed"
header-includes:
  - |
    \usepackage{tikz}
    \usepackage{float}
    \usetikzlibrary{arrows.meta,positioning,fit}
    \tikzset{archbox/.style={draw=black!45,fill=white,inner sep=6pt,align=left,font=\small},
      archrecord/.style={archbox,draw=blue!60,fill=blue!3},
      archview/.style={archbox,dashed},
      archgate/.style={archbox,draw=blue!70,fill=blue!6,line width=.8pt},
      archflow/.style={-{Stealth[length=2mm]},draw=black!65,rounded corners=3pt},
      archlink/.style={draw=blue!55,line width=.6pt},
      archnote/.style={font=\small,align=left,inner sep=0pt}}
---

**Draft scope.** This companion explains the repository's present file and command
contracts. It has not received independent mathematical or reader review. The
repository's QAOA/SK papers are a worked example, not a claim that the system has
verified their mathematical interpretation.

## 1. Start with a mathematical question

A Lean theorem answers a precise question: whether a term has the type stated in
a particular formal environment. A mathematician reading a paper asks additional
questions. Are the hypotheses the ones the prose describes? Which source proves
the analytic step that Lean does not contain? Does the short account omit a
condition retained in the long one? The answers can change while the Lean proof
still compiles.

Lean Exposition keeps these questions connected without making them identical.
Its local evidence graph records selected declarations, assumptions, cited
sources, observations and the relations among them. Three authored texts then
serve different readers: a long reasoning record, a shorter mathematical paper,
and an expository account. A mapping alongside each text binds passages to the
exact graph edition and records the state of review. The repository packages
these materials for inspection; it does not generate a proof from prose or
certify that the prose means what the author intended.

The SK example makes the distinction concrete. An admissible order parameter
is a nonnegative, nondecreasing, right-continuous, integrable function
$\gamma:[0,1)\to[0,\infty)$. Its Stieltjes measure satisfies
$\mu_\gamma([0,t])=\gamma(t)$, so an initial atom is allowed and no probability
normalisation is imposed. The result we will follow is:

**If $\gamma$ minimises the zero-temperature Parisi functional for the pure SK
model at zero external field, then every nonempty relatively open interval in
$[0,1)$ has positive $\mu_\gamma$ mass.** Equivalently,
$\operatorname{supp}_{[0,1)}\mu_\gamma=[0,1)$.

The short paper states this result, the long record reconstructs its proof,
and the exposition teaches its definitions and mechanism. The original result
and its credit remain with the cited full-support manuscript and antecedents.
Minimiser existence is a separate imported theorem. A separate scalar-value argument
and a further QAOA construction use related mathematics but do not follow merely
from the words “full support.” The graph can record those distinct claims and
their sources. The papers must still explain the analytic bridges and say which
steps are formalised, source-checked, conditional or open. The current drafts
retain unresolved review obligations; no bundle status turns them into accepted
theorems of exposition.

\begin{figure}[H]\centering
\begin{tikzpicture}
\path[draw=blue!65,fill=blue!5,line width=.7pt] (-5.55,0)--(5.55,0)--(5.05,-1.45)--(-5.05,-1.45)--cycle;
\node[archnote,align=center,text width=9.3cm] at (0,-.725)
  {\textbf{Pinned source and evidence context}\\Lean, manuscript, graph and status records};
\path[draw=black!55,fill=black!2,line width=.7pt] (-4.6,-2.55)--(4.6,-2.55)--(4.08,-4.0)--(-4.08,-4.0)--cycle;
\node[archnote,align=center,text width=7.7cm] at (0,-3.275)
  {\textbf{Long reasoning record}\\Contact, curvature and all gap cases};
\path[draw=black!55,fill=white,line width=.7pt] (-3.65,-5.1)--(3.65,-5.1)--(3.13,-6.55)--(-3.13,-6.55)--cycle;
\node[archnote,align=center,text width=5.95cm] at (0,-5.825)
  {\textbf{Focused short paper}\\Theorem 1, hypotheses and credit};
\path[draw=blue!65,fill=blue!5,line width=.7pt] (-2.7,-7.65)--(2.7,-7.65)--(2.18,-9.1)--(-2.18,-9.1)--cycle;
\node[archnote,align=center,text width=4.15cm] at (0,-8.375)
  {\textbf{Reader exposition}\\Prerequisites and the gap picture};
\draw[archflow] (0,-1.46)--node[archnote,fill=white,inner sep=2pt,right]{reconstructs selected argument}(0,-2.54);
\draw[archflow] (0,-4.01)--node[archnote,fill=white,inner sep=2pt,right]{selects theorem and credit}(0,-5.09);
\draw[archflow] (0,-6.56)--node[archnote,fill=white,inner sep=2pt,right]{re-explains with prerequisites}(0,-7.64);
\draw[archflow,dashed] (-2.44,-8.375)--(-6.05,-8.375)--(-6.05,-.725)--(-5.3,-.725);
\node[archnote,fill=white,align=center,text width=1.7cm] at (-6.05,-4.55) {claim-site links return to exact sources};
\end{tikzpicture}
\caption{An inverted reader funnel adapted from Will Cook's existing mathematics-map visual. It selects a way into one scoped result; the widths represent editorial selection, not page counts, proof strength or the length of the expository paper. Solid arrows name authoring transitions. The separate dashed route returns a reader from a claim to pinned evidence, without asserting that any text or check certifies mathematical meaning.}
\end{figure}

The sources have different authors and jobs. OpenAI supplies the two original
mathematical manuscripts and the selected Lean development. Earlier papers
supply mathematical results and methods credited where used. Prove2Me supplies
a design for collaborative formalisation and a separate public theorem service.
Our contribution here is the reconstructed accounts, their source
correspondence, and the local tools for inspecting and revising them. Neither
an explanation nor a platform link transfers authorship of the mathematics.

## 2. Open a claim and follow its explanation

The [consumer guide](../../docs/bundle-consumers.md#start-with-the-authored-support-theorem)
gives one complete command to assemble the supplied papers. With that bundle
in `build/qaoa-sk-authored`, a reader can open the theorem directly:

```sh
lean-exposition query-papers build/qaoa-sk-authored \
  --paper short --passage main-result --format text
```

The result identifies the exact edition, the passage's mapped claims and
assumptions, its recorded prerequisites, and the kinds and outcomes of its
associated checks. The JSON format retains the full text and source records.
Both formats read one validated capture; neither opens the external Lean
checkout or proves that a mapping is mathematically faithful.

The starting material is a chosen, pinned source: for example, a Lean checkout
with its toolchain and a mathematical manuscript with a known edition. An author
or extractor records relevant declarations and evidence in a graph. A theorem
that uses a lemma points to that lemma in a dependency relation. A claim's link
to a selected formal statement is a different, formalisation relation; a
citation identifies an external source edition. The reader can follow the
recorded relation from a claim to its stated support, or ask which other claims
refer to a changed item. The meaning and direction of each link remain visible.


An author can work through the SK example in a deliberate order. The long
account reconstructs the full support-gap calculation and its dependence on
the variation formula. The short paper distils the mathematical argument
with its hypotheses visible. The expository account explains why a
hypothetical gap conflicts with the moment identity before returning to the
formal statement. These are authored stages, not automatically generated
summaries. Their emphases differ, but a passage map
binds each account to the same selected graph edition. If an author changes the
source graph or a passage, the corresponding byte hash changes and assembly
requires a revised mapping. A successful hash check establishes correspondence
to recorded bytes, not that the explanation is true.

\begin{figure}[htbp]\centering
\begin{tikzpicture}
\node[archrecord,text width=7.4cm,minimum height=1.08cm] (claim) at (0,0)
  {\textbf{One selected graph claim}\\A zero-field SK minimiser at zero temperature has full relative Stieltjes support on $[0,1)$.};
\node[archbox,text width=3.15cm,minimum height=1.4cm] (long) at (-4.2,-3.0)
  {\textbf{Long record}\\Contact, curvature and the gap proof.};
\node[archbox,text width=3.15cm,minimum height=1.4cm] (short) at (0,-3.0)
  {\textbf{Short paper}\\Theorem 1 and its proof outline.};
\node[archbox,text width=3.15cm,minimum height=1.4cm] (expo) at (4.2,-3.0)
  {\textbf{Exposition}\\Support and gap intuition.};
\draw[archlink,-{Stealth[length=2mm]}] (long.north) -- (-4.2,-1.45) -- (-2.5,-1.45) -- (claim.south -| -2.5,0);
\node[archnote,fill=white,inner sep=2pt,left] at (-4.2,-1.9) {map selects claim};
\draw[archlink,-{Stealth[length=2mm]}] (short.north) -- (claim.south);
\node[archnote,fill=white,inner sep=2pt,align=center,text width=2.2cm] at (1.3,-1.45) {map selects\\claim};
\draw[archlink,-{Stealth[length=2mm]}] (expo.north) -- (4.2,-1.45) -- (2.5,-1.45) -- (claim.south -| 2.5,0);
\node[archnote,fill=white,inner sep=2pt,right] at (4.2,-1.9) {map selects claim};
\node[archnote,text width=11.8cm] at (0,-4.65)
  {Each passage has its own text and mapping. These links select the same claim; they do not make the accounts interchangeable or reviewed.};
\end{tikzpicture}
\caption{Passage-to-claim correspondence, not a proof dependency. Three authored passages can point to one recorded mathematical claim. The forked composition adapts the shared-support, three-version figure in the Plectis Erdős systems paper.}
\end{figure}

The graph supports several *typed views* of the same records. A declaration
view follows formal Lean dependencies; an argument view shows curated support
and formalisation relations with their own meanings and directions;
a citation view follows sources; a platform view
follows public decomposition metadata; and a provenance view follows recorded
source and receipt links. A selected goal determines where traversal starts,
without removing unrelated evidence from the underlying graph. A view of no
recorded links reports an absence in this graph, not mathematical independence.

A reader may instead start from one paper, a section or a named passage. For
example, the short paper's gap argument can be opened beside the contact and
curvature steps it uses. The paper view gives the exact text and its recorded
correspondence to graph claims, then expands their recorded prerequisites,
including assumptions introduced elsewhere. Selecting a smaller piece of prose
does not make its conditions disappear. The source-grounded intermediate records
remain distinct from the selected formal interface and retain their own evidence
status.

Two questions about another account should be kept separate. “Where is this
claim mapped?” asks for passages whose maps name it directly. “Which passages
use it?” asks for passages whose mapped claims reach it through recorded support
relations. The second answer includes a path explaining the match. A passage
may rely on an ingredient without explaining it, and a teaching example may
explain an idea without being a premise. The query therefore reports recorded
correspondence and reachability, not a judgment about what every sentence teaches
or proves.

Section selection follows the actual document outline. If a mapped passage
crosses a section boundary, the view identifies the overlap and retains the full
passage with its support. It also reports text without a passage map, passages
outside the selection, required assumptions and unresolved records. Reading order
is a document relation; it does not enter the mathematical support traversal.
The graph remains partial, so a complete expansion of recorded links is not a
complete mathematical dependency audit.

The three accounts share references to the same graph edition. A front end can
switch from the short paper to the long record or exposition while keeping the
selected claim in view, and can regenerate its answers from the existing bundle.
No second graph or extra bundle member is needed. The architectural companion
itself remains a guide outside the bundle's three mathematical paper stages.

\begin{figure}[htbp]\centering
\begin{tikzpicture}
\node[archrecord,text width=4.35cm,minimum height=1.1cm] (section) at (-3.9,0)
  {\textbf{Paper section}\\Theorem and surrounding explanation};
\node[archrecord,text width=4.35cm,minimum height=1.1cm] (passage) at (-3.9,-2.3)
  {\textbf{Selected passage}\\Its exact text and byte span};
\node[archview,text width=4.35cm,minimum height=1.1cm] (map) at (-3.9,-4.6)
  {\textbf{Passage mapping}\\Recorded claim, citation and assumption IDs};
\node[archgate,text width=4.35cm,minimum height=1.1cm] (claim) at (3.9,-4.6)
  {\textbf{Selected graph claim}\\Recorded links are expanded};
\node[archrecord,text width=4.35cm,minimum height=1.1cm] (supports) at (3.9,-2.3)
  {\textbf{Recorded support}\\Formal statement, assumptions and evidence};
\node[archview,text width=4.35cm,minimum height=1.1cm] (rest) at (3.9,0)
  {\textbf{Other graph records}\\Retained in the bundle};
\draw[archflow] (section) -- node[archnote,fill=white,inner sep=2pt,right]{overlaps text span} (passage);
\draw[archflow] (passage) -- node[archnote,fill=white,inner sep=2pt,right]{hash-bound to} (map);
\draw[archlink,-{Stealth[length=2mm]}] (map) -- node[archnote,fill=white,inner sep=2pt,above]{selects claim ID} (claim);
\draw[archflow] (claim) -- node[archnote,fill=white,inner sep=2pt,right]{expands typed links} (supports);
\node[draw=black!28,dashed,fit=(rest)(supports)(claim),inner sep=9pt] (whole) {};
\node[archnote,anchor=south east] at (whole.north east) {shared graph edition};
\end{tikzpicture}
\caption{A local paper view follows document structure, passage-to-claim mapping and recorded argument relations without discarding other graph records. The selected support includes typed relations whose meanings and directions remain explicit; this is not a uniform proof graph. The selection-and-support shape adapts the registered-support figure in the Plectis Erdős systems paper.}
\end{figure}

### Following one step through the three accounts

Take the positive-coefficient case of the gap argument. The short paper uses
contact at the endpoints and strict convexity of the derivative of a diffusion
moment to obtain a contradiction. The long record reconstructs the analytic
estimate behind that convexity. The exposition first illustrates the missing
area, then defines the moment and derives the argument. These are three
useful ways to approach the same step.

Write $q(t)=\mathbb E[\Phi_x(t,X_t)^2]$, where $\Phi$ is the control value
and $X$ its controlled diffusion for this same coefficient. On a hypothetical
gap $(\ell,r)$ with endpoints in the support and constant coefficient $c>0$,
minimality gives $q(r)-q(\ell)=r-\ell$ and $q'(\ell),q'(r)\le1$.
The separate local curvature estimate gives $q'''>0$, so $q'$ is strictly
convex. Together these statements imply $q'(t)<1$ inside the gap. Integration
then gives $q(r)-q(\ell)<r-\ell$, the contradiction. Zero coefficients and
initial or terminal gaps require their own arguments. The long record's
§§3–5 supply these steps; a picture of a curve alone cannot establish them.

A passage query opens the paragraph with its exact hypotheses. Expanding its
recorded prerequisites leads to the source-located contact and curvature
claims. The latter leads further to the integrated coercive estimate, its
rational identity, the sign inequalities and the approximation step. The
selected Lean interface remains separately identifiable. Its presence does
not certify every intermediate analytic reconstruction or the density
corollary added to the short paper.

\begin{figure}[htbp]\centering
\begin{tikzpicture}
\node[archrecord,text width=8.6cm,minimum height=1.25cm,align=center] (gap) at (0,0)
 {\textbf{The positive-gap contradiction}\\An admissible minimiser, a positive constant interval, and both endpoints in the support};
\node[archbox,text width=4.1cm,minimum height=1.65cm,align=center] (contact) at (-3.8,-3.5)
 {\textbf{Endpoint contact}\\$q(r)-q(\ell)=r-\ell$\\$q'(\ell),q'(r)\le1$};
\node[archbox,text width=4.1cm,minimum height=1.65cm,align=center] (curvature) at (3.8,-3.5)
 {\textbf{Strict curvature}\\$q'''>0$ makes $q'$ strictly convex on the positive plateau.};
\draw[archflow] (-1,-.73)--(-1,-1.8)--(-3.8,-1.8)--(contact.north);
\draw[archflow] (1,-.73)--(1,-1.8)--(3.8,-1.8)--(curvature.north);
\node[archnote,anchor=south,align=center] at (-3.1,-1.65) {uses the endpoint identities};
\node[archnote,anchor=south,align=center] at (3.1,-1.65) {uses the strict estimate};
\node[archnote,text width=11.5cm,align=center] at (0,-5.05)
 {Together: the endpoint slope bounds and strict convexity give $q'<1$,\\contradicting the required integral $r-\ell$.};
\end{tikzpicture}
\caption{A selected argument view. Arrows point from the contradiction to the ingredients it uses. This is the positive-coefficient bounded-gap branch only; zero coefficients and initial and terminal gaps have separate arguments. The figure adapts the shared-support composition above. Its relations are curated from the original proof, not extracted Lean dependencies.}
\end{figure}

The difference between a direct match and a prerequisite match is practical.
A passage that states the final support theorem may use curvature without
teaching the curvature proof. A direct query for the curvature claim finds
its mapped explanations. A prerequisite query also finds passages whose
recorded argument uses it, and returns the relation path. This lets a future
reader interface offer “explain this step” and “show where it is used” as
different actions. Both remain limited by the coverage of the authored graph.

For example, the following commands distinguish those two questions:

```sh
lean-exposition query-papers build/qaoa-sk-authored \
  --node support.positive_curvature --format text
lean-exposition query-papers build/qaoa-sk-authored \
  --node support.positive_curvature --relation prerequisites --format text
```

An example can also test the correspondence. The long record's one-step
Gaussian calculation uses $\gamma=0$, an admissible coefficient which is not
a minimiser. Its map therefore selects conditional rounding, not the
minimiser-dependent asymptotic construction. Labelling the prose an example
would not excuse a map that imported the wrong hypotheses.

Cycles may occur among recorded relations. The consumer reports their strongly
connected components, the kinds of links within and between them, and a
directed acyclic graph of the components. This is a way to navigate mutually
connected records; it is not a proof that a circular mathematical argument is
valid. Choosing the reverse “consumers” direction can show what refers to a
declaration. Neither direction silently changes the original evidence or its
status.

The design follows established work on formal mathematics.
[LeanArchitect's](https://github.com/hanwenzhu/LeanArchitect/tree/9f3bb53916b9d6fa05b7777389e1844f82b1c9a6)
selected collector and output code informed the separation of declaration
identity, extracted references and presentation choices;
[leanblueprint](https://github.com/PatrickMassot/leanblueprint/tree/56e066d30fb7b608a63f4241fee80982d7eae3ef) connects
mathematical prose with named formal declarations and authored dependencies.
The [doc-gen4 index](https://github.com/leanprover/doc-gen4/tree/0e1ffe2e4ba5ecfdfaf15c65b8d3805dbb7134ae) and
[Verso Blueprint](https://github.com/leanprover/verso-blueprint/tree/4932a7e3b283dd763f546e949ece88c3aed58a5a) provide further examples of source and
consumer boundaries. These are documented in the [source study](../../docs/literature.md),
with distinct source revisions. The Lean extractor adapts structural traversal
from [Comparator](https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/Comparator/Util.lean), retaining Lean FRO, LLC and Henrik Böving's Apache-2.0 notice
in its source. The repository does not claim to have invented these mechanisms.

## 3. What each check can say

The formal conclusion is more specific than a shared theorem title. In
`OAI.ZeroTemperatureSK`, the selected declaration takes a Brownian system,
an admissible coefficient and a proof of minimality. Its conclusion asserts
existence of a Stieltjes measure and an associated diffusion, full relative
support for every associated measure, strict increase of the coefficient,
and both selected moment identities for every associated diffusion on
$[0,1)$. It does not assert minimiser existence, positive Stieltjes density
or QAOA convergence. The [challenge](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.lean#L81-L92)
and [implementing theorem](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Main.lean#L35-L59)
are distinct files at the same revision. The challenge's admitted proof
specifies the comparison target; it is not the implementation's proof.

The formal developments depend on Lean and mathlib. Their scholarly sources
are de Moura and Ullrich's [*The Lean 4 Theorem Prover and Programming
Language* (2021)](https://doi.org/10.1007/978-3-030-79876-5_37) and
The mathlib Community's [*The Lean Mathematical Library*
(2020)](https://doi.org/10.1145/3372885.3373824). These credits explain
the software foundations; the exact toolchain and dependency pins identify
the environment of a particular proof.

Lean, Comparator and Prove2Me answer different questions. A successful Lean
build concerns a particular formal statement in a pinned environment. The
Comparator runs a separately stated challenge against a selected implementation
and axiom policy. Lean's versioned [proof-validation documentation](https://lean-lang.org/doc/reference/4.35.0/ValidatingProofs/)
explains these checks and their trust assumptions. The research source uses
Lean 4.34.1 with a historical standalone Comparator; the later integrated
interface does not establish a result for that earlier environment. A platform observation records public metadata at a time:
visibility, status, environment and decomposition links. These observations
must stay separate. In particular, a platform's “proved” label does not mean
this repository replayed the proof, and a Comparator startup failure is not a
mathematical counterexample. The QAOA/SK example preserves distinct observations. An early invocation
could not start the Comparator. Later invocations built and exported the
full-support and scalar-value challenges, then stopped during their solution
builds because imported compiled modules were missing. Neither exported or accepted its solution.
This is an operational failure before comparison, not a refutation. A corrected
local build configuration is a new input edition and requires its own replay;
repairing the configuration does not change the historical outcome.

\begin{figure}[htbp]\centering
\begin{tikzpicture}
\node[archrecord,text width=3.35cm,minimum height=2.0cm,align=center] (formal) at (-4.25,0)
  {\textbf{Lean and Comparator}\\Type check and separate challenge, each with its own run status};
\node[archview,text width=3.35cm,minimum height=2.0cm,align=center] (mapping) at (0,0)
  {\textbf{Passage map}\\Exact text, graph edition, mapped claims and review state};
\node[archview,text width=3.35cm,minimum height=2.0cm,align=center] (platform) at (4.25,0)
  {\textbf{Public platform}\\Theorem status and decomposition; read-only context};
\node[archgate,text width=11.8cm,minimum height=1.25cm,align=center] (review) at (0,-4.3)
  {\textbf{Mathematical and editorial review}\\Compare hypotheses, analytic steps, scope and credit against the formal statement and cited sources.};
\draw[archflow] (formal.south)--node[archnote,fill=white,inner sep=2pt,right]{Lean/Comparator status}(-4.25,-3.65);
\draw[archflow] (mapping.south)--node[archnote,fill=white,inner sep=2pt,right]{mapped claims and text}(0,-3.65);
\draw[archflow] (platform.south)--node[archnote,fill=white,inner sep=2pt,right]{public status context}(4.25,-3.65);
\end{tikzpicture}
\caption{Three distinct records can inform a later human review. Their arrows specify what each channel supplies; none certifies mathematical interpretation or says review has occurred. Adapted from the two-correspondence figure in the Plectis Erdős systems paper.}
\end{figure}

Extraction also has a narrower meaning than proof acceptance. Direct references
in a declaration's type, available proof body and structural metadata are
recorded separately. A hidden proof body limits body traversal even when Lean
can report axiom metadata from the compiled environment. The request, driver,
source set and output belong to the extraction evidence; a changed source set
requires a fresh check. A process exit code alone does not identify which
named challenges were accepted. The [verification guide](../../docs/verification.md)
explains these boundaries and the retained observations.

The system deliberately reports `not_run`, `unverified`, `not_reviewed` and
`needs_revision` where they apply. A build, a source hash, a graph closure and
a rendered PDF each establish a narrower fact than human comprehension. One
can inspect the records now while still asking a mathematician to check the
argument.

## 4. Why the bundle has eight files

The portable bundle has a manifest, the graph, and one Markdown text with a
passage map for each of the three stages. The manifest records the format,
local publication state and hashes of the other seven files. The graph keeps
typed evidence and status. Each map binds its authored text to exact graph
bytes, selected goals, claims, citations, assumptions, passages and review
state. The pairings keep mathematical prose readable while making its
recorded support inspectable.

Removing a map would hide one account's graph correspondence; merging the
texts would erase their distinct audiences. Lean source, manuscript editions
and verification receipts remain external and are identified by records and
digests where available. A consumer validates the directory or ZIP and reads
selected evidence or paper views. The bundle is not a self-contained proof
archive, and its `semantic_certification` field is false.

The work's name, its format and its exact edition serve different purposes. The
name can remain the same when the work changes. The manifest's SHA-256 identifies
one captured edition, including the graph, three texts and their maps. A paper
passage has a reference to its text and mapping, while a graph claim has a
reference to its graph snapshot. A section's byte offset identifies its location
in that particular text. These are precise handles for an edition, not promises
that a passage or claim keeps the same meaning after revision.

Suppose an author leaves a paragraph unchanged but changes its mapping from an
unverified source argument to a selected formal statement. Its words are the
same, but the correspondence now makes a different assertion. The new map and
manifest identify a successor, and the earlier review remains attached to the
old one. Similarly, a changed hypothesis or source edition must not be hidden
behind an unchanged claim name. A query can help find recorded consumers of the
changed item; because the graph is partial, that list does not certify that every
affected passage has been found.

The review request, original response and author decision belong beside the
bundle. If feedback on edition A produces edition B, a later adoption record
names both editions and explains what changed. An author recording a correction
is different from a reader confirming it. The old response is preserved, and
acceptance is not transferred by refreshing hashes. A PDF or HTML representation
also needs its own identity: Markdown bytes do not identify a rendered page or
its appearance.

\begin{figure}[H]\centering
\begin{tikzpicture}
\node[archrecord,text width=5.2cm,minimum height=.85cm,align=center] (fixed) at (0,0)
  {\textbf{Fixed edition}\\Paper and graph hashes};
\node[archbox,text width=5.2cm,minimum height=.85cm,align=center] (proposal) at (0,-1.8)
  {\textbf{Proposed change}\\Revise a passage or claim};
\node[archbox,text width=5.2cm,minimum height=.85cm,align=center] (draft) at (0,-3.6)
  {\textbf{New draft}\\Rebind maps to changed bytes};
\node[archgate,text width=5.2cm,minimum height=.85cm,align=center] (review) at (0,-5.4)
  {\textbf{Review}\\Compare claim, source and scope};
\node[archrecord,text width=4.4cm,minimum height=.85cm,align=center] (accept) at (-3.15,-7.8)
  {\textbf{Accepted edition}\\Store manifest hash and decision};
\node[archview,text width=4.4cm,minimum height=.85cm,align=center] (decline) at (3.15,-7.8)
  {\textbf{Declined proposal}\\Retain reason; no status transfer};
\node[archview,text width=4.4cm,minimum height=.85cm,align=center] (reader) at (-3.15,-9.75)
  {\textbf{Reader view}\\Open the reviewed edition};
\draw[archflow] (fixed.south)--node[archnote,fill=white,inner sep=2pt,right]{proposes edit}(proposal.north);
\draw[archflow] (proposal.south)--node[archnote,fill=white,inner sep=2pt,right]{rebinds changed bytes}(draft.north);
\draw[archflow] (draft.south)--node[archnote,fill=white,inner sep=2pt,right]{submits draft}(review.north);
\draw[archflow] (review.south)--(0,-6.45)--(-3.15,-6.45)--node[archnote,fill=white,inner sep=2pt,right]{accepts exact edition}(accept.north);
\draw[archflow] (review.south)--(0,-6.45)--(3.15,-6.45)--node[archnote,fill=white,inner sep=2pt,right]{declines change}(decline.north);
\draw[archflow] (accept.south)--node[archnote,fill=white,inner sep=2pt,right]{opens reviewed bytes}(reader.north);
\draw[archflow,dashed] (review.west)--(-6.05,-5.4)--(-6.05,-1.8)--node[archnote,fill=white,inner sep=2pt,above]{requests revision}(proposal.west);
\end{tikzpicture}
\caption{Review-state transitions for an immutable edition. A revision creates new bytes and does not inherit an earlier decision. The accept/revise/decline composition adapts the refinement figure in the Plectis Erdős systems paper. The present QAOA/SK drafts have not been approved.}
\end{figure}

The reading experience can be simpler. A PDF can lead with the argument and
offer source and status links at the relevant claim. A consumer can show a
small paper or theorem view, expand dependencies on request, and leave hashes
in the manifest. A duplicate derived view can be regenerated from the graph.
These changes must preserve source versus interpretation, formal check versus
review, and one edition versus another.

## 5. Use and external handoff

The local command-line tool validates graphs, selects goals, creates empty
scaffolds, assembles authored paper-and-map pairs, and checks or inspects a
bundle. Paper queries also find direct correspondences or recorded prerequisite
uses across the three accounts. Their answers retain the exact edition,
matching passages and support boundary. The consumer guide gives commands for
a local directory and its exported ZIP. Assembly requires valid existing
bindings; it neither writes mathematics nor repairs a stale interpretation.

The optional Prove2Me adapter reads partial public theorem and decomposition
metadata using an existing credential and pinned documentation version. It
filters private or unknown children; it does not submit proofs, upload papers
or receive bundle reviews. The Prove2Me paper separates immutable statements,
proof submissions and human audit (Chen, Marwaha, Lu, Yuen and Peng, 2026,
§§3–4). It already includes natural-language descriptions, explanations,
source links and curated milestones; our contribution is the particular
combination of three authored accounts with exact-edition passage maps and
queries that retain distinct support and evidence. This is an analogy, not evidence these papers were attached to a
theorem card. An external paper handoff would need an explicit edition,
attachment and feedback contract.

This companion remains a draft without independent human acceptance.
The next review should test whether a mathematician can start at a paper claim,
find the exact formal and analytic sources, and understand which verification
steps are complete without learning the internal file layout first.

**Sources.** This draft follows the local CLI, graph, bundle and consumer
contracts and QAOA/SK example, revised on 24 October 2026. Figure 1
adapts Will Cook's existing mathematics-map video funnel. The remaining figures adapt
Will Cook's
[*A Repository-Based System for Research and Publication*](https://github.com/wcook04/plectis-erdos/blob/61fb590921e3b5a100dc264bed052c9cf6959daf/paper/systems/claim-faithful-publication-systems-paper.tex)
([CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)); the adapted
compositions are labelled hypothesis, theorem, checks and refinement
in that source. The concrete argument view further adapts its shared-support
composition. The editorial distinctions also follow the author's [public
mathematical writing methods](https://github.com/wcook04/plectis-erdos/tree/a0878310af794d7a0f76cc11f4de3a20c795dc60). The Prove2Me boundary follows Chen, Marwaha, Lu, Yuen and Peng,
[*Prove2Me*](https://arxiv.org/abs/2608.28433v2), §§3–5; its case studies do
not evaluate Lean Exposition.

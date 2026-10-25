---
title: "From a Lean source to a reviewable explanation"
subtitle: "An architectural companion to Lean Exposition"
date: "25 October 2026 · revised draft, not independently reviewed"
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

**Draft scope.** This companion describes the local file and query contracts.
Its worked trace demonstrates recorded correspondence, not mathematical
certification or an observed improvement in reader understanding.

## 1. What a reader needs to recover

A reader reaches the sentence “the gap cannot occur.” They need to know which
hypotheses apply, where the strict inequality is proved, what the formal
statement covers, and which edition they are reviewing. A Lean proof can still
compile after an author changes the answer to any of these questions in prose.
Source links help; the remaining task is to compare the particular claim,
argument and checking record rather than infer support from a shared title.

Lean Exposition makes the author's proposed correspondence inspectable. One
local graph records claims, typed relations, source editions and checks. Three
authored mathematical accounts have separate passage maps into that graph.
The command-line and Python consumers expose those records together with the
exact text. Authors and reviewers still have to judge whether the proposed
correspondence is right. The tools neither write the argument nor discharge
its mathematical obligations.

The example is full support in the zero-temperature Sherrington–Kirkpatrick
(SK) model, which maximises random pair interactions over signs. Its Parisi
formula expresses the limiting optimum as a minimum over nonnegative,
nondecreasing, right-continuous, integrable functions
$\gamma:[0,1)\to[0,\infty)$. Their Stieltjes measures satisfy
$\mu_\gamma([0,t])=\gamma(t)$; an atom at zero is allowed and no probability
normalisation is imposed. The statement to follow is:

**For the pure SK model at zero external field, every admissible minimiser
has $\operatorname{supp}_{[0,1)}\mu_\gamma=[0,1)$.** Every nonempty relatively
open interval therefore receives positive mass. Minimiser existence is an
imported theorem, separate from this conditional conclusion.

The explanation crosses a formal statement, ordinary analytic estimates and
further consequences. OpenAI supplies the two source manuscripts and selected
Lean development; the mathematical results and antecedents retain their
literature credit. Our work here is the reconstructed accounts, their passage
correspondence and the local consumer. Positive density, a scalar value formula
and circuit convergence for the quantum approximate optimization algorithm
(QAOA) each need further arguments; they cannot inherit
verification from the words “full support.”

## 2. Follow the gap argument

For an admissible minimiser, let
$q(t)=\mathbb E[\Phi_x(t,X_t)^2]$, the second moment of the value function's
spatial gradient along its diffusion. Suppose a bounded support gap
$(\ell,r)$ has positive constant coefficient. Contact gives
$q(r)-q(\ell)=r-\ell$ and $q'(\ell),q'(r)\le1$. A separate analytic estimate
gives $q'''>0$. Thus $q'$ is strictly convex, lies below one inside the gap,
and has integral smaller than $r-\ell$: a contradiction. Zero coefficients
and initial or terminal gaps require separate arguments.

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
\caption{A selected argument view. Arrows point from the contradiction to the ingredients it uses. This is the positive-coefficient bounded-gap branch only; zero coefficients and initial and terminal gaps have separate arguments. The figure adapts the shared-support composition in the Plectis Erdős systems paper. Its relations are curated from the original proof, not extracted Lean dependencies.}
\end{figure}

The [consumer guide](../../docs/bundle-consumers.md#start-with-the-authored-support-theorem)
gives the assembly command for the supplied papers. With the result in
`build/qaoa-sk-authored`, ask which short-paper passage uses curvature:

```sh
lean-exposition query-papers build/qaoa-sk-authored \
  --paper short --passage main-result \
  --node support.positive_curvature --relation prerequisites
```

A local run against the revised authored bundle returned the following values (selected fields; JSON nesting omitted):

```text
anchor: main-result
evidence_class: source_argument
root_node_id: support.full_relative_support
target_node_id: support.positive_curvature
review_state: needs_revision
semantic_certification: false
```

Its passage correspondence and returned witness links give this exact route:

```text
short / main-result
  --maps_claim--> support.full_relative_support
  --supports--> support.no_bounded_gap
  --supports--> support.positive_curvature
```

The view retains `assumptions.full_support_minimizer`, including admissibility
and minimality on a Brownian system. The curvature node is `unverified`;
its associated source-byte check is `passed`, while the recorded semantic
review is `not_run`. Its locator is `curvature.tex:9–52; prop:gap-curvature`.
These are distinct returned records, not a single theorem-verification badge.
The captured manifest SHA-256 is:

```text
9e18e224a20e4a57663497a44735399058c38c1d03adf33d20beff1b1d3514e9
```

A successor assembly has a new identity; keep the requested digest with the
review and use `--expect-manifest` to reject a different edition. The query
reads embedded records, not the external source or receipt files.


Here `maps_claim` is an assertion in a passage map; `supports` is an authored
claim-to-ingredient relation. The curvature source locator leads to
[OpenAI's `prop:gap-curvature`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/curvature.tex#L9-L52).
The long record's [“Strict curvature on a constant interval”](../qaoa-sk/long/reasoning-record.md#curvature-and-gap-certificate)
reconstructs the signs, integrated coercivity and approximation behind that
estimate. Read it to recover the strict inequality under its plateau hypotheses,
then return to the [short paper's gap argument](../qaoa-sk/short/paper.md#gap-elimination):
contact supplies the endpoint data used with that inequality.
[“Excluding terminal, interior and initial gaps”](../qaoa-sk/long/reasoning-record.md#gap-elimination)
supplies the other cases. Finding the curvature passage does not explain its
proof, and a rational positivity certificate alone does not justify the
analytic estimate.

The formal route is separate: `full_support` is recorded as
`formalizes` → `lean.full_support`. The selected
[challenge](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.lean#L81-L92)
and [implementation](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Main.lean#L35-L59)
assert measure and diffusion existence, full relative support, strict increase
and two moment identities, conditional on a supplied admissible minimiser.
They do not assert minimiser existence, positive density or circuit convergence.
No formalisation edge from the curvature claim is invented by this walkthrough.

Correspondence can itself require an argument. The long record's
[formal-interface discussion](../qaoa-sk/long/reasoning-record.md#formal-interfaces)
distinguishes a formal limit along a prescribed sequence of step sizes from
the manuscript's ordinary right derivative, which covers all positive step
sizes tending to zero. It supplies the intervening convexity argument. That
mathematical bridge must be read and assessed; following a `formalizes` edge
cannot perform it.

Omitting `--relation prerequisites` instead asks whether curvature is **directly
mapped** in this passage. The theorem passage has no such direct match; its
recorded support reaches curvature. A passage can use an ingredient without
explaining it. Prerequisite
queries follow recorded Lean references, curated support, formalisation
correspondence and explicit assumptions, retaining each kind in the witness
path. Citations, platform decomposition and document order do not enter that
traversal. Reachability does not certify that the ingredients suffice.

The long record's **“An exact one-step calculation”** is a useful negative test.
It uses $\gamma=0$, which is admissible but not a minimiser. Its map selects
conditional rounding, not the minimiser-dependent asymptotic construction.
The calculation and a valid hash cannot supply the missing minimality premise.
This is a judgment about the map's meaning, not a defect traversal can repair.

## 3. Write three accounts from the same sources

\begin{figure}[H]\centering
\begin{tikzpicture}
\path[draw=blue!65,fill=blue!5,line width=.7pt] (-5.55,0)--(5.55,0)--(5.05,-1.45)--(-5.05,-1.45)--cycle;
\node[archnote,align=center,text width=9.3cm] at (0,-.725)
  {\textbf{Pinned mathematical context}\\Lean, Comparator records, proofs and literature};
\path[draw=black!55,fill=black!2,line width=.7pt] (-4.6,-2.55)--(4.6,-2.55)--(4.08,-4.0)--(-4.08,-4.0)--cycle;
\node[archnote,align=center,text width=7.7cm] at (0,-3.275)
  {\textbf{Long reasoning record}\\Contact, curvature and all gap cases};
\path[draw=black!55,fill=white,line width=.7pt] (-3.65,-5.1)--(3.65,-5.1)--(3.13,-6.55)--(-3.13,-6.55)--cycle;
\node[archnote,align=center,text width=5.95cm] at (0,-5.825)
  {\textbf{Focused short paper}\\Contribution, proof and credit};
\path[draw=blue!65,fill=blue!5,line width=.7pt] (-2.7,-7.65)--(2.7,-7.65)--(2.18,-9.1)--(-2.18,-9.1)--cycle;
\node[archnote,align=center,text width=4.15cm] at (0,-8.375)
  {\textbf{Short exposition}\\Prerequisites and the gap picture};
\draw[archflow] (0,-1.46)--node[archnote,fill=white,inner sep=2pt,right]{reconstruct the\\complete argument}(0,-2.54);
\draw[archflow] (0,-4.01)--node[archnote,fill=white,inner sep=2pt,right]{select contribution\\and decisive proof}(0,-5.09);
\draw[archflow] (0,-6.56)--node[archnote,fill=white,inner sep=2pt,right]{teach the\\selected result}(0,-7.64);
\draw[archflow,dashed] (-2.44,-8.375)--(-6.05,-8.375)--(-6.05,-.725)--(-5.3,-.725);
\node[archnote,fill=white,align=center,text width=1.7cm] at (-6.05,-4.55) {claim-site links return to exact sources};
\end{tikzpicture}
\caption{Three writing tasks, adapted from Will Cook's existing mathematics-map visual. Widths indicate editorial selection, not page counts or proof strength. Solid arrows name authored transitions; the dashed arrow follows source correspondence. Each writer retains all earlier inputs. Neither route certifies mathematical meaning.}
\end{figure}

The [three writing skills](../../skills/README.md) guide people and agents;
they are not runtime stages. The long writer reads the selected Lean definitions
and proofs, original arguments, literature and Lean/Comparator records to
reconstruct a complete selected argument. The expert-paper writer retains all
those inputs and the long account, then selects the contribution and decisive
proof. The exposition writer also reads the short paper and chooses one
meaningful result to teach at stated prerequisites. Inputs accumulate; neither
later paper has to cover every earlier result.

| Entry | What that account adds |
| --- | --- |
| [Long record, “Strict curvature on a constant interval”](../qaoa-sk/long/reasoning-record.md#curvature-and-gap-certificate), passage `curvature` | The analytic derivation, boundary control and passage to an integrable coefficient |
| [Short paper's gap proof](../qaoa-sk/short/paper.md#gap-elimination), passage `gap-proof` | The decisive contradiction and distinct gap cases |
| [Exposition, “Why a flat interval cannot minimise”](../qaoa-sk/expository/main.md#5-why-a-flat-interval-cannot-minimise), passage `contact-and-gap` | The contact and area argument at its declared reader prerequisites |

Their maps retain the setting and assumptions of each selected claim. Curvature
itself does not require minimality; contact and the no-gap conclusion do.
Matching the same graph edition must not flatten those differences. Authors
follow omitted proofs to their exact conclusion, then return to the shorter
account. Each draft is also read in sequence: a later definition cannot repair
an earlier unexplained step for the first-time reader.

A graph can index the long record's existing passages. It cannot determine a
sufficient proof order or supply missing prose. Markdown is the prose authority;
maps identify its exact passages. The paper view's `document_parts` partitions
all source bytes into mapped passage blocks and surrounding unmapped text.
`reconstruct_paper` requires the expected manifest and those unchanged parts,
then returns the original Markdown bytes, preserving markers, definitions,
headings and references. It rejects changed, omitted or reordered parts. This
recovers an authored record; a rewritten argument needs fresh editorial judgment.

## 4. What the backend returns

The reader can start from a paper, a mathematical claim or a source they want
to trace. The backend uses the same captured records for each route:

| Reader task | Existing Python entry and CLI |
| --- | --- |
| Inspect every captured graph record and all three papers | `project_corpus` / `inspect-corpus` |
| Follow one kind of relation from selected nodes | `project_graph` / `inspect --view` |
| Find what refers to a source, citation, evidence record or node | `query_corpus` / `query-corpus` |
| Open a paper or passage and its recorded support | `project_paper` / `inspect-bundle --paper`; `query_papers` / `query-papers` also selects sections and finds cross-paper occurrences |

The [API contract](../../docs/bundle-consumers.md#view-the-whole-recorded-corpus)
specifies signatures and versions. The corpus retains disconnected records and
separates paper focus, support membership and direct passage correspondence.
To ask where the curvature source enters the accounts, follow the references
pointing into that source:

```sh
lean-exposition query-corpus build/qaoa-sk-authored \
  --record sources support_tex_curvature --family provenance \
  --direction incoming --max-depth 1 --max-records 40 --format text
```

On the edition identified in Section 2, this selects the source, two claim
nodes, two citations and eight evidence records. The claims include
`support.positive_curvature`; the citation `support_curvature_source` has
direct mappings to the long record's `curvature`, the short paper's `gap-proof`
and the exposition's `contact-and-gap`, among other passages. These are distinct
authored uses of the source. Inspect the long passage and its recorded support:

```sh
lean-exposition inspect-bundle build/qaoa-sk-authored \
  --paper long --passage curvature
```

The neighbourhood query can follow incoming, outgoing or both directions in
selected declaration, argument, citation, platform or provenance families.
Browsing backwards leaves the stored arrows unchanged: a citation still points
to its source, and a claim to its ingredient. The returned subgraph retains
every selected-family link between reached records, including cross-links,
parallel kinds and cycles. Separate witnesses record one deterministic shortest
route to each reached record; they do not replace that subgraph with a tree.

Depth, record budget and optional paper membership define the view's boundary.
Excluded neighbours carry `depth_limit`, `record_limit` or `outside_paper`
reasons. Supplementary records identify boundary endpoints and the records
owning links; they do not extend traversal or count against the selected-record
budget. A paper restriction follows its recorded support membership, not every
mention in its prose. An empty continuation means no further stored relation
under these choices, not mathematical independence or complete source coverage.

A paper subgraph retains selected claims and assumptions, recorded prerequisites
and associated source/evidence records. Document links separately record heading
structure, passage overlap and reading order. Whole passages remain available
when a section cuts across them; unmapped text stays visible. Locations are
half-open **UTF-8 Markdown byte spans**, with line positions. A
`query-papers --byte-range` selection requires the paper and expected manifest
digest. It finds mapped content overlapping the selected bytes and returns
the whole passage's requirements with the exact overlap. Whitespace, markers
and unmapped text create no correspondence. These positions are not PDF
highlight boxes, browser character offsets or formal source coordinates.
A rendered edition needs its own identity and tested source mapping.

A graph's `supports` arrow runs from claim to ingredient; `formalizes` runs
from informal claim to formal declaration; `cites` identifies a reference.
Lean type, value and structural references, platform decomposition and
field-derived provenance retain their separate kinds. Strongly connected
components summarise reachability in the chosen relation set: a reference
cycle may be harmless, while circular proof justification still needs
examination. “Whole” means the whole captured graph, not all Lean declarations
or a complete mathematical dependency audit.

These local read-only projections require no second graph or prose database
and do not open the external source or receipt bytes.
A visual reader is not part of the delivered implementation; the API results
themselves are the demonstrated inspection surface.

## 5. Checks, revisions and review

\begin{figure}[htbp]\centering
\begin{tikzpicture}
\node[archrecord,text width=3.35cm,minimum height=2.0cm,align=center] (formal) at (-4.25,0)
  {\textbf{Lean and Comparator}\\Type check and separate challenge, each with its own run status};
\node[archview,text width=3.35cm,minimum height=2.0cm,align=center] (mapping) at (0,0)
  {\textbf{Passage map}\\Exact text, graph edition, mapped claims and review state};
\node[archview,text width=3.35cm,minimum height=2.0cm,align=center] (platform) at (4.25,0)
  {\textbf{Public platform}\\Theorem status and decomposition; read-only context};
\node[archgate,text width=11.8cm,minimum height=1.25cm,align=center] (review) at (0,-4.3)
  {\textbf{Requires mathematical interpretation}\\A reviewer compares hypotheses, analytic steps, scope and credit. These records supply evidence, not a verdict.};
\draw[archflow] (formal.south)--node[archnote,fill=white,inner sep=2pt,right]{Lean/Comparator status}(-4.25,-3.65);
\draw[archflow] (mapping.south)--node[archnote,fill=white,inner sep=2pt,right]{mapped claims and text}(0,-3.65);
\draw[archflow] (platform.south)--node[archnote,fill=white,inner sep=2pt,right]{public status context}(4.25,-3.65);
\end{tikzpicture}
\caption{Three distinct records can inform a later human review. Their arrows specify what each channel supplies; none certifies mathematical interpretation or says review has occurred. Adapted from the two-correspondence figure in the Plectis Erdős systems paper.}
\end{figure}

A source hash identifies bytes. Extraction records references visible in a
particular Lean environment, with hidden-body and scope limits. A build checks
specified source in that environment; Comparator adds a separately stated
challenge and axiom policy. Public platform metadata records another service's
observation. None establishes that English matches the sources or that a reader
understands it.

For the QAOA/SK evidence reconciled on 25 October 2026, source-byte checks passed,
but the corrected replay was interrupted without a recovered terminal verdict.
Its Comparator and research extraction outcomes remain unknown. Historical
attempts exported the challenges and then failed during solution builds because
compiled imports were missing. This snapshot cannot be cited as successful
Comparator acceptance; it also supplies no mathematical counterexample. A new
configuration or later replay needs its own source-bound result. The
[verification guide](../../docs/verification.md) retains the details;
Lean's [versioned validation guide](https://lean-lang.org/doc/reference/4.35.0/ValidatingProofs/)
explains general trust boundaries. Its later interface does not establish a run
for the source's Lean 4.34.1 environment.

Suppose a paragraph stays unchanged while its map is revised from an unverified
analytic argument to a selected formal statement. The words are identical, but
the claimed correspondence has changed. Its mapping and manifest hashes change;
a review of the earlier edition does not accept the new one. A changed source
or hypothesis likewise needs reassessment, even when a claim's name is retained.

A review account identifies reviewer role, exact edition and claim, question,
sources actually inspected, decision and limits. Preserve the original response,
the author's disposition and any later confirmation separately. The current
drafts have no independent human acceptance. A proposed trial asks a newcomer
to recover the gap's hypotheses, analytic source, formal scope and unresolved
review status from one frozen edition. Separately ask them to explain how the
endpoint data and strict curvature contradict the required integral. Locating
an ingredient and recovering its use are different outcomes. That trial has
not been performed here.

## 6. Why use separate texts and maps?

The exchange format has eight files: a manifest, a graph and three
Markdown/mapping pairs. The manifest binds the other seven files; each mapping
binds its paper and passages to the graph edition and recorded review state.
Separate maps keep ordinary Markdown readable while correspondence metadata
can be revised explicitly. Eight is an implementation choice, not a lower bound:
embedded annotations or one container with separately addressable accounts
could preserve many of the same invariants.

| Alternative or antecedent | Relationship to this design |
| --- | --- |
| Paper with source links | Supplies readable prose and citations. The extra contract here exposes typed recorded paths and mapping-only revisions to local queries. No comparative efficiency result is claimed. |
| [leanblueprint](https://github.com/PatrickMassot/leanblueprint/tree/56e066d30fb7b608a63f4241fee80982d7eae3ef) | Authors already link informal statements to Lean declarations and specify dependencies. This bundle selects a three-account passage contract; it does not originate prose-to-formal links. |
| [TheoremGraph v1](https://arxiv.org/abs/2606.25363v1), “Formal Graph,” “Bridging The Corpora” and “Limitations” | Extracts typed declaration dependencies and proposes statement matches using embeddings and an LLM judge. Its match category includes specialisations and one-way implications. Here passage maps are authored assertions; neither mechanism proves semantic equivalence. |
| [Prove2Me v2](https://arxiv.org/abs/2608.28433v2), §§3–5 | Chen, Marwaha, Lu, Yuen and Peng distinguish immutable statements, proof submissions, explanations, decomposition and human audit. Its case studies do not evaluate this local bundle. |

The [pinned source study](../../docs/literature.md) also records LeanArchitect's
collector, doc-gen4's index and Verso Blueprint's source/presentation boundaries.
The extractor adapts Comparator structural traversal with its Apache-2.0 notice.
The scholarly foundations are de Moura and Ullrich's
[Lean 4 paper](https://doi.org/10.1007/978-3-030-79876-5_37) and
[The mathlib Community](https://doi.org/10.1145/3372885.3373824).
These are specific design and software credits, not claims that related systems
lack an unassessed feature.

The cost is manual correspondence work and review across three texts.
Portability means offline inspection of embedded text, graph and records.
External Lean sources, manuscripts and receipt files are not included; locators
and hashes do not guarantee later retrieval. If those bytes are unavailable,
that source check remains unavailable. The optional Prove2Me adapter reads
public metadata; it does not submit a paper or obtain its review.

**Figure sources.** The funnel adapts Will Cook's mathematics-map visual.
The support and evidence figures reuse the shared-support and two-correspondence
compositions in his
[*A Repository-Based System for Research and Publication*](https://github.com/wcook04/plectis-erdos/blob/61fb590921e3b5a100dc264bed052c9cf6959daf/paper/systems/claim-faithful-publication-systems-paper.tex)
([CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)).
The [authoring guide](../../docs/authoring.md#method-sources-and-redistribution)
locates the public writing methods adapted for the three transitions.

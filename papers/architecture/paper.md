---
title: "One argument, several ways to read it"
subtitle: "An architectural companion to Lean Exposition"
date: "25 October 2026"
portable-local-links: true
header-includes:
  - |
    \usepackage{tikz}
    \usepackage{float}
    \usetikzlibrary{arrows.meta,positioning,fit}
    \tikzset{archbox/.style={draw=black!45,fill=white,inner sep=7pt,align=center,font=\small},
      archrecord/.style={archbox,draw=blue!60,fill=blue!3},
      archview/.style={archbox,dashed},
      archflow/.style={-{Stealth[length=2mm]},draw=black!65,rounded corners=3pt},
      archnote/.style={font=\small,align=center,inner sep=2pt,fill=white}}
---

A mathematician reading a short proof may want to stop at its main idea, check
one difficult estimate, or learn the subject from the beginning. Those are
different requests. A proof assistant can check a precisely stated theorem,
but its successful check does not choose an explanation for any of these
readers. Nor does a readable explanation, by itself, show how faithfully it
represents the checked statement.

Lean Exposition connects three written accounts of selected mathematics to a
shared record of claims, assumptions, sources and checks. Each account has its
own purpose and reading order. Their connections let a reader leave an
explanation at the point of doubt, recover the relevant detail, and return
without losing track of which statement was being discussed. This companion
explains that arrangement and the choices behind it. The mathematical papers
supply the arguments themselves.

## 1. Why write more than one account?

The starting material may include an original research paper, a formal
development in the Lean proof assistant, and earlier literature. These sources
answer different questions.
The research paper explains a mathematical argument in the author's chosen
language. The Lean development gives precise definitions and formal proofs.
Earlier literature establishes what was known, where an input came from and
which conclusions require additional results. Reading one does not necessarily
recover the content of the others.

An author first reconstructs the selected argument in a **long reasoning
record**. This is where a reader should be able to find the derivation behind
an estimate, the treatment of an endpoint, or the reason two formulations
correspond. Its length follows the argument that needs recovering. It can
retain a failed approach when the failure explains why a hypothesis matters.
It also identifies steps that have not been justified.

A **short research paper** then selects a contribution worth presenting as a
connected argument. It gives the statement, its position in the literature
and the decisive proof, with precise destinations for substantial details it
omits. The selection may leave whole further results in the long record.
Those omissions should make the paper more focused without making its claims
stronger.

An **expository paper** makes a different selection. It teaches a result to
readers with stated prerequisites, introducing objects through examples and
explaining why each construction is needed. It may spend more time on a
definition than the specialist paper, while covering fewer consequences.
Its author keeps the original sources and detailed record available; the
exposition need not be produced by repeatedly shortening the short paper.

The supplied example concerns the Sherrington–Kirkpatrick (SK) model, a random
optimisation problem on interacting spins. Its exposition begins with a
two-spin calculation and explains why an optimal function used to express the
model's value cannot stay flat on an interval. The short paper presents this
no-gap theorem and related consequences for a reader familiar with
stochastic calculus. The long record reconstructs the analytic steps and
continues into the separate argument about the Quantum Approximate
Optimization Algorithm (QAOA). A reader interested in the no-gap mechanism
does not have to read the circuit construction first.

These are entrances for different purposes. The writing process gives authors
more context than any one reader is asked to absorb.

## 2. What the shared graph remembers

Maintaining three accounts creates a practical problem. If a hypothesis is
corrected in the detailed argument, which shorter passages need attention?
If a reader doubts an estimate, where is it explained, and which source is
being invoked? A bibliography alone cannot answer these questions at the
level of a particular passage.

The project records selected claims and their relationships in a graph. A
claim has a stated scope and associated assumptions. It can point to an
ingredient used in its argument, an original source, or a formal statement
with which the author proposes a correspondence. Sources retain their editions;
checking records say what was checked and with what outcome. This is a curated,
partial account of the available mathematics. It does not pretend to contain
every declaration or every dependency in the underlying Lean development.

Each written paper has a **passage map**: annotations connecting selected
passages to the claims, assumptions and citations they discuss. Thus two
papers can refer to the same claim while explaining it differently. Their
prose remains independently readable, and text without a recorded mapping
remains visible as such.

\begin{figure}[H]
\centering
\begin{tikzpicture}
\node[archview,text width=3.6cm,minimum height=1.8cm] (long) at (-4.7,0)
  {\textbf{Long record}\\Recover the derivation\\and its separate cases};
\node[archview,text width=3.6cm,minimum height=1.8cm] (short) at (0,0)
  {\textbf{Short paper}\\Read the result\\and decisive proof};
\node[archview,text width=3.6cm,minimum height=1.8cm] (expo) at (4.7,0)
  {\textbf{Exposition}\\Learn the objects\\and the proof idea};
\node[archrecord,text width=13.1cm,minimum height=1.6cm] (corpus) at (0,-3.4)
  {\textbf{Shared record of the mathematics}\\Claims and assumptions, supporting arguments, source editions and checks};
\draw[archflow] (long.south)--node[archnote,text width=3.5cm]{maps its passages\\to recorded support}(-4.7,-2.6);
\draw[archflow] (short.south)--node[archnote,text width=3.5cm]{maps its passages\\to recorded support}(0,-2.6);
\draw[archflow] (expo.south)--node[archnote,text width=3.5cm]{maps its passages\\to recorded support}(4.7,-2.6);
\end{tikzpicture}
\caption{Why three papers need only one shared record. Each paper chooses its own reading order and connects its passages to relevant parts of the same corpus. The arrows denote authored correspondence, not automatic generation or proof. A paper can select fewer results while retaining the assumptions and sources its claims need.}
\end{figure}

An arrow needs a meaning. Here an argument arrow points from a claim to an
ingredient it uses: following it asks what supports the claim. Following the
same relation backwards asks what recorded arguments use that ingredient.
The direction of the stored relationship stays the same. Several ingredients
may be needed together; an arrow to one of them does not say that it alone
proves the conclusion.

Other relationships answer other questions. A citation credits or refers to
a source. A correspondence with a formal statement asks the reader to compare
two formulations. A recorded Lean dependency says that a constant occurs in
a declaration's formal type or proof, or in its structural references. A
checking record identifies the source or claim it concerns. These relations
must remain distinguishable: a source can be historically relevant without
being a premise, and a proposed correspondence can require a mathematical
argument of its own.

The order of paragraphs is another relationship again. An exposition may
give an example before stating the general theorem; a specialist paper may
state the theorem first. Neither order changes the theorem's prerequisites.
A paper's reading route therefore consists of its authored sequence together
with the support selected for its passages. The graph helps readers inspect
that selection; it does not choose a sufficient proof or a good teaching order.

## 3. Follow one claim back to its argument

The SK model asks which choices of signs maximise a random sum of pair
interactions. The Parisi formula expresses its limiting optimum through a
minimisation over functions called order parameters. In the pure model at
zero external field, an admissible order parameter is a nonnegative,
nondecreasing, right-continuous, integrable function
$\gamma:[0,1)\to[0,\infty)$. Its associated measure records the increments
of $\gamma$. A flat interval is a gap in those increments, even if the
function's value there is positive.

The result at issue says that an admissible minimiser has no such gap: its
measure has full support relative to $[0,1)$. The endpoint one is excluded.
Existence of a minimiser comes from a separate theorem of
[Auffinger and Chen](https://arxiv.org/abs/1606.05335v2).
[Hong-Bin Chen](https://arxiv.org/abs/2607.18032v1) had already established
full support by another method. The worked accounts reconstruct the
quantitative argument in [OpenAI's full-support manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/main.tex).
Their contribution here is the explanation and its correspondence to sources.

Consider just one case: a bounded gap $(\ell,r)$ between support points,
with $0<\ell<r<1$, on which $\gamma$ has a positive constant value.
To test whether $\gamma$ could minimise, the proof constructs a differentiable
curve $q$ measuring the average squared response in an auxiliary optimisation
problem. The mathematical papers explain that construction. Here we take two
properties as inputs and follow how they exclude the gap.

Minimality gives **contact** at the endpoints. In the notation of the papers,
this supplies
$$
q(\ell)=\ell,\qquad q(r)=r,\qquad q'(\ell),q'(r)\leq1.
$$
The change in $q$ across the interval must therefore be $r-\ell$.
Separately, a strict-curvature estimate on a positive constant interval
makes $q'$ strictly convex. Since $q'$ is continuous at the endpoints, its
interior values lie strictly below their joining chord, which is at most one.
Consequently
$$
q(r)-q(\ell)=\int_\ell^r q'(t)\,dt<r-\ell.
$$
The two requirements contradict each other. Neither endpoint contact nor
strict curvature alone gives this contradiction.

\begin{figure}[H]
\centering
\begin{tikzpicture}
\node[archrecord,text width=11.7cm,minimum height=1.3cm] (gap) at (0,0)
  {\textbf{A bounded positive gap is impossible}\\The required change in $q$ is $r-\ell$; the integral of $q'$ is smaller.};
\node[archbox,text width=5.25cm,minimum height=1.8cm] (contact) at (-3.55,-3.0)
  {\textbf{Endpoint contact}\\$q(r)-q(\ell)=r-\ell$\\$q'(\ell),q'(r)\leq1$};
\node[archbox,text width=5.25cm,minimum height=1.8cm] (curvature) at (3.55,-3.0)
  {\textbf{Strict curvature}\\$q'''(t)>0$ inside the interval,\\so $q'$ is strictly convex.};
\node[archview,text width=5.25cm,minimum height=1.15cm] (minimum) at (-3.55,-5.8)
  {Minimality and support endpoints};
\node[archview,text width=5.25cm,minimum height=1.15cm] (plateau) at (3.55,-5.8)
  {A positive constant interval\\and the analytic regularity};
\draw[archflow] (-3.55,-.65)--node[archnote]{uses endpoint data}(contact.north);
\draw[archflow] (3.55,-.65)--node[archnote]{uses the strict estimate}(curvature.north);
\draw[archflow] (contact.south)--node[archnote]{requires}(minimum.north);
\draw[archflow] (curvature.south)--node[archnote]{requires}(plateau.north);
\end{tikzpicture}
\caption{Which ingredients does the contradiction use? Arrows point from a conclusion to its inputs. Both branches are needed in the stated SK setting. Minimality supplies contact; the curvature estimate itself applies without minimality. This is one branch of the ordinary argument, not an extracted Lean proof graph. Zero coefficients and initial or terminal gaps require separate treatment.}
\end{figure}

Now suppose a reader accepts the final integral comparison but wants to know
why the curvature is strict. The [short paper, section “Minimality gives
contact; curvature excludes gaps”](../qaoa-sk/short/paper.md#contact) identifies
the estimate at its use. The [long record, section “Strict curvature on a
constant interval”](../qaoa-sk/long/reasoning-record.md#curvature-and-gap-certificate)
reconstructs the analytic proof, including the integrated inequality and the
passage from simpler coefficients to the stated class. It leads in turn to
[Proposition 5.1 of the original manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/curvature.tex#L9-L52).
Having checked that destination, the reader returns to the short proof and
uses the estimate together with contact.

A reader who does not yet understand a gap can instead enter the
[exposition, section “What a gap means”](../qaoa-sk/expository/main.md#2-what-a-gap-means).
Its example separates a positive cumulative value from vanishing increments.
The later section “Why a flat interval cannot minimise” develops the contact
and area argument. This route teaches the objects that the specialist route
assumes. The graph can locate both passages because they discuss shared
claims; reading them supplies the different explanations.

## 4. What survives a shorter account

Shortening the example cannot change “an admissible minimiser” into “an
admissible function”. Constant functions are allowed candidates, and the
curvature estimate does not say they minimise the functional. Without
minimality, the endpoint contact used in the contradiction is missing.
The short account must retain that premise where it states and uses the
no-gap conclusion.

It must also preserve the result's extent. Full support says that every
nonempty relatively open interval receives mass. It does not alone assert
a density, let alone a strictly positive density. The stronger density
conclusion in the source has a further argument. Likewise, the broader QAOA
claim requires approximation and circuit arguments beyond full support.
Different accounts may stop at different conclusions, provided each makes
its own stopping point clear.

The passage maps help enforce this discipline. For the claims an author
selects, the checks require the recorded assumptions, citations and unresolved
obligations to remain attached. They can catch a missing reference or changed
text. They cannot detect every misleading sentence, determine whether an
assumption has been explained well, or decide whether a cited argument is
adequate. Those are questions for mathematical and editorial review.

Attribution survives the same selection. The no-gap theorem retains credit
for the earlier support result and for the quantitative proof being explained.
A reference may supply a theorem, an adapted construction or historical
context. Recording that role avoids treating every citation as a logical
dependency while still letting the reader recover the relevant source.

## 5. Explanation, formal evidence and navigation

A reader may next ask whether the no-gap conclusion has a formal counterpart.
The project records a correspondence with a selected Lean statement. That
statement assumes an admissible minimiser on a Brownian system and supplies
full support, strict increase and associated moment identities. It does not
assert minimiser existence or QAOA circuit convergence. Its
[original formal statement](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.lean#L81-L92)
is a destination for comparison, rather than a formal certificate for every
sentence of the exposition.

Even a close correspondence may need explanation. The [long record's section
“The support statement and the derivative bridge”](../qaoa-sk/long/reasoning-record.md#formal-interfaces)
compares a formal limit along prescribed step sizes with the ordinary
right derivative used in the manuscript. A convexity argument connects them.
Following a link finds that argument; it does not perform it.

The design therefore preserves three distinct activities. The written account
explains why a conclusion follows. Formal checking tests a precise statement
and proof in a specified environment. Navigation helps a reader find the
account, formal statement and records of the checks. None can stand in for
the other two.

Checking outcomes also retain their scope. Identifying unchanged source
bytes, building a Lean project, comparing it with a separately stated challenge,
and reviewing its mathematical interpretation answer different questions.
For the retained SK research example, the corrected formal comparison and
dependency extraction have no recovered final outcome. Their results remain
unknown, and this companion establishes no new formal acceptance. Earlier unsuccessful runs remain observations of
those runs, rather than counterexamples to the theorem.

Reviews concern particular editions. If an author changes a hypothesis or
maps the same paragraph to a different formal statement, the correspondence
has changed even when much of the prose has not. The project keeps the text,
map and sources identifiable together so a review can be understood in its
original context. A revised edition needs review of the affected claim.

## 6. What a reader or author can use today

Today the repository provides the written drafts, their source maps and local
tools for inspecting them. A reader can begin with a paper passage and find
its recorded assumptions and support, look for other accounts of the same
claim, or begin with a source and find its recorded uses. The tools can follow
selected kinds of relationship forwards or backwards. They retain the links
among the records found, rather than replacing a shared argument by a single
chain.

Each query has a boundary. It may be restricted to one paper or stop after
a chosen amount of exploration. The returned boundary distinguishes such
limits from the absence of another recorded connection. Because the corpus
is partial, finding no connection cannot establish mathematical independence
or a complete account of a source.

The papers and their maps can also be packaged together for inspection in
another application. That package contains the captured writing and records;
some original sources remain external. Source references identify what should
be consulted, but cannot guarantee that an unavailable source will later be
retrievable. The current tools provide local queries and a programming
interface. An interactive reading website is a possible consumer of these
operations, not an interface already delivered by this project.

For authors, the cycle begins with reading sources, selecting a result and
recording its support. Reconstruction supplies the long account; editorial
selection and teaching supply the other accounts. Review then asks two
separate questions: does the writing faithfully represent the mathematics,
and can the intended reader follow it? A useful reader task for this example
is to explain why contact and curvature conflict, then say which step fails
without minimality. Finding the right source is helpful, but does not by
itself answer that task. The drafts have received source-based agent review;
independent human acceptance and evidence of improved comprehension remain
to be obtained.

## 7. Why keep this much structure?

Ordinary papers with careful references remain useful. The additional work
here is maintaining explicit relationships across several accounts, so that
a reader or an author can find a claim's assumptions, locate a missing
derivation and identify recorded passages affected by a correction. The
structure earns its place only if these journeys are useful. It also costs
time: maps need authoring, changes need reconciliation, and correspondence
still needs mathematical judgment.

The arrangement builds on existing practices. In particular,
[leanblueprint](https://github.com/PatrickMassot/leanblueprint/tree/56e066d30fb7b608a63f4241fee80982d7eae3ef)
already connects informal statements with formal declarations and their
dependencies. Lean Exposition's emphasis is the maintained relationship
between several authored accounts, their selected passages and the distinct
evidence behind them. It makes no claim to have invented informal-to-formal
links or demonstrated a comparative learning benefit.

One shared corpus avoids maintaining a separate version of each claim for
every paper. Separate annotations allow each account to read as a paper, while
the repository's guides carry the operating instructions. Readers can therefore
understand the design before deciding whether to use the software. The intended
result is a shorter route from
“I do not understand this step” to the argument that resolves it, with its
assumptions and credit still attached.

**Figure credit.** The diagrams adapt the shared-support and parallel-record
compositions previously used in this companion, derived from Will Cook's
[*A Repository-Based System for Research and Publication*](https://github.com/wcook04/plectis-erdos/blob/61fb590921e3b5a100dc264bed052c9cf6959daf/paper/systems/claim-faithful-publication-systems-paper.tex)
([CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)). Their subjects,
labels and reading order have been revised for this account.

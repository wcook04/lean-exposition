---
title: "The argument of Alpöge’s formal proof of the Riemann Hypothesis: an account read from the Lean source"
authors:
  - Qui Vincit
  - Fable
---

# The argument of Alpöge’s formal proof of the Riemann Hypothesis: an account read from the Lean source

<ul class="authors"><li>Qui Vincit</li><li>Fable</li></ul>

## Abstract

On 20 November 2026 Levent Alpöge released a Lean 4 formalisation, 17 million lines long, of a proof of the Riemann Hypothesis and of its analogue for every Dirichlet $L$-function, with a note saying that no human-readable proof has been written. We built the archive, twice. It compiles, the five top theorems depend on no axiom beyond the three on which Mathlib rests, and the kernel accepts every theorem, and every definition that is not marked unsafe or partial, of the import closure, 2.7 million declarations in all, replayed from an empty environment by Lean's own checker and by a program of ours. This paper says what the argument is, as read from the Lean source. The exponent $\tfrac12$ comes from one optimisation: an upper bound, of the shape $x/m+m$, for a weighted count of prime powers whose Frobenius lies outside a CM type, where $m$ is the length of a chain of theta lifts between definite unitary groups. The bound is a squeeze between two slopes of Hermitian lattices. Divisibility of periods at inert primes, which comes from the height-two formal group of a CM elliptic curve, raises the slopes of lattices of algebraic modular forms. A slope inequality for nearly tight frames of maps, which we state in full, transfers that to a lattice of periods. The slope of that lattice is bounded above by a period computation that returns exactly the main term of the count, through a dimension count and the Chowla--Selberg formula. We describe each step and each input, determine by machine which parts of the archive the final theorem uses, and identify the published theorems on which the proof rests.


Fable is a language model (Claude, Anthropic). [12](#sec:method) states who did what.

## 1. Introduction

<a id="sec:intro"></a>

On 20 November 2026 Levent Alpöge released a proof of the Riemann Hypothesis ([Riemann 1859](#ref-riemann1859anzahl)), and of the generalised Riemann Hypothesis for the $L$-functions of Dirichlet ([Lejeune-Dirichlet 1837](#ref-dirichlet1837beweis)), formalised in Lean 4 ([Moura and Ullrich 2021](#ref-demoura2021lean4)) on top of Mathlib ([The mathlib Community 2020](#ref-mathlib2020lean)). The release consists of the Lean source ([Alpöge 2026a](#ref-alpoge2026lean)), 175,187 Lean files and 17,374,215 lines, and a four-page note ([Alpöge 2026b](#ref-alpoge2026remark)) with a timeline of twenty steps. The note says that no human-readable proof has been written.

This paper does two things. It reports that the proof is correct as a formal object: we built the archive, it compiles, its five top theorems depend on the three standard axioms and nothing else, and the kernel accepts every theorem, and every definition that is not marked unsafe or partial, of the import closure, replayed from an empty environment by Lean's own checker and by a program of ours ([2](#sec:verification)). And it says what the argument is: an account read from the Lean source, from the final theorem down to the theorems of the published literature on which it rests. The release does not contain one.

### The argument

Fix a primitive Dirichlet character $\chi$. The proof has four movements.

*Reduction to a one-sided bound on windows.* A windowed form of Landau's theorem reduces the non-vanishing of $L(s,\chi)$ for $\operatorname{Re}s>\tfrac12$ to a bound $G(x)\le x^{1/2+\varepsilon}$ for a smoothed sum over prime powers, required only for $x$ in long windows ([4.1](#sec:landau)).

*An exact identity.* For an auxiliary abelian CM field with CM type $\Phi$, a weighted count $\mathrm{ASK}$ of the prime powers whose Frobenius lies outside $\Phi$ equals a main term $\mathrm{MAIN}$ plus a combination of such sums ([4.2](#sec:identity)). After averaging, an *upper* bound $$\mathrm{ASK}\ \le\ \mathrm{MAIN}+\mathrm{Err}$$ becomes the bound on $G$, and the error has three parts of sizes $x/m$, $m$ and a rank term, where $m$ is a parameter. At $m\approx\sqrt x$ they balance. This is the only place where $\tfrac12$ is produced ([4.4](#sec:balance)).

*A squeeze between two slopes.* The upper bound is proved with Hermitian lattices. For each of many indices $u$ there is a lattice $M_u$ of algebraic modular forms on a definite unitary group, and a map $B_u$ sending a form to the periods of its $m$-fold iterated theta lift; $m$ is the number of lifts. At a prime $p$ inert in the CM field those periods are divisible by about $p^{a/p+a/p^3+\cdots}$, where $a$ is the order of the Taylor coefficients of theta functions through which they are expressed, because a CM elliptic curve has a formal group of height two there ([6](#sec:divisibility)). So $B_u$ still maps into the lattice $P$ of periods a lattice $N_u$, obtained by rescaling a sublattice of $M_u$, whose slope exceeds that of $M_u$ by at least the count $\mathrm{ASK}$, up to errors and to correction terms that cancel later. The maps $B_u$ form a nearly tight frame, by a relative trace formula for Bessel--Poincaré series ([7](#sec:frame)), and a slope inequality for such frames bounds the slope of $P$ from below by the mean slope of the $N_u$ ([5.4](#sec:slope)). From above, the slope of $P$ is bounded by $m$ times $\log(a!/\Omega^a)$, with $\Omega$ a CM period, less a term from an auxiliary level prime; a dimension count for that prime and the Chowla--Selberg formula for the mean of $\log\Omega$ turn this into $\mathrm{MAIN}$ and a remainder that the correction terms cancel ([5.5](#sec:period)).

*Three inputs.* The construction needs a bound on Galois cohomology in a cyclotomic tower, which the note calls a weakening of Vandiver's conjecture ([8](#sec:cohomology)); the existence of suitable auxiliary fields at every scale in the windows ([9](#sec:hosts)); and a body of theorems on unitary groups, Shimura varieties and Arakelov geometry, each of which the archive proves for itself ([10](#sec:literature)).

The shape $x/m+m$ is that of Stepanov's method ([Stepanov 1969](#ref-stepanov1969number); [Bombieri 1974](#ref-bombieri1974counting); [Schmidt 1976](#ref-schmidt1976equations)), where a polynomial is made to vanish to order $m$ at the points to be counted. Here the multiplicity is the length of a chain of theta lifts, and the degree bound is replaced by slopes of lattices in the sense of Bost ([Bost 1996](#ref-bost1996periodes), [2001](#ref-bost2001algebraic); [Chambert-Loir 2002](#ref-chambertloir2002theoremes)).

### Findings

Beyond the outline, the reading establishes the following.

1.  The statement proved is Mathlib's `RiemannHypothesis`, and the statements for Dirichlet $L$-functions cover every character of every modulus ([2.3](#sec:statements)).

2.  The final theorem uses 1,075,015 of the archive's 1,548,656 theorems. Outside its cone are earlier forms of several steps, some with their proofs, and conditional statements, among them one that would give only $\operatorname{Re}s>\tfrac34$ ([11](#sec:offpath)).

3.  The central inequality is a theorem about Hermitian lattices alone, a slope inequality for nearly tight frames of maps, which we state in full ([Statement 5.1](#st:F)).

4.  The period side returns the analytic main term identically; there is no discrepancy term ([Statement 5.2](#st:key)).

5.  The slope argument depends on arithmetic intersection theory on a Shimura variety, through the covolume of lattices of integral forms; this is why resolution of singularities and an arithmetic Hilbert--Samuel theorem are among the results the archive formalises ([5.5](#sec:period)).

6.  The cohomological bound is needed only in the weak form "at most $\exp(x^\varepsilon)$". The archive proves more, by a route through congruences between cusp forms and Eisenstein classes on $\mathrm{U}(3)$; no statement of the main conjecture of Iwasawa theory appears among the results it takes from the literature ([8](#sec:cohomology)).

7.  The Galois representations the proof needs are constructed in the archive from theta lifts between definite unitary groups, with less local--global compatibility than the literature provides, and the argument is arranged to need no more ([8.4](#sec:galois)).

8.  The proof contains its own formalisations of 179 named results of the literature, among them global class field theory, the Siegel--Weil formula and Hironaka's theorem ([10](#sec:literature)); beside these the archive proves the theorem of Ferrero and Washington and Kato's Euler system ([8](#sec:cohomology)).

### Scope

This is an exposition of Alpöge's proof, written from its source; the mathematics is his and that of the model he worked with. We do not reprove the theorem, and the certificate of its truth is the kernel's, not ours. [12](#sec:method) states how the reading was done, and [Appendix A](#app:audit) records where each statement of this paper was read.

## 2. What was verified by machine

<a id="sec:verification"></a>

Apart from the statements transcribed in [2.3](#sec:statements), the description of the elaborators in [2.2](#sec:scan), the account of the reviews in [2.8](#sec:checker), and what is said of how Lean and `lean4lean` work, which rests on the reviews and on our reading of their source, every result in this section was computed by a program: on the archive, or, where we say so, on Mathlib and on test modules. The programs and their output are public ([Appendix B](#app:reproduce)).

### The archive

The Lean source is distributed as fourteen parts which concatenate to a single file `lean.tar.gz` of 239,275,554 bytes with SHA-256 $$\texttt{9631b4f020199e580ba86178cb56c6e9}\;\texttt{b09f690c2369a80dc4334aa93f49c7fc}.$$ It unpacks to 175,187 `.lean` files (17,374,215 lines) and 3 build files. The build files pin Lean 4.33.1 and Mathlib at commit 0df444a360eaa60ab8c11dca51a86af692955474.

### 2.2. Static inspection

<a id="sec:scan"></a>

We scanned the text of every file, comments included, for whole words, also where a word follows a dot. No file contains the word `sorry` or `admit`, an `axiom` declaration, or any of `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `csimp`; nor any of the names we know by which a declaration can be put into an environment without the kernel's check or by which the compiler is trusted, which the script lists (among them `skipKernelTC`, `addDeclWithoutChecking`, `doCheck` and `ofReduceBool`). No file begins with the word `module`, so the archive does not use Lean's module system ([2.8](#sec:checker)). Every import names a file of the archive or a module of Mathlib, of its dependency Batteries or of Lean, and the build shows that those modules exist; the import graph is acyclic; every file is in the import closure of `Main.lean`.

Counted by keyword, the text has 87 macros, which abbreviate syntax, and 4 elaborators, programs that run while a file is compiled, in 3 files. We read them: they are two tactics, a command that copies declarations under new names, and a probe. Each produces its result through an ordinary declaration, so the kernel checks what they produce; the copying command is the one place where the text calls Lean's function for adding a declaration, the one that checks. In 5 small files a command is run while the file is compiled; it adds a name to the deny list of Lean's facility for suggesting library lemmas, and declares nothing. The elaborators have 2 helper functions declared `partial`; they are programs, not statements, and they are outside the dependency cone of [2.6](#sec:cone). No file contains `#eval`. A scan of the text can miss a defect, and nothing below rests on it: the replay of [2.7](#sec:replay) examines what the build produced, however it was produced.

### 2.3. The statements

<a id="sec:statements"></a>

`Main.lean` is 12 lines long and proves five theorems.

<a id="st:rh"></a>


**Statement 2.1** (`riemannHypothesis`). For every $s\in\mathbb{C}$ with $\zeta(s)=0$, if $s$ is not of the form $-2(n+1)$ with $n\in\mathbb{N}$ and $s\neq 1$, then $\operatorname{Re}s=\tfrac12$.



The statement is the proposition `RiemannHypothesis` of Mathlib, not a definition of the archive: in the compiled environment that name is declared in the module `Mathlib.NumberTheory.LSeries.RiemannZeta`, as is `riemannZeta`.

<a id="st:grh"></a>


**Statement 2.2** (`LFunction_ne_zero_of_half_lt_re`). For every modulus $N\ge 1$, every Dirichlet character $\chi$ modulo $N$ and every $s\in\mathbb{C}$ with $\operatorname{Re}s>\tfrac12$, if $\chi\neq 1$ or $s\neq1$ then $L(s,\chi)\neq0$.


<a id="st:strip"></a>


**Statement 2.3** (`LFunction_eq_zero_re`). For every modulus $N\ge1$, every Dirichlet character $\chi$ modulo $N$ and every $s$ with $0<\operatorname{Re}s<1$ and $L(s,\chi)=0$, one has $\operatorname{Re}s=\tfrac12$.



The remaining two are `riemannZeta_eq_zero_re`, which is [Statement 2.1](#st:rh) again, and `LFunction_eq_zero_re_of_isPrimitive`, which is [Statement 2.3](#st:strip) for primitive characters. Here $L(s,\chi)$ is Mathlib's `DirichletCharacter.LFunction`, the meromorphic continuation. The characters are not assumed primitive; restricting to the open strip in [Statement 2.3](#st:strip) excludes the zeros on $\operatorname{Re}s=0$ that imprimitive characters have, so the statements are correctly posed.

"GRH" in this paper always means [Statement 2.2](#st:grh) and [Statement 2.3](#st:strip): Dirichlet $L$-functions. The note says the case of Dedekind zeta functions is expected and not done.

### 2.4. The build

<a id="sec:build"></a>

We built the unmodified archive twice, on two rented machines. The first build took Mathlib's compiled files from the community's build cache for the pinned commit and ran `lake build Main` for 13.4 hours on 32 threads (AMD EPYC 9575F 64-Core Processor); its log was not kept, and these figures are from a summary of it made by hand. For the second, Mathlib and the packages it depends on were first compiled from source, 8,312 modules of Mathlib in 19 minutes, the download of the toolchain included, so that no compiled file came from a cache; `lake build Main` then ran for 16.0 hours on 32 threads (AMD EPYC 4565P 16-Core Processor), while most of the tests of [2.8](#sec:checker) on Mathlib and on the test modules ran beside it. Each build ended with the line `Build completed successfully`, after 183,893 jobs in the second, and with exit code $0$. In each, all 175,187 modules of the archive were built and none failed. On the second machine the installed toolchain was compared, file by file, with the release archive of Lean 4.33.1 published on GitHub: all 17,493 files are identical. The first machine's toolchain was the same release, installed in the same way; it was not compared.

The two builds give the same names for the archive. The list of its declarations inside the cone of [2.6](#sec:cone), each with its kind, the list of those outside it, and the list of its modules that meet the cone are the same in both, byte for byte, and so are the counts of the two replays for every kind of declaration but one. They differ in Mathlib. The compiled files of the first build were not kept, so the cache was fetched again on the second machine and compared with the build from source: for every constant its kind, its module and its name, and Lean's hash of its statement and of its value. Compiled from source, Mathlib has 8 theorems that the cached build lacks and lacks 2 that it has. All of these are private auxiliary lemmas that the tactics `simp` and `abel` produce inside 4 proofs; no name that a person wrote is among them. Among the 772,124 constants that both builds have, the hash of the statement is the same in both for all but two: a further auxiliary lemma, to whose generated name the two builds gave different lemmas, and `SimpleGraph.Walk.take.eq_2`, one of the equations that Lean itself generates for a definition, which the two builds state in different forms; both forms are printed in the results. The hash of the value differs for six: these two, three of the four theorems in whose proofs the auxiliary lemmas occur, and an auxiliary definition under the name of the fourth. The hash is the 32-bit one that each compiled file stores with each term; it does not see the names of bound variables, their annotations, or metadata, and nothing here recomputes it. Equal hashes are evidence that two terms are equal, not a proof of it. The second build thus declares 6 theorems more than the first, which is the difference between the two replays, and its cone is larger by one constant. Of the sixteen constants named in this comparison, two are in the cone of `riemannHypothesis` as the second build has it: the theorem `MvPolynomial.coeff_killCompl`, whose proof differs between the builds, and the auxiliary lemma of that proof which only the build from source has, which agrees with the second cone being larger by one. No constant whose statement differs is in the cone. What follows refers to the second build.

### 2.5. Axioms

<a id="sec:axioms"></a>

For each of the five theorems, `#print axioms` reports exactly $$\text{\texttt{propext}},\qquad \text{\texttt{Classical.choice}},\qquad \text{\texttt{Quot.sound}},$$ the three axioms on which Mathlib as a whole rests. In particular none depends on `sorryAx` or on an axiom that trusts the compiler. For a theorem of an imported module this command does not walk the terms. It prints a list that Lean computed and recorded when the module that declares the theorem was compiled, from the terms of that module and from the lists recorded for the modules it imports; it walks the terms only where no list is recorded (`Lean/Util/CollectAxioms.lean` in the source of Lean 4.33.1). So the report is as good as the compiled files it reads, and in the first build those of Mathlib came from the community's cache.

Two programs of ours compute the axioms again from the terms. The replay of [2.7](#sec:replay) does it for each of the five theorems, in the environment that the kernel built, and finds the same three. The program that computes the cone of [2.6](#sec:cone) finds these three and no other axiom among the constants of the cone of the five theorems.

### 2.6. The dependency cone

<a id="sec:cone"></a>

A build proves that every file compiles; it does not say which declarations the final theorem uses. From the compiled environment we computed the set of all constants reachable from `riemannHypothesis` through the type and the value of every declaration reached, the link between an inductive type and its constructors, and the structure that a projection belongs to. It has 1,478,220 elements. Of the 1,548,656 theorems the archive declares, 1,075,015 are in it, and the cone meets 147,489 of the 175,014 modules that declare anything. These are counts of names: Lean lets an auxiliary theorem be declared again in each module that needs it, and 39,597 of the archive's theorem declarations repeat a name declared in another module. When this paper says that a declaration is, or is not, used by the proof, it means membership in this set. [11](#sec:offpath) lists what is outside it.

### 2.7. Kernel replay

<a id="sec:replay"></a>

Some words of Lean are needed here. The *kernel* is the small program that checks a declaration. An *inductive type* comes with its *constructors* and with a *recursor*, its induction principle; the kernel derives these from the declaration of the type, and it alone provides the four constants of the *quotient type*. An *opaque constant* is a definition whose value later declarations cannot use. Lean marks a declaration *unsafe* or *partial* when it is a program and not a statement; no theorem may use one. A file that begins with the word `module` uses Lean's *module system*, by which a file shows the files that import it a reduced version of its declarations. Mathlib and Lean's library use it; the archive does not ([2.2](#sec:scan)).

A build normally checks each declaration once, in the process that elaborated it; code that a file runs while it is compiled can add a declaration that the kernel never sees ([2.8](#sec:checker)). A replay passes the declarations to the kernel a second time, from the compiled files, in a process that does nothing else. We replayed the whole import closure of `Main.lean` into an environment that starts empty: the archive, Mathlib with its dependencies, and Lean's own library, 186,200 modules that declare 2,701,138 distinct names. Of these, 2,695,298 are neither unsafe nor partial, and they are what a replay examines, together with the further declarations of names that more than one module declares.

Each kind is examined in its own way. A theorem, a definition, an opaque constant or an axiom is passed to the kernel's entry point `Kernel.Environment.addDeclCore` against an environment that contains only declarations that precede it in a dependency order. An inductive type is passed with the other types of its mutual block and their constructors, once for the block, and the kernel generates the constructors and the recursors itself. The quotient type is one declaration of the kernel's, which provides four constants. When every declaration has been sent, the environment the kernel has built is compared with what was read from the compiled files, in both directions: each of the 2,695,298 constants must equal, field by field, the constant of the same name in the kernel's environment, and the kernel's environment must contain nothing else. Terms are compared up to the names and annotations of bound variables, which the kernel does not consult. So, apart from the unsafe and partial declarations, the compiled files hold, for the version of each name that Lean's import keeps and as Lean's reader of compiled files presents them to a file outside Lean's module system, exactly what the kernel produces from the declarations in them; and every further version of a repeated name was accepted by the kernel. What a module inside the module system would receive from the same files is compared separately ([2.8](#sec:checker)); in this run that covered 657,071 constants in 11,013 modules.

The kernel accepted every declaration sent to it: 2,084,262 theorems, 556,318 definitions, 3,882 opaque constants, 7 axioms, the quotient type with its 4 constants, and 15,769 inductive types in 15,734 blocks.

The comparison found every one of the 2,695,298 constants of the files, among them 19,159 constructors and 15,897 recursors, equal to the kernel's, and nothing else in the kernel's environment. There was no failure. The run took 116 minutes on 32 threads.

The 7 axioms are all declared in Lean's core library; the archive declares none, and the five theorems depend on three of them. In 40,595 cases a name is declared again by a further module, which Lean's import accepts for theorems with the same statement; every version was checked. The 5,840 declarations not replayed are those that Lean marks unsafe or partial: 5,008 are the compiled forms of recursive definitions and the rest are programs and the unsafe axioms that Lean's compiler uses. Lean's own replay does not check them either, and outside Lean's module system the kernel accepts no theorem or safe definition that refers to one; [2.8](#sec:checker) says what holds inside it.

For each of the five theorems the program also reports that it was checked as a theorem and that nothing it depends on failed, and computes the axioms it depends on from the terms, in the environment the kernel built. They are `propext`, `Classical.choice` and `Quot.sound` for each, and the program that computes the cone finds the same three among the constants of the cone. This matters because `#print axioms`, for a theorem of an imported module, prints a list that was recorded in the compiled file when it was written; it does not walk the terms again. For `riemannHypothesis` the replay program counts 1,478,222 names, following types, values, constructors, the blocks and rules of the recursors reached, the structures of projections and the names into which numerals and strings unfold; the cone of [2.6](#sec:cone), which follows types, values, the link between an inductive type and its constructors and the structures of projections, has 1,478,220.

### 2.8. The checker

<a id="sec:checker"></a>

The replay was done by a program of ours, of 594 lines, published with this paper.

It imports once, orders the declarations, and runs the kernel checks of theorems, definitions, opaque constants and axioms in parallel, each against a snapshot of the environment as it stood when the declaration's turn came; inductive types and the quotient type are checked on the main thread. Lean's own checker is `leanchecker` ([Morrison and Ullrich 2023](#ref-lean4checker)).

Its ordinary mode imports the import closure again for every module it checks. Run as described below, 8 processes at a time and beside the other runs named there, it took 61 minutes for 501 names; at that rate, checking each of the 175,187 modules once would take about 15 days on that machine. Its function for one module, called on one module at a time, took 2 to 3 seconds on each of the 30 modules named below. Its other mode, `--fresh`, replays one closure in one process, as our program does, but on one thread. We ran it on the whole import closure of `Main`, on the second machine. It accepted the closure, ending with exit code $0$ after 8.0 hours, 7.3 of them processor time, and printing nothing; for about its first two hours three of the runs below ran beside it: the sample run whose time is quoted, the second implementation on the closure of the $L$-function, and the checks of single modules. So each of the 2,695,298 constants of [2.7](#sec:replay), which are those that are neither unsafe nor partial, each in the version that Lean's import keeps of its name, has been accepted by the kernel twice from an empty environment, once driven by Lean's own checker and once by our program. What rests on our programs alone is what Lean's replay does not do: the comparison of the kernel's environment with the compiled files beyond constructors and recursors, the check of the further versions of repeated names, the comparison of the files of the module system, and the axioms computed from the terms.

For those we give the grounds for trusting the replay program. The runs behind [Table 1](#tab:hostile), and those with `--fresh` on Mathlib and on the module that declares `RiemannHypothesis`, were made on the second machine, on its own build of Mathlib from source, while it was building the archive. Everything else in this subsection was run after the build: the run of `leanchecker --fresh` on `Main`, the second implementation on the closure of the $L$-function, the runs on a sample of names of the archive's modules, and the checks of single modules, with the two tests of the way of calling them. The sample run whose time is quoted ran beside the run on `Main` and, for its first half hour, beside that run of the second implementation.

*Review.* The program has been reviewed four times against the source of Lean 4.33.1, by further instances of the language model that wrote it; no person has reviewed it. All four reports are published with this paper. The first two, made independently of each other, found among other things that the program used for the first two versions of this paper compared only constructors and recursors with the kernel's, so that an inductive type or a quotient constant written directly into a compiled file was counted and never examined; and that it rebuilt an inductive type from those of its listed constructors that it found, dropping one that was missing. Neither found a way for this to affect the five theorems, and Lean's own replay shares the first gap. But a replay with those gaps establishes less than those versions said. The program was rewritten along the lines the two reviews proposed. The third review, which had the first two before it, built and ran the rewritten program. It found one further gap. Mathlib and Lean's library use Lean's module system, in which a module is compiled to several files, and the program read only the one that a file outside the module system reads; a false theorem in another would not have been seen. It also found that two of the program's checks were exercised by no test module. The program was changed to compare the other files, and test modules were added. The fourth review, of those changes, found two more routes of the same kind, by which a module inside the module system could receive a constant that the program had not seen, and found that the test script could report on files left by an earlier run. The two routes were closed, each with a test module, and the script was corrected. The reviewer then checked the corrections, building the program and running the tests, and found no input on which the corrected program reports success wrongly; that check, with the points it leaves open, is appended to the fourth report. None of the gaps found by the third and fourth reviews touches the five theorems, which are stated and checked outside the module system ([2.2](#sec:scan)). After that check only the comment at the head of the program was changed, to correct sentences that the reviewer had named and to add a paragraph on the memory it uses; its instructions are the ones checked, as a comparison with the program of version 1.2 of this paper's repository shows. The script that runs the tests was also changed after the check: it refuses an empty or repeated list of modules and tests the program's list of axioms. The tests below were made with the program as it now stands, whose SHA-256 begins 5e695c0b2bb77f49.

So was the replay reported here. The first run, made with the earliest form of the program on the first build, had given the same counts of modules, definitions, opaque constants, axioms, inductive types, constructors and recursors, and 6 theorems fewer, the difference between the two builds of Mathlib ([2.4](#sec:build)).

*Modules built to be wrong.* We made 29 small modules ([Table 1](#tab:hostile)). 11 are compiled files written directly; every other one has a source and compiles. 25 of them have, in their import closure, a compiled file that holds something the kernel never accepted, or whose parts disagree in a way that Lean never writes: a theorem added without a check, a recursor altered after the kernel made it, a constant of a kind that only the kernel creates. Among them is a theorem whose statement is `False`, in a module that compiles and for which `#print axioms` reports that the theorem depends on no axioms. A successful build and a clean list of axioms do not, then, by themselves show that a theorem holds; they show it for code that does not write into the environment behind the kernel's back and that imports only compiled files that Lean itself wrote. A replay covers the rest, within what a replay examines. Our program rejects all 25, each with failures recorded under exactly the names its design predicts, and accepts the 4 controls. Lean's checker with `--fresh` rejects 9 of the 25, and in its ordinary mode, which examines the module it is given and trusts that module's imports, 7. In the table a checker *rejects* when it exits with an error.

<a id="tab:hostile"></a>

<table>
<caption>The modules built to test the checkers, and what each checker does with each. The first 4 are controls, which a checker should accept; a sound replay rejects the others. The ordinary mode of <code>leanchecker</code> examines the named module and trusts its imports; <code>lean4lean</code> is the second implementation of the kernel of <a href="#sec:checker" data-reference-type="ref+label" data-reference="sec:checker">2.8</a>.</caption>
<tbody>
<tr>
<td style="text-align: left;">The compiled file holds</td>
<td colspan="2" style="text-align: center;"><code>leanchecker</code></td>
<td style="text-align: center;"><code>lean4lean</code></td>
<td style="text-align: center;">ours</td>
</tr>
<tr>
<td style="text-align: left;"></td>
<td style="text-align: center;">ordinary</td>
<td style="text-align: center;"><code>--fresh</code></td>
<td style="text-align: center;"><code>--fresh</code></td>
<td style="text-align: center;"></td>
</tr>
<tr>
<td style="text-align: left;">nothing wrong: a theorem, a definition, an inductive type, a structure</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
</tr>
<tr>
<td style="text-align: left;">nothing wrong: the tool the other modules use to write into a compiled file</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
</tr>
<tr>
<td style="text-align: left;">a proof of <code>False</code> from a declared axiom, which the list of axioms shows</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
</tr>
<tr>
<td style="text-align: left;">a proof by <code>sorry</code>, which the list of axioms shows</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
</tr>
<tr>
<td style="text-align: left;">a theorem <code>False</code> whose proof is <code>True.intro</code>, added with no check</td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">a definition whose value is of another type, added with no check</td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">a theorem whose proof uses an unsafe definition</td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">a recursor whose two rules were exchanged after the kernel made it</td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">a constructor given a false number of fields</td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">a theorem two modules declare; the version Lean keeps has no proof</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">the same; the version Lean sets aside has no proof</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">an inductive type that lists a constructor that does not exist</td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">a definition stored under the name of another constant</td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">an inductive type with no recursor, and a theorem that uses one</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">an inductive type whose record was altered after the kernel made it</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">a constant of the quotient kind with the type <code>False</code></td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">a theorem <code>False</code> proved from that constant, with no axioms</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">a constant of the inductive kind with the type <code>False</code></td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">an inductive type whose listed constructor is an unsafe definition</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">a theorem <code>False</code> in the first part of a module-system file only</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">the same, the part replayed marked as outside the module system</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">in the first part, an axiom <code>False</code> under the name of a true theorem</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">in the first part, an axiom with other universe parameters</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">in the first part, an axiom <code>False</code> for a partial definition, not marked unsafe</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">the same for an unsafe definition</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">the same for an unsafe opaque constant</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">a first part whose import list names one module more</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">a theorem <code>False</code> in the file of compiled code</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
<tr>
<td style="text-align: left;">a file of compiled code whose import list names one module more</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;">accepts</td>
<td style="text-align: center;"><strong>rejects</strong></td>
</tr>
</tbody>
</table>

*Agreement with Lean's checker.* Besides the closure of `Main`, `leanchecker --fresh` was run on the module of Mathlib that declares the statement `RiemannHypothesis`, and on Mathlib as a whole; it accepted both. Our program accepts the same closures; those two have 430,239 and 766,714 declarations. All of this ran on the second machine's build.

In its ordinary mode `leanchecker` takes a name as a prefix: it checks the module of that name and every module whose name extends it, each module's own declarations against its imports, importing the closure again for each and all at once. We ran it on 501 names, one process a name and 8 at a time: `Main` and 500 taken from the modules that hold a declaration of the cone by a fixed selection that can be repeated (`shuf` with a constant in place of random bytes; the names are listed in the results). One of the names has modules under it, 29 of them, so that the names cover 530 modules. It accepted the 500 names that are single modules. On the remaining name the system killed the process at the container's memory limit (exit code 137), which is no verdict of the checker; the command imports the closure 30 times at once there. Run by itself, it was killed in the same way; the container's anonymous memory, read once a second, had reached 59.7 GB of its limit of 64 GB. We then called the function that the checker applies to one module, `replayFromImports`, on that module and on each of the 29 under it, one at a time; it accepted all 30, in 2 to 3 seconds each. Called in that way it also rejects a test module of [Table 1](#tab:hostile) that it must reject and accepts one that it must accept. The checker also accepts the module `Statements`, which holds the archive's own definitions of the statements and is not among the modules a sample could draw.

*The files of the module system.* A module that uses Lean's module system is compiled to five files: a first part, a part for the language server, a private part, and two files of compiled code. A file outside the system, such as every file of the archive, reads the private part, and that is what a replay replays; a module inside the system that imports with `import all` reads it too. Otherwise a module inside the system receives its constants from the first part, from the modules that the first part's import list names, and, when a module is loaded only for its compiled code, from a file of compiled code and from the modules that its import list names. Lean writes the first part from the declarations of the private part, each unchanged, reduced to an axiom with the same statement, or left out; it gives the first part and that file of compiled code the import list of the private part; and the command `lean`, which compiles a file, writes no constants into the files of compiled code. Our program fails unless all of that holds. In Mathlib's closure every one of the 10,498 modules uses the module system, and the 644,284 constants of their first parts are what Lean derives from the parts replayed, with one qualification. For a recursive definition that is compiled to code Lean stores a second constant, marked partial, which a replay does not examine and which no theorem outside the module system may use. Lean 4.33.1 writes its statement into the first part as an axiom marked unsafe; in the files of Lean's own library that Mathlib imports, as distributed, 531 such axioms are not marked, so that a theorem of a module inside the system may use one, and `#print axioms` would not list it. The program allows the unmarked form in those files and nowhere else, and counts it. This comparison rests on the fourth review's reading of how Lean 4.33.1 imports; it is not a claim that no other route exists.

*A second implementation of the kernel.* All of the above uses the kernel inside Lean. `lean4lean` ([Carneiro 2024](#ref-lean4lean)) is an implementation of the type checker written in Lean. Its authors describe it as derived directly from the C++ code of the kernel and as likely to share errors with it, so it is a second implementation and not a fully independent one. We used a fixed commit of it, made for a release candidate of Lean 4.33.0, and built it with Lean 4.33.1. In its source the terms are Lean's own, with Lean's functions for substitution, and compiled files are read by Lean's reader (`readModuleDataParts` in its `Replay.lean`); type inference and definitional equality (`TypeChecker.lean`), the checking of inductive types (`Inductive/Add.lean`) and the quotient type (`Quot.lean`) are written there in Lean. We ran it where its speed allowed, on the second machine. On the 25 modules that a replay must reject, with `--fresh`, it rejects 9; like Lean's checker, it does not compare the inductive types and the other constants it builds with those of the files ([Table 1](#tab:hostile)). With `--fresh` on the module of Mathlib that declares `RiemannHypothesis` and `riemannZeta`, and on the one that declares the $L$-function of a Dirichlet character, it accepts the whole import closure of each, in that machine's build of Mathlib: every definition on which those three depend was accepted by a second implementation of the kernel.

It was also run on the same 501 names, one process a name and 10 at a time; it takes a name in the same way. It accepted the 500 names that are single modules. On the remaining name the system killed the process at the container's memory limit (exit code 137), which is no verdict of the checker; the command imports the closure 30 times at once there. Run by itself, it was killed in the same way; the container's anonymous memory, read once a second, had reached 59.5 GB of its limit of 64 GB. We then called the function that the checker applies to one module, `replayFromImports`, on that module and on each of the 29 under it, one at a time; it accepted all 30, in 4 to 7 seconds each. Lean's interpreter ran the function. Called in that way it also rejects a test module of [Table 1](#tab:hostile) that it must reject and accepts one that it must accept. It accepts the module `Statements` too. It was not run on the whole archive.

### What this establishes, and what it does not

In Lean 4.33.1 with Mathlib at the pinned commit, [Statement 2.1](#st:rh) and [Statement 2.2](#st:grh) and [Statement 2.3](#st:strip) are theorems, with no assumption beyond the standard axioms. That is the whole of what the machine certifies. It does not certify any description of the proof, including ours.

Three limits should be stated. First, the full replay uses one kernel, the one in Lean 4.33.1: the build, our replay and Lean's checker share it, together with the code that reads compiled files, so their agreement is one witness to the kernel's judgment and not several. That code takes on trust the hashes and flags that names and terms carry in a compiled file; nothing recomputes them, and the third review describes how a file written by hand could use that to make a statement refer to another constant than the one its name shows. The files replayed here were written by Lean in our second build or, for Lean's own library, are those of the published release; and `check.sh` writes out [Statement 2.1](#st:rh) and [Statement 2.2](#st:grh) and [Statement 2.3](#st:strip) and elaborates each afresh against its theorem. The second implementation covered the definitions named above and a sample, not the whole.

The kernel inside Lean also takes on trust the definitions of a few constants of Lean's own library that it recognises by name, among them the arithmetic of the natural numbers. On the second machine we compared the toolchain's files with the published release, and the second implementation ran on closures in which those definitions are declared; when it adds one of them it checks that the definition has the form assumed (`checkPrimitiveDef` in its source). Neither was done on the first machine. A run of another implementation of the kernel over the whole archive is the check most worth adding.

Second, the replay program has been reviewed and tested as described, but by the model that wrote it and by no person. That the kernel accepts each of the 2,695,298 constants no longer rests on it, since Lean's own checker finds the same; the comparisons and the further versions listed in [2.8](#sec:checker) do. Third, both builds are ours; we know of no other at the time of writing.

## 3. The shape of the proof

<a id="sec:overview"></a>

The top of the proof is short. [Statement 2.1](#st:rh) follows from [Statement 2.2](#st:grh) for the trivial character by the functional equation, in a few dozen lines on Mathlib's interface. [Statement 2.2](#st:grh) is obtained for every character from a statement  `ZeroFreeAll` about primitive characters. A theorem (`zero_free_all_of_green_v_win`) derives that statement from three hypotheses, and with the passage to all characters it reads $$\begin{gather*}
\text{\texttt{every\_character\_of\_green\_v\_win}}\colon\\
\mathsf{Green}\ \longrightarrow\ \mathsf{VWin}\ \longrightarrow\ \mathsf{Nonempty}(\mathsf{HypsAlt})
\ \longrightarrow\ \mathsf{EveryCharacter},
\end{gather*}$$  each of which is in turn proved in the archive. They are the three inputs of the argument:

- $\mathsf{Green}$: a statement about the characters of finite general linear groups, in the parametrisation of J. A. Green ([Green 1955](#ref-green1955characters)), used to count local types;

- $\mathsf{VWin}$: a bound on Galois cohomology groups attached to an auxiliary field, valid on windows of scales ([8](#sec:cohomology));

- $\mathsf{HypsAlt}$: a record of forty-six fields about families of lattices of automorphic forms on unitary groups ([5](#sec:lattices) and [7](#sec:frame) and [10](#sec:literature)).

The body of that theorem applies a windowed form of Landau's theorem, on windows $[Y,Y^{3/2}]$, to a statement $\mathsf{TopG}$, which says: for every small $\varepsilon>0$ there is a family of arithmetic data, indexed by scales $x$ in long windows, on which a condition `ChainTied` holds. `ChainTied` packages eleven inequalities between real numbers ([5](#sec:lattices)), with size conditions and with the identification of those numbers with the arithmetic data of the count and with slopes and heights of lattices. The inequalities, with the size conditions and the identification of the count, imply $G(x)\le x^{1/2+C\varepsilon}$ by an argument that involves no arithmetic beyond an identity of character sums ([4](#sec:analytic)).

So the proof has two halves that meet in eleven real inequalities:

| *Analytic half* ([4](#sec:analytic)) | *Arithmetic half* (Sections [5](#sec:lattices)--[9](#sec:hosts)) |
|:---|:---|
| Landau on windows; an exact identity for a count of prime powers; averaging; balancing three error terms at $m\approx\sqrt x$. | Lattices of forms, period maps, divisibility at inert primes, a slope inequality, a period computation, a trace formula, a cohomological bound, auxiliary fields. |

The analytic half is elementary. Almost all of the archive is the arithmetic half and the published theorems it formalises.

### Notation

<a id="notation"></a>

In the account of the argument ([4](#sec:analytic) and [5](#sec:lattices) and [6](#sec:divisibility) and [7](#sec:frame)) the letters of the following table have the meaning given here, except where one is the index or the bound variable of a formula, or carries a subscript other than those of the table. [8](#sec:cohomology) and [10](#sec:literature) describe inputs in the notation of their sources, and there $E$, $G$, $H$, $\lambda$, $h$, $n$, $o$, $p$ and $q$ are also used as the sources use them. Any other letter is local to the statement or paragraph in which it occurs.

|  |  |
|:---|:---|
| $x$, $\varepsilon$, $b$ | the scale, a large real number; a small fixed exponent; $b=\exp(x^\varepsilon)$ |
| $m$, $k$ | the number of lifts, $x^{1/2-\varepsilon}\le m\le x^{1/2+\varepsilon/2}$; the rank parameter, $xm\le k\le n^2x^{1/2-\varepsilon}$ |
| $E$, $\mathfrak G$, $H$, $n$ | the host field; its Galois group $(\mathbb{Z}/2)^2\times H$ over $\mathbb{Q}$; $n=\lvert H\rvert$ |
| $\Phi$, $\chi_\Phi$, $f$ | the CM type, a subgroup of index two of $\mathfrak G$; its quadratic character; $f=\lvert \Phi\rvert=2n$, the number of infinite places of $E$ |
| $q$, $d$, $e_2$, $\sigma$ | the two primes of the host and the exponent of its $2$-power layer ([9](#sec:hosts)); the non-trivial element of the inertia group at $d$ |
| $G_\chi$, $G$ | the smoothed sum over prime powers attached to a character [(4.1)](#eq:G); $G=G_1$ |
| $\mathcal L$, $\mathcal K$, $\psi_{\mathcal K}$, $o$ | a level: its set of characters, its distinguished character, its integer [(4.2)](#eq:level) |
| $A_0$, $TT$, $T_2$, $\delta_T$ | a subgroup of $H$; the set of top places; the thick set; its density $\lvert T_2\rvert/n$ |
| $t$, $a_t$, $w$, $u_0$ | a top place, an element of $TT$; its size; a system of weights on $\Phi$; a translate in $A_0$ |
| $\mathcal K'$, $\beta$ | the kept characters and their common weight ([4.3](#sec:reduction)) |
| $\mathrm{ASK}$, $\mathrm{MAIN}$, $\mathrm{Err}$ | the count [(4.3)](#eq:ask), its main term [(4.4)](#eq:main), the error of [4.4](#sec:balance) |
| $u$, $M_u$, $N_u$, $B_u$ | a word; its lattice of forms; the rescaled sublattice; its period map ([5.2](#sec:cast)) |
| $h(u)$, $T(u)$, $P$ | the height bound of $B_u$; the level prime; the lattice of periods |
| $\lambda$, $g(u,\lambda)$ | a finite place of the coefficient field; the exponent of the rescaling there, a sum of gains and corrections [(5.1)](#eq:Nu) |
| $p$, $h_p$, $\gamma_p$ | a rational prime; the component in $H$ of its Frobenius element; $\gamma_p=p/(p^2-1)$ |
| $\ell$ | the prime of [6](#sec:divisibility) and of [8](#sec:cohomology) |
| $\gamma$, $\Omega$, $\operatorname{ph}$ | Euler's constant; a CM period; $\operatorname{ph}(y)=y\log y-y$, so that $\operatorname{ph}(a)=\log a!+O(\log a)$ |
| $\bar\mu$, $HH$, $u_F$, $\delta_F$, $\eta_F$, $e_F$ | the parameters of the slope inequality ([Statement 5.1](#st:F)) |
| $t_0$, $\operatorname{len}_\ell(e)$ | the number of twists $\lfloor x^{401}\rfloor$; the length of $\mathrm{Sha}(E,\ell,e)$ ([8](#sec:cohomology)) |

The weights of a frame are written $\gamma_i$ with an index.

## 4. The analytic half

<a id="sec:analytic"></a>

### 4.1. Landau on windows

<a id="sec:landau"></a>

For a Dirichlet character $\chi$ and $y>0$ put <a id="eq:G"></a> $$\begin{equation}
\tag{4.1}
G_\chi(y)=
\begin{cases}
\displaystyle\sum_{n\le y}\Lambda(n)\Bigl(\frac yn-1\Bigr)-y\log y+(1+\gamma)\,y, & \chi=1,\\[1.2em]
\displaystyle\sum_{n\le y}\Lambda(n)\chi(n)\Bigl(\frac yn-1\Bigr)+y\,\frac{L'}{L}(1,\chi), & \chi\neq1,
\end{cases}
\end{equation}$$ where $\Lambda$ is the von Mangoldt function and $\gamma$ Euler's constant. This is a prime sum with the smooth weight $(y/n-1)_+$, less its expected main term; by the explicit formula ([Montgomery and Vaughan 2007](#ref-montgomery2007multiplicative)) it is a sum of $-y^{\rho}/(\rho(\rho-1))$ over zeros $\rho$, plus lower-order terms. We write $G=G_1$. A *family* $F$ is a finite set of characters $\chi_i$, each either non-trivial or of modulus $1$, with positive weights $a_i$, and $G_F(y)=\sum_i a_i\,\operatorname{Re}G_{\chi_i}(y)$.

<a id="st:landau"></a>


**Statement 4.1** (`zeroFree_of_rpow_window`). Let $0<\theta<1$, $\omega>0$ and $C$ be real. Suppose that for every $Y_0$ there is $Y\ge Y_0$ with $G_F(y)\le C\,y^{\theta}$ for all $y\in[Y,Y^{1+\omega}]$. Then $L(s,\chi_i)\neq0$ for every $i$ and every $s$ with $\operatorname{Re}s>\theta$.



 In the application the family is a *level* $\mathcal L$ : a finite set $\mathcal K$ of primitive characters that contains the trivial character and is closed under inversion, at most one distinguished odd real character $\psi_{\mathcal K}\in\mathcal K$, and a natural number $o$, with <a id="eq:level"></a> $$\begin{equation}
\tag{4.2}
G_{\mathcal L}(y)=G(y)+\sum_{\psi\in\mathcal K,\ \psi\neq1}\mathrm{wt}(\psi)\,\operatorname{Re}G_\psi(y),\qquad
\mathrm{wt}(\psi)=\begin{cases}1,&\psi=\psi_{\mathcal K},\\ (3o+1)^{-1},&\text{otherwise}\end{cases}
\end{equation}$$ (`Level.Gm`). The theorem is proved level by level (`zeroFreeOn_of_levels`).

 Landau's classical theorem ([Landau 1905](#ref-landau1905tschebyschef)) concerns a Dirichlet series with non-negative coefficients and needs the bound for all large $x$. The windowed form is what lets the rest of the proof work only at scales where suitable auxiliary fields exist. Its proof takes the Laplace transform of $v\mapsto G(e^v)$ and looks at its Taylor coefficients at a real point $s_0$; the coefficient of order $N$ is an integral of $G$ against a Gamma kernel which, for $N\approx(1+\omega/2)s_0\log Y$, is concentrated in the window. A zero to the right of $\theta$ contributes a residue of a definite sign and makes these coefficients grow; a two-case argument on whether the zero nearest to $s_0$ is real handles complex zeros. The only input from the theory of $L$-functions is non-vanishing on $\operatorname{Re}s\ge1$.

The theorem is applied with $\omega=\tfrac12$, that is on windows $[Y,Y^{3/2}]$, and with $\theta=\tfrac12+C\varepsilon$ for every small $\varepsilon$.

### 4.2. An exact identity

<a id="sec:identity"></a>

Let $H$ be a finite abelian group and $\mathfrak G=(\mathbb{Z}/2)^2\times H$; in the application $\mathfrak G$ is the Galois group of an abelian CM field $E/\mathbb{Q}$, the *host* ([9](#sec:hosts)). Let $\Phi\subset\mathfrak G$ be the subgroup of index two of the elements whose component in the first factor $\mathbb{Z}/2$ is $0$; in the application it does not contain complex conjugation, so it is a CM type. Every rational prime $p$ has a Frobenius element and an inertia group in $\mathfrak G$, and every character $\psi$ of $\mathfrak G$ is a Dirichlet character with its own function $G_\psi$. The host is required to satisfy the following (`HostFactsS`): there are a prime $d$ and a finite set $S$ of primes containing $2$ and a second prime $q$, with $d\notin S$, such that every prime outside $S\cup\{d\}$ is unramified, the inertia group and the Frobenius element of every prime of $S$ lie in $\Phi$, and the inertia group at $d$ is $\{0,\sigma\}$ for a fixed element $\sigma$.

Fix a size $a>0$, an element $t\in H$, and a weight $w(\rho)>0$ for each $\rho\in\Phi$. A fixed bijection, depending on $t$, pairs each $g\notin\Phi$ with a partner $\rho_g\in\Phi$. Put <a id="eq:ask"></a> <a id="eq:main"></a> $$\begin{align}
\mathrm{ASK}&= \sum_{p}2\log p\sum_{\substack{i\ge1\\ \operatorname{Frob}_p^{\,i}\notin\Phi}}
        \max\!\Bigl(\frac{a}{p^{i}}-w(\rho_{p,i}),\,0\Bigr)\ +\ (\text{a term at } d),
        \tag{4.3}\\
\mathrm{MAIN}&= a\Bigl(\log a-1-\gamma+\frac{L'}{L}(1,\chi_\Phi)
        -\frac1{\lvert \Phi\rvert}\sum_{\rho\in\Phi}\log w(\rho)\Bigr),\tag{4.4}
\end{align}$$ where $\rho_{p,i}$ is the partner of $\operatorname{Frob}_p^{\,i}$ and $\chi_\Phi$ is the quadratic character that cuts out $\Phi$.

<a id="st:balance"></a>


**Statement 4.2** (`ch_balance`). For a host satisfying the conditions above, $$\mathrm{ASK}-\mathrm{MAIN}\;=\;\frac1{\lvert \Phi\rvert}\sum_{g\notin\Phi}\ \sum_{\psi\in\widehat{\mathfrak G}}
\overline{\psi}(g)\,w(\rho_g)\,G_\psi\!\Bigl(\frac{a}{w(\rho_g)}\Bigr).$$



 This is orthogonality of characters applied to the count; nothing is estimated. Its meaning is that $\mathrm{ASK}$, a count of prime powers $p^i\le a/w$ whose Frobenius avoids $\Phi$, weighted so that each contributes about $2\log p\cdot a/p^i$, has an explicit main term, and that its deviation from the main term is a combination of the sums $G_\psi$ at the points $a/w(\rho)$. An *upper* bound for $\mathrm{ASK}$ is therefore a one-sided statement about those sums.

### 4.3. From the count to $G$

<a id="sec:reduction"></a>

Let $A_0\subset H$ be a subgroup, and let $\Psi(A_0)$ be the set of characters of $\mathfrak G$ that are trivial on $A_0$. Take a set $TT\subset H$ of sizes with $\lvert a_t/b-x\rvert\le1$, a set $T_2\subset A_0$, and $m$ systems of weights $w_{u_0,j}$, indexed by $j=1,\dots,m$ and by a translate $u_0\in A_0$. The weights are of two kinds (`SizesA`):

- on the *thick* places, the images of $T_2+u_0$, the weight lies in $[b,\,b+\eta+1]$, so that $a/w\approx x$, the scale of interest;

- on the other places of $\Phi$ the weight is at most $2b'$, with $b'X'\le xb$, so that $a/w\ge X'/3$, a scale at which every $G_\psi$ is assumed negligible: $\lvert G_\psi(y)\rvert\le\vartheta y$ for $y\ge X'/3$, with $\vartheta\le(2\lvert \Phi\rvert\,x(x+1))^{-1}$ (`ThinScales`, `CostWindows`). In the application $X'=\exp(x^{\varepsilon/3})$ and $\vartheta=\exp(-c\,x^{\varepsilon/8})$ (`Char_at`), the quality of the classical zero-free region.

Let $\mathcal K'\subset\Psi(A_0)$ be a set of *kept* characters, containing the trivial one, each with $\psi(\sigma)=1$, and let $\lvert \beta\rvert\le1$. Put $$G_{\mathcal K'}(x)=\sum_{\psi\in\mathcal K'}\mathrm{wt}_\beta(\psi)\,\operatorname{Re}G_\psi(x),\qquad
\Sigma_{\mathcal K'}(x)=\sum_{\psi\in\Psi(A_0)\setminus\mathcal K'}\lvert G_\psi(x)\rvert,$$ where $\mathrm{wt}_\beta(\psi)$ is $1$ if $\psi$ is trivial on $H$ and $\beta$ otherwise.

<a id="st:core"></a>


**Statement 4.3** (`ch_core`). Let $C\ge0$, $\varepsilon>0$, $\lvert \beta\rvert\le1$ and constants $M$, $K_o$, $C_E$ be given. For all sufficiently large $x$ the following holds. Assume the conditions on the host and the sizes above, the size conditions of [4.4](#sec:balance), and

1.  $\lvert \Psi(A_0)\rvert\le M$, and for each kept $\psi$ that is not trivial on $H$, $\bigl|\sum_{t\in TT}\psi(0,t)-\beta\,\lvert TT\rvert\bigr|\le M\,x^{-1+\varepsilon}\lvert TT\rvert$;

2.  $\lvert \tfrac{L'}{L}(1,\psi)\rvert\le K_o$ for kept $\psi\neq1$, and $\le C_E\log x$ for the other $\psi\in\Psi(A_0)$;

3.  for every translate $u_0\in A_0$, $$\sum_{t\in TT}\sum_{j=1}^{m}\bigl(\mathrm{ASK}-\operatorname{Re}\mathrm{MAIN}\bigr)(a_t,t,w_{u_0,j})\ \le\ x^{C\varepsilon}\,\mathrm{Br},$$ where $\mathrm{Br}$ is the bracket of [4.4](#sec:balance).

Then $G_{\mathcal K'}(x)\le x^{1/2+(C+3)\varepsilon}+\Sigma_{\mathcal K'}(x)$.



  The proof applies [Statement 4.2](#st:balance) to each term of (3). Condition (1) says that the sizes  $TT$ see each kept character with the same weight $\beta$, which is what turns the sum over $t\in TT$ of $\psi(0,t)\,G_\psi(a_t/b)$ into $\lvert TT\rvert\,\mathrm{wt}_\beta(\psi)\,G_\psi(x)$ up to an error; the characters that are not kept are bounded by their absolute values. The outcome is  <a id="eq:reduction"></a> $$\begin{equation}
\tag{4.5}
\lvert TT\rvert\,m\,b\,\frac{\delta_T}{2}\,\Bigl(G_{\mathcal K'}(x)-\Sigma_{\mathcal K'}(x)-4x^{1/2+\varepsilon}\Bigr)\ \le\
x^{C\varepsilon}\,\mathrm{Br}+\frac{2\lvert TT\rvert\,m\,b}{x},
\end{equation}$$ where $\delta_T=\lvert T_2\rvert/\lvert H\rvert$ is the density of the thick set, and [4.4](#sec:balance) converts this into the statement.

For a level $\mathcal L$ and a host adapted to it, $\mathcal K'$ is the image of the level's characters, $\beta=(3o+1)^{-1}$ and $M=4o$. Adapted means in particular (`ExceptionalCharacterKept`) that the quadratic character of $\mathfrak G$ that is trivial on $H$ and on $\sigma$ is induced from $\psi_{\mathcal K}$ if the level has a distinguished character, and is not kept otherwise; it and the trivial character are the only kept characters that can be trivial on $H$. Then $G_{\mathcal K'}=G_{\mathcal L}$ (`gmA_eq`) and $\Sigma_{\mathcal K'}(x)\le4o\,x^{1/2+\varepsilon}$ (`sigA_le`), the latter because the host is chosen so that its other characters satisfy $\lvert G_\psi(x)\rvert\le x^{1/2+\varepsilon}$ at the single point $x$; [9](#sec:hosts) explains why this is not circular. Hence (`core_gm`), applying [Statement 4.3](#st:core) with $C=e_D+e_L+3$, <a id="eq:coregm"></a> $$\begin{equation}
\tag{4.6}
G_{\mathcal L}(x)\ \le\ x^{1/2+(e_D+e_L+7)\varepsilon},
\end{equation}$$ where $e_D$ and $e_L$ bound the exponents of $x^\varepsilon$ that the record of [5.2](#sec:cast) allows in the errors of its divisibility and loss clauses. Condition (3) is the lattice inequality of [5](#sec:lattices), applied to each translate (`ch_top`).

### 4.4. Three costs and the exponent $\tfrac12$

<a id="sec:balance"></a>

The size conditions (`SizeWindows`) involve a rank parameter $k$ with $xm\le k\le n^2x^{1/2-\varepsilon}$, where $n=\lvert H\rvert$, and they bound the two sets from below: $\lvert TT\rvert\ge\tfrac12x^{-\varepsilon/8}n$ and $\delta_T\ge x^{-\varepsilon}$. The bracket of [Statement 4.3](#st:core) is $$\mathrm{Br}=\lvert TT\rvert\,a_E\,\bigl(1+\tfrac{m^2}{k}\bigr)
   +m\,\bigl(2nmb\,x^{\varepsilon}+\lvert T_2\rvert\,k\,b\,x^{2\varepsilon}/n^2\bigr),\qquad a_E\le 2xb,$$ and we write $\mathrm{Err}=x^{C\varepsilon}\,\mathrm{Br}$. Divided by the normalisation $\lvert TT\rvert\,m\,b\,\delta_T$ on the left of [(4.5)](#eq:reduction), the three terms are at most $$\frac{2x}{m\,\delta_T}\Bigl(1+\frac{m^2}{k}\Bigr),\qquad
2m\,x^{\varepsilon}\,\frac{n}{\lvert TT\rvert\,\delta_T},\qquad
\frac{k}{n^{2}}\,x^{2\varepsilon}\,\frac{n}{\lvert TT\rvert},$$ which by the two lower bounds are of sizes $x/m$, $m$ and $k/n^2$ up to factors $x^{O(\varepsilon)}$; the factor $m^2/k$ is at most $m/x$ because $k\ge xm$. The first falls with the number of lifts and the second rises with it. At $m\approx\sqrt x$, with $k\le n^2\sqrt x$, all three are $x^{1/2+O(\varepsilon)}$ and [(4.5)](#eq:reduction) gives $G_{\mathcal K'}(x)-\Sigma_{\mathcal K'}(x)\le x^{1/2+(C+3)\varepsilon}$ (`GrowthSizeBound`).

*Remark 7*. This is the only place where $\tfrac12$ is produced. Everything that follows is devoted to proving one inequality, $\mathrm{ASK}\le\mathrm{MAIN}+\mathrm{Err}$ with $\mathrm{Err}$ of the size above.

## 5. The squeeze between two slopes

<a id="sec:lattices"></a>

This section describes how the inequality $\mathrm{ASK}\le\mathrm{MAIN}+\mathrm{Err}$ is proved. The objects are Hermitian lattices over the ring of integers of a number field, and the tool is the slope method of Bost ([Bost 1996](#ref-bost1996periodes), [2001](#ref-bost2001algebraic)), which rests on the filtration of Harder and Narasimhan ([Harder and Narasimhan 1975](#ref-harder1975cohomology)) in the arithmetic form due to Stuhler and Grayson ([Stuhler 1976](#ref-stuhler1976bemerkung); [Grayson 1984](#ref-grayson1984reduction)).

### Slopes

Let $K$ be a totally complex number field. A *Hermitian lattice* over $\mathcal{O}_K$ is a finitely generated projective $\mathcal{O}_K$-module $L$ with a positive Hermitian form on $L\otimes_v\mathbb{C}$ for each infinite place $v$. Its slope $\mu(L)$ is its Arakelov degree divided by its rank, in the normalisation $$\mu(L)=2\,\frac{\widehat{\deg}\,L}{[K:\mathbb{Q}]\,\operatorname{rk}L}-\log 2+\frac{\log\lvert d_K\rvert}{[K:\mathbb{Q}]},$$ and $\mu_{\max}$, $\mu_{\min}$ denote the largest and smallest slopes of the pieces of its Harder--Narasimhan filtration. The height $\operatorname{ht}(\varphi)$ of a $K$-linear map between such lattices is the mean over the infinite places of $\log\lVert \varphi\rVert_v^2$.

### 5.2. The cast

<a id="sec:cast"></a>

Fix a translate $u_0$. The index set is a finite set of "words" $u$; each word determines an archimedean type of automorphic form. For each $u$ there are :

- a lattice $M_u$: an integral structure on a space of vector-valued algebraic modular forms, in the sense of Gross ([Gross 1999](#ref-gross1999algebraic)), on a definite unitary group over the host field $E$, with the Petersson norm at one place. The space is the whole space of forms of the given weight and level, namely all functions on the finite set of classes of a genus with values in the weight representation, invariant under the stabilisers (`Fi`); nothing is selected by Hecke eigenvalues;

- a sublattice of $M_u$ of forms "ramified at $T$", where $T=T(u)$ is an auxiliary level prime, and its rescaling <a id="eq:Nu"></a> $$\begin{equation}
  \tag{5.1}
    N_u\;=\;\Bigl(\prod_{\lambda}\mathfrak{P}_\lambda^{-\lfloor e_\lambda\,g(u,\lambda)\rfloor}\Bigr)\cdot(\text{that sublattice}),
  \end{equation}$$ where $\lambda$ runs over finite places of the coefficient field, $e_\lambda$ is a ramification index, and the exponent is a sum over the $m$ lifts, $$g(u,\lambda)=\sum_{j=1}^{m}\bigl(\mathrm{gain}_j(\lambda)+\mathrm{fo}_j(\lambda)-\mathrm{ee}_j(u,\lambda)\bigr),$$ of the *gain* at $\lambda$ for the $j$-th lift ([5.3](#sec:adm)) and of two correction terms, of which the second depends on the word (`Iu`, `NprimeDef`, `sg`). The record does not make $g(u,\lambda)$ non-negative;

- a map $B_u$ from the space of $M_u$ to a fixed space $W$, sending a form to the periods of its $m$-fold iterated theta lift against test vectors;

- a real number $h(u)$ bounding the height of $B_u$.

There is one target: a lattice $P\subset W$, the dual of a lattice $R$ glued prime by prime from images of integral forms under the lift. We call $P$ the *lattice of periods*.

 The final theorem requires, for the family at each scale, a record of eleven clauses (`SizeData₂`) . Four of them make the chain:  <a id="eq:loss"></a> <a id="eq:gain"></a> <a id="eq:slope"></a> <a id="eq:div"></a> $$\begin{align}
&\mathrm{ASK}(u_0)-\mathrm{Ga}(u_0)\ \le\ \mathrm{Lo}, \tag{\textsf{Loss}}\\
&\mu(M_u)+\mathrm{Ga}(u_0)+\mathrm{Fo}-\mathrm{Ee}(u)-\mathrm{Lo}_5(u)\ \le\ \mu(N_u),
   \tag{\textsf{Gain}}\\
&\bar\mu-\log\lvert I\rvert-\frac{1}{1-\delta_F}\Bigl(4u_F\log\bigl(1+\tfrac{HH}{u_F}\bigr)
     +(\eta_F+4\sqrt{e_F})\,HH\Bigr)\ \le\ \mu(P), \tag{\textsf{Slope}}\\
&\mu(P)+h(u)-\mathrm{Fo}\ \le\ \sum_{t\in TT}\Bigl(m\bigl(\operatorname{ph}(a_t)-a_t\log\Omega\bigr)-a_t\log T(u)\Bigr)
     +(\text{small}). \tag{\textsf{Div}}
\end{align}$$ Here a sum over $\lambda$ weighted by $2e_\lambda$ times a normalised logarithm of the norm of $\lambda$ turns the three parts of the exponent into three real numbers: $\mathrm{Ga}(u_0)$, the total gain, from which a cost $\tau_\lambda$ at each place is first subtracted; $\mathrm{Fo}$; and $\mathrm{Ee}(u)$ (`Ga`, `Fo`, `Ee`). Further, $\bar\mu$ is the rank-weighted mean over $u$ of $\mu(N_u)-h(u)$; the term marked small is an error of the kind of [4.4](#sec:balance), with a factor $x^{e_D\varepsilon}$; and $\mathrm{Lo}$, $\mathrm{Lo}_5(u)$ are losses that are small. Read in order: the count is at most the total gain [(Loss)](#eq:loss); rescaling raises the slope of $N_u$ above that of $M_u$ by the total gain and the two corrections [(Gain)](#eq:gain); the mean slope of the $N_u$, less heights, is at most the slope of $P$ [(Slope)](#eq:slope); and the slope of $P$ is at most the period term on the right of [(Div)](#eq:div). The term $\mathrm{Fo}$ enters [(Gain)](#eq:gain) and [(Div)](#eq:div) with opposite signs and cancels. The term $\mathrm{Ee}(u)$ is not small, and it is cancelled otherwise, as follows.

Four further clauses close the chain. One bounds $\mu(M_u)$ from below and $\mu_{\max}(M_u)$ from above by error terms (`Slopes`); one bounds the variation with $u$ of $h(u)+\sum_ta_t\log T(u)$ by error terms (`HComp`); one bounds $\log T(u)$ from below by a dimension count (`Count5`, [5.5](#sec:period)); and one (`EComp5`) says that $\mathrm{Ee}(u)$ equals $m\,\ell_g\sum_ta_t$ up to an error term, where $\ell_g$ is the logarithm of the product of two auxiliary level primes of the host. The lower bound for $\log T(u)$ contains the term $m\,\ell_g$, so after the dimension count the right side of [(Div)](#eq:div) is at most $\mathrm{MAIN}-m\,\ell_g\sum_ta_t$ up to an error term, by an exact identity ([Statement 5.2](#st:key)); and the term $m\,\ell_g\sum_ta_t$, which is not an error term, cancels $-\mathrm{Ee}(u)$ in [(Gain)](#eq:gain). The remaining three clauses are positivity and size conditions.

### 5.3. Why $N_u$ still maps into $P$

<a id="sec:adm"></a>

Rescaling the sublattice by negative powers of primes raises its slope by the total gain and the two corrections, less what passing to the sublattice costs, but it is only useful if the rescaled lattice is still mapped into $P$ by $B_u$. This is the statement (`adm2`):

> for every form $\varphi$ in the unscaled sublattice, every place $\lambda$ and every integral test vector $F$, the period of the lift of $\varphi$ against $F$ is $0$ or has $\lambda$-adic valuation at least $\lfloor e_\lambda\,g(u,\lambda)\rfloor$.

It is proved by `admissible_level_two`, and it is where the arithmetic of [6](#sec:divisibility) is spent.

The gain is a closed formula (`gainP`), one for each of the $m$ lifts. It is used at the primes of two of the classes into which the host sorts the primes, the inert class and one other; at the rest the gain is $0$, and it is replaced by $0$ at a set of dropped primes, which contains every prime of the inert class for which $h_p$ below has odd order and is not $0$. For a prime $p$ let $h_p\in H$ be the component in $H$ of its Frobenius element. The top places are the elements $t$ of $TT$; they fall into orbits under translation by $h_p$ (by $2h_p$ for the primes of one class), and each orbit has a fixed base point. Call a place of *even position* if the least number of steps of $h_p$ that leads to it from the base point of its orbit is even (`IsV`; positions are used only at primes of the inert class). For a top place $t$ and $e\ge1$ the *partner* is the place $t+e\,h_p$ (taken on a second copy of the places when $p$ is of that class and $e$ is odd), and the *capacity* $c_t(e)$ is the weight at the partner less an amount that depends on the lift (`capU`). On one orbit, with sizes $\alpha_t$ equal to $a_t$ less a fixed constant, put <a id="eq:gU"></a> $$\begin{align}
g_U&=\gamma_p\sum_{t}\alpha_t\;-\;\sum_{t\ \text{of odd position}}\ \sum_{e\ \mathrm{odd}}
\min\Bigl(\frac{\alpha_t}{p^{e}},\,c_t(e)\Bigr)\;-\;\delta_p,
\qquad \gamma_p=\frac{p}{p^2-1}=\sum_{e\ \mathrm{odd}}\frac1{p^{e}},\tag{5.2}\\
g_0&=\sum_{t}\ \sum_{e\ \mathrm{odd},\ \text{not excluded}}\max\Bigl(\frac{\alpha_t}{p^{e}}-c_t(e),\,0\Bigr)-\delta_p ,\notag
\end{align}$$ the sums over the top places $t$ of the orbit (`gU`, `g0`). Here $\delta_p$ is a correction of lower order that depends on the orbit, and an odd $e$ is *excluded* for $t$ if the partner of $t$ at $e$ is another top place, on the first copy, and $e$ is the least positive exponent that reaches it (`Excl`). The formula gives $0$ if $p$ is of the inert class with $h_p=0$, or if $p$ exceeds a bound. Otherwise it gives $$\sum_{\text{orbits in }VV}\max\bigl(g_U-\mathrm{Pr},\,g_0,\,0\bigr)
\;+\;\sum_{\text{other orbits}}\max\bigl(g_0,\,0\bigr),$$ with a penalty $\mathrm{Pr}$. The set $VV$ of orbits (`VV`) is empty unless $p$ is a *candidate*, that is a prime of the inert class below a bound whose orbits have length at least $x^{\varepsilon/4}$ and which, if it is above a second bound, has no power within a small ratio of the first, fixed at each scale, and a smallness condition holds; then it is the set of orbits that satisfy a regularity condition on the positions of their top places (`Good`).

Since $\gamma_p\alpha_t=\sum_{e\,\mathrm{odd}}\alpha_t/p^e$, a place of odd position contributes to $g_U$, as it does to $g_0$ at the exponents that are not excluded, $$\sum_{e\,\mathrm{odd}}\max\bigl(\alpha_t/p^e-c_t(e),\,0\bigr),$$ and a place of even position contributes the whole of $\gamma_p\alpha_t$. This is the shape of the count [(4.3)](#eq:ask), in which only odd powers of Frobenius occur because $\Phi$ has index two, with the capacity in the place of the weight. That is why [(Loss)](#eq:loss) holds with a small loss. The divisibility of [6](#sec:divisibility) supplies the rate $\gamma_p$.

### 5.4. The slope inequality

<a id="sec:slope"></a>

The clause [(Slope)](#eq:slope) is an instance of a theorem about Hermitian lattices that involves no automorphic forms. We state it in full because it is the cleanest self-contained new statement we met.

<a id="st:F"></a>


**Statement 5.1** (`TheoremF`). Let $K$ be a totally complex number field, $P$ a Hermitian lattice over $\mathcal{O}_K$ in a $K$-space $W$, and for $i$ in a finite set $I$ let $N_i$ be a Hermitian lattice in a $K$-space $V_i$ and $B_i\colon V_i\to W$ a $K$-linear map with $B_i(N_i)\subseteq P$ and $\operatorname{ht}(B_i)\le h_i$ whenever $B_i\ne0$. Let $\bar\mu\in\mathbb{R}$, $u_F\ge0$ and $HH\ge0$ satisfy $$\bar\mu\sum_i\operatorname{rk}N_i\le\sum_i\operatorname{rk}N_i\,\bigl(\mu(N_i)-h_i\bigr),\qquad
\mu_{\max}(N_i)-h_i\le\bar\mu+u_F,\qquad \bar\mu-\mu_{\min}(P)\le HH .$$ Suppose that at one infinite place $v$, after a change of bases, after extending $W_v$ to a space $W_v'$ in which the added part has dimension at most a fraction $\delta_F<1$ of the total, and after extending each $B_i$ to a map into $W_v'$, arbitrarily on the added part, there are weights $\gamma_i>0$ with $$\begin{gather*}
\sum_i\lVert \gamma_iB_i^*B_i-1\rVert_{\mathrm{HS}}^2\le e_F\sum_i\operatorname{rk}N_i,\qquad e_F\le\tfrac14,\\
\operatorname{tr}(Q^2)\le(1+\eta_F)\,\frac{(\operatorname{tr}Q)^2}{\dim W_v'},\qquad Q=\sum_i\gamma_iB_iB_i^* .
\end{gather*}$$ Then $$\mu(P)\ \ge\ \bar\mu-\log\lvert I\rvert-\frac1{1-\delta_F}\Bigl(4u_F\log\bigl(1+\tfrac{HH}{u_F}\bigr)+(\eta_F+4\sqrt{e_F})\,HH\Bigr),$$ the term $4u_F\log(1+HH/u_F)$ being read as $0$ when $u_F=0$.



The classical slope inequality says that an injective map $\varphi\colon N\to P$ of height $h$ forces $\mu_{\max}(N)\le\mu_{\max}(P)+h$; it bounds the top of the target. [Statement 5.1](#st:F) bounds the slope of the whole target from below, from many maps at once. The hypothesis on $Q$ says that the maps form a nearly tight frame: each is nearly an isometry up to a scalar, and their images together nearly fill the target evenly.

 The proof runs level by level. For each $\tau\in[0,HH]$: cut each $N_i$ at the step of its Harder--Narasimhan filtration of slope $\bar\mu-\tau+h_i$; a Markov inequality (`frameB_share`) shows that the parts cut away have at most the share $u_F/(u_F+\tau)$ of the total rank; the classical inequality, in  its $\mu_{\min}$ form, sends what is kept into the step of the filtration of $P$ of slope $\bar\mu-\tau$; and a lemma of linear algebra on nearly tight frames shows that the images of what is kept span all but a share $\eta_F+4u_F/(u_F+\tau)+4\sqrt{e_F}$ of the frame space. So the filtration of $P$ at slope $\bar\mu-\tau$ has almost full rank for every $\tau$, and integrating over $\tau$ gives the bound: $\int4u_F/(u_F+\tau)\,d\tau$ is the term $4u_F\log(1+HH/u_F)$ and $\int(\eta_F+4\sqrt{e_F})\,d\tau$ is the term $(\eta_F+4\sqrt{e_F})\,HH$. The term $\log\lvert I\rvert$ is a slack: the form of the theorem without it is also proved, and the form with it is obtained by discarding a non-negative quantity.

### 5.5. The period side

<a id="sec:period"></a>

The clause [(Div)](#eq:div) bounds $\mu(P)$ from above. Three things enter.

*A determinant.* The $m$-fold lift is a composite of $m$ single lifts $\theta_1,\dots,\theta_m$ through auxiliary spaces. A general inequality about Hermitian lattices over a CM field (`BoundsMu`) takes as its hypothesis a factorisation of determinants at every archimedean place, of the shape $\det(\text{composite})=\kappa^{D}\prod_j\det(\theta_j)$, and bounds the slope of $P$ in terms of the slopes of $m$ auxiliary lattices $M'_1,\dots,M'_m$, one for each lift. The scalars are bounded below by a theorem (`lamLow_of_hypotheses_alt_alt`) whose hypotheses are seven statements of the literature, each proved in the archive: rapid decay of cusp forms, the Siegel--Weil formula for unitary groups in two forms ([Weil 1965](#ref-weil1965formule); [Ichino 2004](#ref-ichino2004regularized), [2007](#ref-ichino2007siegel)), the basic identity of the doubling method ([Piatetski-Shapiro and Rallis 1987](#ref-piatetskishapiro1987lfunctions)) with the continuation of the Siegel Eisenstein series (under a name that refers to the local zeta integrals; see [10](#sec:literature)), the unramified computation of the local doubling integral, a finiteness theorem of Bernstein and Zelevinsky, and Harish-Chandra's formula for the formal degree of a discrete series representation of a unitary group. The identities have the shape of the Rallis inner product formula ([Rallis 1984](#ref-rallis1984injectivity)).

*A ledger.* The clause [(Div)](#eq:div) is assembled from one inequality per lift $j$ and place $\rho$ (`divisor_inequality_assembly`): a covolume term $w_j(\rho)\log\Omega$, plus a kernel term $\operatorname{ph}(\nu)$, minus an eigenvalue term and minus $\nu\log\Omega$, is at most $\operatorname{ph}(a_\rho)-a_\rho\log\Omega$ if $\rho$ is a top place and $0$ otherwise, up to errors. Here $\operatorname{ph}(\nu)\approx\log\nu!$ and $\Omega$ is a period. Summed over the $m$ lifts and all places, and with $-a_t\log T$ from the last map, this is $m\sum_t\bigl(\operatorname{ph}(a_t)-a_t\log\Omega\bigr)-\sum_ta_t\log T$, the right side of [(Div)](#eq:div). Every factorial but the top one has cancelled against an eigenvalue, and every $\log\Omega$ but the top one against a covolume.

*Arithmetic geometry.* The covolume of the auxiliary lattices is an input of a different kind, and a large one. $M'_j$ is a lattice of integral forms on a moduli space attached to an *indefinite* unitary group, integrality meaning non-negative valuation at every point over every finite place (`cuspA`). Its covolume is bounded through a chain of slope comparisons (`lcv_le`): the covolume is at most minus the slope of a "good" sublattice cut out by an orthogonal idempotent; the complementary "bad" part has rank share at most $3\exp(-x^{\varepsilon_z/7})$, with $\varepsilon_z$ an exponent of the scale; the slope of the lattice of that type is at least a core slope less a small error; and the core slope is at least minus a main term, which is within a small error of $(p'-q')\sum_\tau\mathrm{anchor}_\tau\,\log\Omega$, with two integers $p'$, $q'$ of the datum of the indefinite group and a sum over an index $\tau$ of that datum. The theorem that assembles this (`topCovolSlim2_use_alt_alt`) has fifteen hypotheses. Among them are resolution of singularities and principalisation in characteristic zero ([Hironaka 1964a](#ref-hironaka1964resolution)), an arithmetic Hilbert--Samuel statement ([Gillet and Soulé 1992](#ref-gillet1992arithmetic); [Zhang 1995](#ref-zhang1995positive); [Abbes and Bouche 1995](#ref-abbes1995theoreme)), a bigness statement of Moriwaki, toroidal compactifications ([Faltings and Chai 1990](#ref-faltings1990degeneration); [Lan 2013](#ref-lan2013arithmetic)), Riemann--Roch for nef bundles, semi-negativity of the Lie algebra of a semi-abelian scheme, Zarhin's trick, a statement of Fargues, and Grothendieck's deformation theory; one hypothesis is a bundle of twenty-eight further statements, among them heights of Chow forms and the vanishing theorems of Kawamata--Viehweg and Nadel. So the slope argument is not lattice theory and automorphic forms alone: it rests on arithmetic intersection theory on a Shimura variety. Each of these statements is proved inside the archive.

*The period.* $\Omega$ is a CM period. What the argument needs is its mean, and here the archive proves the Chowla--Selberg formula ([Chowla and Selberg 1949](#ref-chowla1949epstein); [Selberg and Chowla 1967](#ref-selberg1967epstein)) in the form (`chowla_selberg_eta`) <a id="eq:cs"></a> $$\begin{equation}
\tag{5.3}
\frac1{h_K}\sum_{c\in\mathrm{Cl}(K)}\log\bigl(4\pi\,\operatorname{Im}\tau_c\,\lvert \eta(\tau_c)\rvert^4\bigr)
=\gamma+\log\frac{2\pi}{\sqrt d}-\frac{L'}{L}(1,\chi_d),
\end{equation}$$ for an imaginary quadratic field $K$ of discriminant $-d$ with $d>4$ and its quadratic character $\chi_d$, from the factorisation $\zeta_K=\zeta\cdot L(\cdot,\chi_d)$ and Kronecker's first limit formula ([Siegel 1980](#ref-siegel1980advanced)), which is also proved there . This is how $\tfrac{L'}{L}(1,\chi_\Phi)$ enters [(4.4)](#eq:main).

*The count for $T$.* The dimension of the space of forms is known exactly: the number of classes is a mass times an index times $(T^k-1)^f$ (`ClassNumberFormula₂`). A lower bound for $\log T(u)$ is the clause (`Count5`), $$\sum_{j=1}^m\frac1f\sum_{\rho}\log\frac{w_j(\rho)\,v}{\pi}+m\,\ell_g-c\Bigl(L_a+\frac{m^2L_a}{k}\Bigr)\ \le\ \log T(u),$$ where $f=\lvert \Phi\rvert$, the numbers $v$ and $\ell_g$ are constants of the data, $L_a$ is a logarithmic size parameter and $c$ a constant of the record.

<a id="st:key"></a>


**Statement 5.2** (`key_identity5`). With the notation above, the sum $m\sum_t\bigl(\operatorname{ph}(a_t)-a_t\log\Omega\bigr)$ on the right of [(Div)](#eq:div), less $\sum_ta_t$ times the lower bound for $\log T$ just displayed, plus $m\,\ell_g\sum_ta_t$, equals $$\mathrm{MAIN}(u_0)\;+\;\Bigl(\sum_ta_t\Bigr)\,c\,\Bigl(L_a+\frac{m^2L_a}{k}\Bigr).$$



The $\log(\pi/v)$ inside $\log\Omega$ cancels the $\log(v/\pi)$ of the count. There is no discrepancy term: the lattice side returns the analytic main term [(4.4)](#eq:main) identically. What is left is the term $m\,\ell_g\sum_ta_t$, which the clause `EComp5` sets against $\mathrm{Ee}(u)$ ([5.2](#sec:cast)), and an error of the shape of the first term of the bracket of [4.4](#sec:balance), with the same factor $1+m^2/k$.

### Chaining

From [(Loss)](#eq:loss), [(Gain)](#eq:gain), [(Slope)](#eq:slope), [(Div)](#eq:div) and [Statement 5.2](#st:key), with the four clauses that bound $\mu(M_u)$, the variation of $h(u)$, $\log T(u)$ and the difference between $\mathrm{Ee}(u)$ and $m\,\ell_g\sum_ta_t$, for every translate $u_0$, $$\mathrm{ASK}(u_0)\ \le\ \mathrm{MAIN}(u_0)+\mathrm{Err},$$ where $\mathrm{ASK}(u_0)$ is the sum over $t\in TT$ and $j\le m$ of the counts [(4.3)](#eq:ask) with the weights $w_{u_0,j}$, and $\mathrm{MAIN}(u_0)$ the corresponding sum of main terms. This is what [4.3](#sec:reduction) needs. The archive proves it as `each_unit_bound_statement` , for every translate and not only on average.

## 6. Divisibility at inert primes

<a id="sec:divisibility"></a>

The gains of [5.2](#sec:cast) are paid for by one phenomenon: Taylor coefficients of theta functions at a CM point are highly divisible at primes inert in the CM field. The note states it as: a coefficient of order $a$, divided by $\Omega^a$, is divisible by $p^{a/p+a/p^3+\cdots-O(\log a)}$. In this section $\ell$ is such a prime and $$\gamma_\ell=\frac{\ell}{\ell^2-1}=\frac1\ell+\frac1{\ell^3}+\frac1{\ell^5}+\cdots,\qquad
\rho_\ell=\frac1{\ell^2-1}.$$

### The mechanism

Let $F$ be the formal group over $\mathbb{Z}_\ell$ whose logarithm is (`ltLog`) $$\log_F(X)=\sum_{j\ge0}\frac{X^{\ell^{2j}}}{\ell^{j}},$$ a Lubin--Tate formal group of height two ([Lubin and Tate 1965](#ref-lubin1965formal); [Honda 1970](#ref-honda1970theory)). Its exponential has $r$-th coefficient of valuation at least $-\rho_\ell(r-1)$ (`LemmaSt`). Hence if $\vartheta$ is a power series with $\ell$-integral coefficients in $X$ and we expand it in the variable $z=\upsilon\log_F(X)$ with $\upsilon$ a unit, the $r$-th Taylor coefficient of $\vartheta$ in $z$, multiplied by $r!$, has valuation at least $$v_\ell(r!)-\rho_\ell\,r\ \ge\ \frac{r}{\ell-1}-\frac{r}{\ell^2-1}-(\log_\ell r+1)
\ =\ \gamma_\ell\,r-(\log_\ell r+1).$$ That is the whole reason for the exponent $a/\ell+a/\ell^3+\cdots$: derivatives in the logarithmic coordinate of a height-two formal group gain a factor $\ell^{\gamma_\ell}$ per order. The archive's general form (`LemmaRA`) bounds, for a function $U(\mathsf g(z))\exp(\pm\mathsf b(z))$ in several variables, the valuation of a derivative of multi-order $\kappa$ by $\sum_i\kappa_i(\gamma_\ell-\varsigma_i)$ less a logarithmic loss, with weights $\varsigma_i\ge0$, and a second theorem treats several "letters" at once, where the top terms take the form $\sum_{e\text{ odd}}\nu/\ell^e$ cut off by a capacity: the same shape as the count [(4.3)](#eq:ask). Both are on the path of the final theorem . The exponential factor is of the kind that Dwork introduced ([Dwork 1960](#ref-dwork1960rationality)).

### Why the function is integral: complex multiplication

A CM elliptic curve really is used; the argument is not carried out with power series alone.

<a id="st:cm2"></a>


**Statement 6.1** (`CM2`). Let $d$ be squarefree with $d\equiv3\pmod4$ and let $L$ be a lattice with complex multiplication by $\mathbb{Z}[(1+\sqrt{-d})/2]$. For every prime $\ell\ge5$ not dividing $d$ and every isomorphism $\iota\colon\mathbb{C}\cong\mathbb{C}_\ell$ there is $\xi\ne0$ such that $\xi^4\iota g_2(L)$ and $\xi^6\iota g_3(L)$ are integral in the maximal unramified extension of $\mathbb{Q}_\ell$ and the discriminant of the resulting Weierstrass equation is a unit.


<a id="st:cm3"></a>


**Statement 6.2** (`CM3`). In the situation of [Statement 6.1](#st:cm2), suppose moreover that $-d$ is not a square modulo $\ell$. Then there is a unit $\upsilon$ of the maximal unramified extension of $\mathbb{Q}_\ell$ such that the local series of the curve, composed with $\upsilon\log_F$, has integral coefficients in that extension.



[Statement 6.1](#st:cm2) is good reduction ([Serre and Tate 1968](#ref-serre1968good)); the archive derives it from global Artin reciprocity (`cmGoodModel_of_globalArtinReciprocity`), which it also proves. [Statement 6.2](#st:cm3) says that at an inert prime the formal group of the curve is the height-two group $F$, so that the complex uniformising coordinate $z$ is a unit times $\log_F$ of an integral parameter. The reduction is supersingular by Deuring's criterion ([Deuring 1941](#ref-deuring1941typen)), and a formal group of height two with this action of the ring of integers is the Lubin--Tate group $F$ up to isomorphism ([Lubin and Tate 1965](#ref-lubin1965formal); [Honda 1970](#ref-honda1970theory)).

From these the archive proves, for every prime $\ell\ge5$ with $\bigl(\tfrac{-d}{\ell}\bigr)=-1$ and every embedding of $\overline{\mathbb{Q}}$ into $\mathbb{C}_\ell$, that the kernel of the theta lift attached to a pair of admitted lattices is integral (`IntInert`). A *jet* is the value at the origin of a differential operator applied to the Taylor series of the kernel; the periods of [5.3](#sec:adm) are expressed through jets, and that is how the divisibility reaches them.

The jet theorem itself is applied to an arbitrary series satisfying the integrality hypothesis (`prvF_of_orbitLetterBounds`); the work is in showing that the actual kernel satisfies it. The letters of the general theorem index the positions along an orbit of Frobenius at $\ell$ acting on the embeddings of the CM field.

### Integrality of the periods

The periods themselves, for forms on the definite group, are finite sums over the classes of a genus. Their integrality rests on a statement about representations of general linear groups (`standard_weyl_lattices_fock_dual`): the integral forms of the Weyl module and of the dual Weyl module are exact duals of each other under the pairing of the polynomial (Fock) model; compare ([Carter and Lusztig 1974](#ref-carter1974modular)). Denominators coming from orders of finite groups are controlled by Minkowski's theorem ([Minkowski 1887](#ref-minkowski1887theorie)), in the form (`minkowski_bound_rat`): the order of a finite subgroup of $\mathrm{GL}_N(\mathbb{Q})$ divides an explicit integer depending on $N$ alone.

## 7. The frame: Bessel--Poincaré series

<a id="sec:frame"></a>

[Statement 5.1](#st:F) needs the period maps $B_u$ to form a nearly tight frame. The clause that supplies this is (`InputSG`): for matrices $B_i$ with a common target of dimension $\lvert \alpha\rvert$, weights $\gamma_i$, and the normalised Gram blocks $\Gamma_{ij}=(\gamma_i\gamma_j)^{1/2}B_i^*B_j$, $$\begin{align*}
\lVert \Gamma_{ij}\rVert_{\mathrm{HS}}^2&\le(1+\eta_0)\,\frac{d_i\,d_j}{D^*}\quad(i\ne j),&
\lVert \Gamma_{ii}-1\rVert_{\mathrm{HS}}^2&\le e_0\,d_i,&
\lvert \alpha\rvert&\le(1+\eta_1)\,D^*,
\end{align*}$$ where $d_i$ is the rank of the $i$-th source. Each map is nearly an isometry, and two different maps overlap no more than two independent random subspaces of dimensions $d_i$, $d_j$ in a space of dimension $D^*$ would. This is a nearly *tight* frame and not a nearly orthonormal family: tightness comes from there being many indices, with $\sum_id_i$ far larger than $D^*$. Passing from these three bounds to the hypotheses of [Statement 5.1](#st:F) is linear algebra.

### The maps

The forms live on a definite unitary group $\mathbf H=\mathrm{U}(W_0)$ of rank $k$ over the host field; in the application $k$ is the rank parameter of [4.4](#sec:balance). The common target is a space of automorphic forms on an *indefinite* unitary group $\mathbf G=\mathrm{U}(V)$, of signature $(k+r,\,r+1)$ at each infinite place, with a fixed discrete-series type at infinity. The two are related by a Bessel subgroup $\mathbf N\rtimes\mathbf H\subset\mathbf G$, attached to an isotropic flag and a vector of norm $-T(u)$: this is the setting of the Gan--Gross--Prasad conjectures ([Gan et al. 2012](#ref-gan2012symplectic)). The map $\mathcal P_u$ sends a form on $\mathbf H$ of archimedean type $\pi_u$ to the Poincaré series on $\mathbf G$ built from the Bessel function of the discrete series, and up to unitary changes of basis and a non-zero scalar the period map $B_u$ is a compression of $\mathcal P_u$.

### A relative trace formula

The pairing $\langle\mathcal P_u\phi,\mathcal P_{u'}\phi'\rangle$ is expanded as a convergent sum of operators indexed by integral double cosets, each an archimedean orbital integral (`KExpansion`); the terms that are not *relevant* vanish. The three bounds are read off this sum.

- *The identity term.* For a term whose representative lies in the unipotent group $\mathbf N$, the operator is a scalar (`oot_eq`): a character value times $\mathrm{vol}(\mathbf N\text{-domain})\cdot\mathrm{vol}(\mathbf H)/\dim\pi_u$. The normalisation of the maps makes this $1$.

- *Different indices.* If the archimedean parameters of $u$ and $u'$ differ at every place, then for a relevant degenerate term every intertwining operator between the two representations vanishes (`SchurNFC`); so such terms contribute nothing off the diagonal.

- *Uniqueness of Bessel models.* At the archimedean place, in a range where the parameters are separated by a gap of at least $120\,(2r+k+1)^3$, any two Bessel maps from a discrete series of $\mathrm{U}(k+r,r+1)$ to $\pi_u$ are proportional on smooth vectors (`UniqGap`); compare ([Sun and Zhu 2012](#ref-sun2012multiplicity); [Jiang et al. 2010](#ref-jiang2010uniqueness)).

- *The Siegel--Weil formula* is used in its convergent range, for frames of fewer vectors than half the dimension of the Hermitian space, and as a mass formula (`SiegelDensities`): the mean over $[\mathrm{U}(V)]$ of the theta series of frames with a given non-degenerate Gram matrix is the product of the local densities. The main term of the off-diagonal blocks is derived from it and from the uniqueness of Bessel models (`rowMainEqP_of_siegelWeil`).

The outcome for two different indices is (`pbApplied`): for $k$ large, if the rows of the expansion that are large or not scalar contribute at most $\exp(-c\,kf\log k)$ times the main term, and the non-generic rows at most $2^{-(k-2r-5)}\exp\bigl(C(2r+2)^5f\log b\bigr)$ times it, then $$\lVert \Gamma_{uu'}\rVert^2\ \le\ \bigl(1+b^{-6}\bigr)\,\frac{d_u\,d_{u'}}{D^*}.$$ Here $f=\lvert \Phi\rvert$ is the number of infinite places of the host. The decay is driven by the rank $k$.

Every ingredient is standard: unfolding as in the Petersson formula, Schur orthogonality, decay of matrix coefficients, uniqueness of Bessel models, Siegel--Weil as a mass formula, lattice-point counting. What appears to be new is the uniformity: the bound holds for the whole family of archimedean types at once, with every off-diagonal block within a factor $1+b^{-6}$ of the random-subspace value.

The abstract maps to which [Statement 5.1](#st:F) is applied are these period maps, up to linear isometries and a non-zero scalar (`BesselId`).

## 8. The cohomological bound

<a id="sec:cohomology"></a>

Item 17 of the note's timeline claims "a significant weakening of Vandiver" as a by-product. This section says what the formal statement is, where the slope argument uses it, and how it is proved.

### The statement

Let $E$ be a number field, $\ell$ a prime, and $e\ge1$. Let $\Sigma$ be the set of places of $E$ above $\ell$ and $\infty$, and $G_\Sigma$ the Galois group of the maximal extension of $E$ unramified outside $\Sigma$. Define $$\mathrm{Sha}(E,\ell,e)=\ker\Bigl(H^1\bigl(G_\Sigma,\mathbb{Q}_\ell/\mathbb{Z}_\ell(-e)\bigr)\longrightarrow
\prod_{v\mid\ell}H^1\bigl(E_v,\mathbb{Q}_\ell/\mathbb{Z}_\ell(-e)\bigr)\Bigr),$$ the classes that are locally trivial above $\ell$, and let $\operatorname{len}_\ell(e)$ be its length. By duality this is governed by $H^2(G_\Sigma,\mathbb{Z}_\ell(e+1))$, and hence, through Soulé's Chern class maps ([Soulé 1979](#ref-soule1979ktheorie)), by the even $K$-groups $K_{2e}(\mathcal{O}_E)\otimes\mathbb{Z}_\ell$. For $E=\mathbb{Q}$ the vanishing of $K_{4i}(\mathbb{Z})\otimes\mathbb{Z}_\ell$ for all $i$ is equivalent to Vandiver's conjecture at $\ell$ ([Kurihara 1992](#ref-kurihara1992remarks)); over $\mathbb{Q}(\mu_\ell)$ the conjecture concerns the eigenspaces of one parity ([Washington 1997](#ref-washington1997introduction)).

<a id="st:vwin"></a>


**Statement 8.1** (`VVle`, `VWin`). For the host field $E$ at scale $x$, with $t_0=\lfloor x^{401}\rfloor$ twists, every $\operatorname{len}_\ell(e)$ with $1\le e<t_0$ is finite and $$\sum_{\ell}\log\ell\sum_{1\le e<t_0}\operatorname{len}_\ell(e)\ \le\ \sqrt{b},\qquad b=\exp(x^{\varepsilon}),$$ for all $x$ in a window $[Y_1,Y_1^2]$; there is $J\ge1$ such that for every large $X$ such a window lies in $[X^{1/J},X]$.



Nothing is averaged or discarded: every prime $\ell$ and every twist is bounded. The statement is far from Vandiver's conjecture, which would make part of these groups vanish for $\mathbb{Q}(\mu_\ell)$; it says that the total size of these groups, for a field of degree about $x^2$ and conductor exponential in a power of $x$, is at most exponential in a small power of $x$.

### Where it is used

The bound has a single use . The record of [5.2](#sec:cast) carries, for each lift level $j$, a quantity $\eta_j$: the normalised logarithm of the index of a sublattice $\mathrm{cut}_j$ in a lattice $\mathcal T_j$, summed over the places above the level primes. The clause `LinkN_at` bounds it by a size term plus the total of [Statement 8.1](#st:vwin), $$\eta_j\ \le\ d_j\Bigl(C\bigl(fmb\,L_x^2+(\log x)^2N_c\bigr)+\sum_\ell\log\ell\sum_{1\le e<t_0}\operatorname{len}_\ell(e)\Bigr),$$ where $d_j$ is a rank attached to the level, $L_x$ a logarithmic size parameter of the scale, and $B_0$, $N_c$ are the quantities that the second and third terms of the bracket of [4.4](#sec:balance) bound (`BNBounds`). The consumer needs only $\eta_j\le D_0\,C\,x^{\varepsilon}(B_0+N_c)$ with $B_0=fmb\,x^\varepsilon$. The  lemma that passes from one to the other (`divinN_of_hypV`) weakens $\sqrt b$ to $b$ at once. *So the slope argument needs from [Statement 8.1](#st:vwin) only that the total is at most $\exp(x^{\varepsilon})$*; the square root is slack. The Sha lengths in the record are the true ones:  they are tied to the Galois-cohomological definition by a field of the base data (`vvRecord`). In the source the weakened bound is used in one place besides its producer (`inEta_num`).

What it controls is a congruence module . At each place $\lambda$ above a prime $\ell$ the record has a local Hecke algebra $\mathbf T$, in spectral form: a subalgebra of the functions from a  finite set $\mathcal X$ of eigensystems to a discrete valuation ring $\mathcal{O}$. A subset $\mathcal Z\subset\mathcal X$ consists of the eigensystems that have an automorphic point whose parameter contains a block  of length $t_0$ (`ZN`); these are the lifts. The *congruence ideal* is the kernel of  $\mathbf T\to\prod_{y\notin\mathcal Z}\mathcal{O}$ (`ccIdeal`), and the local part of $\eta_j$ is the length of the corresponding congruence module, $V_{\mathcal Z}\cap(\mathcal M+V_{\mathcal Z^c})$ modulo $\mathcal M\cap V_{\mathcal Z}$ for the lattice $\mathcal M$ of forms (`etaLoc`).

<a id="st:cong"></a>


**Statement 8.2** (`CongBound_at`). Let $\ell$ be large, not exceptional, and different from the two auxiliary level primes of the host; assume two further conditions that we do not reproduce (`WeightTie`, `HG`), and let the Galois representations of the forms be given over the ring of coefficients by a family satisfying a third (`GoodR`). Let $\pi\in\mathcal Z$, and suppose that the Galois representation of $\pi$ is, over the fraction field, the sum of a representation $\rho$ and the $t_0$ characters $\chi_1,\dots,\chi_{t_0}$. Then the valuation at $\pi$ of the congruence ideal is at most $$\operatorname{len}\,\mathrm{Sel}(\rho)\;+\;\sum_{0<e<t_0}\operatorname{len}_\ell(e)\;+\;v_\ell(h_E)\;+\;t_0\sum_{\mathfrak q\in\mathcal Q}v(\zeta_{\mathfrak q}-1),$$ where $\mathrm{Sel}(\rho)$ is a Selmer group attached to $\rho$, $h_E$ is the class number of the host field and $\mathcal Q$ is a finite set of auxiliary primes.



This is a bound of the type of Ribet's lemma ([Ribet 1976](#ref-ribet1976modular)): a congruence between a lift and a form that is not a lift produces a cocycle, and cocycles are counted by Selmer groups, by the groups $\mathrm{Sha}(E,\ell,e)$ and by the class group. The twists $1\le e\le t_0-1$ are those of the block: in the source the characters are $\chi_c=\chi_1\,\chi_{\mathrm{cyc}}^{-(c-1)}$, with $\chi_{\mathrm{cyc}}$ the cyclotomic character.

This step uses Galois representations attached to every eigensystem, lifted or not. They are supplied by a theorem of the archive ([8.4](#sec:galois)).

### How it is proved

 One theorem assembles [Statement 8.1](#st:vwin) (`of_four_alt`). Its hypotheses are a record of statements from the literature, the crude bound `LemmaK` below, and four counting statements (`CountI`, `CountII`, `CountIII`, `CountV`), each of which bounds the contribution of one class of pairs $(\ell,e)$; its proof calls, besides these, the theorem of Ferrero and Washington and the bound for the odd part.

*The odd part.* For a character $\psi$ of $\operatorname{Gal}(E/\mathbb{Q})$ whose value at complex conjugation is $(-1)^{e+1}$, the length of the $\psi$-eigenspace of the group with twist $e$ is at most the valuation of an explicit number attached to $\psi$ and $e$ (`PsiBound`). This is proved by a theorem (`ML.iv`) whose hypotheses are Poitou--Tate duality and an orthogonality statement for unramified classes. The archive's proof contains a step of Kolyvagin's derivative construction (`kolStep`); compare ([Kolyvagin 1990](#ref-kolyvagin1990euler); [Rubin 2000](#ref-rubin2000euler)). The eigenspaces of the other parity are the side on which Vandiver's conjecture bears.

*Cyclotomic towers.* The theorem of Ferrero and Washington ([Ferrero and Washington 1979](#ref-ferrero1979iwasawa)) that $\mu=0$ is proved in the archive, by Sinnott's method ([Sinnott 1984](#ref-sinnott1984mu)) (`sinnott`); compare ([Iwasawa 1973](#ref-iwasawa1973extensions)). The twists it does not reach are bounded crudely (`LemmaK`): for a totally complex field $F\supset\mu_\ell$ and every $e\ge1$, the group $H^2(G_\Sigma,\mathbb{Z}_\ell(e+1))$ of $F$ is finite and the logarithm of its order is at most an explicit function of $e$, $[F:\mathbb{Q}]$ and $\lvert d_F\rvert$; compare ([Soulé 1979](#ref-soule1979ktheorie); [Borel 1974](#ref-borel1974stable)).

*One integer for all $\ell$.* For $\mathrm{U}(3)$ over an imaginary quadratic field there is a statement of the following shape (`NumberU3U_s`): for $K$ imaginary quadratic there are constants $c,A$ such that for every twist $e$, level $N$, prime $p\ge7$ not dividing $N\,d_K$ and finite Galois-stable family $(z_o)_{o\in O}$ of roots of unity, there is a non-zero integer $NN$ with $$\log\lvert NN\rvert\le c\cdot\lvert O\rvert\cdot\bigl(N(e+1)\bigr)^A\log p$$ such that, for every $\ell\ne2,p$ and all finite sets $X_o$, one for each $o\in O$, of pairwise non-isomorphic admissible Galois representations of that weight and level, $$\lvert NN\rvert_\ell\ \le\ \prod_{o\in O}\ \prod_{\rho\in X_o}\bigl|\operatorname{tr}\rho(\mathrm{Fr}_\lambda^{-1})-\mathrm{eis}(z_o)\bigr|_\ell,
\qquad \mathrm{eis}(z)=(\mathrm N\lambda)^{-e}z+1+(\mathrm N\lambda)^{e}z^{-1},$$ at a Frobenius element $\mathrm{Fr}_\lambda$ at a place $\lambda$ above $p$, with every factor non-zero. Here $\mathrm{eis}(z)$ is the trace at $\mathrm{Fr}_\lambda$ of a reducible representation $\Psi\oplus1\oplus\Psi^{-1}$, so $NN$ is a congruence number between cusp forms and an Eisenstein class. Summing $\log\ell$ times the valuations over all $\ell$ therefore costs only $\log\lvert NN\rvert$.

*From the integer to Sha.* A companion statement (`OneCharU_s`) bounds the length in question by $2\sum_{\rho}v_\ell\bigl(\operatorname{tr}\rho(\mathrm{Fr})-t_\Psi\bigr)$ over such a set of representations, for an element $\mathrm{Fr}$ of the Galois group and $t_\Psi=\Psi(\mathrm{Fr})+1+\Psi(\mathrm{Fr})^{-1}$, provided no admissible $\rho$ has trace exactly $t_\Psi$. Behind it is a lemma of commutative algebra (`LemmaM`) about a graded complete local algebra with an augmentation: under five conditions, the length of the weight $-1$ part of its cotangent space is at most $2\sum_\xi v(\xi(a))$ over a finite covering set of points. This is the pattern in which an Eisenstein congruence bounds a Selmer group, as in the work of Ribet ([Ribet 1976](#ref-ribet1976modular)), Mazur and Wiles ([Mazur and Wiles 1984](#ref-mazur1984class)) and Skinner and Urban ([Skinner and Urban 2014](#ref-skinner2014iwasawa)). Two further theorems that the archive proves for this purpose are on the path of the final theorem : one on Hida families for unitary groups (`hida_unitary_of_printed_hida`; compare ([Hida 1986](#ref-hida1986galois))), and Kato's Euler system ([Kato 2004](#ref-kato2004padic)) (`zetaUr`); compare ([Bloch and Kato 1990](#ref-bloch1990lfunctions)).

No statement of the main conjecture of Iwasawa theory appears among the results the archive takes from the literature ([10](#sec:literature)).

### 8.4. Galois representations from theta lifts

<a id="sec:galois"></a>

The representations needed above are supplied by one theorem of the archive (`galoisRepresentations_of_thetaLift`): for a CM field $E$, a prime $\ell$ and a regular algebraic, polarised, cuspidal automorphic representation $\pi$ of $\mathrm{GL}_\nu$ over $E$ there is a continuous semisimple $\ell$-adic representation of $\operatorname{Gal}(\overline E/E)$ with the Hodge--Tate weights prescribed by $\pi$ and with stated properties at the places above $\ell$. In the literature this is the work of Clozel, Harris--Taylor, Shin and Chenevier--Harris ([Clozel 1991](#ref-clozel1991representations); [Harris and Taylor 2001](#ref-harris2001geometry); [Shin 2011](#ref-shin2011galois); [Chenevier and Harris 2013](#ref-chenevier2013construction)). Two features of the formal version should be recorded.

First, its compatibility with $\pi$ away from $\ell$ is partial (`AwayB`): the dimensions agree; the parameters are equal when $\pi$'s is a sum of characters with trivial monodromy; and for tame, square-free parameters with trivial monodromy at places with completion $\mathbb{Q}_p$, where $p>16\nu^2$ unless $\nu=1$, the characteristic polynomials on inertia agree. This is less than the theorem of Caraiani ([Caraiani 2012](#ref-caraiani2012local)).

Second, the theorem has a single hypothesis, which the archive proves (`TLiftK`, proved as `tLiftK`): theta lifts exist between *definite* unitary groups. Precisely, for a Hermitian space of rank $n_1$ and a skew-Hermitian space of rank $n_2\ge n_0$ over $E$, both definite, and an automorphic representation of $\mathrm{U}(n_1)$ whose weights satisfy an inequality against $n_2$, there is a lift to $\mathrm{U}(n_2)$; compare the work of J.-S. Li ([Li 1992](#ref-li1992nonvanishing)). Neither an eigenvariety nor a stable trace formula appears in the statement.

## 9. Hosts and the auxiliary characters

<a id="sec:hosts"></a>

### The host field

Given a primitive character $\psi$, an integer $e_2$ and two primes $q$ and $d$, a *host* is a field $E$ of the following kind (`IsChiField`): $E$ embeds in a cyclotomic field $\mathbb{Q}(\zeta_N)$ with $2^{e_2+2}$, the conductor of $\psi$, $q$ and $d$ all dividing $N$, and the automorphism $\zeta_N\mapsto\zeta_N^{r}$ fixes $E$ exactly when $$r\equiv\pm1\pmod{2^{e_2+2}},\qquad \psi(r)=1,\qquad \Bigl(\frac rq\Bigr)=1,\qquad
\Bigl(\frac rd\Bigr)=1 .$$ So the Galois group of $E$ is the product of a group of order four, coming from $q$ and $d$, and a group $H$ built from a layer of the cyclotomic $\mathbb{Z}_2$-tower and from $\psi$. It is the  field to which [Statement 8.1](#st:vwin) applies. The host contains $\sqrt{-d}$, and $\Phi$ is the subgroup that fixes it (`HostRaw`); so the CM field of [5.5](#sec:period) and [6](#sec:divisibility) is $\mathbb{Q}(\sqrt{-d})$, and $\chi_\Phi$ is its quadratic character.

The sizes are fixed by two parameters (`WinPair`, `PageN`): a parameter $Y$, which is constant on a window of scales, and the scale $x$ itself. The prime $q$ satisfies $q\equiv3\pmod8$ and $\tfrac12Y^{\varepsilon/5}<\log q\le Y^{\varepsilon/5}$; the prime $d$ satisfies $d\equiv7\pmod{16}$ and $\log d\approx Y^{\varepsilon/5}(\log Y)^2$, and $d+1$ is divisible by $q$ and by every odd prime up to $Y^{\varepsilon/5}$; and $2^{e_2}$ lies between $x^{2+8\varepsilon}$ and $2x^{2+8\varepsilon}$. The scales of a window lie between $Y$ and a fixed power of $Y$, so the conductor of $E$ exceeds every power of $x$, while the degree of $E$ is a power of $x$.

### Supply

<a id="st:supply"></a>


**Statement 9.1** (`supplyChi`). For every primitive $\psi$, if the cohomological bound holds for $\psi$ with exponent $401$, then hosts with the required properties exist at every scale in a set containing windows of exponent $\tfrac32$.



 The only assumption about $\psi$ is its cohomological bound. The windows come from [Statement 8.1](#st:vwin), which holds on windows $[Y_1,Y_1^2]$; this is why [Statement 4.1](#st:landau) is needed in its windowed form.

### The auxiliary characters and the absence of a circle

The reduction of [4.3](#sec:reduction) assumed $\lvert G_\chi(x)\rvert\le x^{1/2+\varepsilon}$ at the point $x$ for the characters of the host that are not kept. They are the twists $\xi\cdot\bigl(\tfrac\cdot q\bigr)^i\bigl(\tfrac\cdot d\bigr)^j$ with $(i,j)\ne(0,0)$ of characters $\xi$ whose modulus is that of $\psi$. That looks like the statement being proved. It is supplied by the choice of the primes:

<a id="st:pairs"></a>


**Statement 9.2** (`PairEx`). For every modulus $M_0$, every $0<\varepsilon<\tfrac1{52}$ and every $A\ge1$, for all large $Y$ there are primes $q$ and $d$ of the sizes above, prime to $M_0$, such that for every character $\xi$ modulo $M_0$ and every $(i,j)\neq(0,0)$ the twist $\chi$ of $\xi$ satisfies $$\lvert G_\chi(y)\rvert\le y^{1/2+\varepsilon/2}\quad\text{and}\quad
\Bigl|\frac{L'}{L}(1,\chi)\Bigr|\le4\log y\qquad\text{for all } Y\le y\le Y^{A},$$ and such that the twists of the real characters of modulus dividing $8M_0$ have no zero with $\operatorname{Re}s>1-\tfrac1{400}$ up to a stated height.



There is no circle, for a reason of size: the conductors of the twists are at least $q>\exp(\tfrac12Y^{\varepsilon/5})$, far larger than any power of $y$, so the bound concerns sums much shorter than the conductor, and it is required only for one suitable pair $(q,d)$, not for a  given one. The archive proves the statement from a mean-square estimate over prime moduli (`meanSqK`) and a zero-density estimate (`zero_density_box`) for zeros with $\operatorname{Re}s>1-\tfrac1{400}$, in the tradition of Bombieri ([Bombieri 1965](#ref-bombieri1965large)); compare ([Siegel 1935b](#ref-siegel1935classenzahl); [Page 1935](#ref-page1935number)) for the exceptional real zero that the second clause excludes.

### Two combinatorial devices

The thick set of [4.3](#sec:reduction) is built from Behrend's construction ([Behrend 1946](#ref-behrend1946sets)), which the archive takes from Mathlib (`noRel_image`, `hostThickExists`). The property used is stronger than the absence of three-term progressions: for three distinct elements $s_1,s_2,s_3$ of the set and distinct non-zero integers $i,j$ of absolute value at most a given bound, one has $j(s_2-s_1)\ne i(s_3-s_1)$.

The statement $\mathsf{Green}$ of [3](#sec:overview) is : for every prime $p$ and every $\nu\ge1$, the cuspidal characters of $\mathrm{GL}_\nu(\mathbb{F}_p)$ are parametrised, without repetition, by the monic irreducible polynomials of degree $\nu$ with non-zero constant term, in a fixed labelling, and each has degree $\prod_{i=1}^{\nu-1}(p^i-1)$. This is part of Green's theorem ([Green 1955](#ref-green1955characters)).

## 10. The published theorems the proof rests on

<a id="sec:literature"></a>

The archive does not assume the literature; it formalises it. One file collects 186 theorems, each returning a named statement, and each is proved inside the archive. All of them are used by the final theorem ([11](#sec:offpath)). [Appendix C](#app:rows) lists them, with what each Lean statement asserts and its sources. This section describes the collection.

### What the file contains

Two statements are entered twice, so there are 184 distinct statements. One of them is the conclusion itself, non-vanishing of every Dirichlet $L$-function to the right of $\tfrac12$, returned under the hypothesis of [Statement 8.1](#st:vwin). One is an empty slot, the proposition `True`. Three are statements in the archive's own terms that correspond to no single published theorem. The remaining 179 are formal statements of published results. We compared each with the theorem its name refers to. The comparison rests on the Lean statement, which we read, and on the published theorem as we know it; we did not open the papers for it. [Appendix C](#app:rows) gives the reason for each verdict, so that each can be checked:

|  |  |
|:---|---:|
| The published theorem, in the generality of a cited source | 90 |
| A special case of it, or a weaker form, restricted to what the proof uses | 86 |
| Not a statement of the cited literature as it stands | 3 |

The restricted statements follow a pattern. Results on automorphic forms are stated for totally complex base fields or for unitary groups of CM extensions; results on real groups for $\mathrm{U}(p,q)$; results on $\mathrm{GL}_n$ over local fields in characteristic zero; theorems about reductive groups are stated for $\mathrm{GL}_n$, and depth-zero cases replace general ones; results on the characters of $\mathrm{GL}_n(\mathbb{F}_q)$ are stated for prime fields. The Galois representations attached to automorphic representations are stated with only part of the compatibility away from $\ell$ that the literature proves: equal dimension, equality when the local parameter is a sum of characters with trivial monodromy, and agreement on inertia for tame, square-free parameters at large primes. The three statements that differ are a global consequence of the local theorem of Gelfand and Kazhdan, a form of the rapid decay of cusp forms in Sobolev norms, and a statement named after the local zeta integrals of the doubling method that contains the global identity instead. The proof was evidently formalised to the extent it needs and no further. A reader who wants to use one of these formalisations elsewhere should read its statement first.

### By area

*Class field theory and Galois cohomology.* Global Artin reciprocity ([Takagi 1920](#ref-takagi1920theorie); [Artin 1927](#ref-artin1927beweis); [Chevalley 1940](#ref-chevalley1940theorie); [Tate 1967b](#ref-tate1967global)), ray class fields and characters, the Hasse norm theorem ([Hasse 1924](#ref-hasse1924darstellbarkeit), [1931](#ref-hasse1931beweis)), class field theory for quadratic extensions ([Hilbert 1899](#ref-hilbert1899theorie)), Chebotarev's theorem ([Tschebotareff 1926](#ref-chebotarev1926bestimmung)), a lemma of Chevalley on units ([Chevalley 1951](#ref-chevalley1951deux)); local and global Tate duality, the Euler characteristic formulas and Poitou--Tate duality ([Tate 1963](#ref-tate1963duality); [Poitou 1966](#ref-poitou1966remarques); [Milne 1986](#ref-milne1986arithmetic)), and the formula of Greenberg and Wiles ([Wiles 1995](#ref-wiles1995modular); [Darmon et al. 1995](#ref-darmon1995fermat)). Mathlib does not contain global class field theory; the archive proves it.

*Complex multiplication and Hecke characters.* The theory of the $j$-invariant and the main theorem of complex multiplication for imaginary quadratic fields ([Hasse 1927](#ref-hasse1927neue); [Shimura 1971](#ref-shimura1971introduction)); Hecke's $L$-functions and Tate's thesis ([Hecke 1918](#ref-hecke1918neue), [1920](#ref-hecke1920neue); [Tate 1967a](#ref-tate1967fourier)); the $\ell$-adic characters of algebraic Hecke characters and their $p$-adic Hodge theory ([Serre 1968](#ref-serre1968abelian)); the rationality theorem of Siegel and Klingen ([Klingen 1962](#ref-klingen1962werte); [Siegel 1969](#ref-siegel1969berechnung)) and the integrality theorem of Deligne and Ribet ([Deligne and Ribet 1980](#ref-deligne1980values); [Cassou-Noguès 1979](#ref-cassounogues1979valeurs)); curves with complex multiplication and minimal discriminant ([Gross 1980](#ref-gross1980arithmetic), [1982](#ref-gross1982minimal)).

*Representations of $p$-adic and finite groups.* The theory of Bernstein and Zelevinsky ([Bernstein and Zelevinsky 1976](#ref-bernstein1976representations), [1977](#ref-bernstein1977induced); [Zelevinsky 1980](#ref-zelevinsky1980induced)), Bernstein's irreducibility theorem ([Bernstein 1984](#ref-bernstein1984pinvariant)), the generic unitary dual ([Tadić 1986](#ref-tadic1986classification)), the Langlands classification ([Silberger 1978](#ref-silberger1978langlands)), Iwahori-fixed vectors ([Borel 1976](#ref-borel1976admissible); [Casselman 1980](#ref-casselman1980unramified)), depth zero ([Moy and Prasad 1994](#ref-moy1994unrefined), [1996](#ref-moy1996jacquet)), the local converse theorem ([Henniart 1993](#ref-henniart1993caracterisation)), the local Langlands correspondence for $\mathrm{GL}_n$ as a list of laws ([Harris and Taylor 2001](#ref-harris2001geometry); [Henniart 2000](#ref-henniart2000preuve); [Scholze 2013](#ref-scholze2013local)), the splitting of the metaplectic cover for unitary dual pairs ([Kudla 1994](#ref-kudla1994splitting)), and Green's cuspidal characters of $\mathrm{GL}_n(\mathbb{F}_p)$ ([Green 1955](#ref-green1955characters); [Gel'fand 1970](#ref-gelfand1970representations)).

*Representations of real groups.* Harish-Chandra's discrete series for $\mathrm{U}(p,q)$ with their lowest $K$-types and formal degrees ([Harish-Chandra 1965](#ref-harishchandra1965discrete), [1966](#ref-harishchandra1966discrete); [Schmid 1975](#ref-schmid1975some)), the theorem of Casselman and Wallach ([Casselman 1989](#ref-casselman1989canonical); [Wallach 1983](#ref-wallach1983asymptotic)), the factorisation theorem of Dixmier and Malliavin ([Dixmier and Malliavin 1978](#ref-dixmier1978factorisations)), Schur orthogonality for square-integrable representations ([Godement 1947a](#ref-godement1947orthogonalite)), Howe duality ([Howe 1989a](#ref-howe1989remarks), [1989b](#ref-howe1989transcending)), Weyl's branching rule ([Weyl 1946](#ref-weyl1946classical)), and the metaplectic representation ([Weil 1964](#ref-weil1964certains); [Shale 1962](#ref-shale1962linear)).

*Automorphic forms and Galois representations.* Finiteness and rapid decay of cusp forms ([Harish-Chandra 1968](#ref-harishchandra1968automorphic); [Gel'fand et al. 1969](#ref-gelfand1969representation); [Moeglin and Waldspurger 1994](#ref-moeglin1994decomposition)), reduction theory and strong approximation ([Borel and Harish-Chandra 1962](#ref-borel1962arithmetic); [Kneser 1965](#ref-kneser1965starke); [Platonov 1969](#ref-platonov1969problem)), the tensor product theorem ([Flath 1979](#ref-flath1979decomposition)), multiplicity one and the theorem of Jacquet and Shalika ([Shalika 1974](#ref-shalika1974multiplicity); [Piatetski-Shapiro 1979](#ref-piatetskishapiro1979multiplicity); [Jacquet and Shalika 1981b](#ref-jacquet1981eulerI), [1981a](#ref-jacquet1981eulerII)), purity and cohomologicality ([Clozel 1990](#ref-clozel1990motifs)), base change from unitary groups ([Labesse 2011](#ref-labesse2011changement)), and the Galois representations attached to polarised regular algebraic cuspidal representations ([Shin 2011](#ref-shin2011galois); [Chenevier and Harris 2013](#ref-chenevier2013construction); [Caraiani 2012](#ref-caraiani2012local)).

*The theta correspondence.* Weil's convergence criterion and the Siegel--Weil formula for unitary groups ([Weil 1965](#ref-weil1965formule); [Ichino 2007](#ref-ichino2007siegel); [Yamana 2011](#ref-yamana2011siegel); [Ikeda 1996](#ref-ikeda1996residue)), the mass formula ([Siegel 1935a](#ref-siegel1935analytische); [Braun 1941](#ref-braun1941theorie)), the doubling method ([Piatetski-Shapiro and Rallis 1987](#ref-piatetskishapiro1987lfunctions); [Gelbart et al. 1987](#ref-gelbart1987explicit)), the continuation of Eisenstein series ([Langlands 1976](#ref-langlands1976functional); [Bernstein and Lapid 2024](#ref-bernstein2024meromorphic)), and the Rallis inner product formula ([Rallis 1984](#ref-rallis1984injectivity); [Li 1992](#ref-li1992nonvanishing)).

*$p$-adic Hodge theory.* Fontaine's rings ([Fontaine 1982](#ref-fontaine1982certains), [1994a](#ref-fontaine1994corps), [1994c](#ref-fontaine1994semistables)), the $p$-adic monodromy theorem ([Berger 2002](#ref-berger2002representations); [André 2002](#ref-andre2002filtrations); [Mebkhout 2002](#ref-mebkhout2002analogue); [Kedlaya 2004](#ref-kedlaya2004padic)), the local theory of Bloch and Kato ([Bloch and Kato 1990](#ref-bloch1990lfunctions)), prismatic $F$-crystals and the prismatic Dieudonné functor ([Bhatt and Scholze 2023](#ref-bhatt2023prismatic); [Anschütz and Le Bras 2023](#ref-anschutz2023prismatic)), the deformation theory of Grothendieck and Messing ([Messing 1972](#ref-messing1972crystals); [Mazur and Messing 1974](#ref-mazur1974universal)), and Fargues's theorem on the Hodge--Tate map ([Fargues 2008](#ref-fargues2008isomorphisme); [Tate 1967c](#ref-tate1967pdivisible)).

*Algebraic and arithmetic geometry.* Resolution of singularities and principalisation ([Hironaka 1964a](#ref-hironaka1964resolution); [Kollár 2007](#ref-kollar2007lectures)), the vanishing theorems of Kawamata--Viehweg and Nadel ([Kawamata 1982](#ref-kawamata1982generalization); [Viehweg 1982](#ref-viehweg1982vanishing); [Nadel 1990](#ref-nadel1990multiplier)), the separation of points ([Angehrn and Siu 1995](#ref-angehrn1995effective)), extension with $L^2$ estimates ([Ohsawa and Takegoshi 1987](#ref-ohsawa1987extension); [Demailly 2016](#ref-demailly2016extension)), the numerical theory of nef bundles ([Kleiman 1966](#ref-kleiman1966toward); [Lazarsfeld 2004](#ref-lazarsfeld2004positivity)), the comparison of algebraic and analytic sections ([Serre 1956](#ref-serre1956geometrie)), formal algebraisation ([Grothendieck 1961](#ref-grothendieck1961elements)), abelian schemes and their duals ([Mumford 1965](#ref-mumford1965geometric); [Mumford 1970](#ref-mumford1970abelian)), semistable reduction ([Grothendieck et al. 1972](#ref-grothendieck1972groupes)), toroidal compactifications ([Ash et al. 1975](#ref-ash1975smooth); [Faltings and Chai 1990](#ref-faltings1990degeneration); [Lan 2013](#ref-lan2013arithmetic); [Pink 1989](#ref-pink1989arithmetical)), arithmetic intersection theory, the arithmetic Hilbert--Samuel theorem and arithmetic volumes ([Gillet and Soulé 1990](#ref-gillet1990arithmetic), [1992](#ref-gillet1992arithmetic); [Bost et al. 1994](#ref-bost1994heights); [Abbes and Bouche 1995](#ref-abbes1995theoreme); [Zhang 1995](#ref-zhang1995positive); [Moriwaki 2009](#ref-moriwaki2009continuity)), Chow forms ([Chow and Waerden 1937](#ref-chow1937algebraischen)), the Poincaré--Lelong formula ([Lelong 1957](#ref-lelong1957integration)), semi-negativity of Lie algebras ([Bost 2004](#ref-bost2004germs)), good metrics ([Mumford 1977](#ref-mumford1977hirzebruch)), and Zarhin's trick ([Zarhin 1977](#ref-zarhin1977endomorphisms)).

*Other.* Linnik's theorem on the least prime in a progression ([Linnik 1944a](#ref-linnik1944least1), [1944b](#ref-linnik1944least2)), an estimate for $L'/L(1,\chi)$ ([Davenport 1980](#ref-davenport1980multiplicative)), Brauer's induction theorem ([Brauer 1947](#ref-brauer1947artin)), Radford's theorem on shuffle algebras ([Radford 1979](#ref-radford1979natural)), a simplicity theorem for induced modules in characteristic $p$ ([Andersen 1980](#ref-andersen1980strong); [Jantzen 2003](#ref-jantzen2003representations)), the Hasse principle for Hermitian forms ([Landherr 1936](#ref-landherr1936aquivalenz); [Jacobowitz 1962](#ref-jacobowitz1962hermitian)), and the theorem of Stone and von Neumann ([Stone 1930](#ref-stone1930linear); [Neumann 1931](#ref-vonneumann1931eindeutigkeit)).

### What this means for the result

The certificate for the Riemann Hypothesis does not depend on any of these names being accurate: the kernel checked a closed term of type `RiemannHypothesis`, whatever its intermediate statements are called. But the archive's worth beyond that one theorem depends on them a great deal. If the formal statements are what [Appendix C](#app:rows) reports, the archive contains verified proofs of 179 published theorems, 90 of them in the generality of their sources. That is a second result, separable from the first, and each row can be checked independently against the published theorems it names.

## 11. What the final theorem does not use

<a id="sec:offpath"></a>

Nearly every file of the archive imports nearly every other, so the import graph says nothing about what depends on what. The statements of this section are instead computed from the compiled archive: the *cone* of `riemannHypothesis` is the set of all declarations reachable from it through the type and the value of every declaration reached, the link between an inductive type and its constructors, and the structure of a projection ([2.6](#sec:cone)). It has 1,478,220 declarations: 1,265,256 of the archive and

203,036 of Mathlib and 9,928 of Lean's library and the other packages.

The other four theorems of `Main.lean` are derived from the same statement for all characters, by short arguments of their own: the cone of all five has 1,478,244 declarations, 24 more.

<a id="tab:cone"></a>

|                                | in the archive | in the cone | share |
|:-------------------------------|---------------:|------------:|------:|
| Theorems                       |      1,548,656 |   1,075,015 |   69% |
| Definitions                    |        331,347 |     178,298 |   54% |
| Modules that declare something |        175,014 |     147,489 |   84% |

: The archive and the cone of `riemannHypothesis`, counted by distinct names. A module is counted in the cone if it declares at least one declaration of the cone. The definitions include 621 compiled forms of recursive definitions, none of them in the cone.

So about a third of the archive's theorems, 473,641 of them, are not used by the final theorem. They are compiled and checked by the kernel like the rest ([2](#sec:verification)); they are simply not on the path. Of the archive's 175,187 files, 27,698 declare nothing that is in the cone

. By top-level directory they number 22,037 of 141,928 in `Development`, 3,224 of 18,254 in `Formalism`, 1,814 of 8,507 in `GroundTheory`, 360 of 3,845 in `ReciprocityTheory`, 140 of 2,027 in `CompanionTheory`, 106 of 449 in `PositivityTheory`, and 17 in the four small directories that remain; these totals count every file, including the 173 that declare nothing at all.

What is unused includes earlier and parallel forms of steps that are on the path. Each of the following was confirmed outside the cone by its full name.

- *Conditional reductions.* Several statements of the form "if such data exist at every scale, then the Riemann Hypothesis holds":

  |  |  |
  |:---|:---|
  | `RiemannHypothesisOfLowerBounds` | `RiemannHypothesisOfHalfLinks` |
  | `WeightedSieveImpliesRH` | `WeightedSieveImpliesRHThreeParameter` |
  | `GrowthBoundGivesRiemannHypothesis` | `RiemannHypothesisOfBalanceAndGrowthData` |

  One more of this kind, `ZetaQuarterPowerCorollary`, takes the number of lifts $m\approx x^{1/4}$ and concludes only that $\zeta(s)\neq0$ for $\operatorname{Re}s>\tfrac34$.

- *A first form of the analytic half.* The identity of [Statement 4.2](#st:balance) and the reduction of [4.3](#sec:reduction) exist a second time, as `AskMainBalance` (proved as `colour_balance`) and `GrowthInequalityForm`, with the record `HostFacts`, for hosts ramified at most at $2$ and two odd primes. The path uses the versions that allow a set $S$ of primes in place of $2$ and the first odd prime (`ch_balance`, `ch_core`, `HostFactsS`).

- *Other definitions of the gain.* Three further definitions named `gainP`, in other namespaces than the one of [5.3](#sec:adm).

- *Other forms of single steps:* the jet statement `thmBGauss`; a jet form of the integrality at inert primes, `JetsInert`; a second form of the mean bound, `MeanBoundSecondForm`; the determinant statements `DetGain` (if $g_p\le v_p(\Delta)$ on a set of primes then $\sum g_p\log p\le\log\lvert \Delta\rvert$), `DetChain` and `DetBlocks`; a Bessel period statement `BesselPeriodGGP`; the congruence-number statements for $\mathrm{GSp}_4$ (`NumberSp4`) and the first form for $\mathrm{U}(3)$ (`CongruenceNumberRankThree`); and one of the derivations of the lower bound for the scalar of the lifts, `lamLow_of_classicalTheorems`.

In the other direction, every theorem declared in the file that collects the results taken from the literature ([10](#sec:literature)), 198 in all with the auxiliary ones, is in the cone: the proof term of the final theorem refers to every one of them.

The archive declares no axiom of its own, on the path or off it: its 1,905,922 declared names are theorems, definitions, inductive types with their constructors and recursors, and 2 opaque constants (0 of them in the cone), and nothing else.

## 12. Scope and method

<a id="sec:method"></a>

This paper describes a proof that exists as Lean source. It was written by reading that source from the last line upward: each hypothesis was followed to the declaration that supplies it, and each definition was transcribed into ordinary notation, until every branch reached a theorem of the published literature. Three rules governed the reading.

*Definitions are transcribed, not inferred from names.* Names in the source are labels. The same name is used for different propositions in different namespaces, and several formulations of one step coexist.

*Membership in the proof is decided by the compiled environment.* Almost every file of the archive imports almost every other, so the text alone cannot show that a declaration is used by the final theorem. The dependency cone of [2.6](#sec:cone) decides it by machine, and every statement in this paper that something is or is not used by the proof refers to it.

*Every statement about the proof has a recorded basis.* [Appendix A](#app:audit) lists the statements of this paper with the file and line where each was read.

The paper does not reprove anything, and it describes what the proof does, not how it was found. Constants and lower-order terms are abbreviated; each inequality displayed here holds in the source with explicit constants. The proofs of the published theorems that the archive formalises were not read; [10](#sec:literature) identifies them.

Qui Vincit directed the work and set its standards. Fable, a language model (Claude, Anthropic), ran the build, read the source and wrote the text, with further instances of the model reading bounded parts of the source; their reports are published with the paper. Corrections are welcome at the repository of [Appendix B](#app:reproduce).

## 13. Consequences and directions

<a id="sec:directions"></a>

### What follows at once

The truth of [Statement 2.1](#st:rh) and [Statement 2.2](#st:grh) and [Statement 2.3](#st:strip) has many known consequences, and none of them depends on how the theorem was proved. We list those that seem most useful to state formally; the first three are proved in a short Lean file published with this paper, against the compiled archive, with the same three axioms.

- $\zeta(s)\ne0$ for $\operatorname{Re}s>\tfrac12$, $s\neq1$.

- No exceptional zeros: for a non-trivial character $\chi$, $L(\sigma,\chi)\neq0$ for real $\sigma>\tfrac12$.

- Zeros of $L(s,\chi)$ in the open critical strip lie on the critical line.

The following are stated there as targets and are not proved by us.

- The prime number theorem in the form $\pi(x)=\mathrm{li}(x)+O(\sqrt x\log x)$ ([Koch 1901](#ref-vonkoch1901distribution)), and primes in intervals $(x,x+C\sqrt x\log x]$ ([Cramér 1921](#ref-cramer1921some)).

- Miller's deterministic primality test ([Miller 1976](#ref-miller1976riemann)) with the explicit bound of Bach ([Bach 1990](#ref-bach1990explicit)): an odd $n>2$ is prime if and only if it is a strong probable prime to every base $a$ with $2\le a<n$ and $a\le2(\log n)^2$. This becomes unconditional. It is slower in practice than the probabilistic tests in use; beside the unconditional test of Agrawal, Kayal and Saxena ([Agrawal et al. 2004](#ref-agrawal2004primes)) its merit is simplicity. The gain is a short deterministic test whose correctness can now be proved formally.

- Bounds for the least quadratic non-residue ([Ankeny 1952](#ref-ankeny1952least)) and the least prime in an arithmetic progression ([Bach and Sorenson 1996](#ref-bach1996explicit)).

### What does not follow

No method of factoring integers follows, and nothing in the argument suggests one. The statement was already assumed by everyone who would use it, so its truth changes "fast if GRH holds" into "fast" and makes nothing faster than was believed. The argument itself bounds averaged counts of primes by means of auxiliary fields of degree about $x^2$ and conductor exponential in a power of $x$; it never computes with a single integer.

The scope should also be kept in view. The theorem covers Dirichlet $L$-functions. Results that need the Riemann Hypothesis for Dedekind zeta functions of non-abelian fields, for elliptic curves or for Hecke characters are not covered.

### Directions

*An intelligible proof.* The present account describes the proof; it does not make it short. A statement of the whole argument on one page, each step a statement of the archive, is published with this paper (`one-page.pdf` in the repository of [Appendix B](#app:reproduce)). It is a skeleton, not a proof that can be checked by hand. Two statements seem to us to be the right core of a human proof: the slope inequality for nearly tight frames ([Statement 5.1](#st:F)), which is self-contained, and the identity ([Statement 5.2](#st:key)) that turns the period side into the analytic main term. A proof organised around them, with the divisibility of [6](#sec:divisibility) as its one arithmetic input and everything else quoted from the literature, would be the next thing to write.

*What is not needed.* The dependency cone shows that about a third of the archive's theorems are not used by the final theorem ([11](#sec:offpath)), and several inputs are used far below their strength: the cohomological bound is needed only in the form "at most $\exp(x^\varepsilon)$" ([8](#sec:cohomology)), and the term $\log\lvert I\rvert$ in [Statement 5.1](#st:F) is slack. A systematic weakening of each input to what is used would shorten the proof and show which of the deep theorems are essential.

*The by-products.* If the archive's proofs of the published theorems it relies on are what their names say, it contains formalisations of a substantial part of modern number theory: class field theory, Galois representations for unitary groups, the Siegel--Weil formula, arithmetic intersection theory, resolution of singularities. Each deserves its own audit of statement against literature, and extraction into a form that others can use.

*The cohomological bound.* [Statement 8.1](#st:vwin) is a new kind of result about the groups that Vandiver's conjecture concerns. Whether its method reaches the plus part of the class groups of cyclotomic fields themselves, which some arguments in lattice-based cryptography assume to be small ([Cramer et al. 2016](#ref-cramer2016recovering)), we do not know.

*Other $L$-functions.* The note says that Dedekind zeta functions are expected to yield to the same method.

## A. Basis of the statements

<a id="app:audit"></a>

This appendix records the basis of the paper's statements about the proof. M: computed from the compiled files, of the archive or, where the row says so, of Mathlib. S: the Lean statement was read and transcribed by the authors. P: the Lean source was read by the authors. C: the Lean statement was compared by the authors with the published theorem as they know it, without opening the papers. R: taken from a reader's report, published with this paper. Paths are relative to the archive's `src` directory, except in the row on `lean4lean`, where they are relative to its repository; a line number follows a colon; paths beginning `results/` are in `verify/` of the repository of [Appendix B](#app:reproduce), and those beginning `refs/` beside the source of this paper.

| Claim | Level | What was read |
|:---|:---|:---|
| The archive's size and hash, the counts of files and lines, and the static inspection | M | results/scan.txt |
| The five theorems of Main.lean and their statements | S | Main.lean:4-12; Statements.lean; the three main statements are also written out in check.sh and elaborated against the theorems (results/check.txt) |
| and riemannZeta are Mathlib's, and where the Dirichlet $L$-function is declared | M | results/check.txt |
| The builds succeed; every module is built | M | results/build-summary.txt, results/run1/build-summary.txt |
| Each of the five theorems depends on propext, Classical.choice, Quot.sound only | M | results/check.txt (the recorded lists); results/replay-targets.txt and CONE-AXIOMS in results/cut-result.txt (from the terms) |
| The dependency cone and every statement that a declaration is or is not used by the proof | M | results/cut-result.txt, results/cut-in.txt.xz, results/cut-out.txt.xz, results/cut-modules.txt.xz, results/cut-five-extra.txt |
| The kernel replay and its counts | M | results/replay-summary.txt, results/replay-provenance.txt, results/replay-targets.txt, results/replay-axioms.txt, results/replay-skipped.txt |
| How the two builds agree and differ | M | results/run1/, compared by paper/tools/numbers.py; for the two builds of Mathlib, results/mathlib-diff.txt |
| What lean4lean is and does | P | its README.md, Lean4Lean/Replay.lean:296, Lean4Lean/TypeChecker.lean, Lean4Lean/Inductive/Add.lean, Lean4Lean/Quot.lean, Lean4Lean/Environment.lean:45 and Lean4Lean/Primitive.lean:246, at commit 5518bf83; results/independent-build.txt |
| What the elaborators of the archive do | P | Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:87; Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean:5; Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:53-60; BuildAid/D1.lean to D5.lean |
| is rhOfAll, which is Formalism.VW.rh_of_every allChi | P | Main.lean:4; Supplements/Kernels/MainTheorems.lean:9 |
| The three hypotheses Green, VWin, Nonempty (HypsAlt ...); the window exponent 3/2; hosts from supplyChi | P | Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12-18 |
| The assembly of the record's fields into the links and the final call | P | .../ThirdPlaceSeries/TopShape.lean, whole file |
| The definition of G and of a family | S | Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean:10-36 |
| Landau on windows | S | .../DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean:11 |
| Its proof: the window hypothesis in the logarithmic variable, zeros with real part at least 1 excluded separately, iterated derivatives of a Laplace transform under the bound C$\cdot$e\^(2u), a kernel integral, a dichotomy and a nearest-zero lemma | P | .../LandauTheorems/lemmaL.lean:13-23; statements at IteratedDerivLaplace.lean:84, LandauDichotomy.lean:24, LandauNearest.lean:36, kernelIntegral.lean:9 |
| A level and its function | S | Level, Level.Gm, Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:8-39; KSet, .../TotientGaloisClasses/PrimePairSizeCondition.lean:39 |
| ASK, MAIN and the conditions on a host | S | ASK, MAIN, De, Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:84-93; HostFactsS, Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean:14 |
| The exact identity | P | ch_balance, .../DedekindLFunctions/LandauTheorems/ChBalance.lean:200-262 |
| Thick and thin weights, kept characters, and the sums over them | S | SizesA, CharsA, GmA, SigA, gapA, .../DedekindLFunctions/SplitInertia.lean:26-66; ThinScales, Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean:55; CostWindows, Formalism/SizeWindowBrackets/SChain.lean:50 |
| The scales of the thin places in the application | S | Char_at, Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean:221 |
| From the count to G, for kept characters | P | ch_core, .../LandauTheorems/ChCore.lean:343-444; statements of one_char and core, same file, 202 and 283 |
| The bound for a level; the lattice inequality for each translate | P | core_gm, Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:12-74; ch_top, .../LandauTheorems/ChTop.lean:37-74; statements of gmA_eq, sigA_le, EAtH |
| What a host adapted to a level is; which kept characters are trivial on H | S | EAtH, Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:144; ExceptionalCharacterKept, .../TotientGaloisClasses/Analytic.lean:158; wtA, .../DedekindLFunctions/SplitInertia.lean:32; statement of gmA_eq_triv, Development/AutomorphicArithmetic/PrimitiveCosets/GmAEq.lean:16; toE, .../PrimitiveCosets/RecH.lean:10 |
| The size conditions and the three costs | S | SizeWindows, GrowthSizeBound, Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean:109-123; RestSize, SChain.lean:53 |
| The record of eleven clauses | S | SizeData~2~, Formalism/SizeWindowBrackets/SChain.lean:17 |
| The space of forms is all algebraic modular forms of the weight and level | S | Fi, Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/PredMemGamRanks.lean:151 |
| The rescaled lattice | S | Iu, NprimeDef, Formalism/LocalRingCardinality/DataDIVDefs.lean:17-24 |
| The clauses Loss, Gain, the comparison of Ee and the count for T | S | LossBounds, QuotientSlopeBoundsWith, EComp5, Count5, Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean:19-35 |
| The clauses Slope and Div; the clauses that bound the slopes of the lattices of forms and the variation of the heights | S | SlopeIneq, DIV, Slopes, HComp, Formalism/RankGapBounds/MeanBoundSecondForm.lean:118-156 |
| Periods of the unscaled lattice are divisible to the order of the rescaling exponent | S | adm2, Formalism/SharpRestriction/Divisibility/LocalQuadraticParts.lean:206 |
| The gain formula: positions along the Frobenius orbit, partners, capacities, excluded exponents, candidate primes | S | IsV, Good, capU, Excl, g0, gU, Cand, VV, gainP, Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean:179-361; sg, Fo, Ga, Ee, Formalism/LocalRingCardinality/DataParams~2~.lean:212-224 |
| The slope inequality for nearly tight frames | S | TheoremF, Formalism/HarderNarasimhan/StatementFrameF.lean |
| Its proof | P | theoremFSharp_of, Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean:168-390; frameB_share, FrameHermSharpB.lean:25 |
| The ledger over the lift steps | P | divisor_inequality_assembly, Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DivAssembly.lean:11-46 |
| The inequality for slopes under a factorisation of determinants | S | BoundsMu, Formalism/DivisorInequality/StatementObj.lean:17 |
| The lower bound for the scalars of the lifts and its seven hypotheses | S | lamLow_of_hypotheses_alt_alt, .../ThirdPlaceSeries/LamLowOfPublished.lean:17 |
| The auxiliary lattices: integral forms on a moduli space | S | cuspA, nrmM_le_one_iff, Formalism/LocalToGlobal/ProjectiveLattices/CuspidalL2Subspace.lean:47-60 |
| The covolume clause and the chain of slope comparisons | S | L3, Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean:315; lcv_le, Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovolumeFromGramAndBounds.lean:39; its inputs at Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean:53-103 |
| The hypotheses of the covolume theorem from arithmetic geometry | S | topCovolSlim2_use_alt_alt, .../ThirdPlaceSeries/TopCovolSlim2Use.lean:16 |
| The Chowla--Selberg formula and Kronecker's limit formula | S | chowla_selberg_eta with the hypotheses of its section, Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean:212-225; tendsto_realEisenstein_sub_pole, .../TendstoRealEisensteinSubPole.lean:352 |
| The class number formula and the level prime | S | ClassNumberFormula~2~, Formalism/SharpRestriction/GlobalSchurBounds/StandardLattice.lean:453; LevelPrime, Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LogCondLeThree.lean:81 |
| The lattice side equals MAIN identically | S | key_identity5, Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:105 |
| The height-two logarithm; the radius lemma; the general form and the rate | S | ltLog, Formalism/LocalToGlobal/TorsionIntegrality/CMGoodModels/Statement.lean:35; LemmaSt, Formalism/GaussJetBounds/Statement.lean:107; LemmaRA, Formalism/GaussJetBounds/StatementG.lean:12 |
| Good models of CM curves and their formal groups at inert primes | S | CM2, CM3, .../CMGoodModels/Statement.lean:45-55 |
| Good reduction is derived from Artin reciprocity | S | cmGoodModel_of_globalArtinReciprocity, Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CmGoodModelOfGlobalArtinReciprocity.lean:10 |
| Integrality of the theta kernel at inert primes | S | IntInert, Formalism/LocalToGlobal/InertKernelTheory/StatementInt.lean:18 |
| The jet theorem is applied to an arbitrary series with the integrality hypothesis | P | prvF_of_orbitLetterBounds, Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitValuationBounds/PrvFOfOrbitLetterBounds.lean:17-61 |
| Duality of the integral Weyl modules; Minkowski's bound | S | standard_weyl_lattices_fock_dual, Development/AbelianVarietyTheory/Proofs/FoundationProofs/StandardWeylLatticesFockDualStatement.lean:14; MinkowskiBoundQ, Formalism/PeriodIntegrals/MinkowskiQ.lean:11 |
| The frame hypothesis | S | InputSG, Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean:30 |
| The period map is a Bessel pairing up to isometries and a non-zero scalar | S | BesselId, Formalism/SharpRestriction/GlobalTheoremInputs.lean:65 |
| The expansion of the pairing; the identity term; vanishing for different indices | S | KExpansion, LemmaV, Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/TermOpStmt.lean:23-36; oot_eq, .../ClosedLocalOrbits/GaugeLatticeShifts/IdBlocks.lean:672; SchurNFC, .../SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/KappaOffDiagonal.lean:47 |
| Uniqueness of Bessel models with a gap | S | UniqGap, CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/AtFormAdmOneOfSteps.lean:15 |
| Siegel--Weil as a mass formula; the main row | S | SiegelDensities, Formalism/UnipotentAdelicQuotients/SiegelWeilUnitaryConvergent.lean:18; rowMainEqP_of_siegelWeil, Development/AbelianVarietyTheory/Proofs/FlagMeasures/RowMainEqPOfSiegelWeil.lean:10 |
| The bound for two different indices | S | pbApplied, Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/TheoremS.lean:19 |
| In the application the parameter k of the frame is the rank parameter of the data | P | Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/TheoremSClosedP.lean:102 |
| The cohomological bound and its windows | S | VVle, VWinAt, VWin, Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:12-49 |
| The clause through which it is used, and the weakening of the square root | P | LinkN_at, DIVinN_at, Formalism/SharpRestriction/GlobalTheoremInputs.lean:31-63; divinN_of_hypV, vvRecord, Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:17-131 |
| The two quantities in which the bound is stated | S | BNBounds, Formalism/SizeWindowBrackets/SChain.lean:33 |
| It is used in one place besides its producer | S | a search of the source for DIVinN_at |
| The congruence ideal, the congruence module, and their bound | S | ccIdeal, etaLoc, vcc, Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean:25-225; chi_def, same file, 126; ZN, same file, 1292; CongBound_at, IsRankRPart, Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/BaseSizes.lean:57-93 |
| The assembly of the bound | S | of_four_alt, Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/HVCore.lean:18-22 |
| The crude bound for the second cohomology group | S | LemmaK, Development/AutomorphicArithmetic/AutomorphicVarieties/GeneratorCountTuples/LemmaK.lean:13 |
| The odd part: from Poitou--Tate duality, with Kolyvagin derivative classes | S | ML.iv, Development/AutomorphicArithmetic/AutomorphicVarieties/PrimitiveFrobeniusFixed/Iv.lean:4; PsiBound, .../AutomorphicVarieties/OddResidueBounds/ZeroMemUnrHom.lean:97; kolStep, .../KolStep.lean:135 |
| Ferrero--Washington by Sinnott's theorem | S | sinnott, Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/Sinnott.lean:10 |
| The congruence number, the Eisenstein trace, and the bound of a length by valuations | S | NumberU3U_s, OneCharU_s, Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/NumberU3US.lean:30-60; eis3, .../AutomorphicForms/CongruenceNumberRankThree.lean:121 |
| The lemma on a graded local algebra | S | LemmaM, Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/OrbitVanishingLocal.lean:111 |
| The theorem on Hida families; Kato's Euler system | S | hida_unitary_of_printed_hida, .../DenseThresholdCases/THidaU.lean:38; zetaUr, .../KatoQuadraticCharacters/UnramifiedZeta/ZetaUr.lean:9 |
| The partial compatibility of the Galois representations | S | AwayB, Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:26 |
| The theorem and its single hypothesis | S | galoisRepresentations_of_thetaLift, Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GaloisRepresentationsOfThetaLift.lean:6; Row0b, .../TypeConditions/WeightsConjBis.lean:69; TLiftK, .../GaloisRepresentations/ThetaParseval/HalfIndexLattices/TLiftK.lean:12 |
| The host field and the sizes of its primes | S | IsChiField, WinPair, PageN, Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:19-40 |
| The host contains the imaginary quadratic field and the CM type fixes it | S | HostRaw, Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:12 |
| Supply of hosts on windows | S | supplyChi, .../CharacterBoxes/SupplyChi.lean:8 |
| Good pairs of primes exist on a range of scales | S | PairGood, PairEx, .../CharacterBoxes/PairGood.lean:19-32 |
| The mean square and the zero-density estimate | S | meanSqK, Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean:51; zero_density_box, Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13 |
| The thick set without small relations; the statement Green | S | NoRel, Formalism/FrobeniusOrbits/HostThickExists.lean:13; noRel_image, hostThickExists, Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:85-181; IsPrimeLab, Green, Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:91-112 |
| What each of the 186 literature statements asserts | S | the Lean statement of each row and, where it is a conjunction of named parts, the head of each part, at the path recorded for the row in refs/rows-A.jsonl, rows-B.jsonl, rows-C.jsonl; our descriptions are in refs/rows-author.json |
| Whether each is the published theorem in the generality of a source, a restricted form, or a different statement | C | the Lean statement of each row; the verdict and its reason are recorded in refs/rows-scope-author.json and printed in the table of the next appendix |
| The sources of each row | R | the reference research recorded in the same three files |
| What the final theorem does not use | M | results/cut-result.txt, cut-in.txt.xz, cut-out.txt.xz, cut-modules.txt.xz; statements of the named declarations read at Formalism/ProductFormula/StatementOCCM.lean:137-160, Formalism/HalfLinks/Statement.lean:144, Formalism/JacobiWeightFamilies/Statement.lean:57, Formalism/StatementOC.lean:65, Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:47 |
|  |  |  |

## B. Reproducing the verification

<a id="app:reproduce"></a>

Everything needed to repeat [2](#sec:verification) is in the repository

<https://github.com/vincitamore/riemann-lean-account>

together with the source of this paper, the reading notes, the delegated reports, the reviews of the replay program and the audit. The archive itself is not redistributed there; it is fetched from the author's site and checked against the hash of [2](#sec:verification).

### Requirements

<a id="requirements"></a>

The second build ran on a rented Linux machine with 32 threads, in a container whose memory was limited to 64 GB; the first on one with 32 threads limited to 128 GB. The build completed within each. The archive's compiled files come to 100 GB. On the second machine the cone step took about 3.4 hours, by the times at which the files before and after it were written, and the replay 116 minutes on 32 threads; on the first, the replay with the earliest form of the program took 57 minutes on 28 threads, and the time of its cone step was not recorded. The scripts' comments estimate 150 GB of free disk.

The scripts in `verify/` assume `bash` with `git`, `curl`, `zstd`, `tar` and `sha256sum`, and `python3` for the scan; `setup.sh` installs `elan` if it is absent.

### Steps

<a id="steps"></a>

1.  `setup.sh` downloads the fourteen parts, concatenates them, checks the SHA-256, unpacks, installs the pinned toolchain and compiles Mathlib from source at the pinned commit (or, on request, fetches its build cache).

2.  `scan.py` is the static inspection of [2](#sec:verification): it reads the downloaded file without unpacking it and needs nothing else.

3.  `toolchain.sh` compares the installed toolchain with the release archive on GitHub.

4.  `build.sh` runs `lake build Main` with every log line time-stamped and records the exit code.

5.  `janitor.sh` must run beside the build. Lake writes, for every module, a file listing the module's whole import closure

    , 5.9 MB on average here; for this tree those files would total about 1031 GB. The script deletes each one once its module's compiled file exists, which Lake tolerates. With it the disk in use peaked at 115 GiB, as `df` read it once a minute.

6.  `summary.sh` extracts from the logs and the built tree the facts of the build that this paper quotes.

7.  `check.sh` prints the modules in which Mathlib declares its statement of the hypothesis, the zeta function and the $L$-function; the statements of the five theorems, with the archive's definitions of them in full; and the axioms of the five theorems. It writes out [Statement 2.1](#st:rh) and [Statement 2.2](#st:grh) and [Statement 2.3](#st:strip) and elaborates each afresh against its theorem, and it runs both checkers on the module `Statements`.

8.  `corollaries.sh` compiles the Lean file of corollaries and the file of targets of [13](#sec:directions) against the built archive and prints the axioms of the corollaries.

9.  `cut.sh` builds and runs the program `cut/CutMain.lean`, which computes the dependency cone of [2.6](#sec:cone) and writes the list of every declaration of the archive inside it and outside it.

10. `replay.sh` builds and runs the program `replay/ReplayMain.lean`, the kernel replay of [2.7](#sec:replay). The number of threads is set with `LEAN_NUM_THREADS`.

11. `hostile.sh` builds the modules of `hostile/` and runs Lean's checker and the replay program on each ([Table 1](#tab:hostile)).

12. `stock.sh` runs `leanchecker --fresh` and then the replay program on Mathlib, or on the roots named in `FRESH_ROOTS`: with `Main` there, and another directory for the output, it is the check of the whole archive by Lean's own checker. `sample.sh` runs `leanchecker` on a sample of names of the archive's modules ([2.8](#sec:checker)).

13. `independent.sh` fetches `lean4lean` at a fixed commit, builds it with the archive's toolchain, and runs it on the modules of `hostile/`, on the closures of the two modules of Mathlib named in [2.8](#sec:checker) and on the same sample.

14. `sample-exact.sh` lists the modules under each name of the sample and, for a name on which a checker's process was killed, calls that checker's function for one module on each module the name covers, one at a time, after testing that way of calling it on two of the modules of `hostile/`.

15. `mathlib-diff.sh` fetches the community's cached build of Mathlib into a second copy of the package and compares it with the build from source: the names of the constants, and the hashes of their statements and values ([2.4](#sec:build)).

16. `cone-probe.sh` asks, for each constant which that comparison names, whether it is in the cone of `riemannHypothesis`. Its program, `cut/ConeProbe.lean`, computes the cone as the cone program does and prints its size.

The outputs of our runs are in `verify/results/`, with an index that says what wrote each file; those of the first run are in `verify/results/run1/`.

Every number in this paper that was measured is read from those files by `paper/tools/numbers.py`, which also checks that they agree with one another, apart from a few that no file holds and that are typed with their provenance in `version.tex` or, for the second machine's price and start, in that program; and `paper/tools/check_names.py` checks every Lean name cited in the paper against the lists of declarations inside and outside the cone.

### Cost

<a id="cost"></a>

The second run took 19 minutes to compile Mathlib and 16.0 hours to build the archive on 32 threads; the cone then took 3.4 hours and the replay 116 minutes. Lean's own checker took 8.0 hours on one thread for the whole archive, and the replay, run again after it, 59 minutes. The provider billed 26.81 US dollars for the first machine. The second, at its hourly price, cost about 37 dollars from its start to the end of the steps reported here.

## C. The published results formalised in the archive

<a id="app:rows"></a>

One row for each of the 186 theorems of the archive's literature file ([10](#sec:literature)), in the order of the file. The second column says what the Lean statement asserts, in our words; where the statement is a conjunction of named parts the description covers the parts. After it, in italics, is our comparison with the published theorem that the name refers to, and the third column gives its outcome: *general*, the published theorem in the generality of a cited source; *restricted*, a special case of it or a weaker form; *differs*, not a statement of the cited literature as it stands. The other labels are internal (a statement in the archive's own terms), empty, conclusion and repeated. The comparison was made from the Lean statement and from our knowledge of the published theorem; we did not open the papers for it, and a row should be checked against its sources before it is relied on. The fourth column gives the sources, from the reference research.

| Lean statement | What it asserts | Scope | Sources |
|:---|:---|:---|:---|
| LogDerOne | There is $C$ such that $\bigl|\tfrac{L'}{L}(1,\chi)-\sum_\rho\tfrac1{1-\rho}\bigr|\le C\log 3q$ for every primitive $\chi$ modulo $q>1$, the sum over the zeros with $0<\operatorname{Re}\rho<1$ and $\lvert \operatorname{Im}\rho\rvert\le1$. *The value at $s=1$ of the classical formula for $L'/L$ in terms of nearby zeros.* | restricted | ([Davenport 1980](#ref-davenport1980multiplicative)) |
|  | The main theorem of complex multiplication for elliptic curves with CM by an imaginary quadratic field $K$, in idelic form: if $\sigma\in\mathrm{Aut}(\mathbb{C}/K)$ restricts to $\mathrm{Art}(s)$, then $\sigma$ transports an analytic uniformisation $\mathbb{C}/\mathfrak a\to E(\mathbb{C})$ according to the finite part of $s$. *Imaginary quadratic fields and lattices that are fractional ideals of the maximal order; Shimura's theorem covers any lattice and CM abelian varieties.* | restricted | ([Shimura 1971](#ref-shimura1971introduction); [Shimura and Taniyama 1961](#ref-shimura1961complex)) |
|  | For a unitary Hecke character $\chi$ of a totally complex field with non-zero infinity type relative to a CM type, the completed $L$-functions of $\chi$ and $\chi^{-1}$ exist and $\Lambda(s,\chi)=\varepsilon_\infty\,\varepsilon_{\mathrm f}(s)\,\Lambda(1-s,\chi^{-1})$. *Totally complex fields and infinity types coming from a CM type; the published theorem covers every Hecke character of every number field.* | restricted | ([Hecke 1918](#ref-hecke1918neue), [1920](#ref-hecke1920neue); [Tate 1967a](#ref-tate1967fourier)) |
|  | For $K$ imaginary quadratic, $K(j(\mathcal{O}_K))$ is the Hilbert class field, of degree $h_K$; $j(\mathfrak a)=j(\mathfrak b)$ exactly when the ideal classes agree; and the $h_K$ values $j(\mathfrak a)$ are the conjugates of $j(\mathcal{O}_K)$ over $K$. *The first main theorem of complex multiplication for the maximal order.* | general | ([Hasse 1927](#ref-hasse1927neue); [Shimura 1971](#ref-shimura1971introduction)) |
|  | For $F$ totally real of degree $n$ and ideal classes $C,C'$ whose product is the class of the different: $d_F^{s/2}\Gamma_\mathbb{R}(s)^n\zeta(s,C)=d_F^{(1-s)/2}\Gamma_\mathbb{R}(1-s)^n\zeta(1-s,C')$. *Totally real fields; Hecke's functional equation holds for every number field.* | restricted | ([Hecke 1917](#ref-hecke1917zetafunktion); [Tate 1967a](#ref-tate1967fourier)) |
|  | For $F$ totally real and a $\mathbb{Q}$-valued function $\varepsilon$ on ideals that is constant on narrow ray classes modulo $\ell^n$ and $\ell$-integral: $L(1-k,\varepsilon)-N\mathfrak c^{k}L(1-k,\varepsilon(\mathfrak c\,\cdot))$ is $\ell$-integral, for $\mathfrak c$ prime to $\ell$ and $k\ge1$. *Conductor a power of $\ell$ and rational values; the published theorem allows any conductor and $\ell$-adic values.* | restricted | ([Deligne and Ribet 1980](#ref-deligne1980values); [Cassou-Noguès 1979](#ref-cassounogues1979valeurs)) |
|  | The preceding statement together with the theorem of Siegel and Klingen. *A conjunction whose second part is the restricted statement above.* | restricted | ([Klingen 1962](#ref-klingen1962werte); [Siegel 1969](#ref-siegel1969berechnung), [1970](#ref-siegel1970fourierschen); [Deligne and Ribet 1980](#ref-deligne1980values); [Cassou-Noguès 1979](#ref-cassounogues1979valeurs)) |
|  | A conjunction of five statements internal to the archive, on critical values of Hecke $L$-functions of CM fields and on partial zeta values. | internal | --- |
|  | For a continuous $\ell$-adic representation of dimension $a$ of the Galois group of the host field that is de Rham at a place $w$ above $\ell$, and an embedding $\tau$ inducing $w$: the multiset of $\tau$-Hodge--Tate weights has $a$ elements. *Stated for the host fields of the archive's data; the fact holds for every de Rham representation.* | restricted | ([Fontaine 1994c](#ref-fontaine1994semistables), [1982](#ref-fontaine1982certains)) |
|  | An abelian variety of dimension $g$ over an algebraically closed field has exactly $n^{2g}$ points killed by $n$, for $n$ invertible in the field. *The classical count of torsion points.* | general | ([Mumford 1970](#ref-mumford1970abelian); [Weil 1948](#ref-weil1948varietes)) |
|  | For an abelian scheme $A$ of relative dimension $g$ over a ring $R$: $H^1_{\mathrm{dR}}(A/R)$ is finite projective of rank $2g$ and cup product identifies its second exterior power with $H^2_{\mathrm{dR}}$; the submodule of primitive classes is a direct summand, finite projective of rank $g$; both are compatible with base change; the comparison map along a nilpotent divided-power thickening is bijective; and the pairing of a polarisation vanishes on the filtration and is perfect when the polarisation has trivial kernel. *Five standard facts, over an arbitrary affine base.* | general | ([Oda 1969](#ref-oda1969first); [Berthelot et al. 1982](#ref-berthelot1982theorie); [Mazur and Messing 1974](#ref-mazur1974universal)) |
|  | Every continuous de Rham representation of the Galois group of a finite extension of $\mathbb{Q}_\ell$ is potentially semistable. *The $p$-adic monodromy theorem for finite extensions of $\mathbb{Q}_\ell$.* | general | ([Berger 2002](#ref-berger2002representations); [André 2002](#ref-andre2002filtrations); [Mebkhout 2002](#ref-mebkhout2002analogue); [Kedlaya 2004](#ref-kedlaya2004padic)) |
|  | For every number field $E$ there is a homomorphism $\mathbb A_E^\times\to G_E^{\mathrm{ab}}$ with the properties of the global Artin map. *The idelic Artin map: an open quotient map with the classical kernel, compatible with inertia, Frobenius and decomposition groups.* | general | ([Takagi 1920](#ref-takagi1920theorie); [Artin 1927](#ref-artin1927beweis); [Chevalley 1940](#ref-chevalley1940theorie); [Tate 1967b](#ref-tate1967global)) |
|  | The $\ell$-adic character attached to an algebraic Hecke character is de Rham at every place above $\ell$, with Hodge--Tate weights given by the infinity type. *Every algebraic Hecke character of every number field.* | general | ([Serre 1968](#ref-serre1968abelian); [Fontaine 1994c](#ref-fontaine1994semistables)) |
|  | Local--global compatibility for algebraic Hecke characters at every finite place, including those above $\ell$: the Weil--Deligne representation of the $\ell$-adic character at $w$ is the local component composed with the local Artin map. *Every finite place, those above $\ell$ included.* | general | ([Serre 1968](#ref-serre1968abelian); [Fontaine 1994b](#ref-fontaine1994potentiellement)) |
|  | Seven properties of arithmetic intersection numbers of Hermitian line bundles. *Seven standard properties of arithmetic intersection numbers; the normalisations were not compared with the papers.* | general | ([Gillet and Soulé 1990](#ref-gillet1990arithmetic); [Bost et al. 1994](#ref-bost1994heights)) |
|  | Two statements on arithmetic intersection numbers and Chern degrees. *Birational invariance of arithmetic self-intersection and the Chern--Weil formula for the degree, two standard facts.* | general | ([Bost et al. 1994](#ref-bost1994heights); [Gillet and Soulé 1990](#ref-gillet1990arithmetic); [Chern 1946](#ref-chern1946characteristic)) |
|  | For a smooth projective integral variety over a field of characteristic $0$ and a non-zero ideal sheaf $I$: a sequence of blow-ups in smooth centres over the support of $I$ is an isomorphism away from the support and turns $I$ into an effective Cartier divisor with simple normal crossings. *Smooth projective varieties; Hironaka's theorem needs no projectivity.* | restricted | ([Hironaka 1964a](#ref-hironaka1964resolution), [1964b](#ref-hironaka1964resolutionII)) |
|  | For a nef Hermitian line bundle $\bar L$ of arithmetic self-intersection $a$ on an arithmetic variety of relative dimension $D$, and any $\bar N$: the number of sections of $\bar L^{m}\otimes\bar N$ of sup-norm at most $1$ is finite for large $m$ and its logarithm is $\tfrac{a}{(D+1)!}m^{D+1}+o(m^{D+1})$. *The nef form, which is Moriwaki's.* | general | ([Gillet and Soulé 1992](#ref-gillet1992arithmetic); [Abbes and Bouche 1995](#ref-abbes1995theoreme); [Zhang 1995](#ref-zhang1995positive); [Moriwaki 2009](#ref-moriwaki2009continuity)) |
|  | Over a totally complex field, the automorphic forms on $\mathrm{GL}_a$ of a given level, $K_\infty$-type and infinitesimal character span a finite-dimensional space. *$\mathrm{GL}_a$ over totally complex fields; Harish-Chandra's theorem covers reductive groups over any number field.* | restricted | ([Harish-Chandra 1968](#ref-harishchandra1968automorphic)) |
|  | Base change from a definite unitary group to an isobaric sum on $\mathrm{GL}_n$. *Weak base change from a definite unitary group, under hypotheses of the kind Labesse makes.* | general | ([Labesse 2011](#ref-labesse2011changement)) |
|  | The same with the full induced product as local component. *The same with irreducible local components.* | general | ([Labesse 2011](#ref-labesse2011changement); [Bernstein 1984](#ref-bernstein1984pinvariant)) |
|  | Over a non-archimedean local field, the parabolically induced product of two irreducible unitarisable smooth representations of general linear groups is irreducible. *Bernstein's theorem, which is about general linear groups.* | general | ([Bernstein 1984](#ref-bernstein1984pinvariant)) |
|  | For $\mathrm{GL}_n$ over a non-archimedean local field: irreducible smooth representations are admissible; Jacquet functors and parabolic induction preserve finite length; and induction commutes with the contragredient. *Four standard finiteness facts for $\mathrm{GL}_n$.* | general | ([Bernstein and Zelevinsky 1976](#ref-bernstein1976representations), [1977](#ref-bernstein1977induced)) |
|  | For $K/\mathbb{Q}_\ell$ finite, every lattice in a crystalline representation of $G_K$ is the étale realisation of a prismatic $F$-crystal on $\mathcal{O}_K$, and the realisation is fully faithful. *The theorem of Bhatt and Scholze on lattices in crystalline representations.* | general | ([Bhatt and Scholze 2023](#ref-bhatt2023prismatic)) |
|  | The same for lattices with coefficients in the ring of integers of a finite extension of $\mathbb{Q}_\ell$. *The same with coefficients.* | general | ([Bhatt and Scholze 2023](#ref-bhatt2023prismatic)) |
|  | For $K/\mathbb{Q}_\ell$ finite: the dimension formula for the Bloch--Kato subspace $H^1_f$ of a de Rham representation, and its duality with that of the Tate dual, rationally and integrally. *The local results of Bloch and Kato for a finite extension of $\mathbb{Q}_\ell$.* | general | ([Bloch and Kato 1990](#ref-bloch1990lfunctions)) |
|  | For an admissible representation of $\mathrm{GL}_n$ over a non-archimedean local field, the Iwahori-fixed vectors map bijectively onto the fixed vectors of the Jacquet module. *$\mathrm{GL}_n$; the theorem of Borel and Casselman is for reductive groups.* | restricted | ([Borel 1976](#ref-borel1976admissible); [Casselman 1980](#ref-casselman1980unramified)) |
|  | For a representation $\rho$ of a finite group, $\chi_\rho-\dim\rho$ is an integral combination of differences $\mathrm{Ind}(\chi_i)-\mathrm{Ind}(1)$ with $\chi_i$ characters of degree one of subgroups. *The degree-zero form of Brauer's induction theorem.* | general | ([Brauer 1947](#ref-brauer1947artin); [Deligne 1973](#ref-deligne1973constantes)) |
|  | For a prime $p\equiv3\pmod4$, $p>3$, there is an elliptic curve over $\mathbb{Q}(j(\mathcal{O}_K))$, $K=\mathbb{Q}(\sqrt{-p})$, with complex multiplication by $\mathcal{O}_K$, good reduction outside $p$ and minimal discriminant $-p^3$. *Gross's curve $A(p)$.* | general | ([Gross 1982](#ref-gross1982minimal), [1980](#ref-gross1980arithmetic)) |
|  | Over a non-archimedean local field of characteristic $0$, an irreducible smooth representation of $\mathrm{GL}_n$ is essentially square-integrable exactly when it is the quotient $L(\Delta)$ attached to a segment. *Characteristic $0$; the theorem holds for every non-archimedean local field.* | restricted | ([Zelevinsky 1980](#ref-zelevinsky1980induced); [Bernstein and Zelevinsky 1977](#ref-bernstein1977induced)) |
|  | Over a non-archimedean local field of characteristic $0$: two irreducible cuspidal representations of $\mathrm{GL}_n$, $n\ge2$, with the same Rankin--Selberg $\varepsilon$-constants against every irreducible representation of $\mathrm{GL}_{n-1}$ are isomorphic. *Cuspidal representations in characteristic $0$; Henniart's theorem is for generic representations in any characteristic.* | restricted | ([Henniart 1993](#ref-henniart1993caracterisation)) |
|  | At every finite place of a number field there is a map from the irreducible smooth representations of the groups $\mathrm{GL}_n$ to Weil--Deligne representations satisfying a stated list of laws of the local Langlands correspondence. *Existence of a map with a list of consequences of the local Langlands correspondence, not the correspondence itself.* | restricted | ([Harris and Taylor 2001](#ref-harris2001geometry); [Henniart 2000](#ref-henniart2000preuve); [Scholze 2013](#ref-scholze2013local); [Bushnell and Henniart 2005](#ref-bushnell2005essentially)) |
|  | For a CM field $E$ and a regular algebraic cuspidal representation $\pi$ of $\mathrm{GL}_a$ forming a polarised pair, there is a continuous semisimple $r\colon G_E\to\mathrm{GL}_a(\overline{\mathbb{Q}}_\ell)$ attached to $\pi$ with stated compatibilities. *The Galois representation exists, with compatibility away from $\ell$ only in part: equal dimension, equality when the local parameter is a sum of characters with trivial monodromy, and agreement on inertia for a class of tame parameters.* | restricted | ([Chenevier and Harris 2013](#ref-chenevier2013construction); [Shin 2011](#ref-shin2011galois); [Caraiani 2012](#ref-caraiani2012local); [Barnet-Lamb et al. 2012](#ref-barnetlamb2012local), [2014a](#ref-barnetlamb2014local), [2014b](#ref-barnetlamb2014potential)) |
|  | Over a totally complex field, a cusp form on $\mathrm{GL}_a$ whose absolute value is invariant under the split centre is bounded. *$\mathrm{GL}_a$ over totally complex fields.* | restricted | ([Harish-Chandra 1968](#ref-harishchandra1968automorphic); [Moeglin and Waldspurger 1994](#ref-moeglin1994decomposition)) |
|  | Over a totally complex field, two finite families of cuspidal automorphic representations of general linear groups whose isobaric sums have the same Satake parameters at almost all places coincide up to permutation. *Totally complex fields; the theorem of Jacquet and Shalika is for any number field.* | restricted | ([Jacquet and Shalika 1981b](#ref-jacquet1981eulerI), [1981a](#ref-jacquet1981eulerII)) |
|  | Over a totally complex field, every cuspidal automorphic representation of $\mathrm{GL}_n$ is paired with itself twisted by $g\mapsto{}^{t}g^{-1}$. *A global consequence, for cuspidal representations, of the local theorem of Gelfand and Kazhdan.* | differs | ([Gelfand and Kazhdan 1975](#ref-gelfand1975representations); [Bernstein and Zelevinsky 1976](#ref-bernstein1976representations); [Jacquet and Shalika 1981a](#ref-jacquet1981eulerII)) |
|  | Over a non-archimedean local field of characteristic $0$, every irreducible generic representation of $\mathrm{GL}_N$ is an irreducible product $L(\Delta_1)\times\dots\times L(\Delta_h)$ over pairwise unlinked segments. *Characteristic $0$.* | restricted | ([Zelevinsky 1980](#ref-zelevinsky1980induced)) |
|  | For a number field $E$ and $m,b>0$ there is $a>0$ prime to $b$ such that every unit congruent to $1$ modulo $a$ is an $m$-th power of a unit. *Chevalley's theorem on units.* | general | ([Chevalley 1951](#ref-chevalley1951deux)) |
|  | The geometric lemma of Bernstein and Zelevinsky for $\mathrm{GL}_n$ over a non-archimedean local field: the Jacquet module of an induced representation has a finite filtration by cell functors, with a statement on semisimplifications. *The geometric lemma for $\mathrm{GL}_n$, as in Zelevinsky.* | general | ([Bernstein and Zelevinsky 1977](#ref-bernstein1977induced)) |
|  | Over a non-archimedean local field, for any assignment $Z(\Delta)$ of segment classes, the Grothendieck group of finite-length representations of all $\mathrm{GL}_n$ is, with the induction product, the polynomial ring on the $Z(\Delta)$. *Zelevinsky's theorem.* | general | ([Zelevinsky 1980](#ref-zelevinsky1980induced)) |
|  | Over a non-archimedean local field, the segment product $\sigma\times\sigma\nu\times\dots\times\sigma\nu^{l-1}$ of a cuspidal $\sigma$ has a unique irreducible subrepresentation, with Jacquet module $\sigma\otimes\sigma\nu\otimes\dots\otimes\sigma\nu^{l-1}$. *Zelevinsky's segment representations.* | general | ([Zelevinsky 1980](#ref-zelevinsky1980induced); [Bernstein and Zelevinsky 1977](#ref-bernstein1977induced)) |
|  | Over a non-archimedean local field there are segment classes $Z(\Delta)$ and an isomorphism of the Grothendieck ring of the groups $\mathrm{GL}_n$ with $\mathbb{Z}[X_\Delta]$ sending $Z(\Delta)$ to $X_\Delta$. *Zelevinsky's theorem.* | general | ([Zelevinsky 1980](#ref-zelevinsky1980induced)) |
|  | Over a non-archimedean local field of characteristic $0$: if every member of the cuspidal support of an irreducible representation of $\mathrm{GL}_n$ has a non-zero vector fixed by the first congruence subgroup, so has the representation. *$\mathrm{GL}_n$ in characteristic $0$ and depth zero; the theorem of Moy and Prasad is for reductive groups and every depth.* | restricted | ([Moy and Prasad 1994](#ref-moy1994unrefined), [1996](#ref-moy1996jacquet)) |
|  | Over a non-archimedean local field of characteristic $0$, every irreducible smooth representation of $\mathrm{GL}_n$ is $L(\mathfrak m)$ for a multisegment $\mathfrak m$. *Characteristic $0$.* | restricted | ([Silberger 1978](#ref-silberger1978langlands); [Zelevinsky 1980](#ref-zelevinsky1980induced)) |
|  | Over a non-archimedean local field of characteristic $0$: the multisegment $\mathfrak m$ of $L(\mathfrak m)$ is unique, and $L(\mathfrak m+\mathfrak n)$ is a subquotient of $L(\mathfrak m)\times L(\mathfrak n)$. *Characteristic $0$.* | restricted | ([Zelevinsky 1980](#ref-zelevinsky1980induced); [Silberger 1978](#ref-silberger1978langlands)) |
|  | Over a non-archimedean local field of characteristic $0$, a product of segment representations in standard order has a unique irreducible quotient. *Characteristic $0$.* | restricted | ([Silberger 1978](#ref-silberger1978langlands); [Zelevinsky 1980](#ref-zelevinsky1980induced)) |
|  | The same statement as RecTExists above, entered a second time in the file. | repeated | ([Harris and Taylor 2001](#ref-harris2001geometry); [Henniart 2000](#ref-henniart2000preuve); [Scholze 2013](#ref-scholze2013local); [Bushnell and Henniart 2005](#ref-bushnell2005essentially)) |
|  | Every irreducible smooth complex representation of $\mathrm{GL}_n$ over a non-archimedean local field is admissible. *Admissibility of irreducible smooth representations of $\mathrm{GL}_n$.* | general | ([Jacquet 1975](#ref-jacquet1975representations); [Bernstein 1974](#ref-bernstein1974all); [Bernstein and Zelevinsky 1976](#ref-bernstein1976representations)) |
|  | Over a non-archimedean local field, Jacquet functors and parabolic induction for block parabolic subgroups of $\mathrm{GL}_n$ preserve finite length. *Finite length is preserved, for $\mathrm{GL}_n$.* | general | ([Bernstein and Zelevinsky 1977](#ref-bernstein1977induced), [1976](#ref-bernstein1976representations)) |
|  | Over a non-archimedean local field of characteristic $0$, an irreducible smooth representation of $\mathrm{GL}_N$ is tempered exactly when it is a product of square-integrable representations. *Characteristic $0$.* | restricted | ([Jacquet 1977](#ref-jacquet1977generic); [Zelevinsky 1980](#ref-zelevinsky1980induced)) |
|  | For a real unitary group and an irreducible unitary representation $\sigma$: every $(\mathfrak g,K)$-map from the $K$-finite vectors of $\sigma$ to a smooth Fréchet representation of moderate growth extends uniquely to a continuous map on smooth vectors. *Real unitary groups and unitary representations; the theorem is for real reductive groups and admissible modules.* | restricted | ([Casselman 1989](#ref-casselman1989canonical); [Wallach 1983](#ref-wallach1983asymptotic), [1992](#ref-wallach1992real)) |
|  | For a finite Galois extension $L/F$ of number fields, $g\in\operatorname{Gal}(L/F)$ and a finite set $S$ of primes, there is a prime outside $S$ of degree one over $\mathbb{Q}$, unramified in $L$, with Frobenius $g$. *An existence statement that follows from the density theorem.* | restricted | ([Tschebotareff 1926](#ref-chebotarev1926bestimmung)) |
|  | In characteristic $0$, a geometrically prime homogeneous ideal of dimension $D+1$ has a Chow form of degree equal to its Hilbert degree, unique up to a non-zero scalar. *Characteristic $0$.* | restricted | ([Chow and Waerden 1937](#ref-chow1937algebraischen)) |
|  | Over a totally complex field, every regular algebraic cuspidal automorphic representation of $\mathrm{GL}_a$ is cohomological. *Totally complex fields; Clozel's lemma is for any number field.* | restricted | ([Clozel 1990](#ref-clozel1990motifs)) |
|  | Over a totally complex field, for a cuspidal representation of $\mathrm{GL}_a$ with algebraic infinitesimal characters there is an integer $w_0$ with $\mathrm{infChar}(\bar\tau)=w_0-\mathrm{infChar}(\tau)$ for every embedding $\tau$. *Totally complex fields.* | restricted | ([Clozel 1990](#ref-clozel1990motifs)) |
|  | For $K$ imaginary quadratic there are a Hilbert class field $H\subset\mathbb{C}$ and an Artin isomorphism $\mathrm{Cl}(K)\cong\operatorname{Gal}(H/K)$ with $K(j(\mathfrak a))=H$ and $\mathrm{art}([\mathfrak b])\,j(\mathfrak a)=j(\mathfrak b^{-1}\mathfrak a)$. *The main theorem of complex multiplication for $j$-invariants of ideal lattices.* | general | ([Hasse 1927](#ref-hasse1927neue); [Shimura 1971](#ref-shimura1971introduction)) |
|  | On the adelic unitary group of a Hermitian space over a CM field, a smooth cuspidal automorphic function all of whose derivatives have uniform moderate growth is bounded, with all its derivatives. *Unitary groups of Hermitian spaces over CM fields.* | restricted | ([Harish-Chandra 1968](#ref-harishchandra1968automorphic); [Moeglin and Waldspurger 1994](#ref-moeglin1994decomposition)) |
|  | On the same group, a quantitative form: for a given level and exponents, finitely many derivatives bound $\lvert \varphi(g)\rvert\,\mathrm{ht}(g)^N$ for every cusp function of that level. *The same groups, in a quantitative form.* | restricted | ([Moeglin and Waldspurger 1994](#ref-moeglin1994decomposition); [Harish-Chandra 1968](#ref-harishchandra1968automorphic)) |
|  | On the same group, the rapid-decay seminorms of a cusp function of given level are bounded by its Sobolev seminorms of moderate growth. *A Sobolev-norm form of rapid decay, not the statement of rapid decay in the standard references.* | differs | ([Moeglin and Waldspurger 1994](#ref-moeglin1994decomposition); [Harish-Chandra 1968](#ref-harishchandra1968automorphic)) |
|  | On the same group, every smooth cuspidal automorphic function of uniform moderate growth decays rapidly. *Unitary groups of Hermitian spaces over CM fields.* | restricted | ([Gel'fand et al. 1969](#ref-gelfand1969representation); [Harish-Chandra 1968](#ref-harishchandra1968automorphic); [Moeglin and Waldspurger 1994](#ref-moeglin1994decomposition)) |
|  | On the same group, for every smooth compactly supported $f$ the operator $R_{\mathrm{cusp}}(f)$ on the cuspidal $L^2$-space is of trace class. *The same groups.* | restricted | ([Gel'fand et al. 1969](#ref-gelfand1969representation); [Dixmier and Malliavin 1978](#ref-dixmier1978factorisations)) |
|  | For every finite field, $\mathrm{GL}_{n+1}$ has an irreducible cuspidal complex representation, and the restriction of such a representation to the mirabolic subgroup is the induced representation of a non-degenerate character. *Every finite field.* | general | ([Green 1955](#ref-green1955characters); [Gel'fand 1970](#ref-gelfand1970representations); [Zelevinsky 1981](#ref-zelevinsky1981representations)) |
|  | For $\mathrm{GL}_a$ over a totally complex field: the cuspidal part of $L^2$ is a Hilbert direct sum of irreducible subrepresentations, with statements on their finite vectors and on boundedness of cusp forms. *$\mathrm{GL}_a$ over totally complex fields.* | restricted | ([Gel'fand and Pyatetskij-Shapiro 1963](#ref-gelfand1963automorphic); [Godement 1966](#ref-godement1966spectral); [Harish-Chandra 1968](#ref-harishchandra1968automorphic)) |
|  | Arithmetic heights and arithmetic intersection functionals exist, are multilinear in mixed arguments, and satisfy a projection formula for heights. *Existence and standard properties of arithmetic heights; the normalisations were not compared with the papers.* | general | ([Gillet and Soulé 1990](#ref-gillet1990arithmetic); [Bost et al. 1994](#ref-bost1994heights)) |
|  | Over a non-archimedean local field, for an irreducible representation of $\mathrm{GL}_n$ and a standard parabolic subgroup: a vector fixed by the first congruence subgroup and by the integral points of the unipotent radical, whose image in the Jacquet module is zero, is zero. *$\mathrm{GL}_n$ at depth zero, and only injectivity.* | restricted | ([Moy and Prasad 1996](#ref-moy1996jacquet)) |
|  | Over a non-archimedean local field, if an irreducible representation of $\mathrm{GL}_n$ has a non-zero vector fixed by the first congruence subgroup, so has every member of its cuspidal support. *$\mathrm{GL}_n$ at depth zero.* | restricted | ([Moy and Prasad 1994](#ref-moy1994unrefined), [1996](#ref-moy1996jacquet)) |
|  | For the real unitary groups $\mathrm{U}(p,q)$: every Harish-Chandra parameter carries an irreducible unitary square-integrable representation with that infinitesimal character and a unique lowest $K$-type, with stated uniqueness. *The groups $\mathrm{U}(p,q)$, with a weaker statement on $K$-types than Schmid's.* | restricted | ([Harish-Chandra 1965](#ref-harishchandra1965discrete), [1966](#ref-harishchandra1966discrete); [Schmid 1975](#ref-schmid1975some)) |
|  | For the double cover of $\mathrm{U}(p,q)$ defined by a square root of the determinant: the discrete series is a family $D(\lambda)$ indexed by parameters, with prescribed $K$-types, and every discrete series representation is equivalent to one of them. *A double cover of $\mathrm{U}(p,q)$.* | restricted | ([Harish-Chandra 1965](#ref-harishchandra1965discrete), [1966](#ref-harishchandra1966discrete); [Schmid 1975](#ref-schmid1975some)) |
|  | For that double cover and every parameter $\lambda$ there is a discrete series representation with parameter $\lambda$. *A double cover of $\mathrm{U}(p,q)$.* | restricted | ([Harish-Chandra 1966](#ref-harishchandra1966discrete); [Schmid 1975](#ref-schmid1975some)) |
|  | The same as `DiscreteSeriesUpqExists` below. *The groups $\mathrm{U}(p,q)$.* | restricted | ([Harish-Chandra 1966](#ref-harishchandra1966discrete); [Schmid 1975](#ref-schmid1975some)) |
|  | Two discrete series representations of $\mathrm{U}(p,q)$ with the same Harish-Chandra parameter, transported to the unitary group of a Hermitian matrix by two frames, are unitarily equivalent. *The groups $\mathrm{U}(p,q)$ and their conjugates.* | restricted | ([Harish-Chandra 1966](#ref-harishchandra1966discrete)) |
|  | In a discrete series representation of $\mathrm{U}(p,q)$ with Harish-Chandra parameter $\lambda$, the $K$-type of highest weight $\lambda+\rho_n-\rho_c$ occurs with multiplicity one, with a second clause on its uniqueness. *The groups $\mathrm{U}(p,q)$.* | restricted | ([Schmid 1975](#ref-schmid1975some); [Harish-Chandra 1966](#ref-harishchandra1966discrete)) |
|  | For every Harish-Chandra parameter $\lambda$ of $\mathrm{U}(p,q)$ there is an irreducible unitary representation with square-integrable matrix coefficients that contains the $K$-type $\lambda+\rho_n-\rho_c$, with a clause on its other $K$-types. *The groups $\mathrm{U}(p,q)$.* | restricted | ([Harish-Chandra 1966](#ref-harishchandra1966discrete); [Schmid 1975](#ref-schmid1975some)) |
|  | For a group closed in $\mathrm{GL}_n(\mathbb{C})$ with a Haar measure, every smooth compactly supported function is a finite sum of convolutions of two such functions, the first supported in a prescribed neighbourhood of the identity. *Closed linear groups; the theorem is for all Lie groups.* | restricted | ([Dixmier and Malliavin 1978](#ref-dixmier1978factorisations)) |
|  | For a Hermitian space $V$ of positive rank over a CM extension, the Siegel Eisenstein series on the doubled group $\mathrm{U}(V\oplus-V)$ attached to a section of the degenerate principal series continues meromorphically, with poles of finite order. *Siegel Eisenstein series on doubled unitary groups; Langlands's theorem is for all Eisenstein series.* | restricted | ([Langlands 1976](#ref-langlands1976functional); [Moeglin and Waldspurger 1994](#ref-moeglin1994decomposition)) |
|  | The preceding statement together with the basic identity of the doubling method. *The global identity of the doubling method with the continuation above; nothing about local zeta integrals, despite the name.* | differs | ([Gelbart et al. 1987](#ref-gelbart1987explicit); [Langlands 1976](#ref-langlands1976functional)) |
|  | Every irreducible unitary representation of the adelic unitary group of a Hermitian space over a CM extension is a restricted tensor product of irreducible unitary representations of the local groups. *Unitary groups of Hermitian spaces over CM extensions.* | restricted | ([Flath 1979](#ref-flath1979decomposition)) |
|  | Every irreducible unitary representation of a non-archimedean local unitary group of that kind is admissible. *These unitary groups; Bernstein's theorem is for reductive groups.* | restricted | ([Bernstein 1974](#ref-bernstein1974all)) |
|  | The factorisation of `FlathTensorProduct`, with the local factors unramified at almost all places. *These unitary groups.* | restricted | ([Flath 1979](#ref-flath1979decomposition)) |
|  | Seven properties of Fontaine's ring $B_{\mathrm{cris}}$, among them injectivity of Frobenius and of $B_{\mathrm{cris}}\to B_{\mathrm{dR}}$ and the fundamental exact sequence. *Seven standard properties of $B_{\mathrm{cris}}$.* | general | ([Fontaine 1982](#ref-fontaine1982certains), [1994a](#ref-fontaine1994corps), [1994c](#ref-fontaine1994semistables)) |
|  | Grothendieck's algebraisation over a complete noetherian ring, for morphisms from a proper scheme and for schemes. *Grothendieck's existence theorem.* | general | ([Grothendieck 1961](#ref-grothendieck1961elements)) |
|  | With the Haar measure of $\mathrm{U}(p,q)$ normalised through the compact dual, the formal degree of the discrete series representation with Harish-Chandra parameter $\lambda$ is given by the product formula in the differences $\lambda_a-\lambda_b$. *The groups $\mathrm{U}(p,q)$.* | restricted | ([Harish-Chandra 1966](#ref-harishchandra1966discrete); [Atiyah and Schmid 1977](#ref-atiyah1977geometric)) |
|  | For unitary representations of $\mathrm{U}(p,q)$: the closure of an admissible $(\mathfrak g,K)$-submodule is stable under the group, and infinitesimally equivalent irreducible unitary representations are unitarily equivalent. *The groups $\mathrm{U}(p,q)$.* | restricted | ([Harish-Chandra 1953](#ref-harishchandra1953representations)) |
|  | For $n,n'\ge1$, the polynomial functions on $n\times n'$ matrices decompose under $\mathrm{GL}_n(\mathbb{C})\times\mathrm{GL}_{n'}(\mathbb{C})$, and under $\mathrm{U}(n)\times\mathrm{U}(n')$, as the multiplicity-free sum of the $F_n^{a}\otimes F_{n'}^{a}$. *The duality of $\mathrm{GL}_n$ and $\mathrm{GL}_{n'}$ on polynomials.* | general | ([Howe 1989a](#ref-howe1989remarks)) |
|  | For a CM field $E$ and a regular algebraic cuspidal representation $\pi$ of $\mathrm{GL}_a$ polarised by a Hecke character, there is a continuous semisimple $r\colon G_E\to\mathrm{GL}_a(\overline{\mathbb{Q}}_\ell)$ attached to $\pi$ with stated compatibilities. *The Galois representation exists, with compatibility away from $\ell$ only in part: equal dimension, equality when the local parameter is a sum of characters with trivial monodromy, and agreement on inertia for a class of tame parameters; the literature gives full compatibility.* | restricted | ([Clozel et al. 2011](#ref-clozel2011construction); [Shin 2011](#ref-shin2011galois); [Chenevier and Harris 2013](#ref-chenevier2013construction); [Taylor and Yoshida 2007](#ref-taylor2007compatibility); [Caraiani 2012](#ref-caraiani2012local), [2014](#ref-caraiani2014monodromy); [Barnet-Lamb et al. 2012](#ref-barnetlamb2012local), [2014a](#ref-barnetlamb2014local), [2014b](#ref-barnetlamb2014potential)) |
|  | Over a non-archimedean local field of characteristic $0$, every irreducible unitarisable generic representation of $\mathrm{GL}_N$ is a product of unitary segment representations and of complementary pairs. *Characteristic $0$.* | restricted | ([Tadić 1986](#ref-tadic1986classification); [Bernstein 1984](#ref-bernstein1984pinvariant)) |
|  | The filtration half of the geometric lemma for $\mathrm{GL}_n$ over a non-archimedean local field. *The filtration half of the geometric lemma.* | restricted | ([Bernstein and Zelevinsky 1977](#ref-bernstein1977induced); [Zelevinsky 1980](#ref-zelevinsky1980induced)) |
|  | For a metric that is good in Mumford's sense, Chern--Weil integrals compute Chern numbers, with a push-forward formula on flag bundles. *Mumford's theorem for good metrics and the push-forward formula for flag bundles, in the archive's coordinates.* | general | ([Mumford 1977](#ref-mumford1977hirzebruch); [Brion 1996](#ref-brion1996pushforward)) |
|  | The cuspidal characters of $\mathrm{GL}_d(\mathbb{F}_p)$ are parametrised without repetition by the monic irreducible polynomials of degree $d$ with non-zero constant term, each of degree $\prod_{i=1}^{d-1}(p^i-1)$. *Prime fields; Green's theorem is for every finite field.* | restricted | ([Green 1955](#ref-green1955characters)) |
|  | For $K=\mathbb{F}_{p^d}$, each regular character $\theta$ of $K^\times$ gives a cuspidal character of $\mathrm{GL}_d(\mathbb{F}_p)$ of degree $\prod_{i=1}^{d-1}(p^i-1)$ with value $(-1)^{d-1}\sum_i\theta(z^{p^i})$ on elements with irreducible characteristic polynomial; $\tau(\theta)=\tau(\theta')$ exactly for Frobenius conjugates; and every cuspidal character arises. *Prime fields.* | restricted | ([Green 1955](#ref-green1955characters)) |
|  | For a prime $p$ and $N\ge1$ there is a map from square-free polynomials of degree $N$ to irreducible characters of $\mathrm{GL}_N(\mathbb{F}_p)$ with stated properties. *Prime fields.* | restricted | ([Green 1955](#ref-green1955characters)) |
|  | For a surjection of rings whose kernel has nilpotent divided powers, abelian schemes and their homomorphisms lift according to the Hodge filtration in crystalline cohomology. *The lifting half of the theory of Grothendieck and Messing.* | general | ([Grothendieck 1971](#ref-grothendieck1971groupes); [Messing 1972](#ref-messing1972crystals); [Mazur and Messing 1974](#ref-mazur1974universal)) |
|  | For every surjection of rings with nilpotent divided-power kernel: the Grothendieck--Messing statement on canonicity of the comparison and on lifting abelian schemes and their homomorphisms. *The theory of Grothendieck and Messing for abelian schemes.* | general | ([Grothendieck 1971](#ref-grothendieck1971groupes); [Messing 1972](#ref-messing1972crystals); [Mazur and Messing 1974](#ref-mazur1974universal)) |
|  | The same for rings in which a prime $p$ is nilpotent. *The same when a prime is nilpotent.* | general | ([Grothendieck 1971](#ref-grothendieck1971groupes); [Messing 1972](#ref-messing1972crystals); [Mazur and Messing 1974](#ref-mazur1974universal)) |
|  | For a principally polarised abelian variety over an algebraically closed field, the space of sections of the polarising line bundle is one-dimensional. *A classical consequence of Riemann--Roch on abelian varieties.* | general | ([Mumford 1970](#ref-mumford1970abelian)) |
|  | Matrix coefficients of $K$-finite vectors in admissible representations of $\mathrm{U}(p,q)$ are real-analytic, with a density statement for Levi subgroups. *The groups $\mathrm{U}(p,q)$ and their Levi subgroups.* | restricted | ([Harish-Chandra 1953](#ref-harishchandra1953representations)) |
|  | On the adelic unitary group of a Hermitian space over a CM extension, the automorphic forms of a given level, archimedean $K$-type and infinitesimal character span a finite-dimensional space. *Unitary groups of Hermitian spaces over CM extensions.* | restricted | ([Harish-Chandra 1968](#ref-harishchandra1968automorphic)) |
|  | For the double covers of $\mathrm{U}(p,q)$: the Harish-Chandra module of an irreducible unitary representation exists, is admissible and irreducible, and determines the representation; $K$-finite vectors are analytic. *The groups $\mathrm{U}(p,q)$ and their double covers.* | restricted | ([Harish-Chandra 1953](#ref-harishchandra1953representations), [1954a](#ref-harishchandra1954representations2), [1954b](#ref-harishchandra1954representations3)) |
|  | For a number field $F$ and $\delta,x\ne0$: if $x=a^2-\delta b^2$ is solvable at every real place and in every non-archimedean completion, it is solvable in $F$. *Quadratic extensions; the norm theorem is for cyclic extensions.* | restricted | ([Hasse 1924](#ref-hasse1924darstellbarkeit), [1931](#ref-hasse1931beweis)) |
|  | For every number field there is a global Artin map, and for every algebraic Hecke character and every $\ell$ a unique continuous $\ell$-adic character attached to it through that map. *Every number field and every algebraic Hecke character.* | general | ([Weil 1956](#ref-weil1956certain); [Taniyama 1957](#ref-taniyama1957lfunctions); [Serre 1968](#ref-serre1968abelian); [Takagi 1920](#ref-takagi1920theorie); [Artin 1927](#ref-artin1927beweis); [Chevalley 1940](#ref-chevalley1940theorie)) |
|  | The $\ell$-adic character of an algebraic Hecke character is crystalline at every place above $\ell$ at which the Hecke character is unramified. *Every place above $\ell$ at which the character is unramified.* | general | ([Serre 1968](#ref-serre1968abelian); [Fontaine 1982](#ref-fontaine1982certains)) |
|  | At the places above $\ell$, the $\ell$-adic character of an algebraic Hecke character is de Rham, potentially crystalline, and crystalline where the Hecke character is unramified, with the expected Hodge--Tate weights. *The properties at the places above $\ell$.* | general | ([Serre 1968](#ref-serre1968abelian); [Fontaine 1982](#ref-fontaine1982certains), [1994c](#ref-fontaine1994semistables)) |
|  | At a place $w$ above $\ell$, the Weil--Deligne representation given by Fontaine's $D_{\mathrm{pst}}$ for the $\ell$-adic character of an algebraic Hecke character is its local component composed with local class field theory. *Compatibility at the places above $\ell$ for $\mathrm{GL}_1$.* | general | ([Serre 1968](#ref-serre1968abelian); [Fontaine 1994b](#ref-fontaine1994potentiellement)) |
|  | For a unitary Hecke character $\chi$ of a number field: if $\chi$ is not a power of the norm, $L(s,\chi)$ is entire; and if $\chi\ne1$, $L(1,\chi)\ne0$. *Every unitary Hecke character of every number field.* | general | ([Hecke 1918](#ref-hecke1918neue), [1920](#ref-hecke1920neue); [Tate 1967a](#ref-tate1967fourier)) |
|  | For a number field and a finite set $T$ of places: the $L$-function with the Euler factors at $T$ removed of a unitary Hecke character that is not a power of the norm is entire and non-zero on $\operatorname{Re}s\ge1$; and $(s-1)\zeta_K^{T}(s)$ is entire and non-zero there. *The same with finitely many Euler factors removed.* | general | ([Hecke 1918](#ref-hecke1918neue), [1920](#ref-hecke1920neue); [Landau 1903](#ref-landau1903neuer)) |
|  | For a quadratic extension of number fields, two non-degenerate Hermitian matrices that are congruent over every completion are congruent. *Landherr's theorem.* | general | ([Landherr 1936](#ref-landherr1936aquivalenz)) |
|  | Locally, over a quadratic extension of non-archimedean local fields with $2\ne0$, two non-degenerate Hermitian forms of the same rank are congruent exactly when the ratio of their determinants is a norm; with a global statement over CM fields. *The local classification and Landherr's global theorem.* | general | ([Jacobowitz 1962](#ref-jacobowitz1962hermitian); [Landherr 1936](#ref-landherr1936aquivalenz)) |
|  | A discrete series representation of $\mathrm{U}(p,q)$ with Harish-Chandra parameter in the holomorphic chamber is a lowest-weight module. *The groups $\mathrm{U}(p,q)$.* | restricted | ([Harish-Chandra 1955](#ref-harishchandra1955representations4), [1956a](#ref-harishchandra1956representations5), [1956b](#ref-harishchandra1956representations6)) |
|  | For a unitary dual pair over a CM extension, Howe duality at the archimedean places in the polynomial Fock model of the Weil representation. *Unitary dual pairs, and only the lift of the trivial representation.* | restricted | ([Howe 1989b](#ref-howe1989transcending)) |
|  | For $K$ imaginary quadratic and a lattice homothetic to a fractional ideal, $j$ is algebraic over $K$ and its orbit under $\mathrm{Aut}(\mathbb{C}/K)$ is the set of $j$-invariants of all ideal lattices. *The classical statement on the conjugates of $j$.* | general | ([Hasse 1927](#ref-hasse1927neue); [Shimura 1971](#ref-shimura1971introduction)) |
|  | For $\mathrm{GL}_N$ in characteristic $p$ and a dominant weight $\lambda$ with $\lambda_i-\lambda_j+(j-i)\le p$ for $i<j$, the induced module $\nabla(\lambda)$ is non-zero and simple. *$\mathrm{GL}_N$; the statement holds for reductive groups.* | restricted | ([Andersen 1980](#ref-andersen1980strong); [Jantzen 2003](#ref-jantzen2003representations)) |
|  | The rigidity statement `JacquetShalikaRigidity` together with a bound on Satake parameters of cuspidal representations. *Totally complex fields.* | restricted | ([Jacquet and Shalika 1981b](#ref-jacquet1981eulerI), [1981a](#ref-jacquet1981eulerII)) |
|  | Every irreducible unitary representation of $\mathrm{U}(p,q)$ is admissible; its $K$-finite vectors are analytic, dense, stable under the Lie algebra and irreducible as a $(\mathfrak g,K)$-module. *The groups $\mathrm{U}(p,q)$.* | restricted | ([Harish-Chandra 1953](#ref-harishchandra1953representations), [1954a](#ref-harishchandra1954representations2), [1954b](#ref-harishchandra1954representations3)) |
|  | For a smooth projective variety $X$ over an algebraically closed field of characteristic $0$ and a nef and big line bundle $N$: $H^q(X,K_X\otimes N)=0$ for $q>0$. *The vanishing theorem for nef and big line bundles.* | general | ([Kawamata 1982](#ref-kawamata1982generalization); [Viehweg 1982](#ref-viehweg1982vanishing)) |
|  | For a quadratic extension of non-archimedean local fields of characteristic $0$, a Hermitian matrix $Q$ and a character $\chi$ of $E^\times$ restricting to the right power of the quadratic character: a smooth unitary representation of the split unitary group $\mathrm{U}(\nu,\nu)$ itself on the Schwartz space of the Schrödinger model, compatible with the Heisenberg action attached to $Q$ and given on the Levi subgroup by the usual formula. *The split member $\mathrm{U}(\nu,\nu)$ of the pair only; Kudla's splitting covers both members of a unitary dual pair; stated in characteristic $0$.* | restricted | ([Kudla 1994](#ref-kudla1994splitting); [Harris et al. 1996](#ref-harris1996theta)) |
|  | An extension theorem of Ohsawa--Takegoshi type with $L^2$ estimates, from a finite non-degenerate common zero set of $n$ sections of a line bundle on a compact complex manifold of dimension $n$. *Extension from a finite set of points; the theorems of Ohsawa--Takegoshi type cover subvarieties.* | restricted | ([Ohsawa and Takegoshi 1987](#ref-ohsawa1987extension); [Demailly 2016](#ref-demailly2016extension); [Cao et al. 2017](#ref-cao2017general)) |
|  | For a CM field, two non-degenerate Hermitian matrices with the same signature at every embedding and with determinants differing by a norm are congruent. *Landherr's classification over a CM field.* | general | ([Landherr 1936](#ref-landherr1936aquivalenz)) |
|  | There are $C,L>0$ such that for coprime $a,q\ge1$ the least prime $p\equiv a\pmod q$ is at most $C\,q^{L}$. *Linnik's theorem.* | general | ([Linnik 1944a](#ref-linnik1944least1), [1944b](#ref-linnik1944least2)) |
|  | Over a totally complex field, two cuspidal automorphic subrepresentations of $\mathrm{GL}_a$ in the same isomorphism class have the same space. *Totally complex fields.* | restricted | ([Shalika 1974](#ref-shalika1974multiplicity); [Piatetski-Shapiro 1979](#ref-piatetskishapiro1979multiplicity)) |
|  | For a CM field $E$ and a conjugate self-dual regular algebraic cuspidal representation of $\mathrm{GL}_a$, $a\ge2$: the attached $r\colon G_E\to\mathrm{GL}_a(\overline{\mathbb{Q}}_\ell)$ exists with the compatibilities of `CuspUAlt` and with stated properties at the places above $\ell$. *As `CuspUAlt`: compatibility away from $\ell$ only in part.* | restricted | ([Clozel et al. 2011](#ref-clozel2011construction); [Shin 2011](#ref-shin2011galois); [Chenevier and Harris 2013](#ref-chenevier2013construction); [Taylor and Yoshida 2007](#ref-taylor2007compatibility); [Caraiani 2012](#ref-caraiani2012local), [2014](#ref-caraiani2014monodromy); [Barnet-Lamb et al. 2012](#ref-barnetlamb2012local), [2014a](#ref-barnetlamb2014local), [2014b](#ref-barnetlamb2014potential)) |
|  | The same statement as CarUAlt above, entered a second time in the file. | repeated | ([Clozel et al. 2011](#ref-clozel2011construction); [Shin 2011](#ref-shin2011galois); [Chenevier and Harris 2013](#ref-chenevier2013construction); [Taylor and Yoshida 2007](#ref-taylor2007compatibility); [Caraiani 2012](#ref-caraiani2012local), [2014](#ref-caraiani2014monodromy); [Barnet-Lamb et al. 2012](#ref-barnetlamb2012local), [2014a](#ref-barnetlamb2014local), [2014b](#ref-barnetlamb2014potential)) |
|  | For every $n$ there is a two-sheeted covering group of $\mathrm{Sp}_{2n}(\mathbb{R})$ with a unitary representation on $L^2(\mathbb{R}^n)$, continuous on Schwartz space and compatible with the Schrödinger representation of the Heisenberg group. *The oscillator representation of the metaplectic group.* | general | ([Weil 1964](#ref-weil1964certains); [Shale 1962](#ref-shale1962linear); [Segal 1963](#ref-segal1963transforms)) |
|  | Over a non-archimedean local field, for an admissible representation of $\mathrm{GL}_n$ and a standard parabolic subgroup: the vectors fixed by the first congruence subgroup and the integral points of the unipotent radical map bijectively onto the corresponding fixed vectors of the Jacquet module. *$\mathrm{GL}_n$ at depth zero.* | restricted | ([Moy and Prasad 1996](#ref-moy1996jacquet)) |
|  | Nadel vanishing for a pair, and the existence of a divisor with an isolated non-klt point, on a normal projective complex variety. *Vanishing for some ideal with the right support, which is weaker than Nadel's theorem for the multiplier ideal.* | restricted | ([Nadel 1990](#ref-nadel1990multiplier); [Angehrn and Siu 1995](#ref-angehrn1995effective); [Kollár 1997](#ref-kollar1997singularities)) |
|  | Over an algebraically closed field: intersection numbers of nef line bundles are non-negative; a nef line bundle is big exactly when its top self-intersection is positive; and an asymptotic Riemann--Roch statement for nef bundles. *Three standard facts on nef line bundles.* | general | ([Kleiman 1966](#ref-kleiman1966toward); [Lazarsfeld 2004](#ref-lazarsfeld2004positivity)) |
|  | An effective criterion of Angehrn--Siu type for a line bundle on a klt pair to separate two points of a normal projective complex variety. *The criterion of Angehrn and Siu in Kollár's numerical form, with his constants.* | general | ([Angehrn and Siu 1995](#ref-angehrn1995effective); [Kollár 1997](#ref-kollar1997singularities)) |
|  | Poitou--Tate duality with normalised local invariant maps, for finite modules over a number field and a set of primes containing those above $\ell$. *$\ell$-power torsion modules, with $\ell\ne2$ or the field totally complex.* | restricted | ([Tate 1963](#ref-tate1963duality); [Poitou 1966](#ref-poitou1966remarques); [Milne 1986](#ref-milne1986arithmetic)) |
|  | For a complete algebraically closed field of mixed characteristic, a prismatic Dieudonné functor from $p$-divisible groups over its ring of integers to finite free $A_{\inf}$-modules, with its Hodge-theoretic properties. *Over the ring of integers of a complete algebraically closed field; the theory is over quasi-syntomic rings.* | restricted | ([Anschütz and Le Bras 2023](#ref-anschutz2023prismatic); [Bhatt et al. 2018](#ref-bhatt2018integral); [Scholze and Weinstein 2013](#ref-scholze2013moduli)) |
|  | Class field theory for quadratic extensions of number fields: local norm-residue characters, the Hasse norm theorem, an exact sequence and the product formula, with a compatibility in towers. *Class field theory for quadratic extensions, which is what the name says.* | general | ([Hilbert 1899](#ref-hilbert1899theorie); [Hasse 1924](#ref-hasse1924darstellbarkeit); [Takagi 1920](#ref-takagi1920theorie)) |
|  | In characteristic $0$, the shuffle algebra on an ordered alphabet is the polynomial algebra on the Lyndon words. *Radford's theorem.* | general | ([Radford 1979](#ref-radford1979natural)) |
|  | The Siegel--Weil formula for unitary groups in the convergent range, for Hermitian spaces of ranks $n<m\le2n$ satisfying Weil's condition: the theta integral converges and equals the value of a Siegel Eisenstein series. *Ichino's range $n<m\le2n$ under Weil's condition.* | general | ([Ichino 2007](#ref-ichino2007siegel); [Weil 1965](#ref-weil1965formule); [Ikeda 1996](#ref-ikeda1996residue)) |
|  | Weil's criterion: if $V$ is anisotropic or $n+r(V)<\dim V$, the theta integral over $[\mathrm{U}(V)]$ of every adelic Schwartz function on $V^n$ converges absolutely. *Weil's criterion.* | general | ([Weil 1965](#ref-weil1965formule)) |
|  | The Rallis inner product formula in the convergent range, for theta lifts between unitary groups of ranks $n<m\le2n$ under Weil's condition. *The convergent range, for unitary pairs.* | general | ([Rallis 1984](#ref-rallis1984injectivity); [Li 1992](#ref-li1992nonvanishing)) |
|  | A homomorphism from the ideals prime to $\mathfrak m$ to an abelian group that is trivial on principal ideals generated by elements congruent to $1$ modulo $\mathfrak m$ is given by a unique continuous character of the Galois group, unramified outside $\mathfrak m$, through Frobenius elements. *Artin reciprocity for ray class characters.* | general | ([Takagi 1920](#ref-takagi1920theorie); [Artin 1927](#ref-artin1927beweis)) |
|  | Existence of the ray class field of a number field for a non-zero ideal, with its Artin map. *Existence of ray class fields.* | general | ([Takagi 1920](#ref-takagi1920theorie); [Artin 1927](#ref-artin1927beweis)) |
|  | A topological double cover of $\mathrm{Sp}_{2n}(\mathbb{R})$ with a strongly continuous unitary representation on $L^2(\mathbb{R}^n)$ in which the non-trivial element of the kernel acts by $-1$, compatible with the Schrödinger representation and preserving Schwartz space. *The oscillator representation.* | general | ([Segal 1959](#ref-segal1959foundations); [Shale 1962](#ref-shale1962linear); [Weil 1964](#ref-weil1964certains)) |
|  | For a CM field, a regular algebraic cuspidal automorphic representation of $\mathrm{GL}_a$ has pure infinity type and is cohomological. *CM fields; Clozel's lemmas are for any number field.* | restricted | ([Clozel 1990](#ref-clozel1990motifs)) |
|  | For a unimodular locally compact group and an irreducible unitary representation with one non-zero square-integrable matrix coefficient: all matrix coefficients are square-integrable and satisfy the Schur orthogonality relations with a formal degree. *Godement's theorem for unimodular groups.* | general | ([Godement 1947a](#ref-godement1947orthogonalite), [1947b](#ref-godement1947demonstration)) |
|  | Over a noetherian normal scheme, a homomorphism of semi-abelian schemes defined over a dense open extends uniquely. *Extension of homomorphisms over a normal base.* | general | ([Faltings and Chai 1990](#ref-faltings1990degeneration)) |
|  | For a semi-abelian scheme $G$ over a smooth projective curve in characteristic $0$, every subbundle of $\mathrm{Lie}\,G$ has non-positive degree. *Bost's semi-negativity in characteristic $0$.* | general | ([Bost 2004](#ref-bost2004germs), [2006](#ref-bost2006evaluation); [Griffiths 1970](#ref-griffiths1970periods)) |
|  | Every polarised abelian variety over a finite extension of $\mathbb{Q}_p$ acquires a semi-abelian model over the integers of a finite extension. *$p$-adic fields and polarised abelian varieties; Grothendieck's theorem is for any discretely valued field.* | restricted | ([Grothendieck et al. 1972](#ref-grothendieck1972groupes)) |
|  | On a smooth projective complex variety, algebraic sections of a line bundle are the same as holomorphic sections. *Global sections of line bundles on smooth projective varieties; Serre's theorem covers coherent sheaves and all cohomology.* | restricted | ([Serre 1956](#ref-serre1956geometrie)) |
|  | The proposition `True`; an empty slot of the file. | empty | --- |
|  | For a non-degenerate Hermitian form over a CM extension: an Iwasawa decomposition of the adelic unitary group and a Siegel set with the properties of reduction theory. *Unitary groups of Hermitian forms over CM extensions.* | restricted | ([Borel and Harish-Chandra 1962](#ref-borel1962arithmetic); [Borel 1969](#ref-borel1969introduction); [Moeglin and Waldspurger 1995](#ref-moeglin1995spectral)) |
|  | For $g\ge1$ and odd $n\ge3$: the Siegel moduli scheme of level $n$ over $\mathbb{Z}[1/n,\zeta_n]$ has a smooth projective toroidal compactification carrying a semi-abelian scheme that extends the universal abelian scheme. *Odd levels $n\ge3$.* | restricted | ([Faltings and Chai 1990](#ref-faltings1990degeneration)) |
|  | The Siegel--Weil formula in the Schrödinger model of $\mathrm{U}(n,n)$, for $n<\dim V\le2n$ under Weil's condition. *The same formula in another model.* | general | ([Ichino 2007](#ref-ichino2007siegel); [Weil 1965](#ref-weil1965formule); [Ikeda 1996](#ref-ikeda1996residue)) |
|  | Over a non-archimedean local field of characteristic $0$, every irreducible square-integrable representation of $\mathrm{GL}_n$ is the representation $L(\Delta)$ of a segment. *Characteristic $0$.* | restricted | ([Zelevinsky 1980](#ref-zelevinsky1980induced); [Bernstein and Zelevinsky 1977](#ref-bernstein1977induced)) |
|  | For a symplectic space over a non-archimedean local field of characteristic not $2$: the Heisenberg group has an irreducible smooth representation with a given non-trivial central character, unique up to isomorphism. *The theorem for the Heisenberg group of a non-archimedean local field.* | general | ([Stone 1930](#ref-stone1930linear); [Neumann 1931](#ref-vonneumann1931eindeutigkeit); [Mackey 1949](#ref-mackey1949theorem); [Mœglin et al. 1987](#ref-moeglin1987correspondances)) |
|  | Strong approximation for the special unitary group of a non-degenerate Hermitian form of rank at least $2$ over a CM extension, with respect to a set of places at which the group is not compact. *Special unitary groups; the theorem is for simply connected groups.* | restricted | ([Kneser 1965](#ref-kneser1965starke); [Platonov 1969](#ref-platonov1969problem)) |
|  | A statement in the archive's own terms: invariance of spaces of theta functions on CM tori under rational unitary matrices, up to an explicit character. | internal | --- |
|  | For a unitary moduli problem of PEL type over a CM field: a projective model containing the moduli space as a dense open, smooth of the expected dimension, with boundary a divisor with simple normal crossings and a logarithmic Kodaira--Spencer isomorphism. *Unitary moduli problems of PEL type in characteristic $0$.* | restricted | ([Ash et al. 1975](#ref-ash1975smooth); [Pink 1989](#ref-pink1989arithmetical); [Lan 2013](#ref-lan2013arithmetic)) |
|  | The same for a prescribed polarised admissible fan without self-intersection, with toroidal charts along the boundary. *The same.* | restricted | ([Lan 2013](#ref-lan2013arithmetic); [Faltings and Chai 1990](#ref-faltings1990degeneration); [Ash et al. 1975](#ref-ash1975smooth)) |
|  | Over a non-archimedean local field: if no member of the cuspidal support of $\pi_1$ is $\nu^{j}$ times a member of that of $\pi_2$ for $j\in\{-1,0,1\}$, then $\pi_1\times\pi_2$ is irreducible. *An irreducibility criterion in the theory of Bernstein and Zelevinsky.* | general | ([Bernstein and Zelevinsky 1977](#ref-bernstein1977induced); [Zelevinsky 1980](#ref-zelevinsky1980induced)) |
|  | Over a non-archimedean local field: if no member of the cuspidal support of $\pi_1$ is an unramified twist of a member of that of $\pi_2$, then $\pi_1\times\pi_2$ is irreducible. *A hypothesis much stronger than Zelevinsky's unlinked segments.* | restricted | ([Zelevinsky 1980](#ref-zelevinsky1980induced); [Bernstein and Zelevinsky 1977](#ref-bernstein1977induced)) |
|  | Over a non-archimedean local field of characteristic $0$, for an unramified representation of $\mathrm{GL}_n$ the doubling zeta integral of the normalised spherical section against the zonal spherical function converges for $\operatorname{Re}s$ large and is given by the expected quotient of local $L$-factors. *The unramified computation of the doubling integral for $\mathrm{GL}_n$; stated in characteristic $0$.* | general | ([Piatetski-Shapiro and Rallis 1987](#ref-piatetskishapiro1987lfunctions)) |
|  | For a Hermitian line bundle on an arithmetic variety that is nef on fibres with semipositive metric, the arithmetic volume is at least the arithmetic self-intersection number. *The lower bound for the arithmetic volume of a nef Hermitian line bundle.* | general | ([Gillet and Soulé 1992](#ref-gillet1992arithmetic); [Zhang 1995](#ref-zhang1995positive); [Moriwaki 2009](#ref-moriwaki2009continuity)) |
|  | For an arithmetically nef Hermitian line bundle, the arithmetic volume equals the arithmetic self-intersection number. *Moriwaki's equality.* | general | ([Moriwaki 2009](#ref-moriwaki2009continuity); [Zhang 1995](#ref-zhang1995positive)) |
|  | For $K$ imaginary quadratic of discriminant less than $-4$, the field generated over $K$ by the values of the Weber function at the $n$-torsion points of $\mathbb{C}/\mathcal{O}_K$ is the ray class field of conductor $n$. *Ray class fields of imaginary quadratic fields by values of the Weber function.* | general | ([Hasse 1927](#ref-hasse1927neue); [Shimura 1971](#ref-shimura1971introduction)) |
|  | For a Hermitian and a skew-Hermitian space over a CM extension and Hecke characters with the right restrictions, a Weil representation of the product of the two adelic unitary groups exists. *Existence of the Weil representation of a unitary dual pair.* | general | ([Weil 1964](#ref-weil1964certains); [Kudla 1994](#ref-kudla1994splitting)) |
|  | The same in the notation of the archive's base data. *The same.* | general | ([Weil 1964](#ref-weil1964certains); [Kudla 1994](#ref-kudla1994splitting)) |
|  | Weil's formula for unitary groups: under Weil's condition the theta integral is bounded by a continuous seminorm and converges, and in the range $2n<m$ it equals the Siegel Eisenstein series. *Weil's formula in his range.* | general | ([Weil 1965](#ref-weil1965formule)) |
|  | The restriction to $\mathrm{GL}_n(\mathbb{C})$, and to $\mathrm{U}(n)$, of the irreducible representation of $\mathrm{GL}_{n+1}(\mathbb{C})$ of highest weight $\lambda$ is the multiplicity-free sum over the weights interlacing $\lambda$. *Weyl's branching rule.* | general | ([Weyl 1946](#ref-weyl1946classical)) |
|  | Every abelian scheme has a dual abelian scheme of the same relative dimension, with a Poincaré bundle exhibiting each as the dual of the other. *Existence of the dual abelian scheme.* | general | ([Mumford 1965](#ref-mumford1965geometric); [Faltings and Chai 1990](#ref-faltings1990degeneration)) |
|  | Over the valuation ring of an algebraically closed non-archimedean field, an abelian scheme with a relatively ample line bundle is a retract of a principally polarised one. *Over the valuation ring of an algebraically closed non-archimedean field.* | restricted | ([Zarhin 1977](#ref-zarhin1977endomorphisms); [Moret-Bailly 1985](#ref-moretbailly1985pinceaux)) |
|  | For a $p$-divisible group over the ring of integers of a complete algebraically closed field of characteristic $0$: the kernel of the Hodge--Tate map is the annihilator, under the pairing induced by the Weil pairing, of the corresponding part of the dual. *The statement of Fargues on the kernel of the Hodge--Tate map.* | general | ([Fargues 2008](#ref-fargues2008isomorphisme); [Tate 1967c](#ref-tate1967pdivisible)) |
|  | An asymptotic Riemann--Roch statement for a divisor class that is nef on the generic fibre of an arithmetic variety: $D!\,\dim H^0(\tau a)/\tau^{D}$ tends to the generic degree. *The asymptotic Riemann--Roch statement of `NefNumerics`, on the generic fibre of an arithmetic variety.* | restricted | ([Lazarsfeld 2004](#ref-lazarsfeld2004positivity); [Kleiman 1966](#ref-kleiman1966toward)) |
|  | A Poincaré--Lelong formula on an arithmetic variety: the integral of $\log\lVert s\rVert$ against Chern forms equals a sum over the horizontal components of the divisor of $s$, with a correction. *A form of the Poincaré--Lelong formula used for heights; its exact shape was not compared with a published formula.* | restricted | ([Lelong 1957](#ref-lelong1957integration); [Bost et al. 1994](#ref-bost1994heights)) |
|  | For a smooth separated quasi-compact scheme over a field of characteristic $0$, an ideal sheaf and a divisor with simple normal crossings: a sequence of blow-ups in smooth centres having normal crossings with the divisor makes the ideal an effective Cartier divisor with simple normal crossings. *Principalisation compatible with a divisor with simple normal crossings.* | general | ([Hironaka 1964a](#ref-hironaka1964resolution), [1964b](#ref-hironaka1964resolutionII); [Kollár 2007](#ref-kollar2007lectures)) |
|  | Every reduced separated scheme of finite type over a field of characteristic $0$ has a resolution by a sequence of blow-ups that is an isomorphism over the smooth locus, the preimage of the singular locus being a divisor with simple normal crossings. *Hironaka's theorem.* | general | ([Hironaka 1964a](#ref-hironaka1964resolution), [1964b](#ref-hironaka1964resolutionII); [Kollár 2007](#ref-kollar2007lectures)) |
|  | For a number field $F$, an open normal subgroup $U$ of $G_F$, $g\in G_F$ and a finite set of primes: there is a prime outside the set, of degree one and unramified over $\mathbb{Q}$, with inertia in $U$ and a Frobenius in $gU$. *An existence statement that follows from the density theorem.* | restricted | ([Tschebotareff 1926](#ref-chebotarev1926bestimmung)) |
|  | Siegel Eisenstein series on the doubled unitary group attached to standard sections converge in a half-plane and continue meromorphically, with poles of finite order. *Siegel Eisenstein series on doubled unitary groups.* | restricted | ([Bernstein and Lapid 2024](#ref-bernstein2024meromorphic); [Langlands 1976](#ref-langlands1976functional)) |
|  | The Siegel--Weil formula for a definite Hermitian or skew-Hermitian space: the Siegel Eisenstein series is holomorphic at $s_0=(m-n)/2$ and its value there is a constant times the theta integral. *The Siegel--Weil formula for a definite space.* | general | ([Weil 1965](#ref-weil1965formule); [Ichino 2007](#ref-ichino2007siegel); [Yamana 2011](#ref-yamana2011siegel)) |
|  | A statement in the archive's own terms: theta integrals attached to matched data agree up to explicit constants. | internal | --- |
|  | For a finite $\ell^r$-torsion Galois module $M$ over a number field unramified outside $S$: Tate's global Euler characteristic formula. *Tate's formula, for $\ell$-power torsion modules.* | general | ([Tate 1963](#ref-tate1963duality); [Milne 1986](#ref-milne1986arithmetic)) |
|  | For a finite $\ell^r$-torsion Galois module $M$ as above: $H^0$, $H^1$ and $H^2$ are finite and the higher groups vanish for $\ell\ne2$. *Finiteness of Galois cohomology with restricted ramification.* | general | ([Tate 1963](#ref-tate1963duality); [Milne 1986](#ref-milne1986arithmetic)) |
|  | For a finite $\ell^r$-torsion Galois module $M$ at a finite place: Tate's local Euler characteristic formula. *Tate's local formula.* | general | ([Tate 1963](#ref-tate1963duality); [Serre 1964](#ref-serre1964cohomologie)) |
|  | For a finite $\ell^r$-torsion Galois module $M$ at a finite place: $H^0$, $H^1$ and $H^2$ are finite and the higher groups vanish. *Finiteness of local Galois cohomology.* | general | ([Tate 1963](#ref-tate1963duality); [Serre 1964](#ref-serre1964cohomologie)) |
|  | For a finite $\ell^r$-torsion Galois module $M$ at a finite place: Tate local duality. *Tate local duality.* | general | ([Tate 1963](#ref-tate1963duality); [Serre 1964](#ref-serre1964cohomologie)) |
|  | For a finite $\ell^r$-torsion Galois module $M$ and local conditions: the formula of Greenberg and Wiles comparing a Selmer group with the dual Selmer group. *The formula of Greenberg and Wiles.* | general | ([Wiles 1995](#ref-wiles1995modular); [Darmon et al. 1995](#ref-darmon1995fermat)) |
|  | For a finite $\ell^r$-torsion Galois module $M$ at a place not above $\ell$ where $M$ is unramified: the unramified classes of $M$ and of its Tate dual are exact annihilators. *Unramified classes are exact annihilators.* | general | ([Serre 1964](#ref-serre1964cohomologie); [Milne 1986](#ref-milne1986arithmetic); [Tate 1963](#ref-tate1963duality)) |
|  | For a non-degenerate Hermitian form of rank $M$ over a CM extension: $[\mathrm{U}(J)]$ has finite volume, and for $2n<M$ the mean of the theta series of frames with a given Gram matrix is the product of the local densities. *Finite volume, and the formula in Weil's range as a mass formula for representation densities.* | general | ([Siegel 1935a](#ref-siegel1935analytische); [Braun 1941](#ref-braun1941theorie); [Weil 1965](#ref-weil1965formule); [Borel and Harish-Chandra 1962](#ref-borel1962arithmetic)) |
|  | For $K/\mathbb{Q}_\ell$ finite and a finite continuous $\ell^r$-torsion module: $\#H^1=\#H^0\cdot\#H^2\cdot\#M^{[K:\mathbb{Q}_\ell]}$. *Tate's local formula for finite extensions of $\mathbb{Q}_\ell$.* | general | ([Tate 1963](#ref-tate1963duality); [Serre 1964](#ref-serre1964cohomologie)) |
|  | For $K/\mathbb{Q}_\ell$ finite and such a module: $H^0$, $H^1$, $H^2$ are finite and $H^n=0$ for $n\ge3$. *Finiteness for finite extensions of $\mathbb{Q}_\ell$.* | general | ([Tate 1963](#ref-tate1963duality); [Serre 1964](#ref-serre1964cohomologie)) |
|  | For $K/\mathbb{Q}_\ell$ finite: $H^2(G_K,\mu_{\ell^r})\cong\mathbb{Z}/\ell^r$ and the cup-product pairings with the Tate dual are perfect. *Tate local duality for finite extensions of $\mathbb{Q}_\ell$.* | general | ([Tate 1963](#ref-tate1963duality); [Serre 1964](#ref-serre1964cohomologie)) |
|  | The conclusion: $L(s,\chi)\ne0$ for every Dirichlet character $\chi$ and every $s$ with $\operatorname{Re}s>\tfrac12$, $s=1$ excluded for trivial $\chi$. The file returns it under the hypothesis of [Statement 8.1](#st:vwin). | conclusion | --- |
|  |  |  |  |

## References

<a id="refs"></a>

<a id="ref-abbes1995theoreme"></a>

Abbes, Ahmed, and Thierry Bouche. 1995. "Théorème de Hilbert-Samuel «Arithmétique»." *Annales de l'Institut Fourier* 45 (2): 375--401. <https://doi.org/10.5802/aif.1458>.

<a id="ref-agrawal2004primes"></a>

Agrawal, Manindra, Neeraj Kayal, and Nitin Saxena. 2004. "PRIMES Is in p." *Annals of Mathematics (2)* 160 (2): 781--93. <https://doi.org/10.4007/annals.2004.160.781>.

<a id="ref-alpoge2026lean"></a>

Alpöge, Levent. 2026a. *\[Lean 4 Source of the Proof, `lean.tar.gz`, in Fourteen Parts\]*. SHA-256 `9631b4f0…49c7fc`. <https://alpo.ge/lean.tar.gz.part01>.

<a id="ref-alpoge2026remark"></a>

Alpöge, Levent. 2026b. *\[Note Announcing a Formal Proof of the Riemann Hypothesis and of GRH for Dirichlet $L$-Functions\]*. Four pages, untitled, dated 20 November 2026. <https://alpo.ge/remark.pdf>.

<a id="ref-andersen1980strong"></a>

Andersen, Henning Haahr. 1980. "The Strong Linkage Principle." *Journal Für Die Reine Und Angewandte Mathematik* 315: 53--59. <https://doi.org/10.1515/crll.1980.315.53>.

<a id="ref-andre2002filtrations"></a>

André, Yves. 2002. "Filtrations de Type Hasse-Arf Et Monodromie $p$-Adique." *Inventiones Mathematicae* 148 (2): 285--317. <https://doi.org/10.1007/s002220100207>.

<a id="ref-angehrn1995effective"></a>

Angehrn, Urban, and Yum-Tong Siu. 1995. "Effective Freeness and Point Separation for Adjoint Bundles." *Inventiones Mathematicae* 122: 291--308. <https://doi.org/10.1007/BF01231446>.

<a id="ref-ankeny1952least"></a>

Ankeny, N. C. 1952. "The Least Quadratic Non Residue." *Annals of Mathematics (2)* 55 (1): 65--72. <https://doi.org/10.2307/1969420>.

<a id="ref-anschutz2023prismatic"></a>

Anschütz, Johannes, and Arthur-César Le Bras. 2023. "Prismatic Dieudonné Theory." *Forum of Mathematics, Pi* 11: e2. <https://doi.org/10.1017/fmp.2022.22>.

<a id="ref-artin1927beweis"></a>

Artin, Emil. 1927. "Beweis Des Allgemeinen Reziprozitätsgesetzes." *Abhandlungen Aus Dem Mathematischen Seminar Der Universität Hamburg* 5 (1): 353--63. <https://doi.org/10.1007/BF02952531>.

<a id="ref-ash1975smooth"></a>

Ash, A., D. Mumford, M. Rapoport, and Y. Tai. 1975. *Smooth Compactification of Locally Symmetric Varieties*. IV. Math Sci Press, Brookline, MA.

<a id="ref-atiyah1977geometric"></a>

Atiyah, Michael, and Wilfried Schmid. 1977. "A Geometric Construction of the Discrete Series for Semisimple Lie Groups." *Inventiones Mathematicae* 42 (1): 1--62. <https://doi.org/10.1007/BF01389783>.

<a id="ref-bach1990explicit"></a>

Bach, Eric. 1990. "Explicit Bounds for Primality Testing and Related Problems." *Mathematics of Computation* 55 (191): 355--80. <https://doi.org/10.1090/S0025-5718-1990-1023756-8>.

<a id="ref-bach1996explicit"></a>

Bach, Eric, and Jonathan Sorenson. 1996. "Explicit Bounds for Primes in Residue Classes." *Mathematics of Computation* 65 (216): 1717--35. <https://doi.org/10.1090/S0025-5718-96-00763-6>.

<a id="ref-barnetlamb2012local"></a>

Barnet-Lamb, Thomas, Toby Gee, David Geraghty, and Richard Taylor. 2012. "Local-Global Compatibility for $\ell=p$, i." *Annales de La Faculté Des Sciences de Toulouse : Mathématiques (6)* 21 (1): 57--92. <https://doi.org/10.5802/afst.1329>.

<a id="ref-barnetlamb2014local"></a>

Barnet-Lamb, Thomas, Toby Gee, David Geraghty, and Richard Taylor. 2014a. "Local-Global Compatibility for $\ell=p$, II." *Annales Scientifiques de l'École Normale Supérieure (4)* 47 (1): 165--79. <https://doi.org/10.24033/asens.2212>.

<a id="ref-barnetlamb2014potential"></a>

Barnet-Lamb, Thomas, Toby Gee, David Geraghty, and Richard Taylor. 2014b. "Potential Automorphy and Change of Weight." *Annals of Mathematics (2)* 179 (2): 501--609. <https://doi.org/10.4007/annals.2014.179.2.3>.

<a id="ref-behrend1946sets"></a>

Behrend, F. A. 1946. "On Sets of Integers Which Contain No Three Terms in Arithmetical Progression." *Proceedings of the National Academy of Sciences of the United States of America* 32 (12): 331--32. <https://doi.org/10.1073/pnas.32.12.331>.

<a id="ref-berger2002representations"></a>

Berger, Laurent. 2002. "Représentations $p$-Adiques Et Équations Différentielles." *Inventiones Mathematicae* 148 (2): 219--84. <https://doi.org/10.1007/s002220100202>.

<a id="ref-bernstein1974all"></a>

Bernstein, I. N. 1974. "All Reductive $p$-Adic Groups Are Tame." *Functional Analysis and Its Applications* 8 (2): 91--93. <https://doi.org/10.1007/BF01078592>.

<a id="ref-bernstein1976representations"></a>

Bernstein, I. N., and A. V. Zelevinsky. 1976. "Representations of the Group $\mathrm{GL}(n,F)$ Where $F$ Is a Non-Archimedean Local Field." *Russian Mathematical Surveys* 31 (3): 1--68. <https://doi.org/10.1070/RM1976v031n03ABEH001532>.

<a id="ref-bernstein1977induced"></a>

Bernstein, I. N., and A. V. Zelevinsky. 1977. "Induced Representations of Reductive $p$-Adic Groups. i." *Annales Scientifiques de l'École Normale Supérieure (4)* 10 (4): 441--72. <https://doi.org/10.24033/asens.1333>.

<a id="ref-bernstein1984pinvariant"></a>

Bernstein, Joseph N. 1984. "$P$-Invariant Distributions on $\mathrm{GL}(N)$ and the Classification of Unitary Representations of $\mathrm{GL}(N)$ (Non-Archimedean Case)." In *Lie Group Representations, II (College Park, Md., 1982/1983)*, vol. 1041. Springer, Berlin (Lecture Notes in Mathematics). <https://doi.org/10.1007/BFb0073145>.

<a id="ref-bernstein2024meromorphic"></a>

Bernstein, Joseph, and Erez Lapid. 2024. "On the Meromorphic Continuation of Eisenstein Series." *Journal of the American Mathematical Society* 37 (1): 187--234. <https://doi.org/10.1090/jams/1020>.

<a id="ref-berthelot1982theorie"></a>

Berthelot, Pierre, Lawrence Breen, and William Messing. 1982. *Théorie de Dieudonné Cristalline. II*. Vol. 930. Springer-Verlag, Berlin (Lecture Notes in Mathematics). <https://doi.org/10.1007/BFb0093025>.

<a id="ref-bhatt2018integral"></a>

Bhatt, Bhargav, Matthew Morrow, and Peter Scholze. 2018. "Integral $p$-Adic Hodge Theory." *Publications Mathématiques de l'IHÉS* 128: 219--397. <https://doi.org/10.1007/s10240-019-00102-z>.

<a id="ref-bhatt2023prismatic"></a>

Bhatt, Bhargav, and Peter Scholze. 2023. "Prismatic $F$-Crystals and Crystalline Galois Representations." *Cambridge Journal of Mathematics* 11 (2): 507--62. <https://doi.org/10.4310/CJM.2023.v11.n2.a3>.

<a id="ref-bloch1990lfunctions"></a>

Bloch, Spencer, and Kazuya Kato. 1990. "$L$-Functions and Tamagawa Numbers of Motives." In *The Grothendieck Festschrift, Vol. I*, vol. 86. Birkhäuser Boston, Boston, MA (Progress in Mathematics). <https://zbmath.org/?q=an:0768.14001>.

<a id="ref-bombieri1965large"></a>

Bombieri, Enrico. 1965. "On the Large Sieve." *Mathematika* 12 (2): 201--25. <https://doi.org/10.1112/S0025579300005313>.

<a id="ref-bombieri1974counting"></a>

Bombieri, Enrico. 1974. "Counting Points on Curves over Finite Fields \[d'après s. A. Stepanov\]." In *Séminaire Bourbaki, Vol. 1972/73, Exposés 418--435*, vol. 383. Springer, Berlin (Lecture Notes in Mathematics). <https://doi.org/10.1007/BFb0057311>.

<a id="ref-borel1969introduction"></a>

Borel, Armand. 1969. *Introduction Aux Groupes Arithmétiques*. Vol. 1341. Hermann & Cie, Paris.

<a id="ref-borel1974stable"></a>

Borel, Armand. 1974. "Stable Real Cohomology of Arithmetic Groups." *Annales Scientifiques de l'École Normale Supérieure (4)* 7 (2): 235--72. <https://doi.org/10.24033/asens.1269>.

<a id="ref-borel1976admissible"></a>

Borel, Armand. 1976. "Admissible Representations of a Semi-Simple Group over a Local Field with Vectors Fixed Under an Iwahori Subgroup." *Inventiones Mathematicae* 35: 233--59. <https://doi.org/10.1007/BF01390139>.

<a id="ref-borel1962arithmetic"></a>

Borel, Armand, and Harish-Chandra. 1962. "Arithmetic Subgroups of Algebraic Groups." *Annals of Mathematics. Second Series* 75 (3): 485--535. <https://doi.org/10.2307/1970210>.

<a id="ref-bost1994heights"></a>

Bost, J.-B., H. Gillet, and C. Soulé. 1994. "Heights of Projective Varieties and Positive Green Forms." *Journal of the American Mathematical Society* 7 (4): 903--1027. <https://doi.org/10.1090/S0894-0347-1994-1260106-X>.

<a id="ref-bost1996periodes"></a>

Bost, Jean-Benoît. 1996. "Périodes Et Isogénies Des Variétés Abéliennes Sur Les Corps de Nombres \[d'après d. Masser Et g. Wüstholz\]." In *Séminaire Bourbaki, Volume 1994/95, Exposés 790--804*, vol. 237. Société Mathématique de France, Paris (Astérisque). <https://www.numdam.org/item/SB_1994-1995__37__115_0/>.

<a id="ref-bost2001algebraic"></a>

Bost, Jean-Benoît. 2001. "Algebraic Leaves of Algebraic Foliations over Number Fields." *Publications Mathématiques de l'IHÉS* 93: 161--221. <https://doi.org/10.1007/s10240-001-8191-3>.

<a id="ref-bost2004germs"></a>

Bost, Jean-Benoît. 2004. "Germs of Analytic Varieties in Algebraic Varieties: Canonical Metrics and Arithmetic Algebraization Theorems." In *Geometric Aspects of Dwork Theory. Vol. I, II (a. Adolphson Et Al., Eds.)*. Walter de Gruyter, Berlin.

<a id="ref-bost2006evaluation"></a>

Bost, Jean-Benoît. 2006. "Evaluation Maps, Slopes, and Algebraicity Criteria." In *Proceedings of the International Congress of Mathematicians (ICM), Madrid, 2006. Volume II: Invited Lectures (m. Sanz-Solé Et Al., Eds.)*. European Mathematical Society (EMS), Zürich.

<a id="ref-brauer1947artin"></a>

Brauer, Richard. 1947. "On Artin's $L$-Series with General Group Characters." *Annals of Mathematics (2)* 48 (2): 502--14. <https://doi.org/10.2307/1969183>.

<a id="ref-braun1941theorie"></a>

Braun, Hel. 1941. "Zur Theorie Der Hermitischen Formen." *Abhandlungen Aus Dem Mathematischen Seminar Der Universität Hamburg* 14: 61--150. <https://doi.org/10.1007/BF02940742>.

<a id="ref-brion1996pushforward"></a>

Brion, Michel. 1996. "The Push-Forward and Todd Class of Flag Bundles." In *Parameter Spaces: Enumerative Geometry, Algebra and Combinatorics (Warsaw, 1994)*, vol. 36. Banach Center Publications. <https://doi.org/10.4064/-36-1-45-50>.

<a id="ref-bushnell2005essentially"></a>

Bushnell, Colin J., and Guy Henniart. 2005. "The Essentially Tame Local Langlands Correspondence, i." *Journal of the American Mathematical Society* 18 (3): 685--710. <https://doi.org/10.1090/S0894-0347-05-00487-X>.

<a id="ref-cao2017general"></a>

Cao, JunYan, Jean-Pierre Demailly, and Shin-ichi Matsumura. 2017. "A General Extension Theorem for Cohomology Classes on Non Reduced Analytic Subspaces." *Science China Mathematics* 60 (6): 949--62. <https://doi.org/10.1007/s11425-017-9066-0>.

<a id="ref-caraiani2012local"></a>

Caraiani, Ana. 2012. "Local-Global Compatibility and the Action of Monodromy on Nearby Cycles." *Duke Mathematical Journal* 161 (12): 2311--413. <https://doi.org/10.1215/00127094-1723706>.

<a id="ref-caraiani2014monodromy"></a>

Caraiani, Ana. 2014. "Monodromy and Local-Global Compatibility for $\ell=p$." *Algebra & Number Theory* 8 (7): 1597--646. <https://doi.org/10.2140/ant.2014.8.1597>.

<a id="ref-lean4lean"></a>

Carneiro, Mario. 2024. *Lean4Lean: Verifying a Typechecker for Lean, in Lean*. arXiv preprint. <https://github.com/digama0/lean4lean>.

<a id="ref-carter1974modular"></a>

Carter, Roger W., and George Lusztig. 1974. "On the Modular Representations of the General Linear and Symmetric Groups." *Mathematische Zeitschrift* 136: 193--242. <https://doi.org/10.1007/BF01214125>.

<a id="ref-casselman1989canonical"></a>

Casselman, W. 1989. "Canonical Extensions of Harish-Chandra Modules to Representations of g." *Canadian Journal of Mathematics* 41 (3): 385--438. <https://doi.org/10.4153/CJM-1989-019-5>.

<a id="ref-casselman1980unramified"></a>

Casselman, William. 1980. "The Unramified Principal Series of $p$-Adic Groups. I. The Spherical Function." *Compositio Mathematica* 40 (3): 387--406. <http://www.numdam.org/item/CM_1980__40_3_387_0/>.

<a id="ref-cassounogues1979valeurs"></a>

Cassou-Noguès, Pierrette. 1979. "Valeurs Aux Entiers Négatifs Des Fonctions Zêta Et Fonctions Zêta $p$-Adiques." *Inventiones Mathematicae* 51 (1): 29--59. <https://doi.org/10.1007/BF01389911>.

<a id="ref-chambertloir2002theoremes"></a>

Chambert-Loir, Antoine. 2002. "Théorèmes d'algébricité En Géométrie Diophantienne \[d'après j.-b. Bost, y. André, d. & g. Chudnovsky\]." In *Séminaire Bourbaki, Volume 2000/2001, Exposés 880--893*, vol. 282. Société Mathématique de France, Paris (Astérisque). <https://www.numdam.org/item/SB_2000-2001__43__175_0/>.

<a id="ref-chenevier2013construction"></a>

Chenevier, Gaëtan, and Michael Harris. 2013. "Construction of Automorphic Galois Representations, II." *Cambridge Journal of Mathematics* 1 (1): 53--73. <https://doi.org/10.4310/CJM.2013.v1.n1.a2>.

<a id="ref-chern1946characteristic"></a>

Chern, Shiing-Shen. 1946. "Characteristic Classes of Hermitian Manifolds." *Annals of Mathematics (2)* 47 (1): 85--121. <https://doi.org/10.2307/1969037>.

<a id="ref-chevalley1940theorie"></a>

Chevalley, Claude. 1940. "La Théorie Du Corps de Classes." *Annals of Mathematics (2)* 41 (2): 394--418. <https://doi.org/10.2307/1969013>.

<a id="ref-chevalley1951deux"></a>

Chevalley, Claude. 1951. "Deux Théorèmes d'arithmétique." *Journal of the Mathematical Society of Japan* 3 (1): 36--44. <https://doi.org/10.2969/jmsj/00310036>.

<a id="ref-chow1937algebraischen"></a>

Chow, Wei-Liang, and B. L. van der Waerden. 1937. "Zur Algebraischen Geometrie. IX. Über Zugeordnete Formen Und Algebraische Systeme von Algebraischen Mannigfaltigkeiten." *Mathematische Annalen* 113 (1): 692--704. <https://doi.org/10.1007/BF01571660>.

<a id="ref-chowla1949epstein"></a>

Chowla, S., and A. Selberg. 1949. "On Epstein's Zeta Function (i)." *Proceedings of the National Academy of Sciences of the United States of America* 35 (7): 371--74. <https://doi.org/10.1073/pnas.35.7.371>.

<a id="ref-clozel1990motifs"></a>

Clozel, Laurent. 1990. "Motifs Et Formes Automorphes: Applications Du Principe de Fonctorialité." In *Automorphic Forms, Shimura Varieties, and $L$-Functions, Vol. I (Ann Arbor, MI, 1988)*, vol. 10. Academic Press, Boston, MA (Perspect. Math.). <https://zbmath.org/?q=an:0705.11029>.

<a id="ref-clozel1991representations"></a>

Clozel, Laurent. 1991. "Représentations Galoisiennes Associées Aux Représentations Automorphes Autoduales de $\mathrm{GL}(n)$." *Publications Mathématiques de l'IHÉS* 73: 97--145. <https://doi.org/10.1007/BF02699257>.

<a id="ref-clozel2011construction"></a>

Clozel, Laurent, Michael Harris, and Jean-Pierre Labesse. 2011. "Construction of Automorphic Galois Representations, i." In *Stabilization of the Trace Formula, Shimura Varieties, and Arithmetic Applications. Volume 1: On the Stabilization of the Trace Formula (l. Clozel, m. Harris, j.-p. Labesse, b.-c. Ngô, Eds.)*. International Press, Somerville, MA. <https://intlpress.com/site/pub/files/preview/bookpubs/00000265.pdf>.

<a id="ref-cramer2016recovering"></a>

Cramer, Ronald, Léo Ducas, Chris Peikert, and Oded Regev. 2016. "Recovering Short Generators of Principal Ideals in Cyclotomic Rings." In *Advances in Cryptology -- EUROCRYPT 2016, Part II*, vol. 9666. Springer, Berlin (Lecture Notes in Computer Science). <https://doi.org/10.1007/978-3-662-49896-5_20>.

<a id="ref-cramer1921some"></a>

Cramér, H. 1921. "Some Theorems Concerning Prime Numbers." *Arkiv För Matematik, Astronomi Och Fysik* 15 (5).

<a id="ref-darmon1995fermat"></a>

Darmon, Henri, Fred Diamond, and Richard Taylor. 1995. "Fermat's Last Theorem." In *Current Developments in Mathematics, 1995*. International Press, Cambridge, MA. <https://doi.org/10.4310/CDM.1995.v1995.n1.a1>.

<a id="ref-davenport1980multiplicative"></a>

Davenport, Harold. 1980. *Multiplicative Number Theory*. Vol. 74. Springer-Verlag, New York (Graduate Texts in Mathematics). <https://doi.org/10.1007/978-1-4757-5927-3>.

<a id="ref-deligne1973constantes"></a>

Deligne, P. 1973. "Les Constantes Des Équations Fonctionnelles Des Fonctions $L$." In *Modular Functions of One Variable II (Proc. Internat. Summer School, Univ. Antwerp, 1972)*, vol. 349. Springer, Berlin (Lecture Notes in Mathematics). <https://doi.org/10.1007/978-3-540-37855-6_7>.

<a id="ref-deligne1980values"></a>

Deligne, Pierre, and Kenneth A. Ribet. 1980. "Values of Abelian $L$-Functions at Negative Integers over Totally Real Fields." *Inventiones Mathematicae* 59 (3): 227--86. <https://doi.org/10.1007/BF01453237>.

<a id="ref-demailly2016extension"></a>

Demailly, Jean-Pierre. 2016. "Extension of Holomorphic Functions Defined on Non Reduced Analytic Subvarieties." In *The Legacy of Bernhard Riemann After One Hundred and Fifty Years. Volume i*, vol. 35. Advanced Lectures in Mathematics (ALM). <https://zbmath.org/?q=an:1360.14025>.

<a id="ref-deuring1941typen"></a>

Deuring, Max. 1941. "Die Typen Der Multiplikatorenringe Elliptischer Funktionenkörper." *Abhandlungen Aus Dem Mathematischen Seminar Der Hansischen Universität* 14: 197--272. <https://doi.org/10.1007/BF02940746>.

<a id="ref-dixmier1978factorisations"></a>

Dixmier, Jacques, and Paul Malliavin. 1978. "Factorisations de Fonctions Et de Vecteurs Indéfiniment Différentiables." *Bull. Sci. Math. (2)* 102 (4): 307--30. <https://zbmath.org/?q=an:0392.43013>.

<a id="ref-dwork1960rationality"></a>

Dwork, Bernard. 1960. "On the Rationality of the Zeta Function of an Algebraic Variety." *American Journal of Mathematics* 82 (3): 631--48. <https://doi.org/10.2307/2372974>.

<a id="ref-faltings1990degeneration"></a>

Faltings, Gerd, and Ching-Li Chai. 1990. *Degeneration of Abelian Varieties*. Vol. 22. Springer, Berlin. <https://doi.org/10.1007/978-3-662-02632-8>.

<a id="ref-fargues2008isomorphisme"></a>

Fargues, Laurent. 2008. "L'isomorphisme Entre Les Tours de Lubin-Tate Et de Drinfeld Au Niveau Des Points." In *L'isomorphisme Entre Les Tours de Lubin-Tate Et de Drinfeld (l. Fargues, a. Genestier, v. Lafforgue), Progress in Mathematics 262*, vol. 262. Birkhäuser, Basel. <https://doi.org/10.1007/978-3-7643-8456-2_3>.

<a id="ref-ferrero1979iwasawa"></a>

Ferrero, Bruce, and Lawrence C. Washington. 1979. "The Iwasawa Invariant $\mu_p$ Vanishes for Abelian Number Fields." *Annals of Mathematics (2)* 109 (2): 377--95. <https://doi.org/10.2307/1971116>.

<a id="ref-flath1979decomposition"></a>

Flath, D. 1979. "Decomposition of Representations into Tensor Products." In *Automorphic Forms, Representations and $L$-Functions (Corvallis, Oregon, 1977), Part 1*, vol. 33. Proceedings of Symposia in Pure Mathematics. <https://doi.org/10.1090/pspum/033.1/546596>.

<a id="ref-fontaine1982certains"></a>

Fontaine, Jean-Marc. 1982. "Sur Certains Types de Représentations $p$-Adiques Du Groupe de Galois d'un Corps Local; Construction d'un Anneau de Barsotti-Tate." *Annals of Mathematics (2)* 115 (3): 529--77. <https://doi.org/10.2307/2007012>.

<a id="ref-fontaine1994corps"></a>

Fontaine, Jean-Marc. 1994a. "Le Corps Des Périodes $p$-Adiques." In *Périodes $p$-Adiques (Séminaire de Bures, 1988)*, vol. 223. Astérisque (Société mathématique de France). <https://www.numdam.org/item/AST_1994__223__59_0/>.

<a id="ref-fontaine1994potentiellement"></a>

Fontaine, Jean-Marc. 1994b. "Représentations $\ell$-Adiques Potentiellement Semi-Stables." In *Périodes $p$-Adiques (Séminaire de Bures-Sur-Yvette, 1988), j.-m. Fontaine (Ed.)*, vol. 223. Société Mathématique de France, Paris (Astérisque). <https://zbmath.org/?q=an:0873.14020>.

<a id="ref-fontaine1994semistables"></a>

Fontaine, Jean-Marc. 1994c. "Représentations $p$-Adiques Semi-Stables." In *Périodes $p$-Adiques (Séminaire de Bures-Sur-Yvette, 1988), j.-m. Fontaine (Ed.)*, vol. 223. Société Mathématique de France, Paris (Astérisque). <http://www.numdam.org/item/AST_1994__223__113_0/>.

<a id="ref-gan2012symplectic"></a>

Gan, Wee Teck, Benedict H. Gross, and Dipendra Prasad. 2012. "Symplectic Local Root Numbers, Central Critical $L$-Values, and Restriction Problems in the Representation Theory of Classical Groups." In *Sur Les Conjectures de Gross Et Prasad. I*, vol. 346. Société Mathématique de France, Paris (Astérisque). <https://www.numdam.org/item/AST_2012__346__1_0/>.

<a id="ref-gelfand1969representation"></a>

Gel'fand, I. M., M. I. Graev, and I. I. Pyatetskii-Shapiro. 1969. *Representation Theory and Automorphic Functions*. W. B. Saunders Co., Philadelphia. <https://zbmath.org/?q=an:0177.18003>.

<a id="ref-gelfand1963automorphic"></a>

Gel'fand, I. M., and I. I. Pyatetskij-Shapiro. 1963. "Automorphic Functions and Representation Theory." *Transactions of the Moscow Mathematical Society* 12: 438--64. <https://zbmath.org/?q=an:0136.07301>.

<a id="ref-gelfand1970representations"></a>

Gel'fand, S. I. 1970. "Representations of the Full Linear Group over a Finite Field." *Mathematics of the USSR-Sbornik* 12 (1): 13--39. <https://doi.org/10.1070/SM1970v012n01ABEH000907>.

<a id="ref-gelbart1987explicit"></a>

Gelbart, Stephen, Ilya Piatetski-Shapiro, and Stephen Rallis. 1987. *Explicit Constructions of Automorphic $L$-Functions*. Vol. 1254. Lecture Notes in Mathematics (Springer-Verlag). <https://doi.org/10.1007/BFb0078125>.

<a id="ref-gelfand1975representations"></a>

Gelfand, I. M., and D. A. Kazhdan. 1975. "Representations of the Group $\mathrm{GL}(n,K)$ Where $K$ Is a Local Field." In *Lie Groups and Their Representations (Proc. Summer School, Bolyai János Math. Soc., Budapest, 1971)*. Halsted Press, New York-Toronto. <https://zbmath.org/?q=an:0348.22011>.

<a id="ref-gillet1990arithmetic"></a>

Gillet, Henri, and Christophe Soulé. 1990. "Arithmetic Intersection Theory." *Publications Mathématiques de l'IHÉS* 72: 93--174. <https://doi.org/10.1007/BF02699132>.

<a id="ref-gillet1992arithmetic"></a>

Gillet, Henri, and Christophe Soulé. 1992. "An Arithmetic Riemann-Roch Theorem." *Inventiones Mathematicae* 110: 473--543. <https://doi.org/10.1007/BF01231343>.

<a id="ref-godement1947orthogonalite"></a>

Godement, R. 1947a. "Sur Les Relations d'orthogonalite de v. Bargmann. I. Résultats Preliminaires." *Comptes Rendus Hebdomadaires Des Séances de l'Académie Des Sciences, Paris* 225: 521--23.

<a id="ref-godement1947demonstration"></a>

Godement, R. 1947b. "Sur Les Relations d'orthogonalite de v. Bargmann. II. Demonstration Générale." *Comptes Rendus Hebdomadaires Des Séances de l'Académie Des Sciences, Paris* 225: 657--59.

<a id="ref-godement1966spectral"></a>

Godement, R. 1966. "The Spectral Decomposition of Cusp-Forms." In *Proceedings of Symposia in Pure Mathematics*, vol. 9. <https://zbmath.org/?q=an:0172.18503>.

<a id="ref-grayson1984reduction"></a>

Grayson, Daniel R. 1984. "Reduction Theory Using Semistability." *Commentarii Mathematici Helvetici* 59: 600--634. <https://doi.org/10.1007/BF02566369>.

<a id="ref-green1955characters"></a>

Green, James A. 1955. "The Characters of the Finite General Linear Groups." *Transactions of the American Mathematical Society* 80 (2): 402--47. <https://doi.org/10.1090/S0002-9947-1955-0072878-2>.

<a id="ref-griffiths1970periods"></a>

Griffiths, Phillip A. 1970. "Periods of Integrals on Algebraic Manifolds, III (Some Global Differential-Geometric Properties of the Period Mapping)." *Publications Mathématiques de l'IHÉS* 38: 125--80. <https://doi.org/10.1007/BF02684654>.

<a id="ref-gross1980arithmetic"></a>

Gross, Benedict H. 1980. *Arithmetic on Elliptic Curves with Complex Multiplication*. Vol. 776. Springer-Verlag, Berlin (Lecture Notes in Mathematics). <https://doi.org/10.1007/BFb0096754>.

<a id="ref-gross1982minimal"></a>

Gross, Benedict H. 1982. "Minimal Models for Elliptic Curves with Complex Multiplication." *Compositio Mathematica* 45 (2): 155--64. <http://www.numdam.org/item/CM_1982__45_2_155_0/>.

<a id="ref-gross1999algebraic"></a>

Gross, Benedict H. 1999. "Algebraic Modular Forms." *Israel Journal of Mathematics* 113: 61--93. <https://doi.org/10.1007/BF02780173>.

<a id="ref-grothendieck1971groupes"></a>

Grothendieck, A. 1971. "Groupes de Barsotti-Tate Et Cristaux." In *Actes Congr. Internat. Math. 1970, Tome 1*. Actes du Congrès International des Mathématiciens (1970). <https://zbmath.org/?q=an:0244.14016>.

<a id="ref-grothendieck1961elements"></a>

Grothendieck, Alexander. 1961. "Éléments de Géométrie Algébrique : III. Étude Cohomologique Des Faisceaux Cohérents, Première Partie." *Publications Mathématiques de l'IHÉS* 11: 5--167. <https://doi.org/10.1007/BF02684273>.

<a id="ref-grothendieck1972groupes"></a>

Grothendieck, Alexander, M. Raynaud, and D. S. Rim. 1972. *Groupes de Monodromie En Géométrie Algébrique (SGA 7 i)*. Vol. 288. Springer, Berlin. <https://doi.org/10.1007/BFb0068688>.

<a id="ref-harder1975cohomology"></a>

Harder, G., and M. S. Narasimhan. 1975. "On the Cohomology Groups of Moduli Spaces of Vector Bundles on Curves." *Mathematische Annalen* 212: 215--48. <https://doi.org/10.1007/BF01357141>.

<a id="ref-harishchandra1953representations"></a>

Harish-Chandra. 1953. "Representations of a Semisimple Lie Group on a Banach Space. i." *Transactions of the American Mathematical Society* 75 (2): 185--243. <https://doi.org/10.1090/S0002-9947-1953-0056610-2>.

<a id="ref-harishchandra1954representations2"></a>

Harish-Chandra. 1954a. "Representations of Semisimple Lie Groups. II." *Transactions of the American Mathematical Society* 76 (1): 26--65. <https://doi.org/10.1090/S0002-9947-1954-0058604-0>.

<a id="ref-harishchandra1954representations3"></a>

Harish-Chandra. 1954b. "Representations of Semisimple Lie Groups. III." *Transactions of the American Mathematical Society* 76 (2): 234--53. <https://doi.org/10.1090/S0002-9947-1954-0062747-5>.

<a id="ref-harishchandra1955representations4"></a>

Harish-Chandra. 1955. "Representations of Semisimple Lie Groups. IV." *American Journal of Mathematics* 77 (4): 743--77. <https://doi.org/10.2307/2372596>.

<a id="ref-harishchandra1956representations5"></a>

Harish-Chandra. 1956a. "Representations of Semisimple Lie Groups. v." *American Journal of Mathematics* 78 (1): 1--41. <https://doi.org/10.2307/2372481>.

<a id="ref-harishchandra1956representations6"></a>

Harish-Chandra. 1956b. "Representations of Semisimple Lie Groups. VI. Integrable and Square-Integrable Representations." *American Journal of Mathematics* 78 (3): 564--628. <https://doi.org/10.2307/2372674>.

<a id="ref-harishchandra1965discrete"></a>

Harish-Chandra. 1965. "Discrete Series for Semisimple Lie Groups. I. Construction of Invariant Eigendistributions." *Acta Mathematica* 113: 241--318. <https://doi.org/10.1007/BF02391779>.

<a id="ref-harishchandra1966discrete"></a>

Harish-Chandra. 1966. "Discrete Series for Semisimple Lie Groups. II. Explicit Determination of the Characters." *Acta Mathematica* 116: 1--111. <https://doi.org/10.1007/BF02392813>.

<a id="ref-harishchandra1968automorphic"></a>

Harish-Chandra. 1968. *Automorphic Forms on Semisimple Lie Groups*. Vol. 62. Springer-Verlag, Berlin (Lecture Notes in Mathematics). <https://doi.org/10.1007/BFb0098434>.

<a id="ref-harris1996theta"></a>

Harris, Michael, Stephen S. Kudla, and William J. Sweet. 1996. "Theta Dichotomy for Unitary Groups." *Journal of the American Mathematical Society* 9 (4): 941--1004. <https://doi.org/10.1090/S0894-0347-96-00198-1>.

<a id="ref-harris2001geometry"></a>

Harris, Michael, and Richard Taylor. 2001. *The Geometry and Cohomology of Some Simple Shimura Varieties*. Vol. 151. Princeton University Press, Princeton, NJ (Annals of Mathematics Studies). <https://doi.org/10.1515/9781400837205>.

<a id="ref-hasse1924darstellbarkeit"></a>

Hasse, Helmut. 1924. "Darstellbarkeit von Zahlen Durch Quadratische Formen in Einem Beliebigen Algebraischen Zahlkörper." *Journal Für Die Reine Und Angewandte Mathematik* 153: 113--30. <https://doi.org/10.1515/crll.1924.153.113>.

<a id="ref-hasse1927neue"></a>

Hasse, Helmut. 1927. "Neue Begründung Der Komplexen Multiplikation. Erster Teil: Einordnung in Die Allgemeine Klassenkörpertheorie." *Journal Für Die Reine Und Angewandte Mathematik* 157: 115--39. <https://doi.org/10.1515/crll.1927.157.115>.

<a id="ref-hasse1931beweis"></a>

Hasse, Helmut. 1931. "Beweis Eines Satzes Und Widerlegung Einer Vermutung Über Das Allgemeine Normenrestsymbol." *Nachrichten von Der Gesellschaft Der Wissenschaften Zu Göttingen. Mathematisch-Physikalische Klasse* 1931: 64--69. <https://zbmath.org/?q=an:0003.19902>.

<a id="ref-hecke1917zetafunktion"></a>

Hecke, E. 1917. "Über Die Zetafunktion Beliebiger Algebraischer Zahlkörper." *Nachrichten von Der Gesellschaft Der Wissenschaften Zu Göttingen, Mathematisch-Physikalische Klasse* 1917: 77--89. <https://eudml.org/doc/58974>.

<a id="ref-hecke1918neue"></a>

Hecke, E. 1918. "Eine Neue Art von Zetafunktionen Und Ihre Beziehungen Zur Verteilung Der Primzahlen." *Mathematische Zeitschrift* 1 (4): 357--76. <https://doi.org/10.1007/BF01465095>.

<a id="ref-hecke1920neue"></a>

Hecke, E. 1920. "Eine Neue Art von Zetafunktionen Und Ihre Beziehungen Zur Verteilung Der Primzahlen." *Mathematische Zeitschrift* 6 (1-2): 11--51. <https://doi.org/10.1007/BF01202991>.

<a id="ref-henniart1993caracterisation"></a>

Henniart, Guy. 1993. "Caractérisation de La Correspondance de Langlands Locale Par Les Facteurs $\varepsilon$ de Paires." *Inventiones Mathematicae* 113 (2): 339--50. <https://doi.org/10.1007/BF01244309>.

<a id="ref-henniart2000preuve"></a>

Henniart, Guy. 2000. "Une Preuve Simple Des Conjectures de Langlands Pour $\mathrm{GL}(n)$ Sur Un Corps $p$-Adique." *Inventiones Mathematicae* 139 (2): 439--55. <https://doi.org/10.1007/s002220050012>.

<a id="ref-hida1986galois"></a>

Hida, Haruzo. 1986. "Galois Representations into $\mathrm{GL}_2(\mathbb{Z}_p[[X]])$ Attached to Ordinary Cusp Forms." *Inventiones Mathematicae* 85 (3): 545--613. <https://doi.org/10.1007/BF01390329>.

<a id="ref-hilbert1899theorie"></a>

Hilbert, David. 1899. "Ueber Die Theorie Des Relativquadratischen Zahlkörpers." *Mathematische Annalen* 51: 1--127. <https://doi.org/10.1007/BF01905120>.

<a id="ref-hironaka1964resolution"></a>

Hironaka, Heisuke. 1964a. "Resolution of Singularities of an Algebraic Variety over a Field of Characteristic Zero: i." *Annals of Mathematics (2)* 79 (1): 109--203. <https://doi.org/10.2307/1970486>.

<a id="ref-hironaka1964resolutionII"></a>

Hironaka, Heisuke. 1964b. "Resolution of Singularities of an Algebraic Variety over a Field of Characteristic Zero: II." *Annals of Mathematics (2)* 79 (2): 205--326. <https://doi.org/10.2307/1970547>.

<a id="ref-honda1970theory"></a>

Honda, Taira. 1970. "On the Theory of Commutative Formal Groups." *Journal of the Mathematical Society of Japan* 22 (2): 213--46. <https://doi.org/10.2969/jmsj/02220213>.

<a id="ref-howe1989remarks"></a>

Howe, Roger. 1989a. "Remarks on Classical Invariant Theory." *Transactions of the American Mathematical Society* 313 (2): 539--70. <https://doi.org/10.1090/S0002-9947-1989-0986027-X>.

<a id="ref-howe1989transcending"></a>

Howe, Roger. 1989b. "Transcending Classical Invariant Theory." *Journal of the American Mathematical Society* 2 (3): 535--52. <https://doi.org/10.1090/S0894-0347-1989-0985172-6>.

<a id="ref-ichino2004regularized"></a>

Ichino, Atsushi. 2004. "A Regularized Siegel-Weil Formula for Unitary Groups." *Mathematische Zeitschrift* 247 (2): 241--77. <https://doi.org/10.1007/s00209-003-0580-5>.

<a id="ref-ichino2007siegel"></a>

Ichino, Atsushi. 2007. "On the Siegel--Weil Formula for Unitary Groups." *Mathematische Zeitschrift* 255 (4): 721--29. <https://doi.org/10.1007/s00209-006-0045-8>.

<a id="ref-ikeda1996residue"></a>

Ikeda, Tamotsu. 1996. "On the Residue of the Eisenstein Series and the Siegel-Weil Formula." *Compositio Mathematica* 103 (2): 183--218. <https://www.numdam.org/item/CM_1996__103_2_183_0/>.

<a id="ref-iwasawa1973extensions"></a>

Iwasawa, Kenkichi. 1973. "On $\mathbb{Z}_\ell$-Extensions of Algebraic Number Fields." *Annals of Mathematics (2)* 98 (2): 246--326. <https://doi.org/10.2307/1970784>.

<a id="ref-jacobowitz1962hermitian"></a>

Jacobowitz, Ronald. 1962. "Hermitian Forms over Local Fields." *American Journal of Mathematics* 84 (3): 441--65. <https://doi.org/10.2307/2372982>.

<a id="ref-jacquet1975representations"></a>

Jacquet, Hervé. 1975. "Sur Les Représentations Des Groupes Réductifs $p$-Adiques." *C. R. Acad. Sci. Paris Sér. A-B* 280: A1271--72. <https://zbmath.org/?q=an:0309.22012>.

<a id="ref-jacquet1977generic"></a>

Jacquet, Hervé. 1977. "Generic Representations." In *Non-Commutative Harmonic Analysis (Actes Colloq., Marseille-Luminy, 1976)*, vol. 587. Springer, Berlin (Lecture Notes in Mathematics). <https://doi.org/10.1007/BFb0087916>.

<a id="ref-jacquet1981eulerII"></a>

Jacquet, H., and J. A. Shalika. 1981a. "On Euler Products and the Classification of Automorphic Forms. II." *American Journal of Mathematics* 103 (4): 777--815. <https://doi.org/10.2307/2374050>.

<a id="ref-jacquet1981eulerI"></a>

Jacquet, H., and J. A. Shalika. 1981b. "On Euler Products and the Classification of Automorphic Representations. i." *American Journal of Mathematics* 103 (3): 499--558. <https://doi.org/10.2307/2374103>.

<a id="ref-jantzen2003representations"></a>

Jantzen, Jens Carsten. 2003. *Representations of Algebraic Groups*. Vol. 107. Mathematical Surveys; Monographs (American Mathematical Society). <https://zbmath.org/?q=an:1034.20041>.

<a id="ref-jiang2010uniqueness"></a>

Jiang, Dihua, Binyong Sun, and Chen-Bo Zhu. 2010. "Uniqueness of Bessel Models: The Archimedean Case." *Geometric and Functional Analysis* 20 (3): 690--709. <https://doi.org/10.1007/s00039-010-0077-4>.

<a id="ref-kato2004padic"></a>

Kato, Kazuya. 2004. "$p$-Adic Hodge Theory and Values of Zeta Functions of Modular Forms." In *Cohomologies $p$-Adiques Et Applications Arithmétiques (III)*, vol. 295. Société Mathématique de France, Paris (Astérisque). <https://www.numdam.org/item/AST_2004__295__117_0/>.

<a id="ref-kawamata1982generalization"></a>

Kawamata, Yujiro. 1982. "A Generalization of Kodaira-Ramanujam's Vanishing Theorem." *Mathematische Annalen* 261 (1): 43--46. <https://doi.org/10.1007/BF01456407>.

<a id="ref-kedlaya2004padic"></a>

Kedlaya, Kiran S. 2004. "A $p$-Adic Local Monodromy Theorem." *Annals of Mathematics (2)* 160 (1): 93--184. <https://doi.org/10.4007/annals.2004.160.93>.

<a id="ref-kleiman1966toward"></a>

Kleiman, Steven L. 1966. "Toward a Numerical Theory of Ampleness." *Annals of Mathematics. Second Series* 84 (3): 293--344. <https://doi.org/10.2307/1970447>.

<a id="ref-klingen1962werte"></a>

Klingen, Helmut. 1962. "Über Die Werte Der Dedekindschen Zetafunktion." *Mathematische Annalen* 145 (3): 265--72. <https://doi.org/10.1007/BF01451369>.

<a id="ref-kneser1965starke"></a>

Kneser, Martin. 1965. "Starke Approximation in Algebraischen Gruppen. i." *Journal Für Die Reine Und Angewandte Mathematik* 218: 190--203. <https://doi.org/10.1515/crll.1965.218.190>.

<a id="ref-vonkoch1901distribution"></a>

Koch, Helge von. 1901. "Sur La Distribution Des Nombres Premiers." *Acta Mathematica* 24: 159--82. <https://doi.org/10.1007/BF02403071>.

<a id="ref-kollar1997singularities"></a>

Kollár, János. 1997. "Singularities of Pairs." In *Algebraic Geometry (Proceedings of the Summer Research Institute, Santa Cruz, CA, 1995), Proc. Sympos. Pure Math. 62, Part 1*. 62 (Part 1). American Mathematical Society, Providence, RI. <https://arxiv.org/abs/alg-geom/9601026>.

<a id="ref-kollar2007lectures"></a>

Kollár, János. 2007. *Lectures on Resolution of Singularities*. Vol. 166. Princeton University Press, Princeton, NJ. <https://doi.org/10.1515/9781400827800>.

<a id="ref-kolyvagin1990euler"></a>

Kolyvagin, V. A. 1990. "Euler Systems." In *The Grothendieck Festschrift, Vol. II*, vol. 87. Birkhäuser, Boston (Progress in Mathematics).

<a id="ref-kudla1994splitting"></a>

Kudla, Stephen S. 1994. "Splitting Metaplectic Covers of Dual Reductive Pairs." *Israel Journal of Mathematics* 87 (1-3): 361--401. <https://doi.org/10.1007/BF02773003>.

<a id="ref-kurihara1992remarks"></a>

Kurihara, Masato. 1992. "Some Remarks on Conjectures about Cyclotomic Fields and k-Groups of z." *Compositio Mathematica* 81 (2): 223--36. <https://www.numdam.org/item/CM_1992__81_2_223_0/>.

<a id="ref-labesse2011changement"></a>

Labesse, J.-P. 2011. "Changement de Base CM Et Séries Discrètes." In *On the Stabilization of the Trace Formula (Stabilization of the Trace Formula, Shimura Varieties, and Arithmetic Applications, Vol. 1), l. Clozel, m. Harris, j.-p. Labesse, b.-c. Ngô (Eds.)*, vol. 1. International Press, Somerville, MA. <https://zbmath.org/?q=an:1255.11027>.

<a id="ref-lan2013arithmetic"></a>

Lan, Kai-Wen. 2013. *Arithmetic Compactifications of PEL-Type Shimura Varieties*. Vol. 36. Princeton University Press, Princeton, NJ. <https://doi.org/10.23943/princeton/9780691156545.001.0001>.

<a id="ref-landau1903neuer"></a>

Landau, Edmund. 1903. "Neuer Beweis Des Primzahlsatzes Und Beweis Des Primidealsatzes." *Mathematische Annalen* 56 (4): 645--70. <https://doi.org/10.1007/BF01444310>.

<a id="ref-landau1905tschebyschef"></a>

Landau, Edmund. 1905. "Über Einen Satz von Tschebyschef." *Mathematische Annalen* 61 (4): 527--50. <https://doi.org/10.1007/BF01449495>.

<a id="ref-landherr1936aquivalenz"></a>

Landherr, Walther. 1936. "Äquivalenz Hermitescher Formen Über Einem Beliebigen Algebraischen Zahlkörper." *Abhandlungen Aus Dem Mathematischen Seminar Der Universität Hamburg* 11 (1): 245--48. <https://doi.org/10.1007/BF02940728>.

<a id="ref-langlands1976functional"></a>

Langlands, Robert P. 1976. *On the Functional Equations Satisfied by Eisenstein Series*. Vol. 544. Lecture Notes in Mathematics (Springer-Verlag). <https://doi.org/10.1007/BFb0079929>.

<a id="ref-lazarsfeld2004positivity"></a>

Lazarsfeld, Robert. 2004. *Positivity in Algebraic Geometry. I. Classical Setting: Line Bundles and Linear Series*. Vol. 48. Springer, Berlin. <https://doi.org/10.1007/978-3-642-18808-4>.

<a id="ref-dirichlet1837beweis"></a>

Lejeune-Dirichlet, P. G. 1837. "Beweis Des Satzes, Dass Jede Unbegrenzte Arithmetische Progression, Deren Erstes Glied Und Differenz Ganze Zahlen Ohne Gemeinschaftlichen Factor Sind, Unendlich Viele Primzahlen Enthält." *Abhandlungen Der Königlichen Akademie Der Wissenschaften in Berlin* 1837: 45--81. <http://hdl.handle.net/2027/chi.56785536>.

<a id="ref-lelong1957integration"></a>

Lelong, Pierre. 1957. "Intégration Sur Un Ensemble Analytique Complexe." *Bulletin de La Société Mathématique de France* 85: 239--62. <https://doi.org/10.24033/bsmf.1488>.

<a id="ref-li1992nonvanishing"></a>

Li, Jian-Shu. 1992. "Non-Vanishing Theorems for the Cohomology of Certain Arithmetic Quotients." *Journal Für Die Reine Und Angewandte Mathematik* 428: 177--217. <https://doi.org/10.1515/crll.1992.428.177>.

<a id="ref-linnik1944least1"></a>

Linnik, Yu. V. 1944a. "On the Least Prime in an Arithmetic Progression. I. The Basic Theorem." *Matematicheskiĭ Sbornik. Novaya Seriya* 15(57): 139--78. <https://zbmath.org/?q=an:0063.03584>.

<a id="ref-linnik1944least2"></a>

Linnik, Yu. V. 1944b. "On the Least Prime in an Arithmetic Progression. II. The Deuring-Heilbronn Theorem." *Matematicheskiĭ Sbornik. Novaya Seriya* 15(57): 347--68. <https://zbmath.org/?q=an:0063.03585>.

<a id="ref-lubin1965formal"></a>

Lubin, Jonathan, and John Tate. 1965. "Formal Complex Multiplication in Local Fields." *Annals of Mathematics (2)* 81 (2): 380--87. <https://doi.org/10.2307/1970622>.

<a id="ref-mackey1949theorem"></a>

Mackey, George W. 1949. "A Theorem of Stone and von Neumann." *Duke Mathematical Journal* 16 (2): 313--26. <https://doi.org/10.1215/S0012-7094-49-01631-2>.

<a id="ref-mazur1974universal"></a>

Mazur, Barry, and William Messing. 1974. *Universal Extensions and One Dimensional Crystalline Cohomology*. Vol. 370. Springer-Verlag, Berlin (Lecture Notes in Mathematics). <https://doi.org/10.1007/BFb0061628>.

<a id="ref-mazur1984class"></a>

Mazur, B., and A. Wiles. 1984. "Class Fields of Abelian Extensions of q." *Inventiones Mathematicae* 76 (2): 179--330. <https://doi.org/10.1007/BF01388599>.

<a id="ref-mebkhout2002analogue"></a>

Mebkhout, Z. 2002. "Analogue $p$-Adique Du Théorème de Turrittin Et Le Théorème de La Monodromie $p$-Adique." *Inventiones Mathematicae* 148 (2): 319--51. <https://doi.org/10.1007/s002220100208>.

<a id="ref-messing1972crystals"></a>

Messing, William. 1972. *The Crystals Associated to Barsotti-Tate Groups: With Applications to Abelian Schemes*. Vol. 264. Lecture Notes in Mathematics (Springer-Verlag). <https://doi.org/10.1007/BFb0058301>.

<a id="ref-miller1976riemann"></a>

Miller, Gary L. 1976. "Riemann's Hypothesis and Tests for Primality." *Journal of Computer and System Sciences* 13 (3): 300--317. <https://doi.org/10.1016/S0022-0000(76)80043-8>.

<a id="ref-milne1986arithmetic"></a>

Milne, J. S. 1986. *Arithmetic Duality Theorems*. Vol. 1. Academic Press, Boston.

<a id="ref-minkowski1887theorie"></a>

Minkowski, Hermann. 1887. "Zur Theorie Der Positiven Quadratischen Formen." *Journal Für Die Reine Und Angewandte Mathematik* 101: 196--202. <https://doi.org/10.1515/crll.1887.101.196>.

<a id="ref-moeglin1994decomposition"></a>

Moeglin, Colette, and Jean-Loup Waldspurger. 1994. *Décomposition Spectrale Et Séries d'eisenstein. Une Paraphrase de l'écriture*. Vol. 113. Birkhäuser Verlag, Basel (Progress in Mathematics). <https://zbmath.org/?q=an:0794.11022>.

<a id="ref-moeglin1995spectral"></a>

Moeglin, C., and J.-L. Waldspurger. 1995. *Spectral Decomposition and Eisenstein Series*. Vol. 113. Cambridge University Press. <https://doi.org/10.1017/CBO9780511470905>.

<a id="ref-moeglin1987correspondances"></a>

Mœglin, Colette, Marie-France Vignéras, and Jean-Loup Waldspurger. 1987. *Correspondances de Howe Sur Un Corps $p$-Adique*. Vol. 1291. Springer, Berlin. <https://doi.org/10.1007/BFb0082712>.

<a id="ref-montgomery2007multiplicative"></a>

Montgomery, Hugh L., and Robert C. Vaughan. 2007. *Multiplicative Number Theory i: Classical Theory*. Vol. 97. Cambridge University Press, Cambridge (Cambridge Studies in Advanced Mathematics). <https://doi.org/10.1017/CBO9780511618314>.

<a id="ref-moretbailly1985pinceaux"></a>

Moret-Bailly, Laurent. 1985. *Pinceaux de Variétés Abéliennes*. Vol. 129. Société Mathématique de France, Paris.

<a id="ref-moriwaki2009continuity"></a>

Moriwaki, Atsushi. 2009. "Continuity of Volumes on Arithmetic Varieties." *Journal of Algebraic Geometry* 18 (3): 407--57. <https://doi.org/10.1090/S1056-3911-08-00500-6>.

<a id="ref-lean4checker"></a>

Morrison, Kim, and Sebastian Ullrich. 2023. *Lean4checker*. GitHub repository leanprover/lean4checker. <https://github.com/leanprover/lean4checker>.

<a id="ref-demoura2021lean4"></a>

Moura, Leonardo de, and Sebastian Ullrich. 2021. "The Lean 4 Theorem Prover and Programming Language." In *Automated Deduction -- CADE 28*, vol. 12699. Springer, Cham (Lecture Notes in Computer Science). <https://doi.org/10.1007/978-3-030-79876-5_37>.

<a id="ref-moy1994unrefined"></a>

Moy, Allen, and Gopal Prasad. 1994. "Unrefined Minimal $K$-Types for $p$-Adic Groups." *Inventiones Mathematicae* 116 (1-3): 393--408. <https://doi.org/10.1007/BF01231566>.

<a id="ref-moy1996jacquet"></a>

Moy, Allen, and Gopal Prasad. 1996. "Jacquet Functors and Unrefined Minimal $K$-Types." *Commentarii Mathematici Helvetici* 71 (1): 98--121. <https://doi.org/10.1007/BF02566411>.

<a id="ref-mumford1965geometric"></a>

Mumford, D. 1965. *Geometric Invariant Theory*. Vol. 34. Springer, Berlin.

<a id="ref-mumford1977hirzebruch"></a>

Mumford, D. 1977. "Hirzebruch's Proportionality Theorem in the Non-Compact Case." *Inventiones Mathematicae* 42 (1): 239--72. <https://doi.org/10.1007/BF01389790>.

<a id="ref-mumford1970abelian"></a>

Mumford, David. 1970. *Abelian Varieties*. Vol. 5. Oxford University Press, London (Tata Institute of Fundamental Research Studies in Mathematics). <https://zbmath.org/?q=an:0223.14022>.

<a id="ref-nadel1990multiplier"></a>

Nadel, Alan Michael. 1990. "Multiplier Ideal Sheaves and Kähler-Einstein Metrics of Positive Scalar Curvature." *Annals of Mathematics. Second Series* 132 (3): 549--96. <https://doi.org/10.2307/1971429>.

<a id="ref-vonneumann1931eindeutigkeit"></a>

Neumann, J. von. 1931. "Die Eindeutigkeit Der Schrödingerschen Operatoren." *Mathematische Annalen* 104: 570--78. <https://doi.org/10.1007/BF01457956>.

<a id="ref-oda1969first"></a>

Oda, Tadao. 1969. "The First de Rham Cohomology Group and Dieudonné Modules." *Annales Scientifiques de l'École Normale Supérieure (4)* 2 (1): 63--135. <https://doi.org/10.24033/asens.1175>.

<a id="ref-ohsawa1987extension"></a>

Ohsawa, Takeo, and Kensho Takegoshi. 1987. "On the Extension of $L^2$ Holomorphic Functions." *Mathematische Zeitschrift* 195 (2): 197--204. <https://doi.org/10.1007/BF01166457>.

<a id="ref-page1935number"></a>

Page, A. 1935. "On the Number of Primes in an Arithmetic Progression." *Proceedings of the London Mathematical Society (2)* 39: 116--41. <https://doi.org/10.1112/plms/s2-39.1.116>.

<a id="ref-piatetskishapiro1979multiplicity"></a>

Piatetski-Shapiro, I. I. 1979. "Multiplicity One Theorems." In *Automorphic Forms, Representations and $L$-Functions (Corvallis, Oregon, 1977), Part 1*, vol. 33. Proceedings of Symposia in Pure Mathematics. <https://doi.org/10.1090/pspum/033.1/546599>.

<a id="ref-piatetskishapiro1987lfunctions"></a>

Piatetski-Shapiro, I., and S. Rallis. 1987. "$L$-Functions for the Classical Groups." In *Explicit Constructions of Automorphic $L$-Functions (s. Gelbart, i. Piatetski-Shapiro, s. Rallis), Lecture Notes in Mathematics 1254*, vol. 1254. Springer, Berlin. <https://doi.org/10.1007/BFb0078126>.

<a id="ref-pink1989arithmetical"></a>

Pink, Richard. 1989. *Arithmetical Compactification of Mixed Shimura Varieties*. Vol. 209. Universität Bonn, Mathematisch-Naturwissenschaftliche Fakultät.

<a id="ref-platonov1969problem"></a>

Platonov, V. P. 1969. "The Problem of Strong Approximation and the Kneser-Tits Conjecture for Algebraic Groups." *Mathematics of the USSR-Izvestiya* 3 (6): 1139--47. <https://doi.org/10.1070/IM1969v003n06ABEH000838>.

<a id="ref-poitou1966remarques"></a>

Poitou, Georges. 1966. "Remarques Sur l'homologie Des Groupes Profinis." *Colloques Internationaux Du Centre National de La Recherche Scientifique* 143: 201--13.

<a id="ref-radford1979natural"></a>

Radford, David E. 1979. "A Natural Ring Basis for the Shuffle Algebra and an Application to Group Schemes." *Journal of Algebra* 58 (2): 432--54. <https://doi.org/10.1016/0021-8693(79)90171-6>.

<a id="ref-rallis1984injectivity"></a>

Rallis, S. 1984. "Injectivity Properties of Liftings Associated to Weil Representations." *Compositio Mathematica* 52 (2): 139--69. <https://www.numdam.org/item/CM_1984__52_2_139_0/>.

<a id="ref-ribet1976modular"></a>

Ribet, Kenneth A. 1976. "A Modular Construction of Unramified $p$-Extensions of $\mathbb{Q}(\mu_p)$." *Inventiones Mathematicae* 34 (3): 151--62. <https://doi.org/10.1007/BF01403065>.

<a id="ref-riemann1859anzahl"></a>

Riemann, Bernhard. 1859. "Ueber Die Anzahl Der Primzahlen Unter Einer Gegebenen Grösse." *Monatsberichte Der Königlich Preussischen Akademie Der Wissenschaften Zu Berlin* 1859 (November): 671--80. <https://books.google.com/books?id=j-IaAAAAYAAJ>.

<a id="ref-rubin2000euler"></a>

Rubin, Karl. 2000. *Euler Systems*. Vol. 147. Princeton University Press, Princeton, NJ (Annals of Mathematics Studies). <https://doi.org/10.1515/9781400865208>.

<a id="ref-schmid1975some"></a>

Schmid, Wilfried. 1975. "Some Properties of Square-Integrable Representations of Semisimple Lie Groups." *Annals of Mathematics (2)* 102 (3): 535--64. <https://doi.org/10.2307/1971043>.

<a id="ref-schmidt1976equations"></a>

Schmidt, Wolfgang M. 1976. *Equations over Finite Fields: An Elementary Approach*. Vol. 536. Springer, Berlin (Lecture Notes in Mathematics). <https://doi.org/10.1007/BFb0080437>.

<a id="ref-scholze2013local"></a>

Scholze, Peter. 2013. "The Local Langlands Correspondence for $\mathrm{GL}_n$ over $p$-Adic Fields." *Inventiones Mathematicae* 192 (3): 663--715. <https://doi.org/10.1007/s00222-012-0420-5>.

<a id="ref-scholze2013moduli"></a>

Scholze, Peter, and Jared Weinstein. 2013. "Moduli of $p$-Divisible Groups." *Cambridge Journal of Mathematics* 1 (2): 145--237. <https://doi.org/10.4310/CJM.2013.v1.n2.a1>.

<a id="ref-segal1959foundations"></a>

Segal, I. E. 1959. "Foundations of the Theory of Dynamical Systems of Infinitely Many Degrees of Freedom. i." *Mat.-Fys. Medd. Danske Vid. Selsk.* 31 (12).

<a id="ref-segal1963transforms"></a>

Segal, I. E. 1963. "Transforms for Operators and Symplectic Automorphisms over a Locally Compact Abelian Group." *Mathematica Scandinavica* 13: 31--43. <https://doi.org/10.7146/math.scand.a-10686>.

<a id="ref-selberg1967epstein"></a>

Selberg, Atle, and S. Chowla. 1967. "On Epstein's Zeta-Function." *Journal Für Die Reine Und Angewandte Mathematik* 227: 86--110. <https://doi.org/10.1515/crll.1967.227.86>.

<a id="ref-serre1956geometrie"></a>

Serre, Jean-Pierre. 1956. "Géométrie Algébrique Et Géométrie Analytique." *Annales de l'Institut Fourier* 6: 1--42. <https://doi.org/10.5802/aif.59>.

<a id="ref-serre1964cohomologie"></a>

Serre, Jean-Pierre. 1964. *Cohomologie Galoisienne*. Vol. 5. Springer, Berlin.

<a id="ref-serre1968abelian"></a>

Serre, Jean-Pierre. 1968. *Abelian $\ell$-Adic Representations and Elliptic Curves*. W. A. Benjamin, New York-Amsterdam. <https://zbmath.org/?q=an:0186.25701>.

<a id="ref-serre1968good"></a>

Serre, Jean-Pierre, and John Tate. 1968. "Good Reduction of Abelian Varieties." *Annals of Mathematics (2)* 88 (3): 492--517. <https://doi.org/10.2307/1970722>.

<a id="ref-shale1962linear"></a>

Shale, David. 1962. "Linear Symmetries of Free Boson Fields." *Transactions of the American Mathematical Society* 103 (1): 149--67. <https://doi.org/10.1090/S0002-9947-1962-0137504-6>.

<a id="ref-shalika1974multiplicity"></a>

Shalika, J. A. 1974. "The Multiplicity One Theorem for $\mathrm{GL}_n$." *Annals of Mathematics (2)* 100 (2): 171--93. <https://doi.org/10.2307/1971071>.

<a id="ref-shimura1971introduction"></a>

Shimura, Goro. 1971. *Introduction to the Arithmetic Theory of Automorphic Functions*. Vol. 11. Iwanami Shoten, Tokyo; Princeton University Press, Princeton, NJ (Publications of the Mathematical Society of Japan). <https://zbmath.org/?q=an:0221.10029>.

<a id="ref-shimura1961complex"></a>

Shimura, Goro, and Yutaka Taniyama. 1961. *Complex Multiplication of Abelian Varieties and Its Applications to Number Theory*. Vol. 6. The Mathematical Society of Japan, Tokyo (Publications of the Mathematical Society of Japan). <https://zbmath.org/?q=an:0112.03501>.

<a id="ref-shin2011galois"></a>

Shin, Sug Woo. 2011. "Galois Representations Arising from Some Compact Shimura Varieties." *Annals of Mathematics (2)* 173 (3): 1645--741. <https://doi.org/10.4007/annals.2011.173.3.9>.

<a id="ref-siegel1935analytische"></a>

Siegel, Carl Ludwig. 1935a. "Über Die Analytische Theorie Der Quadratischen Formen." *Annals of Mathematics. Second Series* 36 (3): 527--606. <https://doi.org/10.2307/1968644>.

<a id="ref-siegel1935classenzahl"></a>

Siegel, Carl Ludwig. 1935b. "Über Die Classenzahl Quadratischer Zahlkörper." *Acta Arithmetica* 1 (1): 83--86. <https://doi.org/10.4064/aa-1-1-83-86>.

<a id="ref-siegel1969berechnung"></a>

Siegel, Carl Ludwig. 1969. "Berechnung von Zetafunktionen an Ganzzahligen Stellen." *Nachr. Akad. Wiss. Göttingen Math.-Phys. Kl. II* 1969: 87--102. <https://zbmath.org/?q=an:0186.08804>.

<a id="ref-siegel1970fourierschen"></a>

Siegel, Carl Ludwig. 1970. "Über Die Fourierschen Koeffizienten von Modulformen." *Nachr. Akad. Wiss. Göttingen Math.-Phys. Kl. II* 1970: 15--56. <https://zbmath.org/?q=an:0225.10031>.

<a id="ref-siegel1980advanced"></a>

Siegel, Carl Ludwig. 1980. *Advanced Analytic Number Theory*. Vol. 9. Tata Institute of Fundamental Research, Bombay (Tata Institute of Fundamental Research Studies in Mathematics).

<a id="ref-silberger1978langlands"></a>

Silberger, Allan J. 1978. "The Langlands Quotient Theorem for $p$-Adic Groups." *Mathematische Annalen* 236 (2): 95--104. <https://doi.org/10.1007/BF01351383>.

<a id="ref-sinnott1984mu"></a>

Sinnott, W. 1984. "On the $\mu$-Invariant of the $\Gamma$-Transform of a Rational Function." *Inventiones Mathematicae* 75 (2): 273--82. <https://doi.org/10.1007/BF01388565>.

<a id="ref-skinner2014iwasawa"></a>

Skinner, Christopher, and Eric Urban. 2014. "The Iwasawa Main Conjectures for $\mathrm{GL}_2$." *Inventiones Mathematicae* 195 (1): 1--277. <https://doi.org/10.1007/s00222-013-0448-1>.

<a id="ref-soule1979ktheorie"></a>

Soulé, C. 1979. "K-Théorie Des Anneaux d'entiers de Corps de Nombres Et Cohomologie Étale." *Inventiones Mathematicae* 55 (3): 251--95. <https://doi.org/10.1007/BF01406843>.

<a id="ref-stepanov1969number"></a>

Stepanov, S. A. 1969. "On the Number of Points of a Hyperelliptic Curve over a Finite Prime Field." *Izv. Akad. Nauk SSSR Ser. Mat.* 33 (5): 1171--81. <https://www.mathnet.ru/php/archive.phtml?wshow=paper&jrnid=im&paperid=2197&option_lang=rus>.

<a id="ref-stone1930linear"></a>

Stone, M. H. 1930. "Linear Transformations in Hilbert Space. III. Operational Methods and Group Theory." *Proceedings of the National Academy of Sciences of the United States of America* 16 (2): 172--75. <https://doi.org/10.1073/pnas.16.2.172>.

<a id="ref-stuhler1976bemerkung"></a>

Stuhler, Ulrich. 1976. "Eine Bemerkung Zur Reduktionstheorie Quadratischer Formen." *Archiv Der Mathematik* 27: 604--10. <https://doi.org/10.1007/BF01224726>.

<a id="ref-sun2012multiplicity"></a>

Sun, Binyong, and Chen-Bo Zhu. 2012. "Multiplicity One Theorems: The Archimedean Case." *Annals of Mathematics (2)* 175 (1): 23--44. <https://doi.org/10.4007/annals.2012.175.1.2>.

<a id="ref-tadic1986classification"></a>

Tadić, Marko. 1986. "Classification of Unitary Representations in Irreducible Representations of General Linear Group (Non-Archimedean Case)." *Annales Scientifiques de l'École Normale Supérieure (4)* 19 (3): 335--82. <https://doi.org/10.24033/asens.1510>.

<a id="ref-takagi1920theorie"></a>

Takagi, T. 1920. "Über Eine Theorie Des Relativ Abelschen Zahlkörpers." *Journ. Coll. Of Science Tôkyo* 41 (9): 133 pp. <https://zbmath.org/?q=an:47.0147.03>.

<a id="ref-taniyama1957lfunctions"></a>

Taniyama, Yutaka. 1957. "$L$-Functions of Number Fields and Zeta Functions of Abelian Varieties." *Journal of the Mathematical Society of Japan* 9 (3): 330--66. <https://doi.org/10.2969/jmsj/00930330>.

<a id="ref-tate1967fourier"></a>

Tate, J. T. 1967a. "Fourier Analysis in Number Fields, and Hecke's Zeta-Functions." In *Algebraic Number Theory (Proc. Instructional Conf., Brighton, 1965), j. W. S. Cassels and a. Fröhlich (Eds.)*. Academic Press, London. <https://zbmath.org/?q=an:1492.11154>.

<a id="ref-tate1967global"></a>

Tate, J. T. 1967b. "Global Class Field Theory." In *Algebraic Number Theory (Proc. Instructional Conf., Brighton, 1965), j. W. S. Cassels and a. Fröhlich (Eds.)*. Academic Press, London. <https://zbmath.org/?q=an:1179.11041>.

<a id="ref-tate1967pdivisible"></a>

Tate, J. T. 1967c. "$p$-Divisible Groups." In *Proceedings of a Conference on Local Fields (NUFFIC Summer School, Driebergen, 1966)*. Springer, Berlin. <https://doi.org/10.1007/978-3-642-87942-5_12>.

<a id="ref-tate1963duality"></a>

Tate, John. 1963. "Duality Theorems in Galois Cohomology over Number Fields." In *Proceedings of the International Congress of Mathematicians, Stockholm, 1962*. Proc. Int. Congr. Math. 1962 (Stockholm).

<a id="ref-taylor2007compatibility"></a>

Taylor, Richard, and Teruyoshi Yoshida. 2007. "Compatibility of Local and Global Langlands Correspondences." *Journal of the American Mathematical Society* 20 (2): 467--93. <https://doi.org/10.1090/S0894-0347-06-00542-X>.

<a id="ref-mathlib2020lean"></a>

The mathlib Community. 2020. "The Lean Mathematical Library." In *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs*. ACM. <https://doi.org/10.1145/3372885.3373824>.

<a id="ref-chebotarev1926bestimmung"></a>

Tschebotareff, N. 1926. "Die Bestimmung Der Dichtigkeit Einer Menge von Primzahlen, Welche Zu Einer Gegebenen Substitutionsklasse Gehören." *Mathematische Annalen* 95 (1): 191--228. <https://doi.org/10.1007/BF01206606>.

<a id="ref-viehweg1982vanishing"></a>

Viehweg, Eckart. 1982. "Vanishing Theorems." *Journal Für Die Reine Und Angewandte Mathematik* 335: 1--8. <https://doi.org/10.1515/crll.1982.335.1>.

<a id="ref-wallach1983asymptotic"></a>

Wallach, Nolan R. 1983. "Asymptotic Expansions of Generalized Matrix Entries of Representations of Real Reductive Groups." In *Lie Group Representations, i (College Park, Md., 1982/1983)*, vol. 1024. Springer, Berlin (Lecture Notes in Mathematics). <https://doi.org/10.1007/BFb0071436>.

<a id="ref-wallach1992real"></a>

Wallach, Nolan R. 1992. *Real Reductive Groups. II*. 132-II. Academic Press, Boston, MA (Pure; Applied Mathematics). <https://zbmath.org/?q=an:0785.22001>.

<a id="ref-washington1997introduction"></a>

Washington, Lawrence C. 1997. *Introduction to Cyclotomic Fields*. Vol. 83. Springer, New York (Graduate Texts in Mathematics). <https://doi.org/10.1007/978-1-4612-1934-7>.

<a id="ref-weil1948varietes"></a>

Weil, André. 1948. *Variétés Abéliennes Et Courbes Algébriques*. Hermann & Cie, Paris (Actualités scientifiques et industrielles 1064 = Publ. Inst. Math. Univ. Strasbourg 8). <https://zbmath.org/?q=an:0037.16202>.

<a id="ref-weil1956certain"></a>

Weil, André. 1956. "On a Certain Type of Characters of the Idele-Class Group of an Algebraic Number-Field." In *Proceedings of the International Symposium on Algebraic Number Theory, Tokyo & Nikko, September 1955*. <https://zbmath.org/?q=an:0073.26303>.

<a id="ref-weil1964certains"></a>

Weil, André. 1964. "Sur Certains Groupes d'opérateurs Unitaires." *Acta Mathematica* 111: 143--211. <https://doi.org/10.1007/BF02391012>.

<a id="ref-weil1965formule"></a>

Weil, André. 1965. "Sur La Formule de Siegel Dans La Théorie Des Groupes Classiques." *Acta Mathematica* 113: 1--87. <https://doi.org/10.1007/BF02391774>.

<a id="ref-weyl1946classical"></a>

Weyl, Hermann. 1946. *The Classical Groups, Their Invariants and Representations*. Vol. 1. Princeton University Press, Princeton, NJ.

<a id="ref-wiles1995modular"></a>

Wiles, Andrew. 1995. "Modular Elliptic Curves and Fermat's Last Theorem." *Annals of Mathematics. Second Series* 141 (3): 443--551. <https://doi.org/10.2307/2118559>.

<a id="ref-yamana2011siegel"></a>

Yamana, Shunsuke. 2011. "On the Siegel--Weil Formula: The Case of Singular Forms." *Compositio Mathematica* 147 (4): 1003--21. <https://doi.org/10.1112/S0010437X11005379>.

<a id="ref-zarhin1977endomorphisms"></a>

Zarhin, Yu. G. 1977. "Endomorphisms of Abelian Varieties and Points of Finite Order in Characteristic $p$." *Mat. Zametki* 21 (6): 737--44. <https://www.mathnet.ru/php/archive.phtml?wshow=paper&jrnid=mzm&paperid=8004&option_lang=rus>.

<a id="ref-zelevinsky1980induced"></a>

Zelevinsky, A. V. 1980. "Induced Representations of Reductive $p$-Adic Groups. II. On Irreducible Representations of $\mathrm{GL}(n)$." *Annales Scientifiques de l'École Normale Supérieure (4)* 13 (2): 165--210. <https://doi.org/10.24033/asens.1379>.

<a id="ref-zelevinsky1981representations"></a>

Zelevinsky, Andrey V. 1981. *Representations of Finite Classical Groups. A Hopf Algebra Approach*. Vol. 869. Lecture Notes in Mathematics (Springer-Verlag). <https://doi.org/10.1007/BFb0090287>.

<a id="ref-zhang1995positive"></a>

Zhang, Shouwu. 1995. "Positive Line Bundles on Arithmetic Varieties." *Journal of the American Mathematical Society* 8 (1): 187--221. <https://doi.org/10.1090/S0894-0347-1995-1254133-7>.

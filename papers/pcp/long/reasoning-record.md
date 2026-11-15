---
title: "The algebraic PCP theorem: a detailed account of the Lean proof"
authors:
  - "Explanatory reconstruction by AI agents directed by Will Cook"
attribution: "Original algebraic argument: Prashanth Amireddy, Amik Raj Behera, Srikanth Srinivasan, Madhu Sudan and Sophus Valentin Willumsgaard. Lean formalization: Troy Lee."
---

# The algebraic PCP theorem: a detailed account of the Lean proof

*An explanatory account prepared by Will Cook with AI assistance, following Troy Lee's formalization of the algebraic proof of Amireddy, Behera, Srinivasan, Sudan and Willumsgaard.*

<!-- passage:pcp-long-intro-theorem -->
A polynomial-time verifier can check membership in any NP language by reading a constant number of bits from a suitably encoded proof. It uses only logarithmically many random bits, accepts a correct proof with certainty, and rejects every purported proof of a false statement with probability at least one half. We reconstruct the algebraic argument in Troy Lee's Lean formalization and explain how its implementation and machine-simulation theorems establish these resource bounds.

Here is the precise version. Let $L$ be a language of finite binary strings. Say that $L$ is in NP if there are a polynomial $p_0$ and a deterministic polynomial-time Boolean relation $R(x,w)$ such that

$$
x\in L
\quad\Longleftrightarrow\quad
\exists w\in\{0,1\}^{*},\quad |w|\le p_0(|x|)\ \text{and}\ R(x,w)=1.
$$

Then there exist a single probabilistic proof verifier $V$, a polynomial-time implementation of its query protocol, constants $a,b,\ell\in\mathbb N$, and a polynomial $p\in\mathbb N[X]$, with the following properties for every input $x$ of length $n$.

1. The verifier draws exactly $r(n)=a\lceil\log_2(n+2)\rceil+b$ independent fair bits.
2. On every random seed and every branch of its query protocol, it reads at most $\ell$ bits of the proof, all at addresses less than $p(n)$.
3. If $x\in L$, there is one proof $\pi$ for which every random seed makes $V$ accept.
4. If $x\notin L$, then for every proof $\pi$, at most half of the random seeds make $V$ accept.

The verifier may choose its next proof address using the bits already read. The proof is fixed before the seed is drawn; the statement does not allow the prover to choose a new proof after seeing the verifier's randomness. The verifier, its implementation, the constants, and the proof-length polynomial are chosen for the language, before the input. Proofs may depend on the input. This is the forward inclusion

$$
\mathrm{NP}\subseteq\mathrm{PCP}(O(\log n),O(1)).
$$

Conversely, any language with a verifier satisfying these effectiveness, length, completeness and soundness conditions is in NP. Guess the polynomially bounded proof prefix and check every random seed. There are polynomially many seeds because $2^{r(n)}\le 2^b[2(n+2)]^a$. Each simulation takes polynomial time. An input with a perfectly accepted proof passes this deterministic check; a false input cannot pass it because acceptance on every seed would contradict the soundness bound of one half. The first chapter supplies the implementation and witness-checker arguments in both directions, using the machine results identified below. Together the inclusions give

$$
\mathrm{NP}=\mathrm{PCP}(O(\log n),O(1)).
$$

The formal statement uses an infinite Boolean oracle $\pi:\mathbb N\to\{0,1\}$ and bounds every reachable address by $p(n)$; only that finite prefix can affect acceptance. Its exact randomness formula makes the budget computable, and unused random bits may be ignored. The definition of NP is tied to the formalization's concrete machine model and is proved equivalent to the pinned ComplexityLib nondeterministic-machine class. See the [verifier definitions][intro-verifier], [forward theorem][intro-theorem], [concrete reverse theorem][intro-reverse], and [reference NP equivalence][intro-reference].
<!-- /passage:pcp-long-intro-theorem -->

## How the proof is organized

<!-- passage:pcp-long-intro-roadmap -->
The construction treats graph three-colourability first. Interpolation turns a colouring into a polynomial. Two polynomial constraints express colour validity and separation across edges; grid-vanishing certificates make them testable at random ambient points. The proof stores binary encodings of four polynomials and their line restrictions. Its seven checks must force one consistent colouring from arbitrary received bits.

We begin with that verifier and prove the global implication from low rejection to colourability, using precise testing and correction statements. The chapter also gives perfect completeness, parameter choices, fair-bit sampling, repetition and the reductions to and from NP. The later chapters prove the algebraic and binary statements used in this assembly. Thus a reader can first see what each estimate must accomplish, then follow its proof without changing the verifier under discussion.

The algebraic chapter reconstructs the corrected weighted test and point-versus-line soundness, including the bivariate agreement and ruled-surface arguments. The binary chapter proves how two encodings give constant-query tests, how one decoded polynomial satisfies both required label-distance bounds, and how correction handles the nonuniform points requested by a grid certificate. The same auxiliary tables are used for testing and correction throughout.
<!-- /passage:pcp-long-intro-roadmap -->

## Reading this account

<!-- passage:pcp-long-intro-readers -->
The mathematical prerequisites are finite fields, polynomials in several variables, elementary linear algebra, and finite probability. Basic complexity terminology is introduced through the theorem above; the first chapter explains the additional machine and resource accounting. The proof uses normalized Hamming distance, written $\Delta(f,g)=\Pr[f\ne g]$. The same letter may name a degree parameter in different chapters; each local statement fixes its meaning. A distinction worth keeping throughout is between total degree and degree in each variable, and between a formal polynomial and its evaluation function over a finite field.

The detailed proofs include the intermediate estimates, parameter substitutions and boundary cases. The machine-level transition proofs are used through the following contracts; their semantics and cost bounds remain in the formal source. The [specialist paper](../short/paper.md) presents the theorem and main proof structure with less local detail. The [exposition with worked examples](../expository/main.md) develops the construction through concrete calculations. These companion texts have different reading purposes; the detailed proofs remain here, and the linked Lean statements provide the exact formal counterparts.

<!-- /passage:pcp-long-intro-readers -->



[intro-paper]: https://arxiv.org/abs/2608.17429v2
[intro-verifier]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Verifier/Definition.lean
[intro-theorem]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Theorem.lean
[intro-reverse]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/ReverseConcrete.lean
[intro-reference]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/ReferenceNPConverse.lean


### Implementation results used in the argument

<!-- passage:pcp-long-implementation-contracts -->
The immediate model uses deterministic finite multi-stack machines with fixed public encodings. A verifier step takes an input, seed and answer history, and either returns a verdict or requests the next proof address. Its implementation condition identifies the verifier with the query tree obtained by unfolding this step for a bounded number of queries, on both possible answers at every branch. A further query at depth zero becomes rejection. This condition alone does not assert that the unrestricted callback halts within that depth. Polynomial running time is a separate machine property.

| Established source result | Guarantee used here | Application in this account |
| --- | --- | --- |
| [Callback correctness][lean-runtime-correct] | The program computes the mathematical query list and verdict for arbitrary input, seed and answer history. | The seven-check verifier's implementation |
| [Charged cost][lean-runtime-cost] and [machine compilation][lean-runtime] | Polynomial bounds on the complete callback, storage and repetition protocol give a polynomial-time machine. | Time complexity, separately from the number of proof reads |
| [Executable NP reduction][lean-np-runtime] | A concrete certificate checker yields a polynomial-time graph map, with polynomial output size and the required membership equivalence. | Transport from NP to three-colourability |
| [Finite-witness checker][intro-reverse] | Canonical logarithmic randomness and a polynomial address bound permit polynomial-time checking of every seed against a finite proof prefix. | Reverse inclusion |
| [Reference-machine simulations][intro-reference] | The concrete certificate class equals the pinned nondeterministic-machine definition of NP, in both directions. | Interpretation of the endpoint |

The sections on implementation, reduction and the reverse inclusion explain how these results compose. The algebraic testing and correction arguments are proved below rather than imported through this table.
<!-- /passage:pcp-long-implementation-contracts -->

## From the algebraic tests to the PCP theorem

<!-- passage:pcp-long-final-target -->
We first construct the three-colouring verifier and prove its completeness, soundness and resource bounds. The later algebraic and binary chapters establish the testing statements used here. Throughout this chapter, $d$ is the grid dimension, $m$ the digit base, and $Q=|F|$ the field size. The fixed inner degree is $c$ and the decoded degree bound is $D=cm^c$. The difference polynomial is written $Q_*$.

The construction follows Amireddy, Behera, Srinivasan, Sudan and Willumsgaard's corrected [paper, Section 7][paper-pcp], with the concrete choices in Lee's formalization. The paper invokes NP-completeness after proving the three-colouring construction. The formalization also constructs the NP reduction, fair-bit sampler and polynomial-time machine; their composition occupies the rest of this chapter.
<!-- /passage:pcp-long-final-target -->

### Three colours as polynomial equations

<!-- passage:pcp-long-colour-equations -->
Let $F$ be a finite field of characteristic two, of cardinality $Q$, containing a primitive cube root of unity $\omega$. The three colours will be

$$
\mathcal C=\{1,\omega,\omega^2\}.
$$

These are distinct, and they are exactly the roots of $Z^3-1$. For two valid colours $u,v$, the equation

$$
(u-v)^3=1
$$

holds exactly when $u\ne v$. To prove the nontrivial direction, characteristic two gives

$$
(u-v)^4=u^4-v^4=u-v,
$$

because $u^3=v^3=1$. If $u\ne v$, cancellation of the nonzero factor $u-v$ yields $(u-v)^3=1$. Conversely, $u=v$ would make the left side zero. Thus an assignment $f:V(G)\to F$ is a proper three-colouring precisely when

$$
f(v)^3-1=0\quad(v\in V(G)),\qquad
(f(v)-f(w))^3-1=0\quad(vw\in E(G)).
$$

Both families matter. For example, assign the four vertices of $K_4$ the four elements of $\mathbb F_4$. Every difference across an edge is a nonzero element of $\mathbb F_4$, hence has cube one. All edge equations hold, although $K_4$ is not three-colourable. The vertex assigned zero violates its vertex equation. The formal [colour algebra][lean-colour-algebra] proves both implications with the vertex condition present.
<!-- /passage:pcp-long-colour-equations -->

<!-- passage:pcp-long-grid-constraints -->
Choose a nonempty set $H\subseteq F$, of size $h$, and a dimension $d$ large enough to place the input graph's vertices in $H^d$. Unused grid points are isolated vertices. Extending a colouring arbitrarily to these points preserves three-colourability in both directions.

Let $P$ be the coordinatewise interpolation of the colour assignment on $H^d$, and let $E$ be the interpolation of the graph's zero-one adjacency function on $H^d\times H^d$. Writing

$$
d_0=d(h-1),
$$

we have $\deg P\le d_0$ and $\deg E\le2d_0$. Form the difference and constraint polynomials

$$
\begin{aligned}
Q_P(X,Y)&=P(X)-P(Y),\\
A_P(X)&=P(X)^3-1,\\
B_P(X,Y)&=E(X,Y)\bigl(Q_P(X,Y)^3-1\bigr).
\end{aligned}
$$

Their total degrees are at most $d_0,3d_0,5d_0$, respectively. A proper colouring makes $A_P$ vanish on $H^d$ and $B_P$ vanish on $H^{2d}$. Conversely, these two vanishing conditions, together with $Q_P(X,Y)=P(X)-P(Y)$, recover a proper colouring by the preceding scalar argument. The factor $E$ is the public graph's actual adjacency extension: it equals one on edges and zero on nonedges at grid points. It is computed from the input, not supplied by the prover. The [grid construction][lean-colour-grid] implements this equivalence.

Put $Z_H(T)=\prod_{u\in H}(T-u)$. The grid-vanishing theorem, proved in the algebraic chapter, writes any polynomial $A$ vanishing on $H^k$ as $\sum_i Z_H(X_i)U_i(X)$. Its certificate $M(X,Y)=\sum_iY_iU_i(X)$ satisfies $M(X,0)=0$ and $M(X,Z_H(X))=A(X)$, with $\deg M\le\deg A$. Conversely these identities imply grid vanishing, even if a proposed $M$ is nonlinear in $Y$. Apply the theorem to obtain $M_A,M_B$. The sufficient degree bound $5d_0$ covers the colour polynomial and both certificate polynomials. The proper-colouring certificate has two blocks of $2d$ variables; the implementation flattens the first two vertex-coordinate blocks before passing them to the same certificate routines. This is a coordinate bijection and preserves evaluations, total degree and normalized distances.
<!-- /passage:pcp-long-grid-constraints -->

### The eight tables and seven checks

<!-- passage:pcp-long-eight-tables -->
Fix binary coordinates $\rho:F\to\mathbb F_2^t$, where $Q=2^t$. A degree-$r$ Hadamard row for $u\in F$ stores $R(\rho(u))$ at each squarefree Boolean polynomial label $R$ of degree at most $r$. Degree-one labels are affine; homogeneous labels have zero constant term. They preserve sums and distinguish unequal field values with probability one half when sampled uniformly.

The received proof contains four primary tables and four encoded line tables. An honest proof has the following mathematical contents:

| Primary polynomial | Number of field coordinates | Primary binary encoding |
| --- | ---: | --- |
| $P$, the colour extension | $d$ | degree-three Hadamard encoding |
| $M_A$, the vertex certificate | $2d$ | degree-one Hadamard encoding |
| $Q_P$, the difference polynomial | $2d$ | degree-three Hadamard encoding |
| $M_B$, the edge certificate | $4d$ | degree-one Hadamard encoding |

Each primary table has one encoded line table. In the formal implementation every auxiliary line table uses degree-one labels. For a primary domain $F^k$, an auxiliary address consists of an oriented line $(u,v)\in F^k\times F^k$, an inner point $w\in F^{cm}$, and an affine Boolean label. Honest rows encode the line restriction after digit expansion: writing each exponent below $m^c$ in base $m$ turns it into a product of $c$ variables, of total degree $c$. Substitution $\Phi(z)_{i,j}=z^{jm^i}$ recovers the original line value. The binary chapter proves these statements and explains why an arbitrary decoded inner polynomial can have outer degree as large as $D=cm^c$. The paper's Section 7 lists degree-three auxiliary labels for colour and difference; the formal variant uses degree-one auxiliary labels throughout. In particular, the line table used to test a certificate is the same physical table used to correct that certificate inside ZERO. There is no second certificate table whose consistency would have to be assumed. The [proof datatype and read function][lean-seven-checks] specify all eight tags and their address spaces.

The verifier runs four encoded-line low-degree tests, one on each primary/line-table pair. It also runs ZERO on the vertex constraint, ZERO on the edge constraint, and a difference check. It accepts exactly when all seven accept. Each check receives an independent seed with the prescribed finite uniform distribution. This makes each branch's marginal distribution the one analysed in its soundness theorem. Since failure of a branch forces failure of the conjunction, each branch's rejection probability is at most the full rejection probability.
<!-- /passage:pcp-long-eight-tables -->

<!-- passage:pcp-long-derived-constraints -->
The constraint polynomials are not extra proof tables. Suppose $p(x,\Lambda)$ is the received degree-three row intended to encode $P(x)$. To request a linear bit of $P(x)^3-1$, transform the desired linear label $L$ into the degree-three Boolean label $\Lambda_{Z^3-1,L}$ supplied by the encoding lemma. Draw a fresh uniform degree-three label $R$, read

$$
p(x,R+\Lambda_{Z^3-1,L})+p(x,R),
$$

and return their sum in $\mathbb F_2$. The corresponding edge query uses the difference table and the label for $Z\mapsto E(x,y)(Z^3-1)$. Thus each derived read costs two physical bits.

For an exact Hadamard row, linearity in the **label** gives the requested bit exactly, even though $Z\mapsto Z^3-1$ is nonlinear in the field value. For a row close on average to the correct encoding, the two sampled labels are individually uniform, so the probability of an incorrect derived read is bounded by twice the row error. The formal verifier uses fresh masks as part of the actual test seed. Its soundness argument carries this replacement error through the ZERO inequality; it does not postulate a globally good fixed mask.

The difference check selects independent uniform $x,y\in F^d$ and a homogeneous linear functional $L:F\to\mathbb F_2$. It compares the difference table's bit with the sum of the colour-table bits at $x$ and $y$. Homogeneity is essential to the displayed additive identity. The formal proof uses exactly the homogeneous-label distance guarantee supplied by the encoded-line theorem, rather than a stronger assertion about arbitrary affine labels.
<!-- /passage:pcp-long-derived-constraints -->

<!-- passage:pcp-long-query-budget -->
The seven physical query bounds, in the order colour, vertex certificate, difference, edge certificate, vertex ZERO, edge ZERO, and difference check, are

$$
2c+18,\quad2c+14,\quad2c+18,\quad2c+14,
\quad6c+20,\quad6c+20,\quad3.
$$

Their sum is $20c+107$, independent of the graph size. Taking $c=4$ bounds one unamplified run by at most $26+22+26+22+44+44+3=187$ physical bit reads. This count includes the fresh derived reads. A separate congruence theorem says that two proof oracles agreeing on the listed addresses give the same verdict; the count therefore measures actual information read from the proof, rather than merely the number of named subroutines. The [query-list theorem][lean-query-budget] establishes both facts.
<!-- /passage:pcp-long-query-budget -->

### Perfect completeness

<!-- passage:pcp-long-completeness -->
Start with a proper colouring. Interpolate it to obtain $P$, put the exact difference polynomial $Q_P$ in the difference table, and choose grid-vanishing certificates $M_A,M_B$. Put the exact encodings and exact encoded restrictions to lines in their eight locations. Assume the honest degree capacity

$$
5d(h-1)<m^c,
$$

where $m$ is the base used by the degree-reducing inner encoding.

Every outer low-degree test accepts because it sees an exact polynomial of degree below $m^c$ and its honest encoded line restrictions. The two-query derived read agrees exactly with the requested constraint encoding for every mask. Each ZERO check accepts because its polynomial has the supplied vanishing certificate. Finally,

$$
L(Q_P(x,y))=L(P(x))+L(P(y))
$$

for every homogeneous label $L$, so the difference check also accepts. The same eight tables satisfy all these statements simultaneously. Consequently every seven-component random seed accepts. This proves perfect completeness. The [honest-proof construction][lean-completeness] supplies the certificates and verifies each branch.
<!-- /passage:pcp-long-completeness -->

### Soundness of the seven-check verifier

<!-- passage:pcp-long-decoding-contract -->
Set $D=cm^c$. Suppose the field and grid satisfy

$$
Q\ge10^6D^3,\qquad Q\ge100Dh,
\qquad d(h-1)\le D,
$$

with $c,m,h\ge1$ and a primitive cube root of unity. The weighted test uses the first $c+1$ powers of a generator of $F^\times$ and their Lagrange weights. For correction, the $c+1$ powers of its chosen parameter must be distinct and nonzero (the source condition `GoodNodes`); choosing the same generator suffices here. Let $\kappa$ be the rejection probability of an arbitrary received proof. The argument will show that sufficiently small $\kappa$ forces the graph to be three-colourable.

The constants used by the binary tests are

$$
K_c=4(c+2)^2(112(c+2)+60),\quad
E_c=2((c+1)K_c+29),\quad S_c=28+E_c,\quad
C_c=2+2(c+1)K_c.
$$

We need the following three statements, proved in the binary chapter.

| Statement | Guarantee used in the assembly |
| --- | --- |
| Encoded-line soundness (B15) | Under the field bound and $E_c\kappa\le1/4\,000\,000$, one degree-$D$ polynomial has both full-label and homogeneous-label distance at most $S_c\kappa$ from the primary table. Auxiliary rows are arbitrary. |
| Outer correction (B16) | At each fixed target $a$, homogeneous primary error $\delta$ gives failure probability at most $C_cR_a+\delta+D/[2(Q-1)]$. Failure means rejection or a wrong bit; $R_a$ is actual rejection, and the label is uniform homogeneous. |
| Derived ZERO (B25) | Suppose the point-dependent derived values equal one fixed polynomial, and this polynomial and its certificate have degree at most $D$. If the polynomial fails to vanish on the grid, its ideal rejection lower bound is at most $(1+2C_c)(\kappa+2\varepsilon)+2\delta_M+D/(Q-1)$. Here $\varepsilon$ is full primary error and $\delta_M$ is homogeneous certificate error. |

The first statement chooses the witnesses. The second handles prescribed certificate targets, which need not be uniform. The third uses that correction twice, retaining both actual rejection and the fresh-mask replacement error. We now apply them with the same received tables. If

$$
E_c\kappa\le\frac1{4\,000\,000},
$$

the four outer tests supply four actual polynomials $P,Q_*,M_A,M_B$, each of total degree at most $D$. They give full degree-three label distance at most

$$
\varepsilon=S_c\kappa
$$

for $P,Q_*$, and homogeneous linear-label distance at most $\varepsilon$ for all four relevant primary tables. These polynomials are chosen once for the received proof; the later argument uses those same choices. No closeness assumption is imposed on the auxiliary line tables. Their actual test behaviour is already part of the decoding theorem. These are the decoded polynomials used in [the assembled soundness proof][lean-soundness].
<!-- /passage:pcp-long-decoding-contract -->

<!-- passage:pcp-long-difference-soundness -->
First identify the decoded difference polynomial. Replace the three received bits in the difference test by their decoded homogeneous bits. The replacement can change the verdict only if one of these three bits differs, an event of probability at most $3\varepsilon$. Hence the ideal consistency check rejects with probability at most $\kappa+3\varepsilon$.

For a nonzero field element $z$, exactly half of the homogeneous linear functionals satisfy $L(z)=1$. Therefore this ideal rejection rate is exactly half the relative distance between the field-valued functions $Q_*(x,y)$ and $P(x)-P(y)$. If these polynomials differed, their difference would be a nonzero polynomial of degree at most $D$, and the polynomial zero bound would give relative disagreement at least $1-D/Q$. It follows that

$$
\kappa+3\varepsilon<\frac{1-D/Q}{2}
$$

forces the polynomial identity $Q_*(X,Y)=P(X)-P(Y)$. This is an identity of polynomials, not merely agreement at most sampled points. The [difference-consistency theorem][lean-difference] makes the strict inequality explicit.
<!-- /passage:pcp-long-difference-soundness -->

<!-- passage:pcp-long-assembled-zero-soundness -->
Now consider the decoded vertex constraint $A_P=P^3-1$. Its degree is at most $3D$. For the edge constraint, the public adjacency polynomial has degree at most $2D$; using the just-proved difference identity, the decoded edge constraint

$$
B_P=E\bigl((P(X)-P(Y))^3-1\bigr)
$$

has degree at most $5D$. Both certificates have degree at most $D$, so the common degree bound $5D$ is sufficient for the two ZERO arguments.

The derived-ZERO inequality (B25) says that if either decoded constraint fails to vanish on its grid, then

$$
\frac{1-5Dh/Q}{2}
\le
(1+2C_c)(\kappa+2\varepsilon)
+2\varepsilon+\frac{5D}{Q-1}.
$$

Here $2\varepsilon$ inside the parentheses is the replacement loss from the derived read. Multiplying it by $1+2C_c$ is necessary: it enters the same rejection term as the actual ZERO failure probability. The other $2\varepsilon$ comes from the two uses of the certificate's homogeneous proximity bound. The last term is the nonzero-parameter local-correction loss. These terms cannot be dropped by choosing a favourable random seed after the fact.

Consequently, the strict reverse inequality forces $A_P$ to vanish on $H^d$ and $B_P$ to vanish on $H^{2d}$. The scalar colour equations then make $P|_{H^d}$ a proper colouring. The coordinate flattening in the edge branch is a bijection, so its normalized error and vanishing statements transport unchanged. The [decoded soundness theorem][lean-decoded] performs these two applications to the same decoded colour and difference polynomials.
<!-- /passage:pcp-long-assembled-zero-soundness -->

<!-- passage:pcp-long-gap -->
An explicit positive gap makes all three inequalities hold at once. Define

$$
\begin{aligned}
A_c&=1+2C_c,\\
B_c&=1+3S_c,\\
T_c&=A_c(1+2S_c)+2S_c,\\
g_c&=\min\left\{
\frac{1}{4\,000\,000(E_c+1)},
\frac{1}{16B_c},
\frac{1}{16(T_c+1)}\right\}.
\end{aligned}
$$

At the chosen value $c=4$, the constants evaluate to

| $K_4$ | $E_4$ | $S_4$ | $C_4$ | $T_4$ |
| ---: | ---: | ---: | ---: | ---: |
| $105408$ | $1054138$ | $1054166$ | $1054082$ | $4444715947277$ |

All denominators are positive, so $g_c>0$. If $0\le\kappa<g_c$, then $E_c\kappa\le1/4\,000\,000$, $\kappa+3S_c\kappa<1/16$, and $A_c(\kappa+2S_c\kappa)+2S_c\kappa<1/16$. The field bound $Q\ge100Dh$, with $D,h\ge1$, gives

$$
\frac DQ\le\frac14,\qquad
\frac{5Dh}{Q}\le\frac14,\qquad
\frac{5D}{Q-1}\le\frac18.
$$

For the last inequality, $Q\ge100D$ implies $Q-1\ge40D$. The difference error is then below $1/16<3/8$, and the total ZERO error is below $1/16+1/8=3/16<3/8$. These bounds prove the required strict comparisons. Thus rejection below $g_c$ implies colourability. Taking the contrapositive, **every received proof of a non-three-colourable graph has rejection probability at least $g_c$**. The [budget lemmas][lean-budget] establish this explicit rejection gap.
<!-- /passage:pcp-long-gap -->

### Parameters for every finite graph

<!-- passage:pcp-long-parameters -->
The formalization chooses a concrete parameter family different from the paper's asymptotic display. For a graph with $N$ vertices, let $a$ be the least integer at least two with

$$
\lceil\log _2N\rceil\le a2^a.
$$

Use the natural ceiling-log convention at $N=0,1$; the definition still selects $a=2$. Put

$$
s=2^a,\quad d=m=h=s,\quad c=4,
\quad t=12a+32,\quad Q=2^t=2^{32}s^{12}.
$$

The finite field is represented by binary coefficient arrays modulo a computed monic irreducible polynomial of degree $t$. The coordinate map $F\cong\mathbb F_2^t$ reads these stored coefficients. Since $t$ is divisible by four, $3\mid Q-1$; bounded searches in the field's numeric order supply a primitive cube root and a generator of $F^{\times}$. The grid $H$ is the first $s$ field elements in this numeric order. It need not be a subfield.

The grid has $h^d=s^s=2^{a2^a}\ge N$ points. With $D=4s^4$, the soundness field requirement holds because

$$
10^6D^3=64\,000\,000s^{12}\le2^{32}s^{12}=Q.
$$

Also $100Dh=400s^5\le Q$. Since $s\ge4$,

$$
5s(s-1)<s^4=m^c,
$$

which supplies the honest-degree capacity. All hypotheses of completeness and soundness are therefore met for the same field, grid and roots. The [parameter family][lean-parameters] and [least-exponent argument][lean-choice] include small graph sizes explicitly.

To obtain the logarithmic resource bounds, minimality matters. If $a>2$, then

$$
(a-1)2^{a-1}<\lceil\log _2N\rceil,
\qquad
a2^a\le4(a-1)2^{a-1}.
$$

If $a=2$, the volume $a2^a$ is eight. Both cases yield

$$
a2^a\le4\max\{8,\lceil\log _2N\rceil\}
\le32(\lceil\log _2N\rceil+1).
$$

Thus a resource bounded by a fixed multiple of $a2^a$ is logarithmic in $N$; a resource bounded by $2^{O(a2^a)}$ is polynomial in $N$. Merely knowing that the grid can hold the graph would not give these upper bounds.
<!-- /passage:pcp-long-parameters -->

### From finite samples to fair random bits

<!-- passage:pcp-long-fair-bits -->
Some mathematical correctors use uniformly distributed nonzero field parameters. Sampling uniformly from $F^{\times}$ with a fixed fair-bit budget is inconvenient because $Q-1$ is not a power of two. The implemented verifier instead samples all four such parameters from the whole field. If any is zero, it accepts immediately and makes no queries. Otherwise it runs the seven-check verifier.

Conditioned on all four being nonzero, the decoded seed has exactly the original product-uniform distribution. Every other coordinate is unchanged. Therefore

$$
\Pr[\text{new verifier rejects}]
=\left(\frac{Q-1}{Q}\right)^4
\Pr[\text{original verifier rejects}].
$$

Since $Q\ge2$, the factor is at least $1/16$. Perfect completeness survives, and non-colourable graphs have rejection at least $\delta=g_4/16$. This is an exact counting identity on the two finite seed spaces, as proved by [whole-field sampling][lean-sampling]; it does not use an approximation to a uniform distribution.

Every remaining random coordinate is a field vector, a Boolean coefficient vector or a finite product of such objects. The chosen linear coordinates and explicit product codecs give a bijection between the entire seed space and a fixed-length bit string. Uniform bit strings therefore induce exactly the required distribution. Likewise, a tagged mixed-radix codec packs the eight physical tables into one finite binary word. Encoding and decoding are inverse, and the query list is translated through the same codec.
<!-- /passage:pcp-long-fair-bits -->

<!-- passage:pcp-long-resources -->
Here is how polynomial proof length follows for the actual eight-table address space. A degree-$r$ Boolean label on $t$ coordinates has

$$
b_r(t)=\sum_{j=0}^{r}\binom tj
$$

binary coefficients, so there are $C_r=2^{b_r(t)}$ labels. The four primary-table lengths are

$$
Q^dC_3,\quad Q^{2d}C_1,\quad Q^{2d}C_3,\quad Q^{4d}C_1.
$$

A line table for a polynomial on $j$ coordinates indexes two field points specifying a line, the $cm$ coordinates of its reduced-degree encoding, and a linear Boolean label. Its length is $Q^{2j+cm}C_1$. Thus the four auxiliary lengths are

$$
Q^{2d+cm}C_1,\quad Q^{4d+cm}C_1,\quad
Q^{4d+cm}C_1,\quad Q^{8d+cm}C_1.
$$

Since $b_1(t)\le b_3(t)\le(t+1)^3$, the sum of these eight lengths is at most

$$
2^{(8d+cm)t+(t+1)^3+3}.
$$

For $d=m=2^a$, $c=4$ and $t=12a+32$, the exponent is at most $132\,000a2^a$. One elementary estimate controls the cubic term: $a^2\le4\cdot2^a$ for every natural $a$, and $12a+33\le32a$ for $a\ge2$. Hence $(t+1)^3\le131\,072a2^a$; the remaining linear terms fit within the stated bound.

For the seed count, write $u=\binom t2$ and $v=\binom t3$ in the following table. The affine and cubic Hadamard tests use $3(1+t)$ and $5+5t+3u+2v$ bits. The inner test uses $1+3tcm+2t+3(1+t)=4+3tcm+5t$ bits, including the fair choice bit and the data sampled for both alternatives. Expanding the seven product seeds gives:

| Check | Power-of-two exponent | Nonzero-field draws |
| --- | --- | ---: |
| Colour low-degree | $2td+4tcm+12t+9+3u+2v$ | $0$ |
| Vertex-certificate low-degree | $4td+4tcm+10t+7$ | $0$ |
| Difference low-degree | $4td+4tcm+12t+9+3u+2v$ | $0$ |
| Edge-certificate low-degree | $8td+4tcm+10t+7$ | $0$ |
| Vertex ZERO | $5td+8tcm+12t+9+u+v$ | $2$ |
| Edge ZERO | $10td+8tcm+12t+9+u+v$ | $2$ |
| Difference consistency | $2td+t$ | $0$ |

The original seed space therefore has size $(Q-1)^4 2^{35td+32tcm+69t+50+8u+6v}$. Replacing the four nonzero-field draws by whole-field draws adds $4t$ bits. The exact fair-bit seed length is

$$
r=35td+32tcm+73t+50+8\binom t2+6\binom t3.
$$

This counts every product coordinate, even when a branch ignores it or the whole-field wrapper accepts early. The same elementary estimates bound $r$ by $10^6a2^a$. Combining both estimates with $a2^a\le32(\lceil\log_2N\rceil+1)$, and using $2^{\lceil\log_2N\rceil}\le2\max\{1,N\}$, gives

$$
\begin{aligned}
r(N)&\le32\,000\,000(\lceil\log _2N\rceil+1),\\
\operatorname{proofLength}(N)&\le(4\max\{1,N\})^{4\,224\,000},\\
\#\operatorname{queries}&\le187.
\end{aligned}
$$

These are proved upper bounds, with very large constants. They establish the complexity class statement; they are not practical resource estimates. The proof-size estimate concerns the actual packed eight-table address space, and the query estimate concerns addresses in that space. [The exact seed count][lean-seed-size], [address-space estimates][lean-resources] and [binary-verifier guarantees][lean-binary] give these calculations together with perfect completeness and the rejection bound.

For an encoded graph input $x$, its decoded vertex count is at most $n=|x|$. The verifier uses the canonical budget

$$
r_0(n)=32\,000\,000\lceil\log _2(n+2)\rceil+32\,000\,000.
$$

It ignores the surplus bits beyond those needed by the exact seed codec. Every shorter bit string has exactly the same number of extensions, so prefix sampling preserves the acceptance probability. The proof address bound becomes the natural-coefficient polynomial

$$
p_0(n)=\bigl(4(n+1)\bigr)^{4\,224\,000}.
$$

The nonadaptive list of at most 187 physical reads is compiled into a decision tree of that depth. Its evaluation equals the algebraic verdict for every oracle, and all syntactic addresses are below $p_0(n)$. The [canonical verifier][lean-canonical] proves these properties for every bit string, including malformed graph encodings according to its fixed decoder.
<!-- /passage:pcp-long-resources -->

### Repetition on one fixed proof

<!-- passage:pcp-long-amplification -->
With the constants fixed above, exact rational arithmetic gives

$$
g_4=\frac1{71\,115\,455\,156\,448},\qquad
\delta=\frac1{1\,137\,847\,282\,503\,168}.
$$

Set $R=\lceil1/\delta\rceil$. Run the base verifier $R$ times with independent seeds on the **same** proof, and accept only if every run accepts. For a fixed proof with single-run acceptance $u$, independence gives acceptance $u^R$. In a no-instance, $u\le1-\delta$, so it remains to show $(1-\delta)^R\le1/2$.

An elementary inequality proves this without logarithmic approximation:

$$
(1+k\delta)(1-\delta)^k\le1
\quad(k\ge0, 0\le\delta\le1).
$$

The base case is equality. For the induction step,

$$
(1+(k+1)\delta)(1-\delta)
=1+k\delta-(k+1)\delta^2\le1+k\delta;
$$

multiply by the nonnegative factor $(1-\delta)^k$. Since $R\delta\ge1$, division gives

$$
(1-\delta)^R\le\frac1{1+R\delta}\le\frac12.
$$

The same honest proof still accepts on every repeated seed. Repetition leaves the proof-length polynomial unchanged and multiplies the query and random-bit budgets by the fixed constant $R$. Here $R=1\,137\,847\,282\,503\,168$ and $187R=212\,777\,441\,828\,092\,416$. The [rational repetition bound][lean-repetition-bound] and [amplified verifier][lean-amplified] retain these fixed choices. A prover cannot supply a different proof after seeing each seed; the probability statement quantifies over one proof before the product distribution.
<!-- /passage:pcp-long-amplification -->

### The polynomial-time implementation

<!-- passage:pcp-long-runtime -->
The information-theoretic verifier must be implemented by a polynomial-time machine; a bounded number of oracle queries alone does not provide this. The formal implementation computes the parameters, field arithmetic, seed codecs, query addresses and verdict in a fixed program language and compiles that language to Mathlib's finite multi-stack `FinTM2` machine model. A verifier step takes the input, random seed and answer history, then either halts with a verdict or requests the next proof address. The implementation relation states that executing these steps produces the specified bounded query tree, on both possible answers at every queried branch.

The concrete operations can be bounded as follows. Parameter selection is a bounded search for the least admissible $a$. Field elements have $t=12a+32$ binary coefficients; arithmetic reduces polynomial representatives modulo the computed irreducible modulus, and inversion uses powering. The modulus, cube root and full generator are obtained by bounded finite searches, with candidate tests expressed in the same finite arithmetic. Their search ranges are polynomial in the field cardinality $Q$, and $Q=2^{32}s^{12}$ is polynomially bounded in the input length. For example, the charged modulus-construction cost is at most $7\,000\,000(Q+1)^7$; each root search costs at most $400\,000\,000(Q+4)^6$; the combined field-and-roots routine costs at most $10^9(Q+4)^7$. [These cost proofs][lean-field-cost] include candidate testing and storage. The runtime construction computes the parameters and arithmetic data from the input. For the underlying finite-field construction, see Shoup [Sections 20.2 and 21.1][shoup], especially the irreducible-polynomial existence result in Theorem 20.11. Shoup also analyses irreducibility testing and randomized construction. The deterministic bounded searches and charged cost estimates above are those of the formal implementation.

The public edge extension is evaluated from the input adjacency matrix by finite interpolation sums. The grid and its pair space have polynomial size because $s^s=2^{a2^a}$ and the preceding volume bound is logarithmic. Lagrange weights, degree-reduction coordinates and label transformations use bounded arithmetic loops. The proof-address values are polynomially bounded by $p_0(n)$; the implementation proves bounds for the sizes of their stored representations as well as for the number of addresses.

The base callback has two passes. A discovery pass constructs the exact list of physical queries. A replay pass evaluates the algebraic verdict using the answer history at those addresses. The invalid whole-field-seed case emits no queries and returns acceptance. [Callback correctness][lean-runtime-correct] proves that these outputs agree with the mathematical query list and verdict for arbitrary input, seed and answer words. This is stronger than correctness only on honest proof responses.

For cost, the proof assigns polynomial bounds to the setup, generated-query storage and branch computations, then substitutes each bound into the routine that consumes it. Concretely, if query storage is bounded by $C_q(n+1)^{d_q}$ and a branch's cost has degree $d_b$ in the size of its input/history, the combined proof takes an exponent at least

$$
\max\{84,d_q,(d_q+1)d_b\}.
$$

Constants are enlarged to absorb the two passes, fixed seven-branch overhead and setup. The resulting theorem bounds the charged cost by $C(|x|+|r|+|u|+1)^e$ for every answer history $u$. The [polynomial-cost proof][lean-runtime-cost] retains the query-size premise until the separately proved storage bound supplies it.

The repetition protocol slices the random string into $R$ blocks, invokes this same callback, and manages the answer history. Because $R$ is fixed, the protocol's loop and storage overhead are polynomial. Its compiler and public input/output codecs preserve the callback's semantics and translate the charged cost to a step bound on the finite machine. Thus [the runtime theorem][lean-runtime] concludes polynomial-time implementation of the actual amplified query algorithm. The low-level compiler, array arithmetic and finite-search proofs are supporting implementation lemmas; this account uses their stated semantic and cost guarantees and explains their composition, rather than reproducing their individual machine-state derivations.
<!-- /passage:pcp-long-runtime -->

### From every NP verifier to a graph

<!-- passage:pcp-long-np-tableau -->
Fix an NP language $L$, a Boolean witness relation $R(x,w)$, a natural-coefficient witness bound $q$, and its concrete polynomial-time checker. Then

$$
x\in L\iff\exists w\ (|w|\le q(|x|)\ \text{and}\ R(x,w)=1).
$$

Let $T_0$ be the checker's time polynomial. At input length $n$, one bound valid for all permitted witnesses is

$$
T(n)=T_0(n+q(n)+1).
$$

The $+1$ accounts for the delimiter in the fixed pair encoding. If the machine pushes at most $B$ cells per step, a sufficient stack-space bound is

$$
S(n)=n+q(n)+1+B T(n).
$$

Represent a computation by $T(n)+1$ rows of bounded configurations, with the witness length and bits included. The constraints enforce the initial row, every adjacent transition and the accepting final row. Halting is padded by the machine's bounded-evaluation convention. Every true computation gives such a tableau within the space bound. Conversely, determinism and the transition constraints force each successive row to be the actual machine configuration, so an accepting tableau gives a witness with $R(x,w)=1$. This proves the [finite tableau equivalence][lean-tableau] for all witness lengths from zero through $q(n)$.
<!-- /passage:pcp-long-np-tableau -->

<!-- passage:pcp-long-local-constraints -->
To make the tableau a bounded-arity constraint system, use a finite alphabet fixed by the source machine. Each row has one control-and-prefix variable and one optional-symbol variable for each stack position below $S(n)$. Let $w_0$ be the machine's fixed window size. Link constraints identify the stored prefix with the first $w_0$ cells of every stack.

The locality theorem for the machine states that a successor stack consists of the output produced from this prefix followed by the untouched old suffix starting at position $w_0$. The possible output-prefix lengths are bounded by a machine-fixed number $b_0$. Consequently the new symbol at position $j$ is either a symbol in that computed output prefix, or the old symbol at

$$
w_0+(j-\lambda),
$$

where $\lambda\le b_0$ is the actual output-prefix length. A cell constraint reads the old prefix, the new cell, and the $b_0+1$ candidate old cells corresponding to every possible $\lambda$. The finite transition table selects the correct candidate. This gives fixed arity without placing an entire, input-sized stack in one variable. Positions outside the space bound read a single distinguished blank variable. [The cell-step reconstruction][lean-tableau-cells] proves that a row representing a real configuration, with linked prefix and satisfying cell constraints, represents exactly its successor. The proved growth bound ensures that no actual successor cell is lost at the boundary.

Initial constraints fix the input bits, delimiter and all other stacks. In the next $q(n)$ positions they permit guessed Boolean symbols or blanks; adjacent constraints require every blank to be followed by a blank. Thus those cells describe exactly a witness of some length from zero through $q(n)$, without requiring the checker to reject longer words. Final constraints fix the accepting halt configuration. Induction on the rows now reconstructs a real accepting computation from a satisfying assignment. Reading the rows of a real accepting computation supplies the converse.

For $k$ stacks, the source gives the variable count

$$
v(n)=(T(n)+1)(1+kS(n))+1,
$$

including a blank variable. The constraint count is

$$
c(n)=1+(T(n)+1)kw_0+T(n)+T(n)kS(n)
+2(1+kS(n))+q(n).
$$

Both are polynomials: the terms count the blank test, prefix links, control steps, cell steps, two boundaries and witness-adjacency tests respectively. The [cell-constraint construction][lean-cell-constraints] and [assembled reduction][lean-np-reduction] provide these directions and the explicit index codecs. There is also a machine-fixed degenerate case: if the proposed accepting output contains a symbol outside the machine's finite reachable support, the checker can never accept. The reduction then emits a fixed non-three-colourable graph. Thus the theorem needs no extra assumption that acceptance is possible.
<!-- /passage:pcp-long-local-constraints -->

<!-- passage:pcp-long-clause-reduction -->
A constraint over an alphabet of size $A$ is converted to Boolean constraints by one-hot coding. Each source variable receives $A$ bits, exactly one of which is true; its true index is the encoded symbol. Validity constraints enforce this condition. A relation inspects the relevant one-hot blocks and accepts precisely the tuples accepted by the original finite relation. The alphabet size and local arity are constants fixed by the original machine. [The finite-domain encoding][lean-one-hot] proves that decoding a satisfying one-hot assignment and encoding a source assignment preserve all constraints.

For completeness of the next step, consider any Boolean relation $R_e$ on $k_0$ input bits. For every pattern $p\in\{0,1\}^{k_0}$, introduce flags $z_0,\ldots,z_{k_0}$ with

$$
z_0=0,\qquad z_{i+1}=z_i\lor(x_i\mathbin{\mathrm{xor}}p_i),
\qquad R_e(p)\lor z_{k_0}=1.
$$

An OR equation $z=x\lor y$ is enforced by the three clauses

$$
(z\lor\neg x),\qquad(z\lor\neg y),\qquad(\neg z\lor x\lor y),
$$

padding short clauses with false. The flags are forced to record whether the actual input differs from the prefix of $p$. Thus the final clause is automatic when $x\ne p$, and when $x=p$ it requires $R_e(x)=1$. This proves both directions of the reduction, with $2^{k_0}(3k_0+2)$ three-literal clauses per relation. It is polynomial because $k_0$ is fixed, not because an exponential in a varying arity would be harmless. These are the actual [Boolean clauses][lean-boolean-clauses] used by the implementation.
<!-- /passage:pcp-long-clause-reduction -->

<!-- passage:pcp-long-colouring-gadget -->
A three-literal OR clause $a\lor b\lor c$ is equivalent to the existence of a fresh bit $z$ satisfying

$$
\operatorname{NAE}(a,b,z),\qquad
\operatorname{NAE}(\neg z,c,0),
$$

where NAE means that the three values are not all equal. If $a=b=0$, the first clause forces $z=1$, and the second then forces $c=1$. If $a=b=1$, take $z=0$, which makes the second clause automatic. If $a\ne b$, take $z=0$, and both hold. These cases prove equivalence.

To encode NAE by a graph, make a palette triangle with colours $0,1,2$. Each Boolean variable has two adjacent vertices, one for itself and one for its negation; both are joined to palette vertex 2. They must therefore receive complementary colours 0 and 1. Constant literals 0 and 1 use the corresponding palette vertices. For a NAE clause, make a new triangle and join its $i$-th vertex to the vertex for its $i$-th literal. If the three literal colours are equal, every vertex of the new triangle is forbidden that colour, so three distinct colours are impossible. If the literals are not all equal, the triangle can be coloured: for literal colours $(0,0,1)$, use triangle colours $(1,2,0)$; complementing or permuting yields the other cases. A colouring of the whole graph can first be relabelled so the palette has colours 0,1,2, after which it yields a satisfying Boolean assignment. The [NAE graph theorem][lean-nae] proves these two constructions.

The graph has one palette triangle, two vertices per Boolean variable and three vertices per NAE clause. Encoding its adjacency matrix therefore has quadratic length in those counts. Composing with the one-hot and fixed-arity constructions gives a polynomial-length graph encoding $f(x)$, with

$$
G_{f(x)}\text{ is three-colourable}\iff x\in L.
$$
<!-- /passage:pcp-long-colouring-gadget -->

<!-- passage:pcp-long-reduction-runtime -->
The reduction is executable. The program computes $T(n)$, $S(n)$ and the fixed source dimensions, enumerates the tableau variables and relations using arithmetic sum/product indices, emits the fixed-arity clauses and gadgets, and writes the graph's bitstring. The fixed finite alphabet and fixed relation arity make truth-table enumeration constant work per relation up to the machine-dependent factor $2^{k_0}$. Matrix emission is polynomial in the already bounded vertex count.

More explicitly, the [program-bearing reduction theorem][lean-np-runtime] returns $f,p,P,C,e$, all depending only on the NP certificate, such that on every input $x$, program $P$ emits exactly $f(x)$, its charged cost is at most $C(|x|+1)^e$, the output length is at most $p(|x|)$, and graph colourability is equivalent to $x\in L$. The source derives the program cost from fixed polynomial preprocessing plus a sixth-degree bound in the preprocessing size and the variable/constraint counts. Substitution of their polynomial bounds is again a polynomial. The compiler and fixed public symbol codecs give the corresponding finite-machine certificate. These retained data are what the final verifier uses to preprocess its input.
<!-- /passage:pcp-long-reduction-runtime -->

### Transporting the verifier through the reduction

<!-- passage:pcp-long-seed-transport -->
Let the amplified graph verifier use exactly $A\lceil\log _2(n+2)\rceil+B$ random bits, and let $|f(x)|\le p(|x|)$, where $p\in\mathbb N[X]$. Put $e=\deg p$, using the source's natural-degree convention for the zero polynomial. Since the coefficients are nonnegative,

$$
p(n)\le p(1)(n+2)^e,
\qquad
p(n)+2\le(p(1)+2)(n+2)^e.
$$

The first inequality follows term by term from $n^i\le(n+2)^e$ for every exponent with nonzero coefficient; the second also uses $(n+2)^e\ge1$. Therefore

$$
\lceil\log _2(p(n)+2)\rceil
\le e\lceil\log _2(n+2)\rceil
+\lceil\log _2(p(1)+2)\rceil.
$$

Choose source randomness

$$
a=Ae,\qquad b=A\lceil\log _2(p(1)+2)\rceil+B.
$$

These formulas remain valid for constant and zero polynomials; the slope can be zero. On $x$, compute $f(x)$, use the initial portion of the random word needed by the graph verifier, and ignore the rest. Equal-size fibres of the prefix map preserve the exact acceptance probability. If the graph proof bound is $p_0$, the transported bound is $p_0\circ p$, by monotonicity of natural-coefficient polynomials. The query budget is unchanged. [The resource-transport proof][lean-transport] gives these formulas, while [final assembly][lean-assembly] composes the executable reduction with the actual query algorithm.

This completes the forward theorem: membership in $L$ gives an honest proof for the reduced colourable graph; nonmembership gives a non-colourable graph and hence acceptance at most $1/2$ for every proof. Polynomial preprocessing composed with the polynomial-time graph protocol remains polynomial. All coefficients and degrees depend on the original NP verifier, never on the particular input or proof.
<!-- /passage:pcp-long-seed-transport -->

### The reverse inclusion

<!-- passage:pcp-long-converse -->
Suppose a language has a verifier satisfying the target conditions. An NP witness can be the first $p(n)$ proof bits. The deterministic witness checker runs the verifier for every random seed and accepts exactly if all runs accept.

There are polynomially many seeds. Indeed,

$$
2^{a\lceil\log _2(n+2)\rceil+b}
\le2^b\bigl(2(n+2)\bigr)^a.
$$

For each seed, at most $\ell$ answers are requested. Each address is below $p(n)$, and looking up a bit in the supplied finite witness takes polynomial time even using a linear scan. The implementation of each query step is polynomial in the input, random string and bounded answer history. Enumerating all seeds, simulating these runs and accumulating their conjunction therefore takes polynomial time. The [concrete finite-witness checker][lean-concrete-converse] supplies this closure in the same finite-machine model.

If $x\in L$, perfect completeness gives a proof accepted on every seed. Truncating it to its first $p(n)$ bits preserves every run because no branch reads another address. Conversely, if a finite witness is accepted on every seed, extend it by zeros to an infinite oracle. The acceptance probability of this oracle is one. If $x\notin L$, soundness would make it at most $1/2$, a contradiction. Thus the finite witness relation characterizes $L$, proving the reverse inclusion.

The remaining task is to identify this certificate class with the reference nondeterministic-machine definition of NP in the unchanged vendored Complexitylib. The [reference-NP equivalence][lean-reference-np] uses two concrete simulations.

For the direction from a polynomial-time nondeterministic machine to certificates, a witness records the bounded sequence of nondeterministic choices. A deterministic path checker follows the supplied choices and checks that the machine has accepted when the list ends; the time bound limits the admissible witness length. Its compiled program has polynomial cost, giving a certificate verifier in the concrete model used above.

For the converse, translate the concrete certificate checker into a reference decision machine. A bounded-guess construction computes and enforces the polynomial witness-length bound, guesses a witness within it, and runs the translated checker. An accepting branch exists exactly when an accepted certificate does. The translation and bounded-guess theorems supply the simulation and runtime guarantees; they are imported machine proofs, not additional premises left to the reader. Together these directions identify the certificate class in the PCP theorem with the intended reference NP class.
<!-- /passage:pcp-long-converse -->

[paper-pcp]: https://arxiv.org/html/2608.17429v2#S7
[lean-theorem]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Theorem.lean#L25
[lean-colour-algebra]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorAlgebra.lean#L94
[lean-colour-grid]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorGrid.lean#L135
[lean-seven-checks]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorVerifier.lean#L37
[lean-query-budget]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorVerifier.lean#L362
[lean-completeness]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorVerifierCompleteness.lean#L101
[lean-soundness]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorVerifierSoundness.lean#L58
[lean-difference]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BinaryDifferenceConsistency.lean#L297
[lean-decoded]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorDecodedSoundness.lean#L86
[lean-budget]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorSoundnessBudget.lean#L142
[lean-parameters]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorParameters.lean#L168
[lean-choice]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorParameterChoice.lean#L89
[lean-sampling]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorFullFieldSampling.lean#L160
[lean-binary]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorBinaryVerifier.lean#L250
[lean-canonical]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorCanonicalVerifier.lean#L168
[lean-repetition-bound]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/RationalRepetitionBound.lean#L59
[lean-amplified]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorAmplifiedVerifier.lean#L72
[lean-runtime-correct]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/ThreeColorBaseCorrect.lean#L14
[lean-runtime-cost]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/ThreeColorBasePolynomial.lean#L55
[lean-runtime]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/ThreeColorRuntime.lean#L11
[lean-tableau]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/NPTableau.lean#L142
[lean-cell-constraints]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/NPCellConstraints.lean#L227
[lean-np-reduction]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Reduction/NPThreeColor.lean#L144
[lean-boolean-clauses]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Reduction/FiniteBooleanConstraints.lean#L187
[lean-nae]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Reduction/NAEThreeColor.lean#L241
[lean-np-runtime]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Reduction/NPThreeColorRuntime.lean#L257
[lean-transport]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Verifier/ReductionResources.lean#L35
[lean-assembly]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorFinalAssembly.lean#L54
[lean-concrete-converse]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/ReverseConcrete.lean#L33
[lean-reference-np]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/ReferenceNPConverse.lean#L39
[lean-seed-size]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorSeedSize.lean#L170
[lean-resources]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorResourceBounds.lean#L44
[lean-field-cost]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/ThreeColorFieldSetupCost.lean#L45
[lean-tableau-cells]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/TableauCells.lean#L155
[lean-one-hot]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Reduction/FiniteDomainConstraints.lean#L119


## Algebraic tests and correction

<!-- passage:pcp-long-algebra-scope -->
The algebraic part of the construction has two distinct tasks. It must recognize a word that is close to a low-degree polynomial, and it must recover a specified value of that polynomial from the word. This chapter proves the forms of these statements used in Lee's formalization. It also develops the interpolation and vanishing certificates needed to express constraints on an encoded assignment.

Throughout, $F$ is a finite field of cardinality $q$, and $V=F^m$, with $m$ allowed to be zero. Every probability and expectation is uniform on its displayed finite domain. Write

$$
\Delta(f,g)=\Pr_x[f(x)\ne g(x)].
$$

An assertion about the total degree of a polynomial refers to a formal polynomial in $F[X_1,\ldots,X_m]$. Equal evaluation functions need not be equal formal polynomials over a finite field. Where the proof passes from evaluations to polynomial identities, the necessary degree bound will be stated. We use basic field arithmetic, finite-dimensional linear algebra, and the univariate root bound: a nonzero polynomial of degree at most $d$ has at most $d$ roots. All further ingredients needed for the testing argument are proved below.

The primary paper is the corrected public revision of Amireddy, Behera, Srinivasan, Sudan and Willumsgaard, *A Simple Algebraic Proof of the PCP Theorem*, [arXiv:2608.17429v2][paper]. The theorem statements below follow the pinned Lean source when it makes a more specific choice of test or constants. In particular, the short test uses a generator of the whole multiplicative group and Lagrange weights. The point-versus-line test samples its line parameter from all of $F$.

<!-- /passage:pcp-long-algebra-scope -->

### 1. Polynomial distance, interpolation, and grid certificates

<!-- passage:pcp-long-algebra-polynomial-distance -->
**Polynomial distance.** If $P\ne0$ has total degree at most $d$, then

$$
\Pr_{x\in F^m}[P(x)=0]\le d/q.
\tag{A1}
$$

For completeness, induct on $m$. For $m=0$, a nonzero polynomial is a nonzero constant. In the induction step write

$$
P(X,T)=\sum_{j=0}^r P_j(X)T^j,\qquad P_r\ne0.
$$

The coefficient $P_r$ has total degree at most $d-r$. The induction hypothesis bounds the fraction of $X$ for which it vanishes by $(d-r)/q$. For every other $X$, the specialization in $T$ is nonzero of degree $r$, so at most $r/q$ of its evaluations vanish. Bounding the contribution from exceptional bases by their full probability gives at most $(d-r)/q+r/q=d/q$.

Thus distinct polynomials of total degree at most $d$ have evaluation distance at least $1-d/q$. In particular, evaluation is injective on these polynomials when $d<q$. Two such polynomials cannot both lie at distance less than $r$ from one word when $2r\le1-d/q$: the triangle inequality would make their mutual distance strictly smaller than $1-d/q$. This strict inequality will be used when choosing nearest line polynomials. See the [polynomial-distance bound][lean-distance].

<!-- /passage:pcp-long-algebra-polynomial-distance -->

<!-- passage:pcp-long-algebra-grid-interpolation -->
**Grid extension.** Let $H\subseteq F$ be nonempty, and put $h=|H|$. For $a\in H$, define

$$
\ell_a(T)=\prod_{b\in H\setminus\{a\}}\frac{T-b}{a-b}.
$$

The denominators are nonzero, and $\ell_a(b)$ is one for $b=a$ and zero for all other $b\in H$. Therefore a table $f:H^m\to F$ has the extension

$$
\widetilde f(X)=\sum_{z\in H^m}f(z)\prod_{i=1}^m\ell_{z_i}(X_i).
\tag{A2}
$$

Its degree in each variable is at most $h-1$, and its total degree is at most $m(h-1)$. It agrees with $f$ because precisely one summand survives at each grid point. It is the unique polynomial with these individual degree bounds and these evaluations. To prove uniqueness, a difference polynomial vanishing on $H^m$, regarded as a polynomial in its last variable, has $h$ roots after every specialization of the others. Its degree is less than $h$, so each coefficient vanishes on $H^{m-1}$; induction makes every coefficient zero. The empty product and singleton zero-dimensional grid give the same assertion when $m=0$. See the [grid interpolation proof][lean-interpolation].

<!-- /passage:pcp-long-algebra-grid-interpolation -->

<!-- passage:pcp-long-algebra-grid-vanishing -->
**Vanishing on the grid.** Set

$$
Z_i(X)=\prod_{a\in H}(X_i-a).
$$

A polynomial $P$ vanishes on $H^m$ if and only if it admits the formal identity

$$
P=\sum_{i=1}^m Q_i Z_i.
\tag{A3}
$$

Moreover, the coefficients can be chosen so that every nonzero $Q_i$ satisfies

$$
\deg Q_i+h\le\deg P.
\tag{A4}
$$

To see this, divide successively by the monic polynomials $Z_1,\ldots,Z_m$, treating the other variables as coefficients. At the $i$-th step remove every term whose exponent of $X_i$ is at least $h$. Replacing the leading term $X_i^h$ by lower powers never increases total degree. The quotient terms have lost $h$ from their degree, proving (A4). Later divisions do not increase degrees in previously processed variables, since their divisors involve only their own coordinate. The result is $P=\sum Q_iZ_i+R$, where $R$ has individual degrees less than $h$. If $P$ vanishes on the grid, so does $R$; uniqueness in (A2) gives $R=0$. The converse follows by evaluation, since every $Z_i$ vanishes there. This also proves the assertion in dimension zero: a vanishing constant is zero and the sum is empty. See the [grid decomposition][lean-grid].

Package (A3) as one polynomial in two blocks of variables:

$$
M(X,Y)=\sum_i Q_i(X)Y_i.
$$

It satisfies the formal identities

$$
M(X,0)=0,\qquad M(X,Z_1(X),\ldots,Z_m(X))=P(X),
\tag{A5}
$$

and $\deg M\le\deg P$, since $h\ge1$ and (A4) gives $\deg Q_i+1\le\deg P$. Conversely, any polynomial $M$ satisfying (A5), including one nonlinear in $Y$, proves that $P$ vanishes on the grid: at a grid point the two substitutions have the same value. Nonemptiness of $H$ is needed for the degree-bounded existence direction. On an empty grid of positive dimension, the constant one vanishes vacuously but has no degree-zero certificate whose zero substitution is zero. Finally, substitution of the $Z_i$'s into an arbitrary degree-$D$ certificate has degree at most $hD$: each substituted variable has degree at most $h$, so each monomial's degree grows by at most that factor. See the [certificate and substitution bounds][lean-certificate].

<!-- /passage:pcp-long-algebra-grid-vanishing -->

<!-- passage:pcp-long-algebra-line-characterization -->
**From exact lines to total degree.** Suppose $q>2d$, and every function

$$
t\longmapsto f(u+tv),\qquad u,v\in V,
$$

is represented by a univariate polynomial of degree at most $d$. Then $f$ is represented by a multivariate polynomial of total degree at most $d$.

We prove the claim by induction on the dimension. Choose $d+1$ distinct values $a_0,\ldots,a_d\in F$ for the first coordinate. Each slice $y\mapsto f(a_i,y)$ has the same exact-line property in one less dimension and therefore, by induction, is represented by a total-degree-$d$ polynomial $P_i(y)$. Interpolate the slices:

$$
Q(x,y)=\sum_{i=0}^d\ell_i(x)P_i(y).
$$

This polynomial has total degree at most $2d$. For fixed $y$, both $Q(\cdot,y)$ and the prescribed polynomial representing the first-coordinate line have degree at most $d$ and agree at $d+1$ nodes. They are equal, so $Q$ represents $f$ everywhere.

It remains to improve total degree from $2d$ to $d$. For every direction $v$, the formal polynomial $Q(tv)$ has degree at most $2d<q$ and agrees at all $q$ parameters with a degree-$d$ polynomial. The root bound makes the polynomials identical. Write $Q=\sum_k Q_k$, where $Q_k$ is its homogeneous degree-$k$ part. The coefficient of $t^k$ in $Q(tv)$ is $Q_k(v)$, so $Q_k$ vanishes everywhere for $k>d$. Each such component has degree at most $2d<q$; (A1) forces it to be the zero polynomial. Thus $Q$ has total degree at most $d$. No assertion that arbitrary equal polynomial functions have equal formal degree has been used. See the [finite-field line characterization][lean-lines]. The corresponding classical result is Friedl–Sudan, [Lemma 4 of the corrected 2013 reissue][friedl-sudan]: in characteristic $p$, their hypothesis is $q-q/p-1\ge d$. The stronger sufficient hypothesis used here gives the direct interpolation proof above.

<!-- /passage:pcp-long-algebra-line-characterization -->

### 2. The corrected short low-degree test

<!-- passage:pcp-long-algebra-generator-test -->
Let $c\ge0$, assume $q>2c$, and choose a generator $\zeta$ of $F^\times$. Put

$$
a_i=\zeta^i\quad(1\le i\le c+1),\qquad
w_i=\prod_{\substack{1\le j\le c+1\\j\ne i}}
\frac{-a_j}{a_i-a_j}.
\tag{A6}
$$

These nodes are distinct and nonzero. Indeed, $c+1\le q-1$ for $c>0$, and the $c=0$ case has only one node. The weights are all nonzero. They are the Lagrange interpolation coefficients for evaluation at zero, so $\sum_i w_i=1$.

For a word $f:V\to F$, define

$$
A_f(x,v)=\sum_{i=1}^{c+1}w_i f(x+a_iv).
$$

The test chooses $x,v\in V$ and accepts if $f(x)=A_f(x,v)$. It makes $c+2$ listed queries, including the center; coincident points, for example when $v=0$, need not give distinct locations. Every polynomial of total degree at most $c$ passes every test: restrict it to the affine line and apply Lagrange interpolation at zero.

Conversely, if every test accepts, $f$ is a total-degree-$c$ polynomial function. First prove this on $F$. Interpolate a polynomial $P$ of degree at most $c$ through $f(a_1),\ldots,f(a_{c+1})$, and let $h=f-P$. The constraints are linear, so $h$ satisfies them and vanishes at these nodes. The constraint with center zero and direction one gives $h(0)=0$. For $n>c+1$, use center zero and direction $\zeta^{n-(c+1)}$:

$$
0=\sum_{i=1}^{c+1}w_i h\bigl(\zeta^{n-(c+1)+i}\bigr).
$$

All exponents except the last are smaller positive integers. Induction and $w_{c+1}\ne0$ give $h(\zeta^n)=0$. The initial nodes and induction include the exponents $1,\ldots,q-1$, which exhaust $F^\times$. Thus $h=0$.

For a word on $V$, fix any affine line and apply the same univariate argument. Its constraint at parameters $r,s\in F$ is exactly the original constraint at center $u+rv$ and direction $sv$. Every line is consequently degree at most $c$. The exact-line characterization applies because $q>2c$. This proof includes $c=0$ and arbitrary field characteristic. See the [corrected generator test][lean-generator].

<!-- /passage:pcp-long-algebra-generator-test -->

<!-- passage:pcp-long-algebra-weighted-plurality -->
We first prove robustness for weighted affine constraints, before applying it to polynomials. Let $a_1,\ldots,a_n\in F^\times$, allow arbitrary weights $w_i\in F$, and use the same prediction formula with $n$ terms. Neither distinctness of nodes nor nonzero weights is needed in this paragraph. Set

$$
\delta=\Pr_{x,v}[f(x)\ne A_f(x,v)],\qquad
g(x)=\mathop{\mathrm{plurality}}_v A_f(x,v),
$$

breaking any tie arbitrarily. Then

$$
\Delta(f,g)\le2\delta.
\tag{A7}
$$

For a fixed $x$ with $g(x)\ne f(x)$, the probability of prediction $f(x)$ is at most one half, since the distinct plurality value is at least as frequent. Thus the conditional rejection probability is at least one half. Averaging proves (A7).

We next bound predictions at **each** center. Introduce the weighted grid

$$
D(x;y,z,b)=\sum_{i,j}w_iw_j
f(x+a_i y+a_j z+a_i a_j b).
\tag{A8}
$$

For fixed $x,z$, and uniform $y,b\in V$, each pair

$$
(x+a_i y,\ z+a_i b)
$$

is uniform on $V^2$, since multiplication by $a_i\ne0$ is invertible. Except on probability at most $n\delta$, all $n$ corresponding constraints hold. Summing these constraints with weights $w_i$ gives $A_f(x,y)=D(x;y,z,b)$. The expression $D$ is symmetric under exchanging $y,z$, because its double sum can exchange $i,j$. Thus, over independent $y,z,b$, it also equals $A_f(x,z)$ except on probability at most $n\delta$. Consequently

$$
\Pr_{y,z}[A_f(x,y)\ne A_f(x,z)]\le2n\delta.
$$

For any distribution with atom probabilities $p_a$, its plurality error is $1-\max_a p_a\le1-\sum_a p_a^2$, the disagreement probability of two independent samples. Hence

$$
\Pr_v[A_f(x,v)\ne g(x)]\le2n\delta
\quad\text{for every }x.
\tag{A9}
$$

Now fix **both** $x,v$. With random $y,b$, compare the following four values:

$$
g(x),\quad A_f(x,y),\quad D(x;y,v,b),\quad
\sum_iw_i g(x+a_i v).
$$

The first comparison fails with probability at most $2n\delta$, by (A9). The second fails with probability at most $n\delta$, by the grid argument. For the third, rewrite the grid as

$$
D(x;y,v,b)=\sum_iw_i A_f(x+a_i v,\ y+a_i b).
$$

For each $i$, the direction $y+a_i b$ is uniform; (A9) and a union bound give failure probability at most $2n^2\delta$. The two endpoints of this chain are constants, independent of $y,b$. If

$$
(2n^2+3n)\delta<1,
\tag{A10}
$$

their disagreement probability is less than one, so they must be equal. This proves that the corrected word $g$ satisfies every weighted constraint. This last use of strict inequality converts a probability estimate into an exact identity. See the [weighted-constraint soundness proof][lean-weighted].

The plurality correction and double-sampling argument follow the approach of Rubinfeld–Sudan [Section 4, Theorem 5 and Lemmas 6–8 in the retained manuscript][rubinfeld-sudan]. Amireddy et al. identify this antecedent as Theorem 4.1 of the published paper in their discussion after Lemma 3.3. They also relate the test to Kaufman–Sudan [Theorem 2.9][kaufman-sudan], whose general result assumes a 2-ary independent local formal characterization. For that theorem, take $k=c+2$ forms: $\ell_1(u,v)=u$ and $\ell_{i+1}(u,v)=u+a_iv$. Accepted vectors satisfy $y_0=\sum_iw_i y_i$, a linear subspace. The exact characterization proved above supplies the formal characterization, and the nonzero nodes make the center and each other form jointly uniform, giving the required two-ary independence. Its denominator becomes $(2k+1)(k-1)=2c^2+7c+5$, the denominator in (A10). The direct grid proof is retained here because it also explains the fixed-center prediction bound (A9).

<!-- /passage:pcp-long-algebra-weighted-plurality -->

<!-- passage:pcp-long-algebra-generator-soundness -->
Suppose $q>2c$. If the test using a generator of $F^\times$ and its Lagrange weights rejects with probability $\delta<1/[2(c+2)^2]$, then a formal polynomial of total degree at most $c$ agrees with $f$ outside a set of relative size at most $2\delta$.

Indeed, apply the preceding robustness result to (A6), with $n=c+1$. Its hypothesis is

$$
\delta<\frac{1}{2(c+2)^2},
\tag{A11}
$$

then (A10) holds, because $2(c+1)^2+3(c+1)=2c^2+7c+5<2(c+2)^2$. The exact characterization proves that $g$ is represented by a polynomial $P$ of total degree at most $c$, and (A7) gives

$$
\Delta(f,P)\le2\delta.
\tag{A12}
$$

This is the corrected low-degree soundness statement. It needs $q>2c$, not a cubic field-size hypothesis. A downstream closed threshold such as $1/[4(c+2)^2]$ lies strictly below (A11). The full multiplicative generator and the weights are essential parts of the test being proved here; replacing them by a root of order $c+1$ and unit weights changes the equations. See [the paper, Fact 2.7 and Lemma 3.3][paper] and the [proximity theorem][lean-generator].

<!-- /passage:pcp-long-algebra-generator-soundness -->



### 3. Recovering a specified value

<!-- passage:pcp-long-algebra-standard-correction -->
Suppose $P$ has total degree at most $c$, $\Delta(f,P)=\eta$, and the nodes in (A6) are distinct and nonzero. To recover $P(u)$, choose a uniform direction $v\in V$ and return $A_f(u,v)$. If all $c+1$ sampled values agree with $P$, interpolation makes the answer $P(u)$. Each point $u+a_i v$ is uniform on $V$, so a union bound gives

$$
\Pr_v[A_f(u,v)\ne P(u)]\le(c+1)\eta
\quad\text{for every }u.
\tag{A13}
$$

The sampled points are correlated, but the union bound requires no independence. This correction result has no small-distance hypothesis and needs no additional field-size assumption beyond the existence of the distinct nonzero nodes. For an exact polynomial it always succeeds. It uses $c+1$ listed queries. See [the paper, Fact 2.8 and Lemma 3.4][paper] and the [local-correction bound][lean-correction].

<!-- /passage:pcp-long-algebra-standard-correction -->

<!-- passage:pcp-long-algebra-line-table-correction -->
A second corrector uses an auxiliary line table and may reject. Let $P$ have degree at most $d$, let $\Delta(f,P)=\eta$, and fix a center $u\in V$. For each direction $b\in V$, let $T_b\in F[T]$ be **any** polynomial of degree at most $d$. Choose $b$ uniformly and independently choose $\lambda$ uniformly in $F^\times$. If

$$
T_b(\lambda)=f(u+\lambda b),
$$

output $T_b(0)$; otherwise reject. Then

$$
\Pr[\text{accept and output a value different from }P(u)]
\le\eta+\frac{d}{q-1}.
\tag{A14}
$$

An accepted wrong answer requires either corruption at the tested point, or

$$
T_b(0)\ne P(u),\qquad T_b(\lambda)=P(u+\lambda b).
$$

For each nonzero $\lambda$, the tested point is uniform as $b$ varies, so the first event has probability $\eta$. For each fixed $b$ in the second event, $T_b(T)-P(u+Tb)$ is a nonzero degree-$d$ polynomial because its constant coefficient is nonzero. At most $d$ of the $q-1$ nonzero parameters are roots. Averaging proves (A14). No consistency among the different $T_b$'s was assumed. The bound concerns accepted wrong answers; it does not claim that an arbitrary line table accepts frequently. See the [line-table correction bound][lean-line-correction].

<!-- /passage:pcp-long-algebra-line-table-correction -->

### 4. Bivariate agreement

<!-- passage:pcp-long-algebra-bivariate-statement -->
The point-versus-line theorem below needs a substantial agreement result. We prove the explicit form implemented in the formalization:

**Bivariate agreement theorem.** Let $d>0$, $q\ge1000d^3$, and $f:F^2\to F$. For every $y\in F$, let $R_y(X)$ have degree at most $d$; for every $x\in F$, let $C_x(Y)$ have degree at most $d$. Suppose

$$
\Pr_{x,y}[f(x,y)\ne R_y(x)]\le\varepsilon,\qquad
\Pr_{x,y}[f(x,y)\ne C_x(y)]\le\varepsilon,
\qquad\varepsilon\le1/100.
\tag{A15}
$$

Then there exists $P\in F[X,Y]$, of degree at most $d$ in **each** variable, such that $\Delta(f,P)\le4\varepsilon$. The approximating rows and columns need not be nearest approximations. Individual degree at most $d$ allows total degree $2d$, which is sufficient for the use below. This is an explicit variant of [ALMSS Theorem 69, in the author-hosted manuscript][almss]. That theorem uses nearest row and column polynomials and unspecified absolute constants. The arbitrary approximants and numerical bounds in (A15) are justified by the proof below, which adapts the construction in [Arora–Safra §5.2, Lemmas 5.2.2 and 5.2.7 and Corollary 5.2.3][arora-safra]. See the [bivariate agreement theorem][lean-bivariate].

<!-- /passage:pcp-long-algebra-bivariate-statement -->

<!-- passage:pcp-long-algebra-column-selection -->
First, the mean discrepancy between $R_y(x)$ and $C_x(y)$ is at most $2\varepsilon$. Markov's inequality therefore shows that at most $20\varepsilon\le1/5$ of columns have discrepancy greater than $1/10$. Since $q\ge20d$, choose $10d$ distinct good columns, at positions $a_1,\ldots,a_{10d}$. Write their column polynomials as $C_i(Y)$. Thus

$$
\Pr_y[R_y(a_i)\ne C_i(y)]\le1/10\quad\text{for each }i.
\tag{A16}
$$

Let $e(y)$ count the discrepant entries among these $10d$ columns. Its mean is at most $d$. Since $e(y)$ is an integer, the fraction of rows with $e(y)>2d$ is at most $d/(2d+1)<1/2$. Let $S$ be the rows with $e(y)\le2d$; then $|S|\ge q/2$. See the [column-selection argument][lean-column-selection].

<!-- /passage:pcp-long-algebra-column-selection -->

<!-- passage:pcp-long-algebra-error-locator -->
We seek a rectangle on which the chosen row and column polynomials agree exactly: $d+1$ columns and sufficiently many rows. The columns will determine a polynomial of degree at most $d$ in the horizontal coordinate; agreement on many rows will identify most row polynomials with its restrictions. The error locator below removes the inconsistent entries while leaving such a rectangle.

To describe the inconsistent entries algebraically, we use the error-locator construction of [Arora–Safra, Lemma 5.2.5 and its polynomial extension in Lemma 5.2.7][arora-safra]. Seek bivariate polynomials $E,N$ satisfying

$$
\deg_X E\le2d,\qquad\deg_X N\le3d,\qquad
N(a_i,Y)=C_i(Y)E(a_i,Y)\quad(1\le i\le10d).
\tag{A17}
$$

There are $n=5d+2$ unknown coefficient polynomials in $Y$: $2d+1$ coefficients for $E$, and $3d+1$ for $N$. The equations form a $10d$-by-$n$ matrix with entries in $F[Y]$, each of degree at most $d$.

For every $y\in S$, this specialized matrix has a nonzero kernel. Indeed, take $E_y(X)$ to be the product of $X-a_i$ over the discrepant positions, and put $N_y=E_yR_y$. The product has at most $2d$ factors and is nonzero. At a discrepant position both sides of (A17) vanish; at every other position $R_y(a_i)=C_i(y)$. Thus every $n$-by-$n$ minor of the matrix vanishes at all $y\in S$. Each such determinant has degree at most $nd=(5d+2)d$. The field bound gives

$$
|S|\ge q/2>(5d+2)d,
$$

so the root bound makes every maximal minor the zero polynomial.

The following cofactor construction supplies a nonzero polynomial kernel with a degree bound. Choose a largest nonzero $k$-by-$k$ minor. The empty minor has determinant one, so such a $k$ exists, and $k\le n-1$. Append one column outside its columns. Form a vector supported on these $k+1$ columns whose coordinates are the alternating $k$-by-$k$ cofactors. Its coordinate at the appended column is the chosen nonzero determinant. For any row of the original matrix, the row's product with this vector is the determinant obtained by adjoining that row to the chosen $k$ rows. This is a $(k+1)$-minor and vanishes by maximality. Hence the vector is a nonzero kernel vector. Every coordinate is a determinant with $k$ factors of degree at most $d$, so has degree at most $kd\le(n-1)d$.

Assembling these coordinates as coefficients of $E,N$ proves (A17) with

$$
\deg_Y E,\deg_Y N\le K:=(5d+1)d.
\tag{A18}
$$

Also $E\ne0$. If $E=0$, then $N(a_i,Y)=0$ for $10d>3d$ distinct values $a_i$. Regard $N$ as a polynomial in $X$ over the integral domain $F[Y]$; its root bound gives $N=0$, contradicting the nonzero kernel vector. See the [bounded polynomial-kernel construction][lean-matrix] and the [assembled error-locator certificate][lean-locator].

<!-- /passage:pcp-long-algebra-error-locator -->

<!-- passage:pcp-long-algebra-clean-rectangle -->
At most $2d$ of the $10d$ selected columns have $E(a_i,Y)=0$ as a formal polynomial, again by the root bound over $F[Y]$. Choose $d+1$ columns $J$ on which this polynomial is nonzero. For $y\in S$, the polynomial

$$
N(X,y)-E(X,y)R_y(X)
$$

has degree at most $3d$ and vanishes at all uncorrupted selected entries, of which there are at least $8d>3d$. It is therefore identically zero. At any selected $i\in J$, equations (A17) now imply

$$
E(a_i,y)\bigl(C_i(y)-R_y(a_i)\bigr)=0.
$$

Each nonzero polynomial $E(a_i,Y)$ has at most $K$ roots. Removing these roots for all $d+1$ indices in $J$ removes at most $(d+1)K\le q/10$ rows. At least $q/2-q/10=2q/5$ rows remain. Call this set $B$. All entries of the rectangle $J\times B$ agree between $R$ and $C$. See the [clean-rectangle construction][lean-rectangle].

<!-- /passage:pcp-long-algebra-clean-rectangle -->

<!-- passage:pcp-long-algebra-coarse-agreement -->
Interpolate the $d+1$ columns in $J$:

$$
P(X,Y)=\sum_{i\in J}\ell_i(X)C_i(Y).
$$

It has individual degrees at most $d$. For every $y\in B$, $P(X,y)$ and $R_y(X)$ agree at all $d+1$ selected positions, so they are equal as polynomials. Consider any of the original $10d$ columns $a_i$. By (A16), at most $q/10$ rows disagree between its column polynomial and the row values. Thus $P(a_i,Y)$ and $C_i(Y)$ agree at at least $|B|-q/10\ge3q/10>d$ positions. Their degree is at most $d$, so they are identical.

If a row polynomial $R_y$ differs from $P(\cdot,y)$, the two agree at at most $d$ of the $10d$ selected points. Since $P(a_i,y)=C_i(y)$ at every selected column, this row has $e(y)\ge9d$. But the mean of $e(y)$ is at most $d$. Hence at most $1/9$ of the formal rows differ, and therefore

$$
\Delta\bigl((x,y)\mapsto R_y(x),P\bigr)\le1/9,
\qquad \Delta(f,P)\le\varepsilon+1/9.
\tag{A19}
$$

The distinction between the fraction of differing formal rows and their evaluation distance is useful: the former bounds the latter without any additional root estimate. See the [agreement argument from the rectangle][lean-coarse].

<!-- /passage:pcp-long-algebra-coarse-agreement -->

<!-- passage:pcp-long-algebra-agreement-boost -->
To sharpen (A19), put $\tau=d/q$ and $\rho=\Delta(f,P)$. A simple transverse estimate will be used twice. Given two families of univariate degree-$d$ polynomials $A_z,B_z$, let $\alpha$ be the fraction of indices $z$ for which they differ as polynomials. Their mean evaluation distance is at least $\alpha(1-\tau)\ge\alpha-\tau$, so

$$
\alpha\le \mathbb E_z\Delta(A_z,B_z)+\tau.
\tag{A20}
$$

At any fixed evaluation parameter, the disagreement fraction is at most $\alpha$. Apply this to the column polynomials $C_x$ and $P(x,\cdot)$. Their mean evaluation distance is at most $\varepsilon+\rho$, so at every $y$,

$$
\Pr_x[C_x(y)\ne P(x,y)]\le\varepsilon+\rho+\tau.
$$

If $R_y\ne P(\cdot,y)$, polynomial separation gives

$$
\Pr_x[R_y(x)\ne C_x(y)]
\ge1-\tau-(\varepsilon+\rho+\tau).
$$

Since $\rho\le\varepsilon+1/9$, $\varepsilon\le1/100$, and $q\ge20d$, this lower bound is at least $2/3$. The global row/column discrepancy is at most $2\varepsilon$, so at most $3\varepsilon$ of formal rows differ from $P$. Adding the initial row error gives $\Delta(f,P)\le\varepsilon+3\varepsilon=4\varepsilon$, as asserted. See the [sharpening of coarse agreement][lean-boost].

<!-- /passage:pcp-long-algebra-agreement-boost -->

### 5. Point-versus-line soundness

<!-- passage:pcp-long-algebra-point-line-statement -->
A degree-$d$ line table assigns a polynomial $T_{u,v}\in F[T]$ of degree at most $d$ to each ordered pair $u,v\in V$. It need not assign compatible polynomials to different parameterizations of the same geometric line. Zero directions are allowed. Define

$$
\delta=\Pr_{u,v\in V,\ t\in F}
[f(u+tv)\ne T_{u,v}(t)].
\tag{A21}
$$

**Point-versus-line theorem.** If

$$
q\ge10^6d^3,\qquad\delta\le1/(4\cdot10^6),
\tag{A22}
$$

then there is a polynomial $P$ of total degree at most $d$ with $\Delta(f,P)\le2\delta$. The result covers $d=0$ and $m=0$. These are the explicit sufficient constants in the source, rather than optimized values. Its all-field parameter distribution and factor-two conclusion should not be conflated with the paper's formulation using nonzero parameters and a factor-four conclusion. See the [test definition][lean-point-test] and the [complete soundness theorem][lean-point-soundness].

<!-- /passage:pcp-long-algebra-point-line-statement -->

<!-- passage:pcp-long-algebra-nearest-lines -->
Replace each $T_{u,v}$ by a nearest degree-$d$ polynomial $L_{u,v}$ to the received line $t\mapsto f(u+tv)$, choosing arbitrarily among ties. There are finitely many candidate polynomials, so a minimum exists. This can only decrease rejection; denote the new rejection by $\delta'\le\delta$. For every $x\in V$, define predictions and a corrected word by

$$
\pi_x(v,t)=L_{x-tv,v}(t),\qquad
g(x)=\mathop{\mathrm{plurality}}_{v,t}\pi_x(v,t).
\tag{A23}
$$

The change of variables $(x,v,t)\leftrightarrow(u=x-tv,v,t)$ is a bijection. The plurality argument of (A7) therefore gives

$$
\Delta(f,g)\le2\delta'.
\tag{A24}
$$

We must show that $g$ is an actual polynomial of the required total degree. See the [all-parameter correction definition][lean-point-correction].

<!-- /passage:pcp-long-algebra-nearest-lines -->

<!-- passage:pcp-long-algebra-fixed-parameter -->
First obtain an error bound for a **fixed** line parameter $t$. Let

$$
e(u,v)=\Pr_s[f(u+sv)\ne L_{u,v}(s)].
$$

Its mean is $\delta'$. If $e(u,v)<r$, where $2r\le1-d/q$, the nearest polynomial is unique, by (A1). Changing a line's center from $u$ to $u+(t-s)v$ and shifting its parameter by $t-s$ preserves distances and transports the set of minimizing polynomials bijectively. On these good lines, uniqueness ensures that the chosen minimizers themselves are transported. Thus the error at the fixed parameter $t$ can be compared with error at a fresh uniform parameter $s$. Over $u,v,s$, the transported center is again uniform, so the latter error has mean $\delta'$. The exceptional lines with $e(u,v)\ge r$ have probability at most $\delta'/r$. Consequently

$$
\Pr_{u,v}[f(u+tv)\ne L_{u,v}(t)]\le\delta'+\delta'/r.
$$

When $q\ge3d$, take $r=1/3$ to obtain

$$
\Pr_{u,v}[f(u+tv)\ne L_{u,v}(t)]\le4\delta'
\quad\text{for every }t\in F.
\tag{A25}
$$

No global convention for choosing tied minimizers is required. See the [fixed-parameter estimate][lean-parameter].

<!-- /passage:pcp-long-algebra-fixed-parameter -->

<!-- passage:pcp-long-algebra-crossing -->
We need a consequence of bivariate agreement at one crossing. Assume $d>0$ and $q\ge1000d^3$. Suppose a received grid has degree-$d$ approximating rows and columns with global errors at most $\varepsilon\le1/100$. Suppose also that, at the selected crossing $(x_0,y_0)$, its received row is within $\varepsilon$ of the transverse column values, and its received column is within $\varepsilon$ of the transverse row values. Assume

$$
6\varepsilon+2d/q<1/2.
\tag{A26}
$$

If the selected row and column polynomials are nearest approximations, their values at the crossing agree. To prove this, bivariate agreement supplies $P$ within $4\varepsilon$ of the received grid. Each polynomial family is then within $5\varepsilon$ of $P$ in mean evaluation distance. Formula (A20) shows that its transverse distance at every fixed parameter is at most $5\varepsilon+d/q$. The received selected row is therefore within $6\varepsilon+d/q$ of the corresponding row of $P$. Its nearest polynomial is no farther away from the received row, so it lies within $12\varepsilon+2d/q<1-d/q$ of that polynomial row of $P$, by (A26). Polynomial separation forces identity. The same holds for the column, proving agreement at the crossing.

One variant will be needed: the selected row may be a candidate rather than a nearest approximation, provided its own received-row error is at most $\varepsilon$. Its distance from the row of $P$ is then at most $7\varepsilon+d/q<1-d/q$, again by (A26), so the same conclusion holds. The selected column remains a nearest approximation. Thus four small errors suffice when both are nearest, and five suffice in this candidate-row version. See the [crossing-consistency lemma][lean-crossing] and the [candidate-row variant][lean-candidate].

<!-- /passage:pcp-long-algebra-crossing -->

<!-- passage:pcp-long-algebra-mixed-plane -->
For the positive-degree case of (A22), fix a center $u\in V$ and parameter $t\in F$. Choose $0<\varepsilon\le1/100$ satisfying (A26). Choose independent uniform $v,w\in V$ and $s\in F$, and inspect the grid

$$
M(y,z)=f\bigl(u+yv+(z-s)w\bigr).
\tag{A27}
$$

Here a row fixes $y$ and varies $z$; a column fixes $z$ and varies $y$. Use the nearest line polynomials

$$
R_y(z)=L_{u+yv-sw,w}(z),\qquad
C_z(y)=L_{u+(z-s)w,v}(y).
$$

At crossing $(t,s)$, the column prediction is $C_s(t)=L_{u,v}(t)$, and the row prediction is

$$
L_{u+tv-sw,w}(s)=\pi_{u+tv}(w,s).
$$

The four discrepancies needed for crossing consistency are

$$
\begin{aligned}
e_{\rm row}&=\Pr_{y,z}[M(y,z)\ne R_y(z)],&
e_{\rm col}&=\Pr_{y,z}[M(y,z)\ne C_z(y)],\\
e_{\rm cross,row}&=\Pr_z[M(t,z)\ne C_z(t)],&
e_{\rm cross,col}&=\Pr_y[M(y,s)\ne R_y(s)].
\end{aligned}
$$

The last two compare a received slice with the *transverse* polynomial predictions. Each quantity depends on the sampled $v,w,s$; we now bound its mean over those choices. A random affine expression $a+\lambda b$ is uniform in $V$ when $b$ is uniform and $\lambda\ne0$. In the global row error of (A27), the row center contains the coefficient $y$ of $v$; all $y\ne0$ therefore give the global rejection distribution, while the exceptional slice $y=0$ contributes at most $1/q$. In the global column error, the analogous exceptional slice is $z=s$. The local error along the selected column has the same $y=0$ exception. These three means are at most $\delta'+1/q$. For the local error along the selected row, $z\ne s$ makes the center uniform, but the evaluation parameter is the fixed $t$; (A25) bounds this contribution by $4\delta'$, and the exceptional slice contributes at most $1/q$. Thus all four means are at most $4\delta'+1/q$.

Markov's inequality and a union bound show that the probability one of these four errors exceeds $\varepsilon$ is at most $4(4\delta'+1/q)/\varepsilon$. On the complementary event the predictions agree by the crossing lemma. For each $v$, plurality minimizes the probability of disagreeing with the independent prediction $\pi_{u+tv}(w,s)$; comparing it with $L_{u,v}(t)$ costs at most a factor two, exactly as in (A7). Hence

$$
\Pr_v[L_{u,v}(t)\ne g(u+tv)]\le
\gamma:=\frac{8(4\delta'+1/q)}{\varepsilon}
\quad\text{for every }u,t.
\tag{A28}
$$

The endpoint $u+tv$ varies here. This is stronger than merely bounding the average error at a fixed point and is precisely what is needed next. See the [mixed-plane sampling estimates][lean-mixed] and the [endpoint-consistency bound][lean-endpoint].

<!-- /passage:pcp-long-algebra-mixed-plane -->

<!-- passage:pcp-long-algebra-ruled-surface -->
Fix a target line $y\mapsto x+yh$, and choose once and for all a nearest degree-$d$ polynomial $Q(y)$ to $g$ on this line. We prove that it represents $g$ there **exactly**. Fix a parameter $y_0$. For independent uniform $v,w\in V$, use the grid

$$
M(y,z)=
\begin{cases}
g(x+yh),&z=0,\\
f\bigl(x+yh+z(v+yw)\bigr),&z\ne0.
\end{cases}
\tag{A29}
$$

The zero column is the target line in the corrected function. Each nonzero column samples an oriented line with uniform center and direction. The rows join these random comparisons to the target, allowing us to prove that the already chosen $Q$ agrees with every target value. The expression for nonzero $z$ is affine in either variable when the other is fixed. Give row $y$ the candidate polynomial

$$
R_y(z)=L_{x+yh,\,v+yw}(z).
$$

For $z\ne0$, give column $z$ its nearest polynomial

$$
C_z(y)=L_{x+zv,\,h+zw}(y),
$$

and put $C_0=Q$. By its choice, $Q$ is a nearest approximation to the modified zero column. The other row candidates need not remain nearest after this modification, which is why the five-error crossing lemma was proved.

Put $\eta=\Delta(f,g)\le2\delta'$, and $\ell=4\delta'$, the bound in (A25). The five errors at crossing $(y_0,0)$ have the following mean bounds over $v,w$:

| Error | Mean upper bound |
|---|---:|
| global row error | $\gamma+\eta$ |
| global column error | $\delta'+1/q$ |
| received selected row versus column values | $\ell+1/q$ |
| received zero column versus row values | $\gamma$ |
| selected row candidate's own error | $\gamma+\eta$ |

Here are the sampling details. For fixed $y$, $v+yw$ is a uniform direction. Equation (A28) bounds disagreement of its line polynomial with $g$ at each parameter by $\gamma$; at nonzero parameters the sampled point is uniform, adding at most $\eta$ for replacing $g$ by $f$. At parameter zero the received value already is $g$. This proves the first and fifth entries. For a fixed $z\ne0$, the pair $(x+zv,h+zw)$ is uniform on $V^2$, so the mean column error is $\delta'$; discard the exceptional zero column at cost $1/q$. For the third entry, the same uniform pair is evaluated at fixed $y_0$, so (A25) gives $\ell$ off the zero column. For the fourth entry, apply (A28) with parameter zero to each row center. These arguments use invertible affine maps; they do not assume independence among all entries of a grid. See the [ruled-surface sampling estimates][lean-ruled-sampling].

Let

$$
B=2(\gamma+\eta)+\delta'+\ell+\gamma+2/q.
\tag{A30}
$$

Markov and the union bound show that one of the five errors exceeds $\varepsilon$ with probability at most $B/\varepsilon$. Otherwise the crossing lemma gives $R_{y_0}(0)=Q(y_0)$. Separately, (A28) gives

$$
\Pr[R_{y_0}(0)\ne g(x+y_0h)]\le\gamma.
$$

If $B/\varepsilon+\gamma<1$, some seed satisfies both equalities. Their right sides are constants, so $Q(y_0)=g(x+y_0h)$. This holds for each $y_0$, with the same previously chosen $Q$; hence the entire target line has degree at most $d$. Since the line was arbitrary, the exact-line characterization makes $g$ a polynomial of total degree at most $d$. See the [ruled-surface rigidity argument][lean-ruled].

<!-- /passage:pcp-long-algebra-ruled-surface -->

<!-- passage:pcp-long-algebra-point-line-constants -->
We now verify the numerical bounds required by the crossing argument. For $d>0$, (A22) gives $q\ge10^6$ and $q\ge1000d^3$. Take $\varepsilon=1/100$. Then

$$
\gamma\le0.0016,\qquad
\eta\le0.0000005,\qquad
\ell\le0.000001.
$$

Equation (A30) gives $B\le0.00480425$, and therefore

$$
B/\varepsilon+\gamma\le0.482025<1.
$$

Also $d/q\le10^{-6}$, so $6\varepsilon+2d/q<1/2$; all uses of the crossing lemma are valid. The bound $q>2d$ needed for the exact-line characterization follows as well. We have constructed $g=P$, and (A24) finishes the estimate $\Delta(f,P)\le2\delta'\le2\delta$. See the [explicit constants][lean-point-constants].

<!-- /passage:pcp-long-algebra-point-line-constants -->

<!-- passage:pcp-long-algebra-degree-zero -->
For $d=0$ there is a shorter proof requiring no large-field hypothesis. Every table polynomial is a constant $b_{u,v}$. Both $f(u+tv)$ and $f(u+(t+1)v)$ disagree with this constant with mean probability $\delta$; translation $t\mapsto t+1$ preserves the sampling distribution. Thus the mean disagreement between these two function values is at most $2\delta$. For every fixed $t$, the map

$$
(u,v)\longmapsto(u+tv,\ u+(t+1)v)
$$

is a bijection of $V^2$, with inverse $v=y-x, u=x-tv$. Therefore two independent uniform values of $f$ disagree with probability at most $2\delta$. Averaging over the second point gives a value $a\in F$ with $\Pr_x[f(x)\ne a]\le2\delta$. The constant polynomial $a$ is the required approximation. This works in characteristic two and in dimension zero. See the [degree-zero soundness proof][lean-constant].

<!-- /passage:pcp-long-algebra-degree-zero -->

### Source correspondence and scope

<!-- passage:pcp-long-algebra-source-boundary -->
The short-test proof and the point-versus-line proof are separate components. The former uses only $q>2c$ and a weighted affine-constraint argument. The latter uses the bivariate agreement construction and explicit cubic field-size constants. The local correctors then consume proximity to a polynomial; they do not supply the polynomial's existence. Keeping these implications separate prevents a correction guarantee from being used as an unproved testing theorem.

The point-versus-line argument follows the sequence in [ALMSS Appendix A][almss]: plurality correction (Lemma 66), bivariate agreement and crossing consistency (Theorem 69 and Corollary 70), then consistency on randomly sampled surfaces (Lemmas 71–73). The fixed-parameter estimate above handles arbitrary choices among nearest-line ties, and the candidate-row crossing variant handles the modified zero column in (A29). These steps give the stated whole-field test and explicit constants.

<!-- /passage:pcp-long-algebra-source-boundary -->

[paper]: https://arxiv.org/abs/2608.17429v2
[paper-v1]: https://arxiv.org/abs/2608.17429v1
[almss]: https://people.seas.harvard.edu/~madhusudan/papers/1992/almss-journ.pdf
[arora-safra]: https://www.cs.umd.edu/~gasarch/TOPICS/pcp/AS.pdf
[lean-distance]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/PolynomialDistance.lean
[lean-interpolation]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/GridInterpolation.lean
[lean-grid]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/GridVanishing.lean
[lean-certificate]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/VanishingCertificate.lean
[lean-lines]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/PolynomialLineCharacterization.lean
[lean-generator]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/GeneratorLowDegreeTest.lean
[lean-weighted]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/WeightedConstraintSoundness.lean
[lean-correction]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/StandardLocalCorrection.lean
[lean-line-correction]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/LineTableLocalCorrection.lean
[lean-bivariate]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BivariateAgreement.lean
[lean-column-selection]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BivariateColumnSelection.lean
[lean-matrix]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/PolynomialMatrixKernel.lean
[lean-locator]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BerlekampWelchCertificate.lean
[lean-rectangle]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BivariateCleanRectangle.lean
[lean-coarse]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BivariateAgreementFromRectangle.lean
[lean-boost]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BivariateAgreementBoost.lean
[lean-point-test]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/PointLineTest.lean
[lean-point-soundness]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/PointLineSoundness.lean
[lean-point-correction]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/PointLineCorrection.lean
[lean-parameter]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/PointLineParameterError.lean
[lean-crossing]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BivariateCrossingSoundness.lean
[lean-candidate]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/CandidateCrossing.lean
[lean-mixed]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/MixedPlaneSampling.lean
[lean-endpoint]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/PointLineEndpointConsistency.lean
[lean-ruled-sampling]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/RuledSurfaceSampling.lean
[lean-ruled]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/RuledSurfaceRigidity.lean
[lean-point-constants]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/PointLineConstants.lean
[lean-constant]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/PointLineConstant.lean

## From polynomial values to a constant number of bits

<!-- passage:pcp-long-binary-purpose -->

The field-valued tests from the preceding part read a bounded number of field elements, but a field element contains several bits. Moreover, a line restriction can have degree growing with the input size. Two encodings remove these obstacles. A digit substitution represents a univariate polynomial by a polynomial of fixed total degree in more variables. A Hadamard encoding then lets the verifier inspect a binary linear observation of a field value with one bit query. Local tests bound the distance of a received binary table from a valid encoding.

We next combine the two encodings with low-degree testing, local correction and the zero-on-grid test. The construction is due to Amireddy, Behera, Srinivasan, Sudan and Willumsgaard in [the corrected paper, Sections 3–6 and Appendices B–D](https://arxiv.org/abs/2608.17429v2); the quantitative argument below follows Troy Lee's pinned formal implementation. Its explicit constants and sampling conventions sometimes differ from that paper. The changes are identified at the relevant steps.

Throughout, $F$ is a finite field of characteristic two, $q=|F|=2^t$, and

$$
\rho:F\longrightarrow\mathbb F_2^t
$$

is a fixed linear isomorphism over $\mathbb F_2$. Distances and probabilities are uniform finite averages. We write $\Delta(u,v)$ for the fraction of inputs on which two functions disagree. The digit radix is denoted by $b$, to distinguish it from the number of variables of an outer polynomial. The parameters $b,c,r$ are integers with $b\geq1$, $c\geq0$, and $r\geq1$. The construction eventually takes $c=4$. Polynomial degree means total degree for several variables and ordinary degree for one variable; the zero polynomial satisfies every nonnegative bound used below. All auxiliary tables in soundness statements are arbitrary received tables.

<!-- /passage:pcp-long-binary-purpose -->

### A high-degree univariate polynomial as a low-degree multivariate polynomial

<!-- passage:pcp-long-set-multilinear -->

Let $p(Y)=\sum_{j<b^c}p_jY^j$. Write the base-$b$ expansion of $j$ as

$$
j=j_0+j_1b+\cdots+j_{c-1}b^{c-1},\qquad 0\leq j_i<b.
$$

Introduce variables $X_{i,k}$, with $0\leq i<c$ and $0\leq k<b$, and define

$$
\operatorname{Enc}(p)=\sum_{j<b^c}p_j\prod_{i=0}^{c-1}X_{i,j_i}.
$$

Each monomial uses exactly one variable from each of the $c$ groups. Thus the encoding has total degree at most $c$, although the original polynomial may have degree almost $b^c$. To recover the formal polynomial, define the substitution map

$$
\operatorname{Dec}(Q)(Y)=Q\bigl((Y^{k b^i})_{i,k}\bigr).
$$

For $j<b^c$, this substitution sends the encoded monomial $\prod_iX_{i,j_i}$ to $Y^{\sum_i j_i b^i}=Y^j$. Linearity therefore gives the identity

$$
\operatorname{Dec}(\operatorname{Enc}(p))=p\qquad\text{in }F[Y].
$$

Applying $\operatorname{Dec}$ to equal encodings proves injectivity on polynomials of degree strictly below $b^c$. The strict bound matters: the encoding retains only $c$ digits. Evaluating the identity at $z\in F$ then gives

$$
\operatorname{Enc}(p)(\Phi(z))=p(z),
\qquad \Phi(z)_{i,k}=z^{k b^i}.
$$

The formal identity proves more than equality of evaluations. Over a finite field of size $q$, the nonzero polynomial $Y^q-Y$ vanishes at every field element. When $q<b^c$, it lies within the admitted degree range, so equality as functions would not by itself prove injectivity.

Soundness must also handle a received table which decodes to an arbitrary polynomial $Q$ of total degree at most $c$, not necessarily a set-multilinear one. Use the same substitution map $\operatorname{Dec}$.

A monomial of $Q$ has at most $c$ variable occurrences, counted with multiplicity. Each substituted variable has degree at most $b^c$, so

$$
\deg\operatorname{Dec}(Q)\leq c b^c.
$$

The distinction between the honest degree bound $\deg p<b^c$ and the decoded bound $c b^c$ propagates through the outer tests. A low-degree test does not by itself prove that an arbitrary decoded polynomial has the special set-multilinear form of an honest encoding.

The formal source separates [the substitution identity](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/SetMultilinear.lean#L89), [injectivity](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/SetMultilinear.lean#L116), [evaluation recovery](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/SetMultilinear.lean#L101) and [degree control for an arbitrary decoded polynomial](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/SetMultilinearDecode.lean#L75). This is the first encoding in the paper's Section 3.

<!-- /passage:pcp-long-set-multilinear -->

### Binary labels for field elements

<!-- passage:pcp-long-hadamard-labels -->

For $r\geq1$, let $\mathcal B_r$ be the vector space of squarefree Boolean polynomials in $t$ variables of degree at most $r$. A label is a coefficient vector in this space. The reduction $Z_i^2=Z_i$ is appropriate because labels are evaluated on $\mathbb F_2^t$; the formal implementation indexes monomials by subsets of coordinates. A field element $u$ is encoded by the binary word

$$
\mathcal H_r(u)(R)=R(\rho(u)),\qquad R\in\mathcal B_r.
$$

The word has $2^{\sum_{j=0}^{\min(r,t)}\binom tj}$ entries. We will use full labels, affine degree-one labels, and homogeneous degree-one labels. A homogeneous label has the form

$$
L_w(z)=\sum_{i=1}^t w_i z_i,\qquad w\in\mathbb F_2^t.
$$

For a field-valued function $g$, write $\mathcal H_r(g)(x,R)=\mathcal H_r(g(x))(R)$.

If $u\neq v$, choose a coordinate on which $\rho(u)$ and $\rho(v)$ differ. Adding that coordinate label pairs every label giving equal evaluations with one giving unequal evaluations. Consequently, for $r\geq1$,

$$
\Delta(\mathcal H_r(u),\mathcal H_r(v))=\frac12.
$$

The same pairing works among homogeneous linear labels. Averaging over the outer input gives

$$
\Delta(\mathcal H_r(g),\mathcal H_r(h))
=\frac12\Delta(g,h),
\tag{B1}
$$

and the same identity holds when distance is measured only on homogeneous degree-one labels. This exact factor of two converts the rejection probability of a field equality into that of a binary observation.

For an arbitrary received word, small full-label distance does not imply equally small distance on a much smaller subset of labels. We therefore maintain two bounds for the same decoded function: one on all labels and one on homogeneous degree-one labels. When the received oracle itself has degree-one labels, homogeneous labels form half its domain, so their error is at most twice the full affine-label error. No corresponding dimension-independent restriction estimate is inferred from the full degree-$r$ domain for $r>1$.

<!-- /passage:pcp-long-hadamard-labels -->

<!-- passage:pcp-long-hadamard-composition -->

Higher-degree labels allow a bit query about a polynomial in a field value. Let $A(Y)\in F[Y]$ have degree at most $r$, and let $L$ be an affine binary label. Choose the field basis $e_1,\ldots,e_t$ supplied by $\rho$, and write $e_ie_j=\sum_k\mu_{ijk}e_k$. The $k$-th coordinate of a product is then $\sum_{i,j}\mu_{ijk}z_iw_j$. Repeated multiplication gives coordinate polynomials of degree at most $s$ for the $s$-th power. Multiplication by a fixed field coefficient is linear, so every coordinate of $A(\rho^{-1}(z))$ has degree at most $r$. Replacing positive powers of each $z_i$ by $z_i$ preserves evaluations on binary points and cannot increase degree. Composing with $L$ therefore gives a squarefree label $\Lambda_{A,L}\in\mathcal B_r$ satisfying

$$
\mathcal H_1(A(u))(L)=\mathcal H_r(u)(\Lambda_{A,L}).
\tag{B2}
$$

The statement concerns one field value $u$ and one polynomial $A$; its extension to an oracle is pointwise. In particular, cubic labels suffice to observe $u^3-1$, the expression used to enforce membership in the three allowed colours.

For $A(Y)=\eta Y$ and a homogeneous label $L$, the composed label is homogeneous. If $\eta\neq0$, multiplication by $\eta$ is a linear bijection of $F$, and its dual permutes the homogeneous labels. This permutation is essential when averaging noisy answers with Lagrange weights. Zero weights must be treated separately: a zero summand is known without reading the oracle. The formal source proves the general [composition identity](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/HadamardComposition.lean) and the needed [weighted homogeneous relabelling](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/HadamardWeights.lean). This is the scalar homogeneous case stated in Claim 3.7 of the corrected paper.

<!-- /passage:pcp-long-hadamard-composition -->

### Testing a received Hadamard word

<!-- passage:pcp-long-blr-proof -->

The first ingredient is the binary linearity test. For a function $h:V\to\mathbb F_2$, where $V$ is a finite binary vector space, choose uniform independent $x,y$ and check

$$
h(x+y)=h(x)+h(y).
$$

If its rejection probability is $\epsilon$, some linear functional $\ell:V\to\mathbb F_2$ satisfies $\Delta(h,\ell)\leq\epsilon$. The test is due to Blum, Luby and Rubinfeld [Section 4.2][blr]; the sharp characteristic-two bound follows from Bellare, Coppersmith, Håstad, Kiwi and Sudan [Theorem 1.2 and Section 2][bchks], also cited in Amireddy et al., Appendix B, Theorem B.1. We give that Fourier argument. Choose coordinates for $V$, put $s(x)=(-1)^{h(x)}$, and for a linear functional $a$ put $\chi_a(x)=(-1)^{a(x)}$. A nontrivial character has average zero: translation by a point where it is $-1$ negates its sum. Thus the characters are orthonormal. With

$$
\widehat s(a)=\mathbb E_x s(x)\chi_a(x),
$$

orthogonality gives Fourier inversion and Parseval,

$$
s(x)=\sum_a\widehat s(a)\chi_a(x),\qquad
\sum_a\widehat s(a)^2=\mathbb E_xs(x)^2=1.
$$

Expanding each of the three factors in the acceptance bias and averaging first over $x$ and then over $y$ kills every term except those with the same character in all three positions. Hence

$$
1-2\epsilon
=\mathbb E_{x,y}s(x)s(y)s(x+y)
=\sum_a\widehat s(a)^3
\leq\max_a\widehat s(a)\sum_a\widehat s(a)^2
=\max_a\widehat s(a).
$$

Choose a maximising $a$. Since $\widehat s(a)=1-2\Delta(h,a)$, rearrangement gives the claim. This includes every possible rejection rate; no small-error hypothesis is needed for this intermediate result. See [the formal Walsh argument](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BLR.lean).

<!-- /passage:pcp-long-blr-proof -->

<!-- passage:pcp-long-hadamard-self-correction -->

Linearity on the label space is necessary but not sufficient for a Hadamard word to be evaluation at a point: the linear functional must preserve the unit and products. To test these laws reliably on a noisy word, define

$$
\operatorname{SC}_h(Q;R)=h(Q+R)-h(R),
$$

with $R$ uniform on the full label space. If $\Delta(h,\ell)\leq\epsilon$ for an additive $\ell$, both arguments $R$ and $Q+R$ are uniform, even for a fixed or adversarially selected $Q$. Outside two error events, their difference equals $\ell(Q)$. Therefore

$$
\Pr_R[\operatorname{SC}_h(Q;R)\neq\ell(Q)]\leq2\epsilon.
\tag{B3}
$$

The bound remains valid after averaging over any distribution of requests selected before the independent seed $R$. The error events need not be independent.

The pinned formal tester chooses independent full labels $R,R'$, an affine degree-one label $L$, and, for each $j=2,\ldots,r$, a label $P_{j-1}$ of degree at most $j-1$. It checks

$$
\begin{aligned}
h(R+R')&=h(R)+h(R'),\\
\operatorname{SC}_h(1;R)&=1,\\
\operatorname{SC}_h(L;R)&=h(L),\\
\operatorname{SC}_h(LP_{j-1};R)
&=\operatorname{SC}_h(L;R)\operatorname{SC}_h(P_{j-1};R)
\quad(2\leq j\leq r).
\end{aligned}
\tag{B4}
$$

Products are squarefree-reduced. Shared answers are reused, so the query list has length $2r+4$. The corrected arXiv v2 algorithm retains only the last multiplication check and uses eight queries; the pinned formal tester retains the earlier degree checks as well. Its soundness proof needs only the top-degree check, so the extra checks do not weaken soundness. At $r=3$, the formal query count is ten.

<!-- /passage:pcp-long-hadamard-self-correction -->

<!-- passage:pcp-long-hadamard-soundness -->

Suppose the full test rejects with probability at most $\epsilon<1/28$. Each individual check has rejection at most $\epsilon$, because failure of that check implies failure of the conjunction. The linearity bound supplies one linear functional $\ell$ with $\Delta(h,\ell)\leq\epsilon$.

The corrected unit test and (B3) force $\ell(1)=1$. Otherwise the correct target value and the required answer differ on every seed, whereas their discrepancy is at most $2\epsilon+\epsilon<1$.

For $r\ge2$, use the top-degree product check and replace its three corrected answers by their $\ell$-values. The three replacements cost at most $6\epsilon$, and test failure costs at most another $\epsilon$. Thus

$$
\Pr_{L,P}\bigl[\ell(LP)\neq\ell(L)\ell(P)\bigr]
\leq7\epsilon<\frac14,
\tag{B5}
$$

where $L\in\mathcal B_1$, $P\in\mathcal B_{r-1}$. The defect $B(L,P)=\ell(LP)-\ell(L)\ell(P)$ is bilinear. A nonzero bilinear binary form is nonzero on at least a quarter of its domain: at least half the first arguments induce a nonzero linear functional of the second argument, and every such functional is nonzero on exactly half the second arguments. Inequality (B5) therefore forces the defect to vanish identically.

Set $z_i=\ell(Z_i)$. For a squarefree monomial, repeatedly separate one variable from the remaining product. The exact product law and $\ell(1)=1$ give

$$
\ell\Bigl(\prod_{i\in S}Z_i\Bigr)=\prod_{i\in S}z_i.
$$

Linearity then gives $\ell(R)=R(z)$ for every label. For $r=1$, unit preservation and linearity already give this conclusion without a product check. Thus $h$ is $\epsilon$-close to one evaluation word $\mathcal H_r(\rho^{-1}z)$.

The same point also controls affine degree-one labels. Their consistency check compares $h(L)$ with a corrected answer; (B3) bounds the latter's error relative to $\ell(L)$. A union bound gives

$$
\Delta\bigl(h|_{\mathcal B_1},\mathcal H_1(\rho^{-1}z)\bigr)
\leq3\epsilon.
\tag{B6}
$$

This argument is [Hadamard test soundness](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/HadamardSoundness.lean); the quarter-distance step is in [the bilinear characterization](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BilinearHadamard.lean). It reconstructs the formal variant of the paper's Lemma 3.10.

<!-- /passage:pcp-long-hadamard-soundness -->

<!-- passage:pcp-long-hadamard-row-decoding -->

We need this conclusion for a table whose individual rows can be arbitrarily bad. If a row has rejection $e<1/28$, choose the point just constructed. Its full-label error is at most $e$, and its homogeneous-label error is at most $2\cdot3e=6e$. If $e\geq1/28$, choose any point; each distance is at most $1\leq28e$. Consequently every row admits one decoded field value for which both distances are at most $28e$. Choose these values simultaneously and average. If $\overline e$ is average row rejection, the resulting field function $g$ satisfies

$$
\Delta_{\rm full}(h,\mathcal H_r(g))\leq28\overline e,
\qquad
\Delta_{\rm hom}(h,\mathcal H_r(g))\leq28\overline e.
\tag{B7}
$$

The same $g$ occurs in both conclusions. This is an existence argument used in soundness analysis; it does not provide an efficient decoding algorithm. The formal [row-decoding theorem](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/HadamardRowDecoding.lean) deliberately has no global small-error premise.

<!-- /passage:pcp-long-hadamard-row-decoding -->

### A binary version of the weighted low-degree test

<!-- passage:pcp-long-binary-weighted-test -->

Take a generator $\theta$ of $F^\times$, let $a_i=\theta^{i+1}$ for $0\leq i\leq c$, and assume $q>2c$. These nodes are distinct and nonzero. Their Lagrange weights for evaluation at zero are

$$
\eta_i=\prod_{j\ne i}\frac{-a_j}{a_i-a_j}.
$$

Each weight is nonzero. Interpolating a polynomial of degree at most $c$ at the $c+1$ nodes and evaluating at zero gives the field-valued equation

$$
g(u)=\sum_{i=0}^c\eta_i g(u+a_i v).
\tag{B8}
$$

For a received binary table $h(x,L)$, choose a homogeneous label $L$ and check the binary observation of (B8): query the centre with $L$, and the $i$-th other point with the homogeneous label $L\circ(\eta_i\cdot)$. At most $c+2$ bits are read. On an exact encoding $\mathcal H_r(g)$, (B1) says that the binary check rejects with exactly half the rejection probability of (B8).

For a corrupted encoding, suppose $\Delta_{\rm hom}(h,\mathcal H_r(g))=\tau$. Each nonzero weighted label is a permutation of uniform labels; each sampled point $u+a_iv$, and the centre $u$, is uniform. Replacing the at most $c+2$ answers therefore changes the binary decision on at most $(c+2)\tau$ of the seeds. If the received binary check has rejection $\beta$, then

$$
\Pr[(\mathrm{B8})\text{ fails}]
\leq2\beta+2(c+2)\tau.
\tag{B9}
$$

The actual inner tester flips a fair coin between a rowwise Hadamard test and this weighted check. If its rejection is $\kappa$, each branch rejects with probability at most $2\kappa$. Applying (B7) to the Hadamard branch gives a field function $g$ with both binary distances at most $56\kappa$. Equation (B9) then gives

$$
\Pr[(\mathrm{B8})\text{ fails}]
\leq \bigl(112(c+2)+4\bigr)\kappa.
\tag{B10}
$$

The preceding field-valued low-degree theorem applies when $q>2c$, the nodes come from a full multiplicative generator, and this last rejection is below its threshold. The formal argument uses the sufficient threshold

$$
\bigl(112(c+2)+4\bigr)\kappa
\leq\frac{1}{4(c+2)^2},
$$

which is strictly below $1/[2(c+2)^2]$. It gives a polynomial $Q$ of total degree at most $c$ with field distance at most twice (B10). By (B1), encoding that field distance costs one half. A triangle inequality therefore bounds both binary distances to $\mathcal H_r(Q)$ by

$$
\bigl(112(c+2)+60\bigr)\kappa.
$$

For a row above this threshold, use the zero polynomial and the universal distance bound one. Both cases are covered by

$$
K(c)=4(c+2)^2\bigl(112(c+2)+60\bigr):
\quad
\Delta_{\rm full}(h,\mathcal H_r(Q)),\
\Delta_{\rm hom}(h,\mathcal H_r(Q))
\leq K(c)\kappa.
\tag{B11}
$$

Indeed, in the high-rejection case,
$K(c)\kappa>[112(c+2)+60]/[112(c+2)+4]>1$.
This proves a uniform row-decoding statement with no smallness assumption. The decoded polynomial is again the same in both conclusions. The exact proof is [binary polynomial row decoding](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BinaryLocalRowDecoding.lean).

<!-- /passage:pcp-long-binary-weighted-test -->

<!-- passage:pcp-long-binary-inner-correction -->

The weighted local corrector uses a node table $\alpha_i=\zeta^{i+1}$, required only to have distinct entries and $\zeta\ne0$. The formal theorem calls this condition `GoodNodes`. It follows from the generator hypothesis above, but the tester's generator $\theta$ and the corrector's parameter $\zeta$ need not be equal. Let $\omega_i=\prod_{j\ne i}(-\alpha_j)/(\alpha_i-\alpha_j)$. To recover the homogeneous observation of $Q(u)$, the corrector returns

$$
\sum_{i=0}^c
h\bigl(u+\alpha_i v,\ L\circ(\omega_i\cdot)\bigr).
\tag{B12}
$$

On an honest degree-$c$ polynomial this is exactly $L(Q(u))$, by interpolation. Suppose the received table differs from $\mathcal H_1(Q)$ by homogeneous distance $\tau$. For fixed $u$, random $v$, and random homogeneous $L$, each queried point-label pair is uniform: $\alpha_i\ne0$ makes $v\mapsto u+\alpha_iv$ bijective, and $\omega_i\ne0$ makes the label map bijective. A wrong sum requires at least one wrong answer, so

$$
\Pr[(\mathrm{B12})\neq L(Q(u))]\leq(c+1)\tau.
\tag{B13}
$$

The guarantee is averaged over the requested homogeneous label as well as the direction. We do not claim this bound for every fixed label of an arbitrary received table. This is [binary weighted local correction](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BinaryStandardLocalCorrection.lean).

<!-- /passage:pcp-long-binary-inner-correction -->

### Testing a high-degree outer polynomial

<!-- passage:pcp-long-encoded-line-test -->

Let the primary table be $f:F^k\times\mathcal B_r\to\mathbb F_2$. For every oriented line $x=u+zv$, an auxiliary table is intended to encode the set-multilinear image of the univariate restriction $P(u+Yv)$, using degree-one Hadamard labels. Use generator nodes for its inner test and `GoodNodes` for its corrector, as above. Choose uniform $u,v\in F^k$ and $z\in F$, a homogeneous label $L$, an inner correction direction, and independent seeds for the two tests. The formal verifier:

1. runs the Hadamard test on the primary row $f(u,\cdot)$;
2. runs the fair-coin inner test on the auxiliary row belonging to $(u,v)$;
3. corrects that row at $\Phi(z)$, using (B12), and compares the answer with $f(u+zv,L)$.

All three checks must pass. In particular, $z$ ranges over the whole field. Honest polynomials of degree strictly below $b^c$, with their actual encoded line restrictions, pass for every seed. The query list has length at most $2r+2c+12$, as proved by [the actual tester's query bound](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/EncodedLineLowDegreeTest.lean).

<!-- /passage:pcp-long-encoded-line-test -->

<!-- passage:pcp-long-encoded-line-soundness -->

Let the complete tester's rejection probability be $\kappa$. Its Hadamard marginal, inner-test marginal, and comparison error are individually at most $\kappa$. From (B7), choose one primary field function $g$, close to $f$ by at most $28\kappa$ on both relevant label domains. Apply (B11) to every auxiliary row, obtaining inner polynomials $Q_{u,v}$ of degree at most $c$. Their average homogeneous distance is at most $K(c)\kappa$. Define actual univariate line polynomials

$$
T_{u,v}=\operatorname{Dec}(Q_{u,v}),\qquad
\deg T_{u,v}\leq D:=c b^c.
$$

There are three discrepancies between the binary observations of $T_{u,v}(z)$ and $g(u+zv)$:

- replacing the locally corrected auxiliary answer by $L(T_{u,v}(z))$, costing at most $(c+1)K(c)\kappa$ by (B13);
- the comparison checked by the tester, costing at most $\kappa$;
- replacing the received primary answer by $L(g(u+zv))$, costing at most $28\kappa$.

The last bound uses uniformity of $u+zv$ when $u$ is uniform, even for $z=0$. Combining the three discrepancies and applying the exact half-distance identity (B1) gives

$$
\Pr_{u,v,z}[T_{u,v}(z)\neq g(u+zv)]
\leq E(c)\kappa,
\quad E(c)=2\bigl((c+1)K(c)+29\bigr).
\tag{B14}
$$

Now use the field-valued point-versus-line theorem proved in the algebraic part. Its explicit formal hypotheses are

$$
q\geq10^6D^3,\qquad E(c)\kappa\leq\frac1{4\cdot10^6}.
$$

It supplies a formal polynomial $P\in F[X_1,\ldots,X_k]$ of total degree at most $D$ for which $\Delta(g,P)\leq2E(c)\kappa$. Encoding halves this distance. A final triangle inequality proves

$$
\Delta_{\rm full}(f,\mathcal H_r(P)),\
\Delta_{\rm hom}(f,\mathcal H_r(P))
\leq S(c)\kappa,
\qquad S(c)=28+E(c).
\tag{B15}
$$

This is the formal [encoded-line low-degree theorem](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/EncodedLineLowDegreeSoundness.lean). No closeness of the auxiliary rows is assumed: it was proved from their actual rejection rates. The second conclusion concerns homogeneous degree-one labels. The corrected paper's Theorem 4.1 states a bound for all affine degree-one labels; that stronger conclusion is not claimed here. The homogeneous bound is enough for the final difference check, while a certificate table whose full label space already has degree one receives its affine bound from the first conclusion.

<!-- /passage:pcp-long-encoded-line-soundness -->

### Correcting an outer value at a prescribed point

<!-- passage:pcp-long-outer-local-corrector -->

Fix a target $a\in F^k$. A point oracle $f$ has degree-one labels, and an auxiliary table is supplied for each line through $a$. Choose a uniform direction $v\in F^k$, a nonzero uniform parameter $z\in F^\times$, a uniform homogeneous label $L$, an inner correction direction, and an independent inner-test seed. Run the inner test on the line's auxiliary row. If it fails, reject. Otherwise correct that row at $\Phi(z)$ and compare with $f(a+zv,L)$. If the comparison fails, reject. If both checks pass, return the correction at $\Phi(0)$, with the same inner correction direction and label.

Thus the output is either one bit or rejection. The procedure uses at most $3c+9$ queries. With honest point and line tables for a polynomial of degree strictly below $b^c$, it returns $L(P(a))$ for every random seed. See [the local-correction procedure](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BinaryLocalCorrection.lean).

<!-- /passage:pcp-long-outer-local-corrector -->

<!-- passage:pcp-long-outer-correction-soundness -->

Let $P$ have total degree at most $D$, with $D\geq cb^c$, and suppose $f$ is within homogeneous distance $\delta$ of $\mathcal H_1(P)$. Assume $q>2c$, generator nodes for the inner test, and `GoodNodes` for the corrector. Let $R_a$ be the probability that the actual procedure rejects at target $a$. Define

$$
C(c)=2+2(c+1)K(c).
$$

Then the probability of either rejection or a wrong returned bit is at most

$$
C(c)R_a+\delta+\frac{D}{2(q-1)}.
\tag{B16}
$$

To prove this, decode each auxiliary row to $Q_v$ using (B11), and put $T_v=\operatorname{Dec}(Q_v)$. Since failure of the inner test forces rejection, the average auxiliary decoding error is at most $K(c)R_a$. Let $e=(c+1)K(c)R_a$. Equation (B13) bounds by $e$ each replacement of a corrected answer by $L(T_v(z))$, at either $z$ or zero. The comparison check then gives

$$
\Pr[L(T_v(z))\neq f(a+zv,L)]\leq e+R_a.
\tag{B17}
$$

We next relate the decoded line's origin to its random nonzero point. If $T_v(0)\neq P(a)$, the polynomial
$T_v(Y)-P(a+Yv)$ is nonzero and has degree at most $D$. It has at most $D$ roots in $F^\times$. Therefore, averaging first over $v,z$ and then over the binary label,

$$
\Pr_{v,L}[L(T_v(0))\neq L(P(a))]
\leq
\Pr_{v,z,L}[L(T_v(z))\neq L(P(a+zv))]
+\frac{D}{2(q-1)}.
\tag{B18}
$$

The factor one half again comes from the exact distance of two distinct field messages under homogeneous labels. For each fixed nonzero $z$, the map $v\mapsto a+zv$ is a bijection, so replacing the received primary bit in (B17) by the correct bit costs at most $\delta$. Combining (B17) and (B18) bounds the decoded origin's error by $e+R_a+\delta+D/[2(q-1)]$. Replacing its bit by the actual corrected origin costs another $e$, and accounting for rejection costs another $R_a$. This is (B16).

The formal [local-correction soundness theorem](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BinaryLocalCorrectionSoundness.lean) has no smallness assumption on $R_a$, no closeness hypothesis on the auxiliary table, and no claim that rejection is itself small. If only full affine-label distance $\delta$ is known, replace the $\delta$ in (B16) by $2\delta$. The theorem averages over the label: it does not promise reliability for each prescribed label of a corrupted oracle.

<!-- /passage:pcp-long-outer-correction-soundness -->

### Checking that a polynomial vanishes on a grid

<!-- passage:pcp-long-zero-certificate -->

Let $H\subset F$ be nonempty, let $h=|H|$, and put $Z_H(Y)=\prod_{a\in H}(Y-a)$. The algebraic part established that $P$ vanishes on $H^k$ exactly when there is a polynomial certificate $M(X,Y)$, with $k$ coordinates of each kind, such that

$$
M(X,0)=0,\qquad M(X,Z_H(X))=P(X),
\tag{B19}
$$

where $Z_H$ is applied coordinatewise. For the honest certificate, $\deg M\leq\deg P$. For the reverse implication no polynomial division is needed: at $x\in H^k$, the second argument is zero, so the two identities give $P(x)=0$.

Suppose both $P$ and an arbitrary proposed certificate $M$ have degree at most $D$, but $P$ does not vanish on the grid. At least one residual

$$
M(X,0),\qquad M(X,Z_H(X))-P(X)
$$

is a nonzero polynomial. Their degrees are at most $D$ and $Dh$, respectively. The latter bound uses $h\geq1$. The polynomial distance bound therefore shows that the field test checking both residuals at a uniform point rejects with probability at least $1-Dh/q$.

Observe both residuals with the same random homogeneous label. Whenever at least one field residual is nonzero, the binary pair is nonzero with probability at least one half: one selected nonzero residual alone already has that probability. Hence the ideal binary test rejects with probability at least

$$
\frac{1-Dh/q}{2}.
\tag{B20}
$$

The two residuals need not yield independent binary observations. This proof uses only a lower bound for their union. The field argument is [the algebraic grid check](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ZeroOnGridCheck.lean).

<!-- /passage:pcp-long-zero-certificate -->

<!-- passage:pcp-long-zero-actual-test -->

The received certificate is only close to $M$ on the full domain. Directly reading it at $(x,0)$ or $(x,Z_H(x))$ would be unjustified: these points lie in special subsets that could contain all its errors. The actual ZERO test therefore uses the outer local corrector at each of these two points. It reads the received primary bit $p(x,L)$ once, corrects the certificate at $(x,0)$ and requires zero, then corrects it at $(x,Z_H(x))$ and requires $p(x,L)$. It rejects every abstention. The two calls share $x,L$, but use independent remaining seeds. Its query bound is

$$
1+2(3c+9)=6c+19.
$$

For perfect completeness, take the primary table to be exactly $\mathcal H_1(P)$, the certificate table to be exactly $\mathcal H_1(M)$, and all auxiliary line tables to be the honest encodings of the corresponding restrictions of $M$. If $\deg M<b^c$ and (B19) holds, both correction calls are exact, so ZERO accepts for every seed.

<!-- /passage:pcp-long-zero-actual-test -->

<!-- passage:pcp-long-zero-soundness -->

Let $\delta_P$ and $\delta_M$ bound homogeneous distance of the received primary and certificate tables from $\mathcal H_1(P)$ and $\mathcal H_1(M)$, respectively. Let $\kappa$ be actual ZERO rejection. Assume $D\geq cb^c$, $q>2c$, generator nodes for the inner test, and `GoodNodes` for the corrector. As in (B20), $P$ does not vanish on the grid, and both $P$ and $M$ have degree at most $D$. At either requested certificate point, its corrector's rejection event is contained in ZERO rejection. Averaging (B16) over $x$ therefore bounds each call's failure by

$$
C(c)\kappa+\delta_M+\frac{D}{2(q-1)}.
$$

Couple the ideal and received tests by using the same outer point and label. If their verdicts differ, then either the primary bit is wrong or one of the two certificate calls fails to supply the ideal bit. The union bound, followed by (B20), gives the exact formal inequality

$$
\frac{1-Dh/q}{2}
\leq (1+2C(c))\kappa+\delta_P+2\delta_M+\frac{D}{q-1}.
\tag{B21}
$$

The denominator $1+2C(c)$ is positive, so equivalently

$$
\kappa\geq
\frac{(1-Dh/q)/2-\delta_P-2\delta_M-D/(q-1)}{1+2C(c)}.
\tag{B22}
$$

When the numerator is negative this is simply a valid, uninformative lower bound; later parameter choices make it positive. If the hypotheses are stated in full affine-label distances, use $2\delta_P+4\delta_M$ in place of $\delta_P+2\delta_M$. These are the [actual binary grid-test bounds](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BinaryZeroOnGridSoundness.lean), valid for every auxiliary correction table. This explicit inequality supplies the paper's asymptotic constant in Theorem 6.1 for the formal verifier's conventions.

<!-- /passage:pcp-long-zero-soundness -->

### Derived polynomial oracles and fresh correction randomness

<!-- passage:pcp-long-derived-oracle-transfer -->

The final verifier must apply ZERO to expressions such as $g(x)^3-1$, although its proof contains the degree-three encoding of $g$. Equation (B2) converts the desired affine observation to one label of the original row. A corrupted row may be wrong at exactly that label, so the verifier uses two-query self-correction with a fresh uniform full label $R$:

$$
h(x,\Lambda_{A_x,L}+R)-h(x,R).
\tag{B23}
$$

Here $A_x\in F[Y]$ may depend on the outer point, with $\deg A_x\leq r$ for every $x$. For a fixed point and requested label, (B3) bounds the chance of disagreement with $\mathcal H_1(A_x(g(x)))(L)$ by twice the full-label distance of that row from $\mathcal H_r(g(x))$. Averaging over uniform $x$ and any requested-label distribution chosen before $R$ gives an error at most $2\epsilon$, where

$$
\epsilon=\Delta_{\rm full}(h,\mathcal H_r(g)).
$$

This averaging does not require the label transformation $L\mapsto\Lambda_{A_x,L}$ to be a bijection. In particular, it remains valid when the polynomial or an outside multiplier is zero.

Now fix all other random choices of a downstream test, and couple its decision using (B23) to the decision using the ideal derived bit. The decisions can differ only when those two bits differ. If $\kappa_{\rm actual}$ and $\kappa_{\rm ideal}$ are their rejection probabilities, the same coupling yields

$$
\kappa_{\rm ideal}\leq\kappa_{\rm actual}+2\epsilon.
\tag{B24}
$$

This is a statement about the actual joint distribution of the verifier's randomness. It neither fixes a favourable seed nor treats the randomized derived answers as a single deterministic oracle close to the intended one. The distinction avoids an unnecessary exchange of quantifiers.

Suppose there is a polynomial $P$ of total degree at most $D$ such that $P(x)=A_x(g(x))$ at every point. This polynomiality is a hypothesis: arbitrary dependence of $A_x$ on $x$ does not establish it. Also assume that $P$ does not vanish on the nonempty grid, that the decoded certificate $M$ has degree at most $D$, and that the field-size, decoding-degree and node hypotheses of (B21) hold. In (B21), take the ideal primary oracle to be exactly $\mathcal H_1(P)$. Its primary distance is zero. Substituting (B24) gives

$$
\frac{1-Dh/q}{2}
\leq
(1+2C(c))\bigl(\kappa_{\rm actual}+2\epsilon\bigr)
+2\delta_M+\frac{D}{q-1}.
\tag{B25}
$$

The replacement error is multiplied by $1+2C(c)$, because it enters through ZERO's rejection term. Omitting that factor would change the quantitative argument. The formal sources are [fresh derived answers](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/HadamardDerivedOracle.lean) and [their use in ZERO](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/DerivedZeroOnGridSoundness.lean).

These establish the testing and correction statements used in the [seven-check soundness argument](#soundness-of-the-seven-check-verifier). In particular, (B15) supplies the fixed witnesses, and (B25) constrains their derived vertex and edge polynomials. Retaining those witnesses through all the checks is what yields one proper colouring.

<!-- /passage:pcp-long-derived-oracle-transfer -->

## Appendix. Failure of the earlier scalar test

<!-- passage:pcp-long-algebra-old-test-counterexample -->
The earlier test's failure can be seen in a family of arbitrarily large fields, so it is not merely a small-field exception. Let $q=2^{2k}$ for any $k\ge2$, set $c=2$, and choose $\omega$ of order three in $F_q^\times$. Such an element exists because $3$ divides $q-1$. In any dimension $m\ge1$, put $f(x)=x_1^4$. The unit-weight test in v1 accepts when

$$
f(u)+\sum_{i=1}^3 f(u+\omega^i v)=0.
$$

The characteristic-two Frobenius identity $(a+b)^4=a^4+b^4$ gives, for every pair $u,v$,

$$
f(u)+\sum_{i=1}^3 f(u+\omega^i v)
=4u_1^4+v_1^4\sum_{i=1}^3\omega^{4i}=0.
$$

Here $4=0$, $\omega^4=\omega$, and $1+\omega+\omega^2=0$. Thus the test accepts with probability one. Nevertheless, for every polynomial $P$ of total degree at most two, fix the other $m-1$ coordinates. The polynomial

$$
X^4-P(X,x_2,\ldots,x_m)
$$

has degree exactly four and leading coefficient one. It has at most four roots, so averaging over the fixed coordinates proves $\Delta(f,P)\ge1-4/q$. In particular $f$ is not a degree-two polynomial function. The same argument excludes representations of individual degree at most two.

The fields in this family are unbounded. For any proposed absolute constant $C$, choose $k$ large enough that $q>Cc^3=8C$. Then choose $0<\delta<1/[2(c+2)^2]$ with $2\delta<1-4/q$. The word passes every old test but violates the claimed proximity conclusion of v1 Lemma 3.3 under its stated large-field condition. This identifies a failure of that scalar characterization and soundness lemma; it does not construct a cheating proof for every check of the final PCP verifier.

In v2, Fact 2.7 and Lemma 3.3 use the full multiplicative generator and the weights (A6), for which the proof above applies. The v2 acknowledgments thank Troy Lee for pointing out the earlier mistake in Lemma 3.3. The calculation here is an ordinary derived explanation of the correction, not a claim that this particular example was Lee's, a novelty claim, or a separately Lean-checked counterexample. [Paper v1, Fact 2.7 and Lemma 3.3][paper-v1]; [corrected v2 and acknowledgments][paper].

<!-- /passage:pcp-long-algebra-old-test-counterexample -->

## Source and verification account

<!-- passage:pcp-long-intro-source-editions -->
The fixed formal source is [Lee's PCP development at the revision linked throughout this account][formal-source]. The primary paper is the corrected [arXiv v2 of *A Simple Algebraic Proof of the PCP Theorem*][intro-paper], dated 22 October 2026. That public revision corrects the short low-degree test and acknowledges Lee's identification of an earlier mistake. A separate final SOSA proceedings edition has not been established identical to v2. Nor are the paper and Lean development asserted to be textually or parametrically identical: the chapters state the formalization's exact tests, constants and resource guarantees where these differ. Public links identify the supporting statements at the fixed revision. The linked declarations identify the formal statements explained here. The ordinary proofs and illustrative calculations in this account are explanatory reconstructions; they do not constitute a separate kernel check of the prose.

The new prose was prepared by AI agents directed by Will Cook. The underlying algebraic argument is due to Prashanth Amireddy, Amik Raj Behera, Srikanth Srinivasan, Madhu Sudan and Sophus Valentin Willumsgaard; the Lean formalization is Troy Lee's. This account is an explanation of that work, not a new proof claimed by its explanatory authors. It does not imply the original authors' endorsement or human review.
<!-- /passage:pcp-long-intro-source-editions -->

## References

<!-- passage:pcp-long-references -->
The version notes identify the copies consulted. Theorem and section numbers refer to those copies; a linked author manuscript is not assumed to have the published article's pagination.

**[ABSSW26]** Prashanth Amireddy, Amik Raj Behera, Srikanth Srinivasan, Madhu Sudan and Sophus Valentin Willumsgaard. *A Simple Algebraic Proof of the PCP Theorem*. [arXiv:2608.17429v2](https://arxiv.org/abs/2608.17429v2), 22 October 2026. Primary paper for the construction; the corrected weighted test is in Fact 2.7 and Lemma 3.3. This public revision has not been identified with a separate final SOSA proceedings edition.

**[ABSSW26v1]** Prashanth Amireddy, Amik Raj Behera, Srikanth Srinivasan, Madhu Sudan and Sophus Valentin Willumsgaard. *A Simple Algebraic Proof of the PCP Theorem*. [arXiv:2608.17429v1](https://arxiv.org/abs/2608.17429v1), 18 August 2026. Historical version used only to state and analyse the earlier unit-weight test in Fact 2.7 and Lemma 3.3.

**[ALMSS98]** Sanjeev Arora, Carsten Lund, Rajeev Motwani, Madhu Sudan and Mario Szegedy. “Proof Verification and the Hardness of Approximation Problems.” *Journal of the ACM* **45**(3), 501–555, 1998. [DOI: 10.1145/278298.278306](https://doi.org/10.1145/278298.278306). Consulted version: the [author-hosted journal manuscript](https://people.seas.harvard.edu/~madhusudan/papers/1992/almss-journ.pdf), especially Theorem 45 on point-versus-line testing and Theorem 69 on bivariate agreement.

**[AS98]** Sanjeev Arora and Shmuel Safra. “Probabilistic Checking of Proofs: A New Characterization of NP.” *Journal of the ACM* **45**(1), 70–122, 1998. [Journal-format copy](https://www.cs.umd.edu/~gasarch/TOPICS/pcp/AS.pdf). Section 5.2 supplies the bivariate agreement antecedent, including the error-locator and interpolation construction.

**[BCHKS96]** M. Bellare, D. Coppersmith, J. Håstad, M. Kiwi and M. Sudan. “Linearity Testing in Characteristic Two.” *IEEE Transactions on Information Theory* **42**(6), 1781–1795, 1996. [DOI: 10.1109/18.556674](https://doi.org/10.1109/18.556674). Consulted version: the [author manuscript](https://www.csc.kth.se/tcs/projects/publications/bchks.pdf). The characteristic-two Fourier analysis is the quantitative linearity-testing antecedent used in the primary paper's Appendix B and reconstructed in the binary chapter.

**[BLR93]** Manuel Blum, Michael Luby and Ronitt Rubinfeld. “Self-Testing/Correcting with Applications to Numerical Problems.” *Journal of Computer and System Sciences* **47**(3), 549–595, 1993. [DOI: 10.1016/0022-0000(93)90044-W](https://doi.org/10.1016/0022-0000(93)90044-W). Consulted version: the [author-hosted manuscript](https://people.csail.mit.edu/ronitt/papers/selftestcorrect.pdf), including Section 4.2 on linear self-testing. This is the source of the BLR test used in the Hadamard analysis.

**[FS95/13]** Katalin Friedl and Madhu Sudan. “Some Improvements to Total Degree Tests.” In *Proceedings of the Third Israel Symposium on Theory of Computing and Systems*, 190–198. IEEE Computer Society, 1995. [DOI: 10.1109/ISTCS.1995.377032](https://doi.org/10.1109/ISTCS.1995.377032). Consulted version: [arXiv:1307.3975v1](https://arxiv.org/abs/1307.3975v1), 15 July 2013, which corrects typographical errors in the conference version. Lemma 4 is the exact-line characterization cited in the primary paper's Appendix A; the algebra chapter gives the pinned formalization's explicit degree-bound argument.

**[KS08]** Tali Kaufman and Madhu Sudan. “Algebraic Property Testing: The Role of Invariance.” In *Proceedings of the 40th Annual ACM Symposium on Theory of Computing*, 403–412, 2008. [DOI: 10.1145/1374376.1374434](https://doi.org/10.1145/1374376.1374434). Consulted version: the [conference manuscript](https://people.csail.mit.edu/madhu/papers/2007/apt-conf.pdf), especially Theorem 2.9. The weighted affine-constraint argument is the specialization used in the corrected short test.

**[RS96]** Ronitt Rubinfeld and Madhu Sudan. “Robust Characterizations of Polynomials with Applications to Program Testing.” *SIAM Journal on Computing* **25**(2), 252–271, 1996. [DOI: 10.1137/S0097539793255151](https://doi.org/10.1137/S0097539793255151). Consulted version: the [retained manuscript][rubinfeld-sudan], Section 4, Theorem 5 and Lemmas 6–8, pp. 10–12. The primary PCP paper cites the corresponding published result as Theorem 4.1; numbering differs between these editions.

**[Lee26]** Troy Lee. *tcs-formalizations: PCP development*. Lean source, 2026. [Revision a0ce13ed0fa264f051c1278e039596ce65557fa4](https://github.com/troyjlee/tcs-formalizations/tree/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP). This fixed revision is the formal source of the theorem statements, explicit constants, verifier implementation and concrete complexity-model results explained here. The chapter links identify individual files and declarations within it.

**[Shoup05]** Victor Shoup. *A Computational Introduction to Number Theory and Algebra*. First edition. Cambridge University Press, 2005. Consulted version: [Version 1 of the author's electronic edition](https://shoup.net/ntb/ntb-v1.pdf), 15 January 2005. Chapters 20–21 provide the finite-field construction background cited in the primary paper's Fact 2.3. The detailed bounded-search algorithms and explicit cost bounds in the implementation section are those of Lee's formalization, not bounds attributed to this book.
<!-- /passage:pcp-long-references -->

[friedl-sudan]: https://arxiv.org/abs/1307.3975v1
[rubinfeld-sudan]: https://www.cs.princeton.edu/courses/archive/spring04/cos598B/bib/RubinfeldS.pdf
[kaufman-sudan]: https://people.csail.mit.edu/madhu/papers/2007/apt-conf.pdf
[blr]: https://people.csail.mit.edu/ronitt/papers/selftestcorrect.pdf
[bchks]: https://www.csc.kth.se/tcs/projects/publications/bchks.pdf
[shoup]: https://shoup.net/ntb/ntb-v1.pdf
[formal-source]: https://github.com/troyjlee/tcs-formalizations/tree/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP

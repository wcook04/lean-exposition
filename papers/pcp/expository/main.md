# Checking a long proof by reading a few bits

## An algebraic proof of the PCP theorem, through worked examples

15 November 2026

<!-- passage:pcp-expository-opening -->
Suppose someone hands you a graph and claims that its vertices can be coloured
with three colours, with different colours at the ends of every edge. A
colour for each vertex would let you check the claim by inspecting all the
edges. By the PCP theorem, there is a more redundant certificate that a
randomised checker can test by reading only a constant number of bits. If
the graph is three-colourable, some certificate always passes. Otherwise,
every certificate fails with probability at least one half.

The same statement holds for every problem whose proposed solutions can be
checked in polynomial time. The encoded certificate still has polynomial
length. PCP stands for *probabilistically checkable proof*.

The constant bounds the number of **certificate bits read**. The checker may
read the input and perform a polynomial amount of computation. The certificate
is specially encoded; it is not an ordinary written proof read at a few
randomly selected places. The verifier checks relations among entries of
the encoding.

These notes explain the algebraic construction of Amireddy, Behera,
Srinivasan, Sudan and Willumsgaard, and its formalisation in Lean by Troy
Lee. The construction combines polynomial identities with binary encodings;
it does not use composition of PCP verifiers. We follow the corrected
[October 2026 paper][paper-v2] and identify consequential differences in
the pinned formal development. The theorem itself predates this construction:
its original proofs are due to [Arora and Safra][arora-safra] and
[Arora, Lund, Motwani, Sudan and Szegedy][almss].

The intended reader knows polynomial arithmetic, finite sums and elementary
probability, but need not know complexity theory, coding theory or Lean.
We will calculate small examples of the operations the proof uses, then
explain why they fit together. The difficult general testing theorems are
stated at their uses; their proofs are in the [full argument][long].
The [specialist paper][short] gives a shorter mathematical account.
<!-- /passage:pcp-expository-opening -->

<!-- passage:pcp-expository-colouring -->
## 1. Why checking a few edges is not enough

A proper three-colouring of a graph assigns one of three colours to each
vertex so that the ends of every edge have different colours. Finding the
colouring may be difficult, but checking a supplied colouring is easy:
inspect every edge. The colouring is an ordinary certificate.

Consider the complete graph on four vertices, $K_4$. It has six edges and
cannot be three-coloured: among four vertices, two must have the same
colour, and those two are joined by an edge. Give its vertices the colours
$({\rm red},{\rm red},{\rm green},{\rm blue})$. Exactly one edge has equal
colours at its ends. A checker that samples one edge uniformly catches this
failure with probability $1/6$.

Now add $t$ disjoint triangles, each properly coloured. The graph is still
not three-colourable, because it still contains $K_4$, but the displayed
assignment has only one bad edge among $6+3t$ edges. Uniform edge sampling
rejects with probability

$$
\frac{1}{6+3t}.
$$

For example, three added triangles reduce this to $1/15$. A fixed number
of samples becomes ineffective as $t$ grows: the one bad edge accounts for
a smaller fraction of the sampled edges.

In the PCP construction, the prover supplies redundant tables related by
algebraic identities. The checker tests only a few entries, but the soundness
proof shows that tables passing very often would determine a proper colouring
of the original graph. For $K_4$, that is impossible.

There are two obligations. First, the tables must describe coherent
mathematical objects rather than arbitrary strings. Second, those objects
must satisfy the colouring conditions. Testing the second without the
first would allow a dishonest prover to give unrelated answers to different
questions.
<!-- /passage:pcp-expository-colouring -->

<!-- passage:pcp-expository-theorem -->
## 2. What the theorem promises

A decision problem is a set $L$ of finite bit strings; a string $x$ is a
yes-instance when $x\in L$. The class NP consists of problems for which
membership has a polynomial-length certificate that a deterministic
polynomial-time algorithm can check. Three-colouring is one such problem.

A verifier is one algorithm, fixed for the problem. The prover fixes its
certificate before the verifier chooses its random bits.

**PCP theorem.** For every $L\in\mathrm{NP}$, there are a polynomial-time
verifier $V$, natural-number constants $a,b,q$, and a polynomial $p$, such
that on every input $x$ of length $n$:

* $V$ uses exactly $a\lceil\log_2(n+2)\rceil+b$ independent fair random bits;
* on every run it reads at most $q$ bits of a certificate, all at positions
  below $p(n)$;
* if $x\in L$, some certificate is accepted for every choice of the random
  bits;
* if $x\notin L$, every certificate is accepted with probability at most
  $1/2$.

The constants, polynomial and verifier are chosen once for $L$, before
$x$. The certificate may depend on $x$, but it may not depend on the random
bits that will be used to check it. A yes-instance has **perfect
completeness**; the upper bound $1/2$ on acceptance of false instances is
the **soundness error**. These conditions are expressed in the formal
[verifier definitions][verifier-definitions] and
[main theorem][lean-theorem].

The formula for the random-bit budget is convenient for the formal proof.
Extra random bits can be ignored, so requiring this exact form does not
force the verifier to make use of each bit. It also makes the budget a
specified computable function of the input length.

Conversely, suppose a problem has a verifier with these properties. Guess
the first $p(n)$ certificate bits, and run the verifier on **all** its
random strings. There are

$$
2^{a\lceil\log_2(n+2)\rceil+b}
\leq 2^{a+b}(n+2)^a
$$

such strings, a polynomial number because $a,b$ are fixed. Accept the
guessed certificate if every run accepts. Perfect completeness supplies
such a certificate on yes-instances. On a no-instance no certificate can
pass every run, since acceptance probability one would exceed $1/2$.
The certificate and the exhaustive computation both have polynomial size.
Thus the problem is in NP. This proves the equality usually written

$$
\mathrm{NP}=\mathrm{PCP}(O(\log n),O(1)).
$$

The hard direction is constructing the verifier. We first explain it for
three-colouring. A polynomial-time reduction then transfers it to any
problem in NP.
<!-- /passage:pcp-expository-theorem -->

<!-- passage:pcp-expository-polynomial-distance -->
## 3. Why polynomial tables can reveal a hidden defect

Work first with arithmetic modulo $5$, in the field
$\mathbb F_5=\{0,1,2,3,4\}$. Addition and multiplication are performed
modulo $5$. In particular, nonzero elements can be divided by:
$2^{-1}=3$, since $2\cdot3=1$ modulo $5$.

The polynomial $Z(X)=X(X-1)$ has the following values:

| $x$ | $0$ | $1$ | $2$ | $3$ | $4$ |
| --- | --- | --- | --- | --- | --- |
| $Z(x)$ | $0$ | $0$ | $2$ | $1$ | $2$ |

It vanishes at two points and is nonzero at three. This reflects a general
fact: a nonzero polynomial of degree at most $d$ over a field has at most
$d$ roots. Each root permits a factor $(X-r)$ to be removed, and repeatedly
removing distinct roots cannot reduce the degree below zero.

Consequently, two different polynomials of degree at most $d$ disagree at
at least a fraction $1-d/Q$ of the elements of a field with $Q$ elements.
Apply the root bound to their difference. For multivariate polynomials,
the corresponding bound uses **total degree**: if $P$ is a nonzero
polynomial of total degree at most $d$ in $m$ variables, then

$$
\Pr_{u\in\mathbb F_Q^m}[P(u)=0]\leq\frac dQ.
$$

The probability is uniform over the whole ambient space. This is the
polynomial distance estimate used throughout the proof; a proof by
induction on the number of variables is given in the full account.
It is informative when the field is large compared with the degree.

If a claimed polynomial identity is false, its difference is a nonzero
polynomial. A uniformly random point then finds a failure with high
probability. A false identity cannot differ at just one arbitrarily chosen
location while both sides retain low degree.

An arbitrary table can agree with a polynomial everywhere except one
entry. A received table therefore needs a separate low-degree test before
we can use the polynomial distance bound.
<!-- /passage:pcp-expository-polynomial-distance -->

<!-- passage:pcp-expository-interpolation -->
### Extending a short table

Interpolation turns values on a small set into a polynomial on a larger
space. A polynomial of degree at most two is determined by its values at
three distinct points. Over $\mathbb F_5$, its value at $3$ can be recovered
from the values at $0,1,2$ by

$$
p(3)=p(0)+2p(1)+3p(2).
$$

For $p(X)=X^2$, those three values are $0,1,4$, and the weighted sum is
$0+2+12=4$ modulo $5$, just as $3^2=4$ modulo $5$.
The coefficients are obtained from the Lagrange polynomials. For instance,
the coefficient of $p(0)$ is

$$
\frac{(3-1)(3-2)}{(0-1)(0-2)}=1
\quad\text{in }\mathbb F_5.
$$

These weights are part of the identity. Replacing them by three unit
weights would give $0+1+4=0$, which is not $p(3)$.

For a set $H$ of $h$ distinct field elements, let $L_s(X)$ be the
degree-$(h-1)$ polynomial equal to one at $s\in H$ and zero at the other
points of $H$:

$$
L_s(X)=\prod_{t\in H,\ t\ne s}\frac{X-t}{s-t}.
$$

Any table $f:H^m\to\mathbb F_Q$ has the extension

$$
\widehat f(X_1,\ldots,X_m)
=\sum_{s\in H^m}f(s)\prod_{j=1}^m L_{s_j}(X_j).
$$

At a grid point, all the basis products are zero except the one indexed
by that point. The extension therefore agrees with $f$ on $H^m$, has
degree at most $h-1$ in each coordinate, and has total degree at most
$m(h-1)$. This gives us an honest polynomial table from an ordinary colouring
table. The proof encodes its values throughout $\mathbb F_Q^m$, not just on
the original grid.
<!-- /passage:pcp-expository-interpolation -->

<!-- passage:pcp-expository-colour-polynomials -->
## 4. Turning three colours into polynomial equations

For the colouring construction we now change fields. We use characteristic
two, where $1+1=0$, and a field containing an element $\omega$ with
$\omega^2+\omega+1=0$. The four elements
$0,1,\omega,\omega^2$ form a copy of $\mathbb F_4$.
The three nonzero elements obey

$$
1^3=\omega^3=(\omega^2)^3=1.
$$

Use $1,\omega,\omega^2$ as the colours. A proposed value $u$ is one of
these colours exactly when $u^3-1=0$. If $u,v$ are valid colours,
they are different exactly when $(u-v)^3-1=0$. The residual values are:

| $(u-v)^3-1$ | $v=1$ | $v=\omega$ | $v=\omega^2$ |
| --- | --- | --- | --- |
| $u=1$ | $1$ | $0$ | $0$ |
| $u=\omega$ | $0$ | $1$ | $0$ |
| $u=\omega^2$ | $0$ | $0$ | $1$ |

For example, the triangle coloured $(1,\omega,\omega^2)$ gives three
zero edge residuals. The assignment $(1,1,\omega^2)$ gives residuals
$(1,0,0)$ on edges $12,23,31$. The colour-validity check remains necessary:
the edge identity was interpreted under the assumption that its two
arguments were allowed colours. To see what goes wrong without that
assumption, give the four vertices of $K_4$ all four elements of
$\mathbb F_4$, including zero. Every edge difference is nonzero and has
cube one, so every edge equation passes. The vertex assigned zero fails
$u^3-1=0$, as it must: this graph cannot be three-coloured.

Label the graph's vertices by a grid $H^m$, adding isolated vertices if
needed. Let $\chi$ be the low-degree extension of a colouring, and let
$\widehat E(x,y)$ extend the adjacency table, whose grid values are one
for an edge and zero otherwise. Define

$$
\begin{aligned}
\operatorname{Val}(x)&=\chi(x)^3-1,\\
\operatorname{Prop}(x,y)&=\widehat E(x,y)
\bigl((\chi(x)-\chi(y))^3-1\bigr).
\end{aligned}
$$

Then $\chi$ describes a proper colouring precisely when
$\operatorname{Val}$ vanishes on $H^m$ and
$\operatorname{Prop}$ vanishes on $H^{2m}$. The adjacency factor makes
the second requirement automatic for nonedges.

This translation has combined all the vertex requirements into one
polynomial and all the edge requirements into another. It has not yet
made them easy to check. In particular, we need vanishing **on the grid**,
not on the whole field. A perfectly valid $\operatorname{Val}$ can be
nonzero away from the grid. A random ambient evaluation cannot simply be
required to equal zero.
<!-- /passage:pcp-expository-colour-polynomials -->

<!-- passage:pcp-expository-grid-certificate -->
## 5. A certificate for vanishing on a grid

Return temporarily to $\mathbb F_5$, with $H=\{0,1\}$ and
$Z(X)=X(X-1)$. Consider

$$
P(X,Y)=Z(X)(Y+1)+Z(Y)(X+2).
$$

It vanishes at all four points of $H^2$: at each of them both $Z(X)$
and $Z(Y)$ vanish. It is not the zero polynomial. For example,

$$
P(2,2)=2\cdot3+2\cdot4=4\pmod5.
$$

The displayed decomposition certifies the grid condition: each term
contains a factor that vanishes on the grid. In more variables, the
corresponding statement is Lemma 2.9 of the [corrected paper][paper-v2]:
a polynomial vanishing on $H^m$ can be written

$$
P(X)=\sum_{j=1}^m Z_H(X_j)Q_j(X),
\qquad Z_H(T)=\prod_{h\in H}(T-h),
$$

with suitable degree bounds on the $Q_j$. Polynomial division in each
variable proves this result. After removing all multiples of the
$Z_H(X_j)$, the remainder has degree less than $|H|$ in every variable;
if it is zero on the whole grid, repeated univariate interpolation makes
the remainder zero. Write $h=|H|\geq1$. Division can choose each nonzero
quotient with $\deg Q_j+h\leq\deg P$: removing a multiple of the monic
degree-$h$ polynomial loses $h$ from its total degree.

Reading all $m$ terms would require a number of queries that grows with
the dimension. Following Corollary 2.10 of the [corrected paper][paper-v2],
package the sum into a single polynomial of two groups of variables:

$$
M(X,U)=\sum_{j=1}^m U_jQ_j(X).
$$

Its degree is at most $\deg P$, because multiplication by $U_j$ adds
one to $\deg Q_j$ and $h\geq1$. This bound will let the honest
certificate fit in the encoding used later.

It satisfies two polynomial identities,

$$
M(X,0)=0,
\qquad M(X,Z_H(X))=P(X),
$$

where $Z_H$ is applied to each coordinate. These identities also imply
the desired grid condition: if $x\in H^m$, then $Z_H(x)=0$, so both
expressions for $M$ give $P(x)=0$.

In the small example, the packaged certificate is

$$
M(X,Y,U,V)=U(Y+1)+V(X+2).
$$

At $(X,Y)=(2,2)$ its two substitutions are
$M(2,2,0,0)=0$ and $M(2,2,2,2)=4=P(2,2)$.
The polynomial $P$ is allowed to be nonzero there. The identity between
the certificate and $P$ holds everywhere.

Now suppose a proposed low-degree pair $P,M$ has $P$ nonzero somewhere
on the grid. At least one of the two identities must be false as a
polynomial identity. A random ambient point detects that failure by the
polynomial distance bound. Thus a large collection of grid conditions
has become two random algebraic checks.

**Question 1.** Could the checker omit the first identity and test only
$M(X,Z_H(X))=P(X)$? Test your answer with the nonvanishing polynomial
$P=1$. Answers to the questions appear in Section 11.

The remaining problem is that a received table is only *close* to a
polynomial, and the points $(x,0)$ and $(x,Z_H(x))$ are special points.
All its errors could lie there. We will return to this after learning
how to recover an intended value from a few random locations.
<!-- /passage:pcp-expository-grid-certificate -->

<!-- passage:pcp-expository-digit-encoding -->
## 6. Keeping the number of queries constant

A low-degree polynomial in many variables restricts to a low-degree
univariate polynomial on each line $u+Yv$. The prover supplies a table
describing these line polynomials. The checker can compare a point
value with the value claimed by a line through that point.

The point-versus-line theorem gives the converse needed for soundness.
Suppose each supplied line polynomial has degree at most $d$, and sample
$u,v$ and the line parameter $\lambda$ uniformly, with $\lambda$ allowed
to be zero. Let $\delta$ be the fraction of comparisons
$f(u+\lambda v)=T_{u,v}(\lambda)$ that fail. The formal theorem says
that if $Q\geq10^6d^3$ and $\delta\leq1/(4\cdot10^6)$, then the point
table is within distance $2\delta$ of one multivariate polynomial of
total degree at most $d$. This conclusion requires no assumption that
the supplied line polynomials agree with one another.

To prove this, compare two families of lines through a plane, giving
row and column descriptions of the same received values. If most of both
families agree with those values, interpolation and an error-locator
polynomial construct one bivariate polynomial close to the whole plane.
Applying this agreement result on random planes makes the predictions
from different lines agree at their crossings. A plurality of line
predictions then corrects the received table. Further plane comparisons
show that every restriction of this corrected function to a line has
degree at most $d$; interpolation then gives total degree at most $d$
in the ambient space. The [full argument][long] proves each step,
including the error-locator construction and the stated constants.

A line polynomial of degree $d$ has $d+1$ coefficients. Reading all
those coefficients is not a constant number of bit queries when $d$
grows. The construction encodes the polynomial in a different set of
variables so that its new degree is fixed.

Here is the operation with two base-$3$ digits. Over $\mathbb F_5$, take

$$
p(Y)=Y^5+2Y+3.
$$

Since $5=2+1\cdot3$, replace $Y^5$ by $X_{0,2}X_{1,1}$.
Likewise, $1=1+0\cdot3$ and $0=0+0\cdot3$. The encoded polynomial is

$$
\widetilde p(X)=X_{0,2}X_{1,1}
 +2X_{0,1}X_{1,0}+3X_{0,0}X_{1,0}.
$$

It has degree two, although $p$ has degree five. There are more variables,
one group for each digit position. To recover $p(\lambda)$, substitute

$$
(X_{0,0},X_{0,1},X_{0,2})=(1,\lambda,\lambda^2),
\qquad
(X_{1,0},X_{1,1},X_{1,2})=(1,\lambda^3,\lambda^6).
$$

At $\lambda=2$, these two triples are $(1,2,4)$ and $(1,3,4)$.
The encoded evaluation is $4\cdot3+2\cdot2+3=4$ modulo $5$,
which agrees with $p(2)=2^5+2\cdot2+3=4$ modulo $5$.

In general, write an exponent $j<b^c$ with $c$ base-$b$ digits and
replace $Y^j$ by the product of the corresponding $c$ variables.
The resulting polynomial has degree at most $c$, and the same
substitution recovers every evaluation of the original polynomial.
The construction fixes $c$, while allowing the number of variables
to grow. This is the **set-multilinear encoding** defined in Section 3.1
of the [corrected paper][paper-v2]; Claim 3.2 states its evaluation identity.

The test need not enforce its exact special form. A received table
may decode to an arbitrary polynomial of degree at most $c$ in these
variables. Substituting the powers of $Y$ still gives a univariate
polynomial, now with a somewhat larger degree bound. We use this larger
bound in the soundness argument. A table which merely passes a low-degree
test is not assumed to have the form of an honest encoding.

We can calculate the larger bound. Each substituted variable is
$Y^{j b^i}$, with $0\leq j<b$ and $0\leq i<c$, so its degree is at
most $(b-1)b^{c-1}$. A monomial of a degree-$c$ polynomial contains
at most $c$ variable occurrences. Its degree after substitution is
therefore at most $c(b-1)b^{c-1}$, and the convenient upper bound
$D=cb^c$ applies to the decoded univariate polynomial.
<!-- /passage:pcp-expository-digit-encoding -->

<!-- passage:pcp-expository-weighted-test -->
### Testing and correcting a polynomial of fixed degree

For degree at most $c$, interpolation needs $c+1$ values, a fixed number.
The nonzero elements of a finite field form a cyclic multiplicative
group: there is an element $\zeta$ whose successive powers run through
every nonzero field element. We use this standard finite-field theorem
as an algebraic input and call $\zeta$ a generator. The formal
construction chooses $a_i=\zeta^{i+1}$ for $i=0,\ldots,c$, and the
Lagrange weights $\eta_i$ for evaluation at zero. It tests

$$
f(u)=\sum_{i=0}^c\eta_i f(u+a_i v)
$$

at uniformly random $u,v$. An honest polynomial of total degree at
most $c$ passes: along a line it is a univariate polynomial of degree
at most $c$, so interpolation applies.

For the converse, use the stated generator nodes and $|F|>2c$.
If the rejection rate is $\delta<1/[2(c+2)^2]$, the function is within
distance $2\delta$ of some polynomial of total degree at most $c$.
Here distance means the fraction of table entries that differ.
Passing the relation rarely or at a few selected lines would not give
this conclusion. The [corrected paper][paper-v2], Section 3.2, develops
this weighted test and its correction procedure; the bounds stated here
are those of the formal development.

The same formula also corrects a value at a prescribed point. Suppose
$f$ differs from a degree-$c$ polynomial $P$ on at most a fraction
$\varepsilon$ of the ambient space. Fix $u$, choose $v$ uniformly,
and return the weighted sum of the $c+1$ surrounding values, without
reading $f(u)$. Each point $u+a_i v$ is uniform because $a_i\ne0$.
If all those values are correct, interpolation returns $P(u)$.
By the union bound, the probability of a wrong answer is at most

$$
(c+1)\varepsilon.
$$

The sampled points need not be independent for this bound: they all
lie on one line, but each individual error event has the required
probability.

A fixed-degree encoding can therefore be checked with a fixed number
of field queries, and a value at a special point can be recovered through
random points. Each field query still returns several bits. To reach
the promised bit-query bound, we need a binary encoding as well.
<!-- /passage:pcp-expository-weighted-test -->

<!-- passage:pcp-expository-hadamard -->
## 7. A field value represented by many one-bit questions

Start with a three-bit message $s=101$. For every three-bit vector
$x$, store the parity

$$
h_s(x)=s\cdot x\pmod2.
$$

The positions of the word are themselves bit vectors. In order
$000,001,010,011,100,101,110,111$, its contents are

$$
(0,1,0,1,1,0,1,0).
$$

This is the homogeneous linear part of a Hadamard encoding. It stores
eight answers about a message with only three bits. Any two different
messages give words differing in exactly half their positions. Indeed,
their difference is a nonzero linear functional. Choose a vector on
which it is one; adding that vector pairs every zero value with a one value.

Thus a uniformly random one-bit observation distinguishes two unequal
messages with probability $1/2$. To compare values, the checker queries
the same random linear functional on each and compares the resulting
bits; it does not need to reconstruct either whole message.

Blum, Luby and Rubinfeld's [linearity test][blr] checks this kind of
word. Choose independent uniform $a,b$ and check

$$
h(a)+h(b)=h(a+b),
$$

where all vector and bit additions are modulo two. An honest word always
passes. Flip the entry at $001$ in our eight-bit word to obtain $g$.
Of the $64$ ordered pairs $(a,b)$, $46$ pass and $18$ fail. One way to
see the rejection count is to track whether an odd number of
$a,b,a+b$ equals $001$. The three relevant sets each have eight
pairs; their pairwise intersections are the three distinct pairs
$(001,001)$, $(001,000)$ and $(000,001)$. Those intersections
contribute two errors, which cancel. The count is therefore
$3\cdot8-2\cdot3=18$.

Bellare, Coppersmith, Håstad, Kiwi and Sudan proved the sharp bound
([Theorem 1.2][bchks]): a function which fails this test with probability
$\varepsilon$ is within distance $\varepsilon$ of a linear functional.
Its proof, included in the formal development, uses Fourier analysis on
a finite binary vector space. Appendix B, Theorem B.1 of the
[corrected paper][paper-v2] states this bound and cites both works.
The eight-point example demonstrates the test; the theorem applies to
arbitrary received words.
<!-- /passage:pcp-expository-hadamard -->

<!-- passage:pcp-expository-hadamard-correction -->
### Recovering a chosen answer

Suppose we want $h_s(x)$ but distrust the entry at $x$. Choose a uniform
$r$ and return

$$
g(r)+g(r+x).
$$

For the honest word this equals $h_s(x)$, because the two appearances
of $h_s(r)$ cancel. If $g$ has error fraction $\varepsilon$, a wrong
answer requires an error at $r$ or at $r+x$. Each is uniform, so the
error probability is at most $2\varepsilon$.

In our word with one corrupted position, $\varepsilon=1/8$. For each
nonzero $x$, exactly six of the eight choices of $r$ give the correct
answer. At $x=0$ the same entry is queried twice, so it cancels even
when corrupt; all eight choices are correct. The general upper bound
$2\varepsilon=1/4$ is attained at every nonzero $x$ in this example.

**Question 2.** Why would choosing $r=x$ deterministically fail to give
the same guarantee against an arbitrary corrupt word? Which property
of the random choice was used in the proof?

Random self-correction lets the verifier request a special algebraic
observation using random query locations. The requested location itself
need not be typical. Arora and Barak explain the same two-query operation
in Section 18.4.1 of their [January 2007 draft][arora-barak].
<!-- /passage:pcp-expository-hadamard-correction -->

<!-- passage:pcp-expository-cubic-labels -->
### Why the construction needs more than linear questions

A field $F$ with $2^t$ elements can be represented as $t$ binary
coordinates using a fixed basis. An element $u$ then becomes a vector
$\rho(u)\in\mathbb F_2^t$. To check the colouring identities, the
verifier needs observations of expressions such as $u^3-1$.

For this purpose, it stores a larger word whose positions are Boolean
polynomials $R$ of degree at most three:

$$
H_3(u)(R)=R(\rho(u)).
$$

The coefficients of $R$ specify the position; the stored answer is
one bit. Boolean variables satisfy $Z_i^2=Z_i$ when evaluated, so
squarefree monomials suffice. For fixed $u$, this word is linear in
the label $R$, even though $R$ may be cubic in the message coordinates.

Multiplication in a finite field is bilinear in its binary coordinates.
Consequently, a linear binary observation $L(u^3-1)$ is a polynomial
of degree at most three in $\rho(u)$. The verifier can compute the
corresponding label and query that one position of $H_3(u)$.
It learns the required bit about $u^3-1$ without reading all $t$
coordinates of $u$.

Linearity in the labels alone is insufficient to establish that a
received word represents a field element. For example, assign values
one to the labels $1$ and $Z_1Z_2$, and zero to $Z_1,Z_2$, then extend
linearly to every label in their span. This is a linear function of
labels, but no evaluation at a point has those values: $Z_1=Z_2=0$
would force $Z_1Z_2=0$. Tests of products and of the constant label
remove this ambiguity.

The formal Hadamard test checks these properties using corrected
answers. Its degree-three version makes ten bit queries. The current
paper gives an eight-query version which retains only the top-degree
product check; the pinned Lean verifier also performs lower-degree
checks. We use the formal version's count when discussing its
resources. The linearity example above explains one component, not
the whole degree-three test.
<!-- /passage:pcp-expository-cubic-labels -->

<!-- passage:pcp-expository-binary-tests -->
## 8. Combining the encodings and returning to the grid

The construction now has two forms of redundancy. A line polynomial
is encoded as a polynomial of fixed degree in more variables. Each
field-valued entry is in turn encoded by binary questions. The
checker tests a received primary row, tests the relevant encoded
line row, and compares a corrected line value with the point value.

Field coefficients in the interpolation formula do not require
reading a whole field element. For a homogeneous binary linear
label $L$ and a field weight $\eta$,

$$
L(\eta u)=(L\circ(\eta\cdot))(u).
$$

The weight is incorporated into the queried label. Applying $L$ to a
weighted field identity therefore produces an identity among a fixed
number of bits. If the field identity is false, a uniform homogeneous
label detects it with probability $1/2$.

The combined low-degree theorem supplies **one** polynomial close to
the primary oracle on the label sets used later. It is not enough to
obtain one polynomial for the cubic questions and an unrelated one for
the linear questions: both checks must refer to the same decoded
polynomial. In the formal version, the additional degree-one guarantee
concerns homogeneous linear labels; this is the label family used for
the final difference check. A certificate table whose entire label
space has degree one also receives the full affine-label guarantee.

We need quantitative versions of these statements to know that the
errors will leave a positive gap. Fix a positive inner degree $c$ and
a positive digit base $b$, put $D=cb^c$, and write $Q=|F|$. The analysis gives
explicit constants depending only on $c$:

$$
\begin{aligned}
K&=4(c+2)^2\bigl(112(c+2)+60\bigr),\\
E&=2\bigl((c+1)K+29\bigr),\qquad S=28+E,\\
C&=2+2(c+1)K.
\end{aligned}
$$

Their sizes are less important here than their independence from the
graph. With the prescribed interpolation nodes, if the complete
encoded-line tester rejects with probability at most $\kappa$, and

$$
Q\geq10^6D^3,
\qquad E\kappa\leq\frac1{4\cdot10^6},
$$

there is one polynomial of degree at most $D$ whose encoding differs from the
received primary table on at most a fraction $\varepsilon=S\kappa$
of full labels, and on at most that fraction of homogeneous labels.
Both distances average over the ambient point as well as the indicated
label. This is the precise combined testing result we use below; the
[full account][long] derives the constants by summing the row-decoding,
line-correction and comparison errors.

The outer local corrector uses a random line through a prescribed
point. It checks the encoded line information and compares at a
random nonzero point of that line before returning the requested
binary value at its origin. It may reject. The soundness theorem
controls incorrect returned answers in terms of the actual
rejection probability, the distance of the primary table from its
polynomial, and a polynomial root bound. More precisely, fix a target
point $a$. If the primary table is within homogeneous distance $\delta$
of a polynomial of degree at most $D$, and the corrector rejects with probability
$R_a$, then

$$
\Pr[\text{rejection or wrong returned bit}]
\leq C R_a+\delta+\frac{D}{2(Q-1)}.
$$

This probability includes a uniformly random homogeneous label; it is
not a guarantee for every fixed label. It assumes no honesty of the
auxiliary line table and no smallness of $R_a$. The term $C R_a$ is
useful because a later test that rejects whenever correction rejects
will bound $R_a$ by its own rejection rate, after averaging over its
requested targets.

We can now return to the two identities for the vanishing certificate:

$$
M(x,0)=0,
\qquad M(x,Z_H(x))=P(x).
$$

The binary ZERO test observes them through a random homogeneous
label. It reads the primary bit at the random point $x$ and locally
corrects the two certificate values at their special points. Every
rejection by a corrector makes the test reject, so a prover that causes
correction to reject also causes the full test to reject.

For an honest zero-on-grid polynomial, the prover supplies its exact
primary encoding, an exact vanishing certificate and the honest encoded
line data for that certificate. All corrections and both identity checks
then succeed for every seed. Honest primary values alone would not
guarantee acceptance with an arbitrary certificate or arbitrary line data.

The soundness argument compares this received-data test with the
ideal test on the decoded polynomials. If the two outcomes differ,
one of the few answers used in the comparison must be wrong.
The correction bounds control that probability. If $P$ fails to
vanish on the grid, the ideal test has a positive rejection rate
by the polynomial distance estimate from Section 5. After deducting
the controlled errors, a positive rejection rate remains for the
actual test. Section 9 gives the exact inequality and the error
budget making it positive; the full argument proves the estimates.

Global closeness by itself would not justify either certificate
read. At each requested point, the correction theorem bounds rejection
or a wrong answer using both the global error fraction and the
corrector's actual rejection rate.
<!-- /passage:pcp-expository-binary-tests -->

<!-- passage:pcp-expository-assembly -->
## 9. From the seven checks to a colouring

The proof contains four main polynomial tables, each accompanied by
an encoded line table. They describe:

1. the colouring extension $\chi(x)$;
2. a certificate for the vanishing of $\chi(x)^3-1$ on the vertex grid;
3. the difference polynomial $\chi'(x,y)=\chi(x)-\chi(y)$;
4. a certificate for the vanishing of
   $\widehat E(x,y)(\chi'(x,y)^3-1)$ on the pair grid.

That is eight tables in total. The verifier runs four low-degree
tests, one for each main table and its line table; two ZERO tests,
one for each colouring condition; and one difference check connecting
$\chi'$ to $\chi$. It accepts only if all seven checks pass.

The separate difference table lets the verifier obtain binary
observations of the cube of a difference using the same local
operations as for the colouring table. The difference check ensures
that, under the high-acceptance assumption of soundness, its decoded
polynomial is the difference of the decoded colouring values.

For perfect completeness, start with a proper colouring, interpolate it,
form its difference polynomial, and construct the two vanishing
certificates. Supply their honest encodings and line tables.
Interpolation identities, binary encoding identities and the two grid
certificates then make every check accept for every seed, provided the
honest degrees fit the encoding capacity. Section 10 checks the
sufficient condition $5m(h-1)<b^c$ for the chosen parameters.

For soundness, suppose an arbitrary proof string is accepted with
probability very close to one. Each of the seven checks must then
reject rarely, because failure of any one makes the whole verifier reject.

The four low-degree tests produce four decoded polynomials.
The difference check and the binary distance identity show that
the decoded $\chi'$ is close to
$\chi(x)-\chi(y)$ at uniform field points. These are both
low-degree polynomials. If they were different, the polynomial
distance estimate would force much greater disagreement.
Hence they are identical. This converts an approximate statistical
comparison into an exact algebraic relation.

The two ZERO checks then force the two decoded colouring
polynomials to vanish on their grids. Their primary values are
obtained from the cubic encodings using freshly randomised
self-correction. The error estimates refer to the same decoded
$\chi$ and $\chi'$ chosen by the low-degree tests. The certificate
arguments therefore imply that $\chi$ assigns a valid colour at
every vertex and different colours at the ends of every edge.
It is a proper colouring.

Thus sufficiently high acceptance implies that the graph is
three-colourable. Taking the contrapositive, every proof for a
non-three-colourable graph is rejected with a fixed positive
probability. The proof selects the field and degree parameters
so that this probability does not shrink with the graph size.

### Why the accumulated errors still leave a gap

Let $\kappa$ now be the rejection rate of the whole seven-check
verifier, and suppose $E\kappa\leq1/(4\cdot10^6)$. Each low-degree
test rejects at most this often, so the four decoded polynomials have
the simultaneous code-distance bounds $\varepsilon=S\kappa$ from
Section 8. Replacing the three bits of the difference check by their
decoded values changes its decision on at most $3\varepsilon$ of
seeds. If the decoded difference polynomial were wrong, polynomial
distance and the half-distance binary encoding would instead force
ideal rejection at least $(1-D/Q)/2$. Thus

$$
\kappa+3\varepsilon<\frac{1-D/Q}{2}
$$

forces the exact difference identity.

Put $h=|H|$. The parameters also ensure $m(h-1)\leq D$, so the public adjacency
extension has degree at most $2D$. The decoded colour polynomial has
degree at most $D$. Consequently
its vertex constraint has degree at most $3D$, and its edge constraint
has degree at most $5D$, including the adjacency factor. The certificate
polynomials also have degree at most $D$. If either constraint fails
to vanish on its grid, the ZERO soundness estimate gives

$$
\frac{1-5Dh/Q}{2}
\leq (1+2C)(\kappa+2\varepsilon)
       +2\varepsilon+\frac{5D}{Q-1}.
$$

The left side is the ideal rejection bound. On the right, replacing
the derived cubic read costs $2\varepsilon$, so the relevant received
test rejects with probability at most $\kappa+2\varepsilon$. Every
certificate-corrector rejection also rejects that test. The two
corrector bounds therefore contribute through the factor $1+2C$;
their certificate-distance terms contribute another $2\varepsilon$.
The final term is the combined polynomial-root loss. In particular,
the corrector's own rejection rate has been bounded by an observed
test rejection rate; it is not an additional unproved assumption.

Choose the field large enough that

$$
\frac DQ\leq\frac14,\qquad
\frac{5Dh}{Q}\leq\frac14,\qquad
\frac{5D}{Q-1}\leq\frac18.
$$

Both ideal lower bounds are then at least $3/8$. Since $E,S,C$ are
fixed constants, we can choose a fixed positive $g$ so that $\kappa<g$
implies the testing threshold and

$$
\kappa+3S\kappa<\frac1{16},\qquad
(1+2C)(\kappa+2S\kappa)+2S\kappa<\frac1{16}.
$$

The difference identity follows because $1/16<3/8$. A false grid
condition would make the ZERO inequality assert
$3/8<1/16+1/8=3/16$, which is impossible. Thus both grid conditions
hold. Section 10 supplies parameters meeting the field requirements.
This calculation explains the fixed gap: the field controls the root
terms, while sufficiently small overall rejection controls every
remaining error term linearly.

The decoded polynomials and the recovered colouring exist in
the soundness argument. Their existence shows what a frequently
accepted string would imply. The verifier performs the prescribed
local queries and calculations without reconstructing these objects.

**Question 3.** Suppose the low-degree tests decoded the main
colouring table to one polynomial for cubic labels and a
different polynomial for the homogeneous linear labels. Which
step of the preceding soundness argument would need repair?
<!-- /passage:pcp-expository-assembly -->

<!-- passage:pcp-expository-resources -->
## 10. Randomness, proof length and repetition

The table sizes and the randomness budget have to be controlled
alongside the query count: the PCP theorem requires polynomial proof
length and logarithmic randomness as well as constant queries.

For a graph with $N\geq2$ vertices, choose the least integer $a\geq2$
such that $\lceil\log_2 N\rceil\leq a2^a$. Put

$$
s=2^a,\qquad |H|=m=s,\qquad c=4,\qquad
|F|=2^{12a+32}=2^{32}s^{12}.
$$

The grid $H^m$ contains $s^s=2^{a2^a}$ points, enough for
the vertices. Minimality of $a$ gives $a2^a=O(\log N)$:
if $a>2$, the preceding value $(a-1)2^{a-1}$ was too small,
and $a2^a\leq4(a-1)2^{a-1}$. The boundary value $a=2$
adds only a constant. The formal definition also covers
$N=0,1$ by taking $a=2$.

A point of $F^m$ takes $m\log_2|F|=s(12a+32)=O(\log N)$
bits to specify. The encoded line data uses $cs=4s$ extra
field coordinates, so it fits the same order of address
length. Degree-three Boolean labels use
$1+t+\binom t2+\binom t3$ coefficients for $t=12a+32$.
This is $O(a^3)$, which is also $O(a2^a)$ because
$a^2=O(2^a)$. Thus an address or a random seed for any of
the fixed number of tests has $O(\log N)$ bits. There
are polynomially many addresses in total.

The digit encoding uses base $b=s$ and degree $c=4$, so
the substitution estimate in Section 6 gives $D=cb^c=4s^4$.
The honest colour and certificate polynomials have degree at
most $5m(h-1)=5s(s-1)$. Since $s\geq4$,

$$
5s(s-1)<s^4=b^c,
$$

so all their line restrictions fit the honest encoding capacity.
The field is large enough for all the testing bounds. For example,
$10^6D^3=64\,000\,000s^{12}\leq2^{32}s^{12}=|F|$.
Also $100Dh=400s^5\leq|F|$. This bounds $D/Q$ by $1/100$
and $5Dh/Q$ by $1/20$; it also gives $Q-1\geq40D$, hence
$5D/(Q-1)\leq1/8$. All three field conditions in Section 9
therefore hold for the same choice of parameters.
Even the smallest field chosen here is much larger than those in
our worked examples.

Fair random bits give uniform field elements directly,
since $|F|$ is a power of two. Four correction parameters
originally range over the nonzero field elements. The
implementation instead samples each from the whole field
and accepts immediately if any of these four is zero.
Conditioned on all four being nonzero, the distribution
is exactly the original one. The rejection probability
is multiplied by $(1-1/|F|)^4\geq1/16$, so a fixed
positive gap survives.

The running-time claim requires more than short addresses.
The formal implementation computes the field, its arithmetic,
the public adjacency extension, the queries and their
acceptance condition in polynomial time, and compiles
these operations to a concrete machine model. The [full
argument][long] separates this implementation proof from
the information-theoretic query and randomness bounds.

"Constant" does not mean small in this formal construction.
One unamplified graph verifier reads at most $187$ bits,
but its proved rejection gap is only

$$
\gamma=\frac{1}{1137847282503168}.
$$

These bounds establish independence from the input size; they do
not give a practical verification protocol. The formal construction
repeats the verifier $R=1137847282503168$ times with independent
random seeds, accepting only when every run accepts.

The elementary calculation is easier with a toy gap.
Suppose one run accepts any fixed false proof with
probability at most $3/4$. Three independent runs accept
that same proof with probability at most

$$
(3/4)^3=27/64<1/2.
$$

The proof string is fixed throughout. The random seeds are
independent, so the acceptance events for that fixed
string multiply. Reusing the same seed would not justify
the product: all three runs might repeat exactly the
same decision.

For the actual gap, $(1-\gamma)^R\leq1/2$ follows from
$R\gamma\geq1$. One algebraic proof uses
$(1-\gamma)^{-1}\geq1+\gamma$ and
$(1+\gamma)^R\geq1+R\gamma$, giving
$(1-\gamma)^R\leq1/(1+R\gamma)\leq1/2$.
The value of $R$ is enormous but fixed, so repetition
preserves constant query complexity and logarithmic
randomness.

### From an arbitrary certificate checker to a graph

For any problem in NP, write a candidate accepting
computation of its certificate checker as a table:
one configuration per time step. Polynomial time gives
polynomially many rows and cells. Constraints require
the first row to contain the input and a permitted
witness, each subsequent row to follow the machine's
transition rule, and the last row to accept. The
machine has a fixed finite alphabet and reads a fixed
number of symbols per transition. Each constraint
therefore involves a bounded number of finite choices.
Their simultaneous satisfaction is equivalent to an
accepting computation with some witness.

The formal reduction represents each finite choice by
a block of bits with exactly one bit equal to one,
then converts the fixed-arity relations into Boolean
clauses of width at most three. Here is how that last
step works. For a relation $R$ on $k$ bits, consider
each possible input pattern $p$ and introduce flags

$$
z_0=0,\qquad z_{i+1}=z_i\lor(x_i\mathbin{\mathrm{xor}}p_i),
\qquad R(p)\lor z_k=1.
$$

The flags record whether the actual input has yet
differed from $p$. The last condition imposes $R(p)$
only when the actual input equals $p$. Because $p_i$
is fixed, $x_i\mathbin{\mathrm{xor}}p_i$ is a literal,
either $x_i$ or its negation. An OR equation $z=u\lor v$
is enforced by three clauses:

$$
(z\lor\neg u),\qquad(z\lor\neg v),\qquad
(\neg z\lor u\lor v).
$$

The first two require $z=1$ if either input is one;
the third requires an input to be one if $z=1$.
Short clauses are padded with the constant false.
Enumerating $2^k$ patterns costs a constant depending
on the original machine because $k$ is fixed, so the
output remains polynomial in size.

The final colouring gadget can be checked by hand.
For Boolean values, write $\operatorname{NAE}(a,b,c)$
when the three values are **not all equal**. A clause
$a\lor b\lor c$ is equivalent to the existence of
a bit $z$ such that

$$
\operatorname{NAE}(a,b,z),\qquad
\operatorname{NAE}(\neg z,c,0).
$$

If $a=b=0$, the first relation forces $z=1$, and the
second then forces $c=1$. If $a=b=1$, choose $z=0$;
if $a\ne b$, the same choice works regardless of $c$.
These cases establish the equivalence.

Now make a palette triangle whose colours we call
$0,1,2$. A Boolean variable and its negation are
adjacent vertices, each joined to palette vertex $2$.
They must take opposite colours $0$ and $1$. For
each NAE relation, create a fresh triangle and join
its three vertices to the three corresponding
literal vertices. If all literal colours are equal,
the new triangle has only two colours available and
cannot be coloured. For literal colours $(0,0,1)$,
the new triangle can use $(1,2,0)$ respectively:
its colours are distinct, and each differs from
its adjacent literal. Permuting and complementing
the literal colours covers every other NAE case.

The graph is therefore three-colourable exactly when
the original input has an accepting certificate.
The formal reduction also implements its construction
in polynomial time. Its polynomial output length
changes $O(\log N)$ random bits into $O(\log n)$,
because the logarithm of a polynomial is logarithmic.
Composing this reduction with the graph verifier
proves the forward direction of Section 2; exhaustive
seed checking proves the reverse direction.

**Question 4.** If the verifier were allowed to use
$\sqrt n$ random bits instead, would the exhaustive-seed
argument still prove that its language is in NP?
Identify the step that changes.

**Question 5.** Consider a smaller hypothetical error budget of the
kind used in Section 9. A false grid condition makes an ideal test
reject with probability at least $3/8$. The actual test rejects with
probability at most $\kappa$, and replacing its answers by ideal answers
changes the verdict with probability at most $4\kappa+1/16$. Does
$\kappa\leq1/32$ rule out a false grid condition? Does
$\kappa\leq1/16$ do so by the same estimates? Explain what follows
at the boundary; these toy constants do not replace the construction's
proved constants.
<!-- /passage:pcp-expository-resources -->

<!-- passage:pcp-expository-answers -->
## 11. Answers and a reconstruction task

**Answer 1.** The second identity alone is insufficient.
Take $P=1$ and let $M(X,U)=1$ independently of $U$.
Then $M(X,Z_H(X))=P(X)$ holds everywhere, although
$P$ never vanishes. The first identity excludes this
choice. With both identities, substituting a grid point
forces $P(x)=M(x,0)=0$.

**Answer 2.** For nonzero $x$, with $r=x$ fixed, the answer uses only the
entries at $x$ and zero. A corrupt word can put an error
at one of precisely those positions. A small global
error fraction does not make either fixed position
reliable. At $x=0$ the answer is always zero because
the two reads cancel, as in the worked example.
For arbitrary $x$, the random choice made both query locations
uniform; the union bound then converted global error
fractions into a bound on this particular request.

**Answer 3.** The difference check would relate the
linearly decoded values, while the ZERO checks for the
cubic expressions could concern different values.
There would be no single colouring polynomial known
to satisfy both the difference identity and the two
grid conditions. The soundness proof needs simultaneous
guarantees for one decoded object, not separate existence
statements with unrelated witnesses.

**Answer 4.** The number of seeds would be
$2^{\sqrt n}$, which is not bounded by any fixed
polynomial in $n$. The exhaustive verification could
take more than polynomial time. This shows why that
argument fails; it does not prove that the language
is outside NP.

**Answer 5.** Ideal rejection is at most actual rejection plus
the probability that the verdict changes, hence at most
$5\kappa+1/16$. At $\kappa\leq1/32$, this is at most
$7/32<12/32=3/8$, which contradicts a false grid condition.
At $\kappa\leq1/16$, the upper bound is $3/8$; equality
gives no contradiction. These estimates then neither certify
grid vanishing nor demonstrate its failure. The strict bound
$\kappa<1/16$ would suffice for this hypothetical budget.

**Reconstruction task.** A received table is close to
a low-degree polynomial $M$, but all its erroneous
entries might lie among points $(x,0)$. Explain why
reading those entries directly cannot establish the
identity $M(x,0)=0$. Then reconstruct the repair,
including the role of line data, the possibility of
rejection, and the final use of a polynomial identity.
The answer requires the connections between Sections
5, 6, 8 and 9 rather than one numerical calculation.
An account of the general proof is successful only
if it explains why the same decoded polynomial is
used at each of these steps.
<!-- /passage:pcp-expository-answers -->

<!-- passage:pcp-expository-correction -->
## 12. Why the low-degree test needed correction

The first version of the source paper used an element of order $c+1$
and unit weights. For $c=2$, let $\zeta$ have order three in a field
$F$ of characteristic two. The old condition was

$$
f(u)=f(u+\zeta v)+f(u+\zeta^2v)+f(u+v).
$$

It holds for quadratic polynomials, but its converse
fails. Take $f(X)=X^4$. In characteristic two,
$(u+av)^4=u^4+a^4v^4$. Since $\zeta^4=\zeta$
and $1+\zeta+\zeta^2=0$, the right-hand side is

$$
3u^4+(\zeta+\zeta^2+1)v^4=u^4.
$$

The test accepts every pair $(u,v)$, although
$X^4$ cannot agree everywhere with a quadratic
when $|F|>4$: their difference is a nonzero
degree-four polynomial with at most four roots.
In fact, their disagreement fraction is at least
$1-4/|F|$.

The failure persists in arbitrarily large fields.
Fields $F=\mathbb F_{2^{2k}}$, for $k\geq2$, contain elements of order
three and have unbounded size. The example therefore survives any fixed
field-size threshold for this old degree-two test. It identifies a
defect in the old test's characterisation, not in the PCP theorem or
the corrected formal proof.

For a concrete comparison, take
$\mathbb F_{16}=\mathbb F_2[t]/(t^4+t+1)$.
This notation means that elements are binary polynomials
of degree below four. Add their coefficients modulo two;
multiply them and reduce using $t^4=t+1$ until the degree
is below four again. The irreducible modulus makes these
16 elements a field.
The old order-three nodes accept $X^4$ on all
$256$ pairs $(u,v)$. The corrected test uses
the generator $t$ and interpolation weights
at $t,t^2,t^3$; it accepts only $16$ pairs.
The accompanying checker enumerates these
cases and verifies the interpolation identity.

Completeness requires honest low-degree polynomials
to pass; the interpolation identity proves that
they do. Soundness must also rule out other
functions that pass too often. The generator
and its weights support that converse.
The corrected paper acknowledges Troy Lee
for finding an error in the earlier lemma;
no priority claim for the example above is
made here.
<!-- /passage:pcp-expository-correction -->

<!-- passage:pcp-expository-evidence -->
## Sources and verification

The mathematical construction is from
[Amireddy, Behera, Srinivasan, Sudan and
Willumsgaard, version 2][paper-v2]. The
formal development discussed here is
[Troy Lee's PCP proof at revision
`a0ce13ed`][lean-project]. It includes the
concrete complexity argument as well as
the algebraic verifier. The full account
records exact statements, proof correspondences
and verification evidence; a Lean source
link by itself does not certify that every
sentence of this exposition says the same
thing as the formal statement.

AI agents wrote this exposition under Will
Cook's direction. The finite calculations
were checked by the accompanying Python
program. They illustrate individual
operations, and their small parameters do
not instantiate the large-field parameter
regime of the complete PCP construction.
The family argument about the earlier test
is an ordinary mathematical deduction,
not a Lean-checked theorem in this project.
No claim of independent human review or
measured reader understanding is made.

Further reading:

* [The full argument][long] develops the
  low-degree tests, the binary correction
  bounds and the final assembly in detail.
* [The specialist paper][short] gives the
  construction and formalisation differences
  in a shorter account.
* [Troy Lee's original reading guide][troy-guide]
  explains how to read the main Lean statement
  and its definitions.
* Arora and Barak, [*Computational Complexity:
  A Modern Approach*][arora-barak], provides
  textbook background. The publicly retained
  January 2007 draft numbers its PCP definition
  differently from the published edition.
* The original [BLR paper][blr] develops
  self-testing and self-correction. The
  [corrected PCP paper][paper-v2] gives
  the precise versions used in this
  construction.
<!-- /passage:pcp-expository-evidence -->

[paper-v2]: https://arxiv.org/abs/2608.17429v2
[arora-safra]: https://www.cs.umd.edu/~gasarch/TOPICS/pcp/AS.pdf
[almss]: https://people.seas.harvard.edu/~madhusudan/papers/1992/almss-journ.pdf
[arora-barak]: https://theory.cs.princeton.edu/complexity/book.pdf
[blr]: https://doi.org/10.1016/0022-0000(93)90044-W
[lean-project]: https://github.com/troyjlee/tcs-formalizations/tree/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP
[lean-theorem]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Theorem.lean
[verifier-definitions]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Verifier/Definition.lean
[troy-guide]: https://wcook04.github.io/proof-reader/#/pcp-reading-guide
[long]: ../long/reasoning-record.md
[short]: ../short/paper.md

[bchks]: https://www.csc.kth.se/tcs/projects/publications/bchks.pdf

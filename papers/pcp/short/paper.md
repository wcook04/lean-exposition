# Constant-query verification by algebraic encoding

*Explanatory reconstruction prepared by Will Cook with AI assistance · 16 November 2026.*

Algebraic construction: Amireddy, Behera, Srinivasan, Sudan and Willumsgaard. Lean formalization: Troy Lee.

## Abstract

<!-- passage:pcp-short-abstract -->
The PCP theorem gives every language in NP a polynomial-time verifier with logarithmic randomness, constantly many proof-bit queries, perfect completeness and soundness error at most one half. We explain Troy Lee's Lean formalization of the algebraic proof of Amireddy, Behera, Srinivasan, Sudan and Willumsgaard. In the soundness proof the verifier's checks force four fixed nearby polynomials to encode a proper colouring. Its central step is local correction at prescribed points, where closeness on average gives no guarantee; we bound the error by the corrector's own rejection probability.
<!-- /passage:pcp-short-abstract -->

## 1. Introduction

<!-- passage:pcp-short-theorem -->
**Theorem 1.1 (PCP theorem; [AS98, ALMSS98]).** For every language $\mathcal L\subseteq\{0,1\}^{*}$ in NP, there are a polynomial-time verifier $V$, natural numbers $\alpha,\beta,\ell$, and a polynomial $p\in\mathbb N[X]$ with the following properties. On an input $x$ of length $n$, the verifier uses exactly

$$
\alpha\lceil\log_2(n+2)\rceil+\beta
$$

fair random bits (the exact randomness formula), makes at most $\ell$ proof-bit queries on every run, and reads only addresses below $p(n)$. If $x\in\mathcal L$, there is one proof accepted for every random seed. If $x\notin\mathcal L$, every proof is accepted with probability at most $1/2$.

The verifier, its implementation, the constants and $p$ are fixed for $\mathcal L$ before $x$ is chosen. The proof may depend on $x$ and is fixed before the seed. Conversely, every language with such a verifier lies in NP (Section 7). Hence

$$
\mathrm{NP}=\mathrm{PCP}(O(\log n),O(1)).
$$

*Remark (formalization).* Lee proves Theorem 1.1 in this form, for a verifier implemented in a concrete machine model; surplus random bits may be ignored. [ABSSW26, Theorem 2.2] states $O(\log n)$ randomness.

The theorem is due to Arora, Lund, Motwani, Sudan and Szegedy [ALMSS98], building on Arora and Safra [AS98]. In a field of size $2^t$, a field value takes $t$ bits, and the coefficient vector of a line polynomial of degree at most $d$ takes $(d+1)t$ bits. Counting either as one symbol, as the point-versus-line test of [ALMSS98] does, does not establish constant bit-query complexity, and binary encoding of whole coefficient vectors can need quasipolynomial proof length. The construction maps a line polynomial of degree below $b^c$ to one of total degree at most $c$ in $cb$ variables, $c$ fixed, and Hadamard-encodes single field values for one-bit queries, without PCP composition [ABSSW26, §1].

If the low-degree tests reject rarely, four nearby polynomials have encodings close to the received tables; the analysis chooses them and the verifier never computes them. The other checks force them to encode a proper colouring, the difficulty being local correction at prescribed points. The construction and analysis are those of [ABSSW26]; Lee [Lee26] formalized them, added explicit constants and a weaker field-size hypothesis for the low-degree test over $F$, and identified the error in version 1 of [ABSSW26]. We contribute an explanation of the correction bound and the soundness argument with those constants.

Sections 2 to 7 give notation, the encodings and the proof, testing, correction, soundness, resources and the converse. The [full argument](../long/reasoning-record.md) proves the testing results; the [worked exposition](../expository/main.md) gives examples.
<!-- /passage:pcp-short-theorem -->

## 2. Preliminaries

<!-- passage:pcp-short-colour-constraints -->
Throughout, $F$ is a field of characteristic two with $q=2^t$ elements and a primitive cube root of unity $\omega$. We write $\Delta$ for relative Hamming distance; $f$ is $\delta$-close to $g$ if $\Delta(f,g)\le\delta$. Probabilities are uniform on the indicated finite sets, rejection probabilities over a test's seed. For $u,v\in F^k$ the line through $u$ with slope $v$ is $z\mapsto u+zv$, with $v=0$ allowed, index $(u,v)$ and base point $u$. By the Schwartz–Zippel lemma [ABSSW26, Theorem 2.5], a nonzero polynomial of total degree at most $d$ vanishes on at most a fraction $d/q$ of $F^k$.

The verifier tests three-colourability of a graph on $N$ vertices. Represent the colours by

$$
\mathcal C=\{1,\omega,\omega^2\}.
$$

For $u,v\in\mathcal C$, their difference satisfies $(u-v)^4=u-v$. Hence $u\ne v$ exactly when $(u-v)^3=1$.

Choose a nonempty grid $H^m\subseteq F^m$ with $|H|^m\ge N$, pad the graph with isolated vertices, and write $h=|H|$. Interpolation gives low-degree extensions [ABSSW26, Fact 2.4]: $P$ of the colouring, of degree at most $d_0=m(h-1)$, and $E$ of the adjacency function on $H^{2m}$, of degree at most $2d_0$, which the verifier computes.

Set

$$
\begin{aligned}
Q_P(X,Y)&=P(X)-P(Y),\\
A_P(X)&=P(X)^3-1,\\
B_P(X,Y)&=E(X,Y)\bigl(Q_P(X,Y)^3-1\bigr).
\end{aligned}
\tag{1}
$$

These are the polynomials $\chi',\mathsf{Val},\mathsf{Prop}$ of [ABSSW26, §7], where $P$ and $E$ are written $\chi$ and $\widehat E$, and the vanishing certificates $M_A,M_B$ below are their $\mathcal M_{\mathsf{Val}},\mathcal M_{\mathsf{Prop}}$.

**Lemma 2.1 (colouring constraints).** The restriction $P|_{H^m}$ is a proper colouring of the padded graph exactly when $A_P|_{H^m}=0$ and $B_P|_{H^{2m}}=0$, and $Q_P,A_P,B_P$ have degrees at most $d_0,3d_0,5d_0$.

The first condition restricts vertex values to $\mathcal C$, the second separates values across edges. Both are needed: colouring $K_4$ by $\mathbb F_4$ satisfies every edge equation, as nonzero elements have cube one, but the vertex coloured zero fails.

**Lemma 2.2 (Combinatorial Nullstellensatz; [ABSSW26, Lemma 2.9 and Corollary 2.10]).** Put $Z_H(T)=\prod_{u\in H}(T-u)$, applied coordinatewise. A polynomial $A$ vanishes on $H^k$ precisely when, for some polynomials $U_i$ each zero or of degree at most $\deg A-h$,

$$
A(X)=\sum_{i=1}^{k} Z_H(X_i)U_i(X).
$$

Equivalently, some polynomial $M(X,Y)$ of degree at most $\deg A$, a vanishing certificate, satisfies

$$
M(X,0)=0,\qquad M(X,Z_H(X))=A(X).
\tag{2}
$$

*Proof.* Monic division by $Z_H$ in each coordinate leaves a remainder of degree below $h$ in every variable; if $A$ vanishes on the grid, so does the remainder, and interpolation makes it zero. Packing the quotients into

$$
M(X,Y)=\sum_iY_iU_i(X)
$$

gives (2), and each $Y_iU_i$, hence $M$, has degree at most $\deg A$ because $h\ge1$. Conversely, (2) implies grid vanishing even when $M$ is nonlinear in $Y$, since $Z_H(X)=0$ on the grid. $\square$
<!-- /passage:pcp-short-colour-constraints -->

## 3. Set-multilinear and Hadamard encodings

<!-- passage:pcp-short-digit-encoding -->
**Definition 3.1 (set-multilinear encoding; [ABSSW26, Definition 3.1 and Claim 3.2]).** For positive integers $b,c$ and $T(Y)=\sum_{j<b^c}t_jY^j$, write $j=\sum_{i=0}^{c-1}j_ib^i$ in base-$b$ digits $0\le j_i<b$, introduce $cb$ variables $X_{i,s}$, and set

$$
\Psi(T)=\sum_{j<b^c}t_j\prod_{i=0}^{c-1}X_{i,j_i},
\qquad
\Phi(z)_{i,s}=z^{s b^i}.
\tag{3}
$$

Each monomial of $\Psi(T)$ uses one variable from each of $c$ groups, so $\Psi(T)$ has total degree at most $c$, and substitution recovers $T$:

$$
\Psi(T)(\Phi(z))
=\sum_{j<b^c}t_jz^{\sum_i j_i b^i}=T(z).
\tag{4}
$$

An honest proof stores $\Psi(T)$ for line restrictions $T$. The soundness proof chooses $U$ of total degree at most $c$ with binary encoding close to a received table; $U$ need not have the form (3), but

$$
T_U(Y)=U(\Phi(Y)),\qquad \deg T_U\le D:=cb^c.
\tag{5}
$$

Indeed, a monomial of $U$ has at most $c$ variable occurrences, each of degree at most $b^c$ after substitution. Honest line polynomials have degree below $b^c$, those from (5) only at most $D$, so Section 4's field-size hypotheses use $D$.
<!-- /passage:pcp-short-digit-encoding -->

<!-- passage:pcp-short-hadamard-encoding -->
Fix a linear isomorphism $\rho:F\to\mathbb F_2^t$.

**Definition 3.2 (labels and Hadamard encoding; [ABSSW26, Definitions 3.5–3.6]).** A label is a multilinear polynomial over $\mathbb F_2$ in $Z_1,\dots,Z_t$ of degree at most $r$; labels form a vector space $\mathcal B_r$. Affine labels $\lambda_0+\lambda\cdot Z$ have degree at most one, constants included; homogeneous labels $\lambda\cdot Z$ have no constant term. For $r\ge1$, the degree-$r$ Hadamard encoding of $u\in F$ stores $R(\rho(u))$ at label $R$:

$$
\mathcal H_r(u)(R)=R(\rho(u)),\qquad R\in\mathcal B_r.
\tag{6}
$$

Any $w:\mathcal B_r\to\mathbb F_2$ is a word, and $\mathcal H_r(f)$ encodes each value of a function $f$; the label degree $r$ is independent of the degree of $f$.

**Lemma 3.3 (half-distance identity; [ABSSW26, Observation 3.8]).** For field-valued functions $f,g$ on one finite point domain,

$$
\Delta(\mathcal H_r(f),\mathcal H_r(g))=\tfrac12\Delta(f,g),
\tag{7}
$$

where the encoded distance averages over points and all labels, or homogeneous labels, as subscripts $\mathrm{full}$ and $\mathrm{hom}$ indicate.

*Proof.* Adding a coordinate label $Z_i$ on which two distinct values differ pairs agreeing labels with disagreeing ones, and preserves homogeneous labels. $\square$

Identify affine labels with maps $L:F\to\mathbb F_2$ through $\rho$. Multiplication in $F$ is bilinear in binary coordinates. For $A\in F[Y]$ of degree at most $r$ and an affine label $L$, reduction modulo $Z_i^2-Z_i$ gives a label $\Lambda_{A,L}\in\mathcal B_r$ satisfying

$$
L(A(u))=\mathcal H_r(u)(\Lambda_{A,L}).
\tag{8}
$$

Cubic labels suffice for (1). Homogeneous labels preserve sums, so the verifier uses them for weighted sums: $\eta u$ is observed through the label $L\circ(\eta\cdot)$, and for $\eta\ne0$ this permutes the homogeneous labels.

**Lemma 3.4 (self-correction; [BLR93]).** Let $w$ be a word and $\Lambda\in\mathcal B_r$ a requested label. The self-corrected read is

$$
\operatorname{SC}_w(\Lambda;R)=w(\Lambda+R)-w(R),
\tag{9}
$$

where $R$ is a fresh random label, uniform in $\mathcal B_r$. If $w$ is $\epsilon$-close to a linear functional $\varphi$ on labels, (9) differs from $\varphi(\Lambda)$ with probability at most $2\epsilon$ for every fixed $\Lambda$, since both read positions are uniform and $\varphi(\Lambda+R)-\varphi(R)=\varphi(\Lambda)$.

Encodings are linear on labels, so Lemma 3.4 applies to the possibly nonuniform labels of (8).

We call the distance of a word or table from an encoding its full-label or homogeneous error. For $r=1$ the homogeneous error is at most twice the full-label error. For $r>1$, a full-label distance bound alone gives no bound on the homogeneous error by a constant multiple independent of $t$. Lemmas 4.2 and 4.3 below supply both bounds for the same field value or polynomial.
<!-- /passage:pcp-short-hadamard-encoding -->

<!-- passage:pcp-short-proof-inventory -->
**The proof.** The proof is the bit string the verifier queries; it consists of eight tables, which [ABSSW26, §7] call proof oracles. Four are points tables, honestly the degree-$r$ Hadamard encodings of polynomials:

| Points table | Honest polynomial | Point domain | Label degree $r$ |
| :--------------- | :------------------------- | :--------------- | :----------------- |
| $f_P$ | $P$ | $F^m$ | $3$ |
| $f_Q$ | $Q_P$ | $F^{2m}$ | $3$ |
| $f_A$ | certificate $M_A$ of $A_P$ | $F^{2m}$ | $1$ |
| $f_B$ | certificate $M_B$ of $B_P$ | $F^{4m}$ | $1$ |

An address is a point $x$ and a label $R\in\mathcal B_r$; an honest table stores $R(\rho(u))$ for the encoded value $u$. The lines table of $P$ on $F^k$ assigns to each index $(u,v)$ the restriction $z\mapsto P(u+zv)$; stored after both encodings, it gives each points table $f$ on $F^k$ a lines table $f'$ with entries

$$
f'_{u,v}:F^{cb}\times\mathcal B_1\longrightarrow\mathbb F_2.
$$

The argument $\xi\in F^{cb}$ of $\Psi(T)$ is the inner point, $\Phi(z)$ that for parameter $z$; honestly $f'_{u,v}(\xi,L)$ is the affine observation $L$ of $\Psi(T)(\xi)$. Received tables are arbitrary. The verifier accepts if seven checks with independent seeds pass: a low-degree test on each pair $(f,f')$ (Theorem 4.6), a zero-on-grid test for each certificate (Section 5), correcting through the same lines tables, and a consistency check (17).
<!-- /passage:pcp-short-proof-inventory -->

## 4. Low-degree tests over the binary alphabet

<!-- passage:pcp-short-weighted-test -->
The standard low-degree test on the inner domain $F^{cb}$, with constant degree bound $c$, accepts when (10) holds at uniform $u,v$.

**Lemma 4.1 (standard low-degree test; [ABSSW26, Fact 2.7 and Lemma 3.3]).** Assume $q>2c$, let $\zeta$ generate $F^\times$, and let

$$
a_i=\zeta^i,\qquad
\eta_i=\prod_{j\ne i}\frac{-a_j}{a_i-a_j}
\quad(1\le i\le c+1).
$$

The nodes and weights are nonzero, and by Lagrange interpolation every polynomial $f$ on $F^{cb}$ of total degree at most $c$ satisfies

$$
f(u)=\sum_{i=1}^{c+1}\eta_i f(u+a_iv).
\tag{10}
$$

Conversely, a function satisfying (10) for all $u,v$ is such a polynomial. If (10) fails on a fraction $\delta<1/[2(c+2)^2]$ of pairs $(u,v)$, then $f$ is $2\delta$-close to such a polynomial, and the plurality correction $g$ [KS08, Lemma 3.1], with $g(x)$ a most frequent value of $\sum_i\eta_i f(x+a_iv)$ over $v\in F^{cb}$, satisfies

$$
\Pr_v\left[\sum_i\eta_i f(x+a_iv)\ne g(x)\right]
\le2(c+1)\delta\quad\text{for every }x.
$$

The [proof of Lemma 4.1](../long/reasoning-record.md#42-the-standard-low-degree-test) derives the pointwise estimate and shows that $g$ satisfies (10) exactly. As $\zeta$ generates $F^\times$, exact satisfaction gives line restrictions of degree at most $c$, and [FS95/13, Lemma 4] applies since in characteristic two $q>2c$ gives $q/2-1\ge c$. Earlier robust characterisations are [RS96, §4] and, for linear-invariant families, [KS08, Theorem 2.9]. Unit weights fail (Appendix A).

*Remark (formalization).* [ABSSW26, Lemma 3.3] assumes $q$ larger than a constant multiple of $c^3$; Lee assumes only $q>2c$ and makes the constants explicit.
<!-- /passage:pcp-short-weighted-test -->

<!-- passage:pcp-short-binary-decoding -->
**Lemma 4.2 (Hadamard test; [ABSSW26, Lemma 3.10]).** The Hadamard test on a word $w:\mathcal B_r\to\mathbb F_2$ combines the BLR linearity test [BLR93], a unit check at the constant label, product checks and affine consistency checks. For every $w$ there is one field value $u$, chosen in the analysis, such that $\mathcal H_r(u)$ has full-label and homogeneous error at most $28$ times the test's rejection probability.

*Proof sketch.* For rejection probability $\epsilon<1/28$, the characteristic-two linearity estimate [BCHKS96, Theorem 1.2; ABSSW26, Theorem B.1] and the unit and product checks give $u$ with full-label error at most $\epsilon$. Affine consistency costs $\epsilon$ for the check and $2\epsilon$ for self-correction, so the affine error is at most $3\epsilon$ and the homogeneous error, on half that domain, at most $6\epsilon$. If $\epsilon\ge1/28$, any $u$ works since $1\le28\epsilon$. See the [complete proof](../long/reasoning-record.md#53-the-hadamard-test). $\square$

*Remark (formalization).* Lee's test keeps product checks at every degree from two to $r$, sharing reads, and makes at most $2r+4$ queries, ten for cubic labels; [ABSSW26, Lemma 3.10] checks only the top degree, with eight. The factor 28 is Lee's.

**Lemma 4.3 (inner low-degree test; cf. [ABSSW26, Lemma 4.3]).** On a table $w:F^{cb}\times\mathcal B_r\to\mathbb F_2$, the inner low-degree test flips a fair coin between the Hadamard test on $w(\xi,\cdot)$ at a uniform inner point $\xi$ and a one-bit observation of the standard low-degree test, (10) read through a uniform homogeneous label at uniform $u,v$. If $q>2c$ and the test rejects with probability $\kappa$, some polynomial $U$ of total degree at most $c$ satisfies

$$
\Delta_{\rm full}(w,\mathcal H_r(U)),\quad
\Delta_{\rm hom}(w,\mathcal H_r(U))\le K\kappa,
\qquad K=4(c+2)^2\bigl(112(c+2)+60\bigr).
\tag{11}
$$

*Proof sketch.* Each branch rejects with probability at most $2\kappa$, and Lemmas 4.2, 4.1 and 3.3 give (11). No small-rejection hypothesis is needed: outside the small-error regime of Lemma 4.1 the trivial bound suffices. See the [complete proof](../long/reasoning-record.md#54-the-inner-low-degree-test). $\square$
<!-- /passage:pcp-short-binary-decoding -->

<!-- passage:pcp-short-outer-decoding -->
**Lemma 4.4 (standard local correction; cf. [ABSSW26, Lemma 3.4]).** At a prescribed inner point $\xi$, the standard local corrector for $w:F^{cb}\times\mathcal B_1\to\mathbb F_2$ samples a uniform direction $v$, possibly zero, and homogeneous label $L$, and returns $\sum_i w(\xi+a_iv,L\circ(\eta_i\cdot))$, with no separate query at $\xi$. If $w$ has homogeneous distance $\tau$ from the encoding of $U$ of total degree at most $c$, the answer differs from $L(U(\xi))$ with probability at most $(c+1)\tau$.

*Proof.* As $a_i,\eta_i\ne0$, each queried point and each label $L\circ(\eta_i\cdot)$ is uniform, although $\xi$ is prescribed. Correct reads sum to $L(U(\xi))$ by (10); take a union bound. $\square$

**Theorem 4.5 (point-versus-line test; [ALMSS98, Theorem 45]).** Suppose

$$
q\ge10^6D^3,\qquad \theta\le\frac1{4\cdot10^6},
$$

and arbitrary degree-at-most-$D$ line polynomials, one for each line index, disagree with a point function on a fraction $\theta$ of uniform triples $(u,v,z)$. Then the point function is within $2\theta$ of one polynomial of total degree at most $D$.

Here $z\in F$, slopes may be zero, and different indices of one line may carry inconsistent polynomials. The test is also called the line-point test [ABSSW26, §1]. The [bivariate argument](../long/reasoning-record.md#45-bivariate-agreement) follows [AS98, §5.2] and [ALMSS98, Appendix A]; the [point-versus-line proof](../long/reasoning-record.md#46-the-point-versus-line-test) gives the constants.

*Remark (formalization).* The constants are Lee's. [ABSSW26, Theorem 2.12] samples nonzero parameters and concludes $4\theta$-closeness.

The binary low-degree test on $f$ and its lines table $f'$ samples uniform $u,v\in F^k$, $z\in F$ (including $z=0$), a homogeneous label $L$, a corrector direction and independent inner-test seeds, and accepts if:

1. the Hadamard test accepts the word $f(u,\cdot)$;
2. the inner low-degree test accepts $f'_{u,v}$;
3. $f(u+zv,L)$ equals the standard local correction of the same entry $f'_{u,v}$ at $\Phi(z)$ with label $L$.

**Theorem 4.6 (binary low-degree test; [ABSSW26, Theorem 4.1]).** Let $D=cb^c$ and $q\ge10^6D^3$, and with $K$ as in (11) put $J=2((c+1)K+29)$ and $S=28+J$. If this test rejects $(f,f')$ with probability $\kappa$ and $J\kappa\le1/(4\cdot10^6)$, then some polynomial $P$ of total degree at most $D$ has $\Delta_{\rm full}(f,\mathcal H_r(P))\le S\kappa$ and $\Delta_{\rm hom}(f,\mathcal H_r(P))\le S\kappa$.

*Proof.* Lemma 4.2 on each word $f(x,\cdot)$ gives a function $g$ whose encoding has full-label and homogeneous error at most $28\kappa$. Lemma 4.3 and (5) give each entry $f'_{u,v}$ a line polynomial $T_{u,v}$ of degree at most $D$. Replacing the corrected answer in check 3 by $L(T_{u,v}(z))$ costs at most $(c+1)K\kappa$ by Lemma 4.4, the comparison fails with probability at most $\kappa$, and replacing $f(u+zv,L)$ by $L(g(u+zv))$ costs at most $28\kappa$. Hence

$$
\Pr_{u,v,z}[T_{u,v}(z)\ne g(u+zv)]
\le J\kappa,
\qquad J=2\bigl((c+1)K+29\bigr).
\tag{12}
$$

The factor two is exactly (7). No consistency among different entries has been assumed. Theorem 4.5 with $\theta=J\kappa$ gives $P$ with $\Delta(g,P)\le2J\kappa$, and encoding by (7) yields

$$
\Delta_{\rm full}(f,\mathcal H_r(P)),\quad
\Delta_{\rm hom}(f,\mathcal H_r(P))
\le S\kappa,
\qquad S=28+J,
\tag{13}
$$

which proves the theorem. $\square$

*Remark (formalization).* The restricted bound concerns homogeneous linear labels. For its own tester, [ABSSW26, Theorem 4.1] bounds the distance on all affine labels; restricting such a bound to homogeneous labels can double it, and it is not needed here. For a certificate, whose full domain is $\mathcal B_1$, the full-label bound also controls affine labels. Lee's lines tables all use affine labels; [ABSSW26, §7] uses cubic labels on those of $P$ and $Q_P$.
<!-- /passage:pcp-short-outer-decoding -->

## 5. Local correction and the zero-on-grid test

<!-- passage:pcp-short-outer-correction -->
The points $(x,0)$ and $(x,Z_H(x))$ of (2) lie in prescribed subsets, where a table close on average can be wrong everywhere. The binary low-degree test need not control entries with a prescribed base point, so the local corrector retests its entry.

At a target $a$, the local corrector for $(f,f')$ samples independent uniform homogeneous label $L$, slope $v$, $z\in F^\times$, corrector direction and inner-test seed. It tests $f'_{a,v}$, corrects it at $\Phi(z)$ and compares with $f(a+zv,L)$, rejecting if either fails, and otherwise returns the correction at $\Phi(0)$ with the same direction and label. It reads at most $3c+9$ bits; exact encodings of $P$ of degree below $b^c$ give $L(P(a))$ for every seed.

**Theorem 5.1 (local correction at a prescribed point; cf. [ABSSW26, Theorem 5.1]).** Let $q>2c$, let $P$ have total degree at most $D\ge cb^c$ with $\Delta_{\rm hom}(f,\mathcal H_1(P))\le\delta$, and let $f'$ be arbitrary. If the local corrector rejects at $a$ with probability $\kappa_a$, the probability over all its randomness, $L$ included, of rejection or a returned bit other than $L(P(a))$ satisfies

$$
\Pr[\text{failure at }a]
\le C \kappa_a+\delta+\frac{D}{2(q-1)},
\qquad C=2+2(c+1)K.
\tag{14}
$$

*Proof* (see the [full proof](../long/reasoning-record.md#56-local-correction-with-a-lines-table)). Lemma 4.3 and (5) give each $f'_{a,v}$ a line polynomial $T_{a,v}$ of degree at most $D$. Inner-test failure implies rejection, so the mean homogeneous error of the nearby polynomials is at most $K\kappa_a$; with $e=(c+1)K\kappa_a$, Lemma 4.4 replaces each correction by $L(T_{a,v}(\cdot))$ at cost at most $e$.

If $T_{a,v}(0)\ne P(a)$, the difference $T_{a,v}(Y)-P(a+Yv)$ is a nonzero polynomial of degree at most $D$. Among the $q-1$ nonzero parameters it has at most $D$ roots. Applying Lemma 3.3 gives

$$
\Pr_{v,L}[L(T_{a,v}(0))\ne L(P(a))]
\le \Pr_{v,z,L}[L(T_{a,v}(z))\ne L(P(a+zv))]
+\frac{D}{2(q-1)}.
$$

At the sampled point, replacing the correction, using the tested comparison and replacing the bit of $f$ cost at most $e$, $\kappa_a$ and $\delta$, the last as $a+zv$ is uniform for each nonzero $z$. At the origin, replacing $L(T_{a,v}(0))$ by the actual correction costs another $e$, and including rejection another $\kappa_a$. The total $2e+2\kappa_a+\delta+D/[2(q-1)]$ is (14). $\square$

Bound (14) holds at every target $a$, so it applies at the certificate points in (2).
<!-- /passage:pcp-short-outer-correction -->

<!-- passage:pcp-short-zero -->
**Lemma 5.2 (zero-on-grid test; cf. [ABSSW26, Theorem 6.1]).** The zero-on-grid test checks (2) on tables of $A$ and a certificate. It samples uniform $x,L$, reads the bit $a_{\rm bit}$ of $A$'s table at $(x,L)$ and, with the same $x,L$ and independent seeds, gets $b_0,b_Z$ or rejection from the certificate's local corrector at $(x,0)$ and $(x,Z_H(x))$; it accepts exactly when neither rejects, $b_0=0$ and $b_Z=a_{\rm bit}$. Under the hypotheses of Theorem 5.1, let $A$ and a proposed certificate $M$ have degree at most $D$, with tables at homogeneous distances $\delta_A,\delta_M$ from their encodings. If $A$ does not vanish on $H^k$ and the test rejects with probability $\kappa$, then (15) holds.

*Proof.* By Lemma 2.2, $M(X,0)$ or $M(X,Z_H(X))-A(X)$ is a nonzero polynomial, of degree at most $Dh$, so by the Schwartz–Zippel lemma a uniform $x$ violates the corresponding identity with probability at least $1-Dh/q$. A uniform homogeneous label detects a nonzero residual with probability $1/2$, so the ideal test, reading exact encodings of $A$ and $M$, rejects with probability at least

$$
\frac{1-Dh/q}{2}.
$$

This needs one nonzero residual and no independence between detections. Each correction's rejection event lies in the test's, which bounds its rejection averaged over requested targets; it need not bound rejection at each fixed target. Coupling the ideal and actual tests and using (14) twice gives

$$
\frac{1-Dh/q}{2}
\le(1+2C)\kappa+\delta_A+2\delta_M+\frac{D}{q-1}.
\tag{15}
$$

$\square$

The proof stores no tables for $A_P,B_P$: $a_{\rm bit}$ is a self-corrected read (9) of $f_P$ or $f_Q$ at the label given by (8). If $\epsilon_x$ is that word's full-label error at $x$, replacing this read costs at most $2\epsilon_x$ for every requested label (Lemma 3.4), so for uniform $x$ at most $2\mathbb E_x\epsilon_x\le2\epsilon$, the full-table bound from (13). Coupling to exact answers for $a_{\rm bit}$, keeping the certificate calls and all other randomness, gives $\delta_A=0$ and rejection probability at most $\kappa+2\epsilon$. Applying (15) gives

$$
\frac{1-Dh/q}{2}
\le(1+2C)(\kappa+2\epsilon)+2\delta_M+\frac{D}{q-1}.
\tag{16}
$$

The coefficient $1+2C$ multiplies the self-correction error because it enters through rejection, and the averaging includes the fresh label $R$ of (9); see the [full analysis](../long/reasoning-record.md#57-the-zero-on-grid-test).
<!-- /passage:pcp-short-zero -->

## 6. Soundness of the verifier

<!-- passage:pcp-short-assembly -->
The difference check samples independent uniform points $x,y$ and a uniform homogeneous label $L$, and tests

$$
f_Q((x,y),L)=f_P(x,L)+f_P(y,L).
\tag{17}
$$

The constants $J,S,C$ depend only on the fixed $c$. Set

$$
\begin{aligned}
T_c&=(1+2C)(1+2S)+2S,\\
g_c&=\min\left\{
\frac1{4\cdot10^6(J+1)},\,
\frac1{16(1+3S)},\,
\frac1{16(T_c+1)}
\right\}.
\end{aligned}
\tag{20}
$$

**Theorem 6.1 (soundness).** Let $D=cb^c$, $q\ge10^6D^3$, $q\ge100Dh$ and $m(h-1)\le D$. Every proof for a graph that is not three-colourable is rejected with probability at least $g_c$.

*Proof.* Let a fixed proof be rejected with probability $\kappa<g_c$. Acceptance is conjunctive, so each check rejects with probability at most $\kappa$. As $J\kappa\le1/(4\cdot10^6)$ by (20), Theorem 4.6 gives nearby polynomials $P,Q,M_A,M_B$ of degree at most $D$, with encodings within full-label and homogeneous distance $\epsilon=S\kappa$ of the four points tables. Fix these choices. Replacing the three bits in (17) by bits of these encodings costs at most $3\epsilon$. If $Q\ne P(X)-P(Y)$, their difference has relative support at least $1-D/q$ by the Schwartz–Zippel lemma, and (7) makes the ideal check reject on at least half that fraction. Hence

$$
\kappa+3\epsilon<\frac{1-D/q}{2}
\tag{18}
$$

forces the polynomial identity $Q=P(X)-P(Y)$.

The constraints $A_P,B_P$ of the nearby polynomials have degree at most $3D$ and $5D$, since $E$ has degree at most $2D$. If either failed to vanish on its grid, (16) with the common bound $5D$ would give

$$
\frac{1-5Dh/q}{2}
\le(1+2C)(\kappa+2\epsilon)+2\epsilon+\frac{5D}{q-1}.
\tag{19}
$$

By (20), (18) holds. The field bound gives $5Dh/q\le1/4$ and $5D/(q-1)\le1/8$, and the $\kappa$-dependent term in (19) is below $1/16$, so its right side is below $3/16$ while its left side is at least $3/8$. Thus both constraints vanish, and Lemma 2.1 gives a proper colouring. $\square$

The same four nearby polynomials serve every check; separate choices for each later check would not suffice. For completeness, a proper colouring, its low-degree extension, exact vanishing certificates and honest lines tables, with degrees below $b^c$, pass every check for every seed: one fixed eight-table proof with perfect completeness.
<!-- /passage:pcp-short-assembly -->

## 7. Resources, implementation and the reverse inclusion

<!-- passage:pcp-short-resources -->
Take $c=4$. For a graph on $N$ vertices, let $\nu\ge2$ be least with $\lceil\log_2N\rceil\le \nu2^\nu$, with natural-number ceiling log equal to zero at $N=0,1$. Set

$$
s=2^\nu,\qquad m=b=h=s,\qquad
t=12\nu+32,\qquad q=2^t=2^{32}s^{12}.
\tag{21}
$$

The grid contains $s^s=2^{\nu2^\nu}\ge N$ points. Also $D=4s^4$ and

$$
10^6D^3=64\cdot10^6s^{12}\le q,
\qquad100Dh\le q.
$$

Since $s\ge4$, the honest degrees satisfy $5s(s-1)<s^4=b^c$. The extension degree $t$ is divisible by four, so the field has the required cube roots. Minimality of $\nu$ gives

$$
\nu2^\nu\le32(\lceil\log_2N\rceil+1).
\tag{22}
$$

Field vectors in the query and seed spaces use $O(st)=O(\nu2^\nu)$ bits, and boundedly many label vectors of degree at most three use $O(t^3)=O(\nu2^\nu)$ bits, as $t=O(\nu)$ and $\nu^2/2^\nu$ is bounded. By (22), for $N\ge2$ the seed length is $O(\log N)$ and each address space has size $2^{O(\nu2^\nu)}=N^{O(1)}$; $N=0,1$ use fixed parameters.

*Remark (formalization).* The four local-corrector calls draw parameters from $F^\times$. For fixed-length fair-bit sampling, Lee's verifier draws them from $F$ and accepts without querying if any is zero; conditionally on all being nonzero the seeds are as analysed, so rejection is multiplied by $((q-1)/q)^4\ge1/16$. Other random coordinates are encoded bijectively by fixed-length bit strings.

An unamplified run makes at most $2c+18$ queries in each colour or difference low-degree test, $2c+14$ in each certificate low-degree test, $6c+20$ in each zero-on-grid test with its self-corrected reads, and $3$ in the difference check, so $20c+107=187$ in all. After fair-bit sampling the rejection gap is at least $g_c/16$, and constantly many independent repetitions on the same proof reduce soundness error to $1/2$, keeping logarithmic randomness and constant queries. The [parameter calculations](../long/reasoning-record.md#36-parameters) and [repetition proof](../long/reasoning-record.md#38-amplification-and-explicit-constants) give the numbers.
<!-- /passage:pcp-short-resources -->

<!-- passage:pcp-short-complexity -->
*Remark (formalization).* Lee's implementation finds the field, generators and cube roots by bounded search in time polynomial in $q$, hence in the input length, and compiles the verifier into Mathlib's finite multi-stack machine model with a polynomial cost bound.

For a fixed NP language, a bounded accepting computation tableau gives a finite constraint system of fixed arity; one-hot coding, Boolean clauses and three-colouring gadgets reduce it in polynomial time to a graph of polynomial size, and composing with the amplified verifier preserves constant queries and polynomial proof length. Writing $p_f\in\mathbb N[X]$ for an output-length bound of this reduction,

$$
\lceil\log_2(p_f(n)+2)\rceil
\le (\deg p_f)\lceil\log_2(n+2)\rceil
+\lceil\log_2(p_f(1)+2)\rceil.
$$

Padding the random string to the resulting fixed length preserves its prefix distribution and gives the exact randomness formula. See the full argument on [machine implementation](../long/reasoning-record.md#39-the-polynomial-time-implementation), [graph reduction](../long/reasoning-record.md#310-the-reduction-from-np-to-three-colourability) and [transport](../long/reasoning-record.md#311-transport-through-the-reduction).

For the converse, take the verifier and bounds $p,\alpha,\beta$ of Theorem 1.1, guess the first $p(n)$ proof bits and simulate the verifier, in polynomial time, on each of the at most $2^\beta(2(n+2))^\alpha$ random strings. Perfect completeness gives a prefix accepted on every run. If such a prefix existed for a no-instance, its zero extension would have acceptance probability one, contradicting soundness. The resulting witness relation is decidable in polynomial time, so the language lies in NP.
<!-- /passage:pcp-short-complexity -->

## Formalization and sources

<!-- passage:pcp-short-formal-correspondence -->
Lee proved the [forward PCP theorem][lean-forward] and the [reverse inclusion][lean-reverse] in Lean for a concrete finite-machine model, and explicit simulations identify its witness class with [the NP class in the unchanged vendored ComplexityLib][lean-reference-np]. The quantitative bounds of Sections 4 to 6 follow his [encoded-line low-degree theorem][lean-line] (Theorem 4.6), [local-correction guarantee][lean-correction] (Theorem 5.1) and [three-colouring soundness proof][lean-assembly] (Theorem 6.1). The [source and verification account](../long/reasoning-record.md#6-formalization-and-sources) records the source revision and validation evidence.

Besides the formalization remarks, Lee's verifier differs from [ABSSW26, §7] as follows: the inner low-degree test flips a fair coin, the binary low-degree test samples $z$ from all of $F$, and the two corrector calls in each zero-on-grid test use independent seeds.

The construction of [ABSSW26] combines its authors' set-multilinear form of inverse-Kronecker degree reduction with the established low-degree Hadamard encoding [ABSSW26, §1]. The formal proof is due to Troy Lee, whom version 2 of [ABSSW26] credits with identifying the version-1 error. No new PCP theorem is claimed; the prose proofs and Appendix A were not checked in Lean.
<!-- /passage:pcp-short-formal-correspondence -->

## Appendix A. The version-1 low-degree test

<!-- passage:pcp-short-old-test-counterexample -->
Lemma 4.1 uses Lagrange weights and a generator of $F^\times$ [ABSSW26, Fact 2.7 and Lemma 3.3]. The version-1 test, with unit weights [ABSSW26v1, Fact 2.7 and Lemma 3.3], fails over arbitrarily large fields. For target degree two, take $q=2^{2k}$ with $k\ge2$, an element $\omega$ of order three and, in dimension $m\ge1$, $f(x)=x_1^4$. In characteristic two,

$$
f(u)+\sum_{i=1}^3f(u+\omega^iv)
=4u_1^4+v_1^4\sum_{i=1}^3\omega^{4i}=0
$$

for every $u,v$. Every polynomial of total degree at most two agrees with $f$ on at most a fraction $4/q$ of $F^m$: fixing the other coordinates leaves a nonzero degree-four difference in $x_1$. Enlarging the field cannot repair the version-1 test. This counterexample concerns only that test.
<!-- /passage:pcp-short-old-test-counterexample -->

## References

**[ABSSW26]** Prashanth Amireddy, Amik Raj Behera, Srikanth Srinivasan, Madhu Sudan and Sophus Valentin Willumsgaard. *A Simple Algebraic Proof of the PCP Theorem*. [arXiv:2608.17429v2](https://arxiv.org/abs/2608.17429v2), 22 October 2026.

**[ABSSW26v1]** Version 1 of [ABSSW26]: [arXiv:2608.17429v1](https://arxiv.org/abs/2608.17429v1).

**[ALMSS98]** Sanjeev Arora, Carsten Lund, Rajeev Motwani, Madhu Sudan and Mario Szegedy. *Proof Verification and the Hardness of Approximation Problems*. Journal of the ACM **45**(3), 1998. [Author-hosted manuscript](https://people.seas.harvard.edu/~madhusudan/papers/1992/almss-journ.pdf).

**[AS98]** Sanjeev Arora and Shmuel Safra. *Probabilistic Checking of Proofs: A New Characterization of NP*. Journal of the ACM **45**(1), 70–122, 1998. [Journal text](https://www.cs.umd.edu/~gasarch/TOPICS/pcp/AS.pdf).

**[BCHKS96]** Mihir Bellare, Don Coppersmith, Johan Håstad, Marcos Kiwi and Madhu Sudan. *Linearity Testing in Characteristic Two*. IEEE Transactions on Information Theory **42**(6), 1781–1795, 1996. [Author-hosted manuscript](https://www.csc.kth.se/tcs/projects/publications/bchks.pdf).

**[BLR93]** Manuel Blum, Michael Luby and Ronitt Rubinfeld. *Self-Testing/Correcting with Applications to Numerical Problems*. Journal of Computer and System Sciences **47**(3), 549–595, 1993. [Author-hosted manuscript](https://people.csail.mit.edu/ronitt/papers/selftestcorrect.pdf).

**[FS95/13]** Katalin Friedl and Madhu Sudan. *Some Improvements to Total Degree Tests*. ISTCS 1995. [Corrected manuscript, arXiv:1307.3975v1](https://arxiv.org/abs/1307.3975v1), 2013.

**[KS08]** Tali Kaufman and Madhu Sudan. *Algebraic Property Testing: The Role of Invariance*. STOC 2008, 403–412. [Conference manuscript](https://people.csail.mit.edu/madhu/papers/2007/apt-conf.pdf).

**[Lee26]** Troy Lee. *Formalization of the PCP theorem*. 2026. [Source and mathematical guide](https://github.com/troyjlee/tcs-formalizations/tree/a0ce13ed0fa264f051c1278e039596ce65557fa4/docs/pcp).

**[RS96]** Ronitt Rubinfeld and Madhu Sudan. *Robust Characterizations of Polynomials with Applications to Program Testing*. SIAM Journal on Computing **25**(2), 252–271, 1996. [Prepublication manuscript](https://www.cs.princeton.edu/courses/archive/spring04/cos598B/bib/RubinfeldS.pdf).

[lean-forward]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Theorem.lean#L24-L35
[lean-reverse]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/ReverseConcrete.lean#L33-L39
[lean-reference-np]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/ReferenceNPConverse.lean#L39-L41
[lean-line]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/EncodedLineLowDegreeSoundness.lean#L325-L339
[lean-correction]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BinaryLocalCorrectionSoundness.lean#L222-L236
[lean-assembly]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorVerifierSoundness.lean#L58-L70

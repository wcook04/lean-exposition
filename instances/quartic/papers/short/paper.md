
<!-- passage:front -->
# Reconstructing OpenAI’s nearly quartic query separation

*Comparing candidates and predicting a hidden address*

Written by AI systems under the direction of Will Cook · November 2026

**Abstract.** OpenAI recently showed that for every fixed integer $k\ge2$ there are total Boolean functions $F_{k,m}$ with $Q(F_{k,m})=\widetilde O_k(\sqrt m)$ and $R(F_{k,m})=\widetilde\Omega_k(m^{2-1/k})$, so that for every $\alpha<4$ some total function has $R(f)\ge Q(f)^\alpha$ ([OpenAI 2026](#cite-OpenAI2026)). Together with the bound $R(f)=O(Q(f)^4)$ of Aaronson, Ben-David, Kothari, Rao and Tal, this shows that the critical exponent of randomized relative to quantum query complexity is four, and it refutes their conjecture that $R(f)=O(Q(f)^3)$ for all total functions. The construction places pointer certificates in cells addressed by answers to $k$-fold Forrelation instances. In this companion we derive the sampling rule of OpenAI's quantum tournament, whose comparisons may have arbitrary outcome probabilities, by requiring every pairwise bias to cancel; and we base the randomized lower bound on the observation that a query to a hidden cell names the cell's address before any answer is returned.



**About this paper.** The separation theorem, its construction and its proof are OpenAI's ([OpenAI 2026](#cite-OpenAI2026)). AI systems wrote this paper, its two companion texts and a Lean development of the theorem, under the direction of Will Cook. No human expert has reviewed them, and the correspondence between the Lean statements and OpenAI's paper has been compared by AI agents only. Section 7 lists the results of the reconstruction that go beyond OpenAI's paper, and Section 8 says what the Lean development checks.
<!-- /passage:front -->

<a id="1"></a>

## 1. Introduction

<!-- passage:sec-1 -->

In the query model an algorithm computes a function $f\colon\{0,1\}^N\to\{0,1\}$ by reading input bits, and we charge one unit for each bit it reads. We write $R(f)$ and $Q(f)$ for the bounded-error randomized and quantum query complexities of $f$. For total functions these measures are polynomially related, and the natural question is how large the largest polynomial gap can be. Following Aaronson, Ben-David and Kothari ([Aaronson et al. 2016](#cite-ABK2016), sec. 2.3), the *critical exponent* of $R$ relative to $Q$ is the infimum of the exponents $r$ such that $R(f)=O(Q(f)^r)$ holds for all total $f$.

Grover's algorithm ([Grover 1996](#cite-Grover1996)) gives a quadratic gap for the OR function, and for many years this was believed to be the largest gap for total functions. Aaronson, Ben-David and Kothari ([Aaronson et al. 2016](#cite-ABK2016)) refuted this with the cheat-sheet technique and a power $2.5$ separation, up to logarithmic factors. Improvements in the underlying partial-function separations then gave power $8/3-o(1)$ by Tal ([Tal 2020](#cite-Tal2020)), and power $3-o(1)$ by Bansal and Sinha ([Bansal and Sinha 2021](#cite-BansalSinha2021)) and, independently, Sherstov, Storozhenko and Wu ([Sherstov et al. 2023](#cite-SSW2023)). On the other side, Aaronson, Ben-David, Kothari, Rao and Tal ([Aaronson et al. 2021](#cite-ABKRT2021)) used Huang's sensitivity theorem ([Huang 2019](#cite-Huang2019)) to prove $D(f)=O(Q(f)^4)$, and conjectured that $R(f)=O(Q(f)^3)$ ([Aaronson et al. 2021](#cite-ABKRT2021), Conjecture 2). OpenAI's theorem closes the gap between these exponents.

\Needspace{12\baselineskip}

**Theorem 1** (OpenAI ([OpenAI 2026](#cite-OpenAI2026), Theorem 1.1)). *For every total Boolean function $f$, $R(f)=O((1+Q(f))^4)$. For each fixed integer $k\ge2$ there are positive constants $c_k$, $C_k$ and $b_k$ and total Boolean functions $F_{k,m}$, defined for powers of four $m$, such that for all sufficiently large $m$, with $\ell=\log_2m$,*
$$
 Q(F_{k,m})\le C_k\sqrt m\,\ell^{b_k},
 \qquad R(F_{k,m})\ge c_k\,\frac{m^{2-1/k}}{\ell^2}.
\tag{1}
$$
*Consequently the critical exponent of $R$ relative to $Q$ is four.*

The first statement is the theorem of Aaronson, Ben-David, Kothari, Rao and Tal, which OpenAI reproves for completeness; the new content is the family $F_{k,m}$, which satisfies both bounds in (1) for the same function. The proof gives $b_k=6$ and the finite form $R(F_{k,m})>\lfloor mL/100\rfloor$ of OpenAI's Proposition 4.2, with $L=\lfloor m^{1-1/k}/\ell^2\rfloor$, from which Section 6 derives $c_k=1/400$. The Lean theorem for Theorem 1 states this finite form, with both bounds beyond a threshold; Section 8 lists which formal statement carries which form. In powers of $Q$ the family gives $R=\widetilde\Omega(Q^{4-2/k})$, so already $k=3$ gives power $10/3$ and refutes the cubic conjecture, and larger fixed $k$ approach four.

<a id="1.1"></a>

### 1.1 Overview of techniques

The input consists of $m$ *columns*. Column $i$ holds an $m$-bit string $X_i$, a few address inputs, and an array of cells. The function asks whether some column *wins*: its string is all ones, and its cell at the address computed from its address inputs contains a correct certificate pointing to a zero in every other string. At most one column can win. Pointers from a column to zeros in other columns go back to the pointer functions of Göös, Pitassi and Watson ([Göös et al. 2018](#cite-GPW2018)) and of Ambainis et al. ([Ambainis et al. 2017](#cite-ABBLSS2017)), and cells addressed by answers to partial-function instances to the cheat sheets of ([Aaronson et al. 2016](#cite-ABK2016)).

*The cost of plain search.* Checking that a given column wins costs about $\sqrt m$ quantum queries, by Grover search over its roughly $m$ local tests. One way to find a winner would be to search over the $m$ columns with this check inside the search. But then the costs multiply to $\sqrt m\cdot\sqrt m=m$, the cost of balanced AND–OR cheat sheets built from the same partial function, whose bounds $\widetilde O(m)$ and $\widetilde\Omega(m^{3-1/k})$ give power $3-1/k$ ([Aaronson et al. 2016](#cite-ABK2016), sec. 3). The new construction instead lists a few candidates with cheap comparisons and verifies only those, so the two costs add to $\widetilde O_k(\sqrt m)$. The classical bound drops to $m^{2-1/k}$, and in powers of $\sqrt m$ the exponent rises from $3-1/k$ to $4-2/k$.

*Why the pointers point outward.* The winner's certificate stores, for every other column, the row of a zero in that column's string. A comparison between two columns reads one pointer in each direction. If the winner's address is decoded correctly, its pointer finds a zero in the rival, while no rival pointer can find a zero in the winner's all-one string. So the winner is selected with high probability even when the rival's address inputs violate their promise.

*Comparisons with arbitrary outcome probabilities.* A loser's address may be undefined, and its decoder can then return any distribution over addresses. So the probability that one loser beats another can lie anywhere in $[0,1]$, with no gap from $1/2$, and majority voting cannot turn these comparisons into the fixed tournament that quantum minimum finding ([Dürr and Høyer 1996](#cite-DH1996)) or king finding ([Mande et al. 2023](#cite-MPS2023)) would need. OpenAI's tournament instead samples pivots with weights equal to the probability of beating all earlier pivots; Section 4 derives this rule from the requirement that every pairwise bias cancel.

*The classical bound.* The hard distributions differ only in one hidden zero and one cell of a uniformly random column. A decision tree notices the difference only if it finds that zero, invests many queries in that column's address inputs, or queries the correct cell while investing few. The last event is a correct prediction of $r$ independent hard values, because the index of a cell query already names its address; a direct-product theorem with per-input caps bounds it, and a capped simulation avoids conditioning on which columns the tree investigates.

Ben-David and Kothari ([Ben-David and Kothari 2026](#cite-BDK2026)) and Ambainis, Iraids and Kokainis ([Ambainis et al. 2026](#cite-AIK2026)) also compare candidate witnesses, in separations of certificate complexity from randomized and quantum query complexity.

*Organization.* Section 2 fixes conventions and the address function, Section 3 defines $F_{k,m}$, Sections 4 to 6 prove the two bounds and the exponent, Section 7 describes further results of the reconstruction and Section 8 the Lean development. The [worked exposition](/library/quartic/exposition/) develops the argument through small examples, and the [full proof reconstruction](/library/quartic/reconstruction/) gives every supporting derivation.
<!-- /passage:sec-1 -->

<a id="2"></a>

## 2. Preliminaries

<!-- passage:sec-2 -->

All query bounds are worst-case: an algorithm with query cap $q$ makes at most $q$ queries on every input and every branch of its randomness or measurements, and computation between queries is free. For a partial function the cap applies on every input, and the error bound only on the promise. We write $R_\varepsilon$ and $Q_\varepsilon$ for error at most $\varepsilon$ and $R=R_{1/3}$, $Q=Q_{1/3}$. The quantum algorithm has a standard bit oracle: an access into the arrays below computes the global bit index reversibly from the column, cell and wire labels, and reads a pointer of $\ell$ bits one bit at a time. We write $[m]=\{1,\ldots,m\}$, use logarithms to base two, and let constants depend on the fixed integer $k$, as in $O_k(\cdot)$.

We require a partial function $P$ with a low-query quantum algorithm on its promise, a nearly linear exact circuit for checking its domain and value, and high randomized query complexity. Each property has one job in the construction.

| Property of $P$ | What it buys |
|---|---|
| Cheap quantum decoding on the promise | cheap address decoding, hence cheap comparisons |
| An exact circuit of size $\widetilde O_k(m)$ for the domain bit and the value | cheap checking of a proposed address, including promise membership |
| $R(P)>L$ with $L$ close to $m^{1-1/k}$ | an address that is hard to compute classically |

The Walsh–Hadamard form of $k$-fold Forrelation, introduced by Aaronson and Ambainis ([Aaronson and Ambainis 2018](#cite-AA2018)), supplies all three. An input is $k$ blocks of $m$ bits; if $x_j(a)$ is the bit at coordinate $a$ of block $j$, we read it as the sign $z_j(a)=(-1)^{x_j(a)}$, so a sign query is a bit query. Let $H$ be the normalized Walsh–Hadamard matrix of order $m$, $u=m^{-1/2}(1,\ldots,1)^{\mathsf T}$ and $D_z$ the diagonal matrix of a sign vector, and put
$$
 \Phi=u^{\mathsf T}D_{z_1}H D_{z_2}H\cdots H D_{z_k}u,\qquad \delta=2^{-5k}.
$$
Set $P=1$ when $\Phi\ge\delta$, $P=0$ when $|\Phi|\le\delta/2$, and leave $P$ undefined elsewhere. Applying the unitary product to $u$ and projecting onto $u$ succeeds with probability $\Phi^2$; for fixed $k$ the two promised cases have a constant gap, and repetition with all trial registers retained gives the decoder. The projection probability depends only on $|\Phi|$, whereas an input with $\Phi\le-\delta$ lies outside the promise, so the decoder alone cannot certify an answer. For the exact circuit we compute the signed numerator of $\Phi$ by $k-1$ unnormalized fast Walsh–Hadamard transforms on integers of $O_k(\ell)$ bits and test the two defining inequalities after clearing denominators. The denominator is $m(\sqrt m)^{k-1}$, which is an integer when $m$ is a power of four; this is why $m$ ranges over powers of four.

**Lemma 2** (OpenAI ([OpenAI 2026](#cite-OpenAI2026), Lemma 2.1)). *Fix $k\ge2$. For all sufficiently large powers of four $m$,*
$$
 L:=\left\lfloor m^{1-1/k}/\ell^2\right\rfloor < R(P).
\tag{3}
$$
*For every $0<\eta<1/2$ a reversible quantum algorithm with $O_k(1+\log(1/\eta))$ queries on every input computes $P$ with error at most $\eta$ on its domain. There is an exact fan-in-two circuit with $S=O_k(m\ell^2)$ gates whose two outputs are the domain bit of $P$ and, on the domain, its value.*

OpenAI imports (3) from the lower bound of Bansal and Sinha ([Bansal and Sinha 2021](#cite-BansalSinha2021), Corollary 1.4). The Lean development and the full reconstruction prove (3) directly, by a different route described in Section 7.
<!-- /passage:sec-2 -->

<a id="3"></a>

## 3. The function

<!-- passage:sec-3 -->

Fix $k\ge2$ and a power of four $m$, and put $r=20\ell$. The input of $F_{k,m}$ consists of the following bits for each column $i\in[m]$; every bit is part of the input, so a cell is an arbitrary bit string and no part of the input is trusted.

- The *string* $X_i\in\{0,1\}^m$. An all-one string protects a genuine winner: no pointer can find a zero in it.
- The *address inputs* $A_{i,1},\ldots,A_{i,r}$, each an input to $P$. When their values are all defined they form the *true address* $s_i=(P(A_{i,1}),\ldots,P(A_{i,r}))$. Computing it is cheap quantumly and hard classically.
- The *cells* $B_{i,s}$, one for each $s\in\{0,1\}^r$, so $2^r=m^{20}$ cells. A cell contains one $\ell$-bit row pointer $p_{i,s,j}$ for each column $j\ne i$, and for each $h\le r$ a proposed *transcript*: one bit per non-input gate of the circuit of Lemma 2 evaluated on $A_{i,h}$. Since $m=2^\ell$, every pointer word names a row.

The input length is $m\bigl(m+rkm+2^r((m-1)\ell+rS)\bigr)=O_k(m^{22}\ell^3)$, so logarithms of the input length are $O_k(\ell)$.

Column $i$ **wins** if $X_i=1^m$, all its address inputs belong to the domain of $P$, and its cell at the true address is correct. Precisely, column $i$ wins if the following four conditions hold.

1. $X_i=1^m$ (the string is all ones).
2. Each $A_{i,h}$ lies in the domain of $P$ (the true address $s_i$ is defined).
3. Each transcript in $B_{i,s_i}$ equals the true evaluation of the circuit on $A_{i,h}$ (the cell certifies the address).
4. $X_j[p_{i,s_i,j}]=0$ for every $j\ne i$ (the cell points to a zero in every other string).

We set $F_{k,m}=1$ if some column wins and $F_{k,m}=0$ otherwise; this defines $F_{k,m}$ on every input, including inputs whose address inputs violate the promise. Two distinct columns cannot both win, since the pointer from one would have to name a zero in the other's all-one string.

To verify column $i$ at a proposed address $s$, we use exact local tests. We check that $X_i[a]=1$ for every row $a$, that $X_j[p_{i,s,j}]=0$ for every $j\ne i$, and, in the transcript for each $A_{i,h}$, that each gate bit agrees with the gate applied to its inputs and that the two output bits equal $(1,s_h)$. By induction in circuit order, a transcript consistent at every gate equals the true evaluation. So a false transcript disagrees at some gate, and a true transcript for an off-promise input or a wrong address bit disagrees at an output. Consequently, for a column that does not win, some test fails at *every* address. There are
$$
 K=m+(m-1)+r(S+2)
\tag{2}
$$
tests, so $K=O_k(m\ell^3)$. Checking a gate costs at most three queries, and following a pointer costs $\ell+1$.

The construction thus supplies two interfaces, and the rest of the proof uses only these.

| Operation | Guarantee used |
|---|---|
| Comparison of two columns | a winner beats every rival with high probability; comparisons between losers may behave arbitrarily |
| Verification at a measured address | every column that does not win fails some exact test at every address |

\Needspace{16\baselineskip}

![A comparison between the winner $i^\star$ and a rival $j$. Decoding the address inputs of $i^\star$ selects its cell $B_{i^\star,s_{i^\star}}$, whose pointer into $X_j$ stores row 6, and $X_j[6]=0$. The rival's cell $B_{j,t}$, at any decoded address $t$, can only point to a one in $X_{i^\star}=1^m$. The comparison therefore selects $i^\star$.](figures/expert_column.svg)
<!-- /passage:sec-3 -->

<a id="4"></a>

## 4. The quantum upper bound

<!-- passage:sec-4 -->

<a id="4.1"></a>

### 4.1 Comparing two columns

For $i\ne j$, decode addresses $s$ for $i$ and $t$ for $j$, each in its own workspace. Read $X_j[p_{i,s,j}]$ and $X_i[p_{j,t,i}]$. If exactly one of these bits is zero, select the column whose pointer found that zero; otherwise select the smaller index. A self-comparison selects neither column and reads no pointer. Suppose $i=i^\star$ is the winning column. If the algorithm decodes its address correctly, it reads a zero in $X_j$ and a one in $X_{i^\star}=1^m$, so it selects $i^\star$ whatever address it decodes for $j$, and even when no address of $j$ is defined.

Write $\varepsilon$ for the allowed error in decoding a whole address on promised inputs, and use error $\varepsilon/r$ for each of its $r$ bits. We order each unordered pair canonically and run a single comparison experiment, with both decoded addresses retained; asking whether $i$ beat $j$ or $j$ beat $i$ reads the same measured outcome. Writing $a_{ij}$ for the probability that this experiment selects $i$, and $a_{ii}=0$ for the self-comparison, we have
$$
 a_{ij}+a_{ji}=1\quad(i\ne j),\qquad a_{ii}=0.
\tag{4}
$$
The winner is *dominant*: $a_{i^\star j}\ge1-\varepsilon$ for every $j\ne i^\star$. One comparison, or its inverse, uses $c=O_k(r\log(r/\varepsilon)+\ell)$ queries.

<a id="4.2"></a>

### 4.2 A tournament for probabilistic comparisons

**Proposition 3** (OpenAI ([OpenAI 2026](#cite-OpenAI2026), Proposition 3.2)). *Let $T=\lceil\log(1000m)\rceil$ and $\varepsilon=1/(1000T)$. Suppose a reversible comparison circuit, controlled by two candidate indices, uses at most $c$ queries and satisfies (4). There is a quantum algorithm making $O(c\sqrt m\,T^2\log T)$ queries on every branch and returning a list of at most $T$ candidates such that, if $a_{i^\star j}\ge1-\varepsilon$ for all $j\ne i^\star$, the list contains $i^\star$ with probability at least $1-2m2^{-T}-T\varepsilon$.*

The algorithm samples a sequence of indices, called *pivots*, and returns them as its list. We first describe an ideal sampling process in which the comparison probabilities are known, and then implement it without knowing them. For deterministic comparisons one can retain the candidates selected over every previous pivot and draw uniformly from this set ([Ambainis et al. 2026](#cite-AIK2026), sec. 6.1). With probabilistic comparisons we weight each candidate by the probability of being selected over every previous pivot in fresh, independent comparisons. After pivots $\rho_1,\ldots,\rho_n$, the individual and total weights are
$$
 w_i=\prod_{h=1}^n a_{i\rho_h},\qquad W=\sum_i w_i.
$$

Initially all weights are one. After drawing $j$, replace each $w_i$ by $w_i a_{ij}$, so the new weight of $j$ is zero. Suppose the probability of drawing $j$ is $q_j$. The contribution of an unordered pair $i,j$ to the expected remaining weight is $w_i q_j a_{ij}+w_j q_i a_{ji}$. With uniform sampling the two coefficients can differ, and the adversarial biases between losers could keep the remaining weight high. To cancel the bias of every pair we impose $w_i q_j=w_j q_i$; by (4) the contribution is then $w_iq_j$, whatever $a_{ij}$ is. Drawing $j$ with probability $w_j/W$ satisfies this for every pair, and summing over pairs gives, for $W>0$,
$$
 \sum_j\frac{w_j}{W}\sum_i w_i a_{ij}
 =\frac{W^2-\sum_i w_i^2}{2W}.
\tag{5}
$$

For $W>0$, the nonnegative sum of squares in (5) gives the bound $\mathbb E[W_{\rm new}\mid w]\le W/2$. Equivalently, draw two independent indices from the weights: the ordered pairs $(i,j)$ and $(j,i)$ have equal probability, their selection probabilities sum to one when $i\ne j$, and the diagonal contributes nothing.

In the ideal process we stop if $W=0$. After $T$ steps the expected total weight is at most $m2^{-T}$. If the winner is still unlisted, its weight is at least $(1-\varepsilon)^T\ge1-T\varepsilon>1/2$. This single inequality does two jobs. First, by Markov's inequality, the probability that the winner remains unlisted is at most $2m2^{-T}$. Second, while the winner is unlisted the total weight exceeds $1/2$, which keeps the sampling step below affordable.

The weights are quantities of the analysis; the algorithm never estimates or stores them. The quantum algorithm has only the reversible comparison circuit and the list of pivots drawn so far. To draw its next pivot, it prepares a uniform superposition of indices $i$ and compares $i$ with every listed pivot in fresh workspaces, coherently controlled by $i$. If $|\phi(i,\rho_b)\rangle$ is the entire state of one comparison, the preparation produces
$$
 \frac1{\sqrt m}\sum_i |i\rangle\bigotimes_{b=1}^n |\phi(i,\rho_b)\rangle.
$$
Set a flag if every comparison selects $i$. For a fixed $i$ the comparison states form a tensor product, so the joint success probability is the product $w_i$, and states with distinct labels are orthogonal. Consequently
$$
 \Pr[i\text{ and flag}]=\frac{w_i}{m},\qquad
 \Pr[\text{flag}]=\frac Wm,\qquad
 \Pr[i\mid\text{flag}]=\frac{w_i}{W}.
\tag{6}
$$
The flagged branch therefore samples the next pivot from the ideal law, without the algorithm knowing any $a_{ij}$. It remains to make the flag likely without disturbing this law.

**Lemma 4** (bounded amplification ([OpenAI 2026](#cite-OpenAI2026), Lemma 3.1); see @BBHT1998 and @BHMT2002). *Let $A$ prepare a state with a success flag, with success probability $p$. For $0<\gamma\le1/2$ and $0<\eta<1/2$ there is a procedure making $O(\gamma^{-1/2}\log(1/\eta))$ calls to $A$ and $A^{-1}$ on every branch, for every $p$, that either reports failure or produces a successful outcome. Conditional on success, the measured label has the same distribution as in the successful part of $A$'s state. If $p\ge\gamma$ it fails with probability at most $\eta$, and if $p=0$ it always fails.*

The label law is preserved because each Grover iteration rotates within the plane spanned by the successful and unsuccessful components of $A$'s state, and so leaves the direction of the successful component unchanged. The [full reconstruction](/library/quartic/reconstruction/#upper-amplification-statement) gives the schedule and its proof.

We apply Lemma 4 with $\gamma=1/(2m)$ and $\eta=\varepsilon$. Before the winner is listed the flag probability $W/m$ exceeds $1/(2m)$, so each stage fails with probability at most $\varepsilon$ and otherwise appends a pivot drawn exactly from the ideal law. We stop on failure or after $T$ stages. Once the winner is listed, later stopping cannot remove it, so the behaviour of the sampler afterwards is irrelevant. Coupling the algorithm with the ideal process at each history before the winner is listed gives
$$
 \Pr[i^\star\text{ absent from the list}]\le 2m2^{-T}+T\varepsilon.
\tag{7}
$$
Each stage rebuilds at most $T$ comparisons per call to the preparation, so the $T$ stages cost $O(c\sqrt m\,T^2\log T)$ queries on every input. This proves Proposition 3.

<a id="4.3"></a>

### 4.3 Verifying the listed columns

For each listed column, decode a fresh address with error at most $\varepsilon$ on promised inputs and measure it. At this fixed address $s$, a uniformly chosen test of the $K$ tests in (2) fails with probability zero if all tests pass and at least $1/K$ otherwise. Lemma 4 with $\gamma=1/K$ and $\eta=\varepsilon$ searches for a failed test with $O(\ell\sqrt K\log(1/\varepsilon))$ queries. Accept the column if no failed test is found. The search is one-sided: exact testing cannot report a failure when all tests pass, so a winner whose address was decoded correctly is always accepted. A column that does not win has a failed test at every address, and is accepted with probability at most $\varepsilon$.

On a one-input the algorithm accepts unless the winner is missing from the list or its address is decoded wrongly, so it errs with probability at most (7) plus $\varepsilon$. On a zero-input the comparisons may list columns with false transcripts, since a comparison never reads a transcript; but each listed column is accepted with probability at most $\varepsilon$, so the error is at most $T\varepsilon$. Both errors are below $1/3$.

With $T=O(\ell)$, $c=O_k(\ell\log\ell)$ and $K=O_k(m\ell^3)$, the tournament costs $O_k(\sqrt m\,\ell^3\log^2\ell)$ and checking the list $O(T(c+\ell\sqrt K\log T))=O_k(\sqrt m\,\ell^{7/2}\log\ell)$. Both are at most $C_k\sqrt m\,\ell^6$, the bound in (1) with a generous $b_k=6$.
<!-- /passage:sec-4 -->

<a id="5"></a>

## 5. The randomized lower bound

<!-- passage:sec-5 -->

<a id="5.1"></a>

### 5.1 The hard distribution

By Yao's principle it suffices to give two input distributions, one supported on zero-inputs and one on one-inputs, that every deterministic decision tree of depth $G=\lfloor mL/100\rfloor$ distinguishes with advantage less than $1/3$. We will show that the advantage is at most
$$
 \underbrace{\frac{4G}{m^2}}_{\text{find the erased zero}}
 +\underbrace{\frac{G}{mL}}_{\text{invest heavily in the planted column}}
 +\underbrace{G\beta^r}_{\text{query its cell while light}},
$$
with $\beta=2/3$; the three terms are proved in Sections 5.2 and 5.3.

For the **dummy input** $Y^{(0)}$, choose the row $J_i$ of the sole zero in $X_i$ independently and uniformly in each column. Draw the address inputs independently of one another and of the zero positions, using a common law $\mu$ on the promise of $P$ chosen below. Set every cell bit to zero. Every column loses. Choose $I$ uniformly and independently of the entire dummy input. For the **planted input** $Y^{(1)}$, set $X_I[J_I]=1$, and in $B_{I,s_I}$ write the gate bits of all $r$ correct circuit evaluations and the row numbers $J_j$ for $j\ne I$. Column $I$ wins.

Because the dummy cells are blank, querying them reveals nothing about which cell is correctly addressed. And because the entire dummy input, hence the tree's entire run on it, is independent of $I$, the tree's investment in the planted column is an average over columns. This independence is what gains the factor $m$ in the lower bound.

\Needspace{17\baselineskip}

![The coupled inputs with $I=3$. Each horizontal row depicts one column of the construction: its string $X_i$, its address inputs and its cells. All dummy cells are zero. Both inputs share the strings $A_{i,h}$; they differ only in $X_I[J_I]$ and in the gate and pointer bits of $B_{I,s_I}$.](figures/expert_planted.svg)

Run a deterministic decision tree on both inputs. The sequences of queried indices and answers coincide until the first query to $X_I[J_I]$ or to a bit of $B_{I,s_I}$. So the acceptance gap is at most the sum of the probabilities that the tree queries these locations on the dummy input ([Aaronson et al. 2016](#cite-ABK2016), Lemma 6; [Ben-David 2015](#cite-BenDavid2015), sec. 5.1).

<a id="5.2"></a>

### 5.2 Searching for the erased zero

Let $Z$ count the columns $i$ in which the tree queries the unique zero of $X_i$ on the dummy input. By independence of $I$, the probability that $I$ is among these columns is $\mathbb E Z/m$. Before the first query to a column's zero, its row is uniform among the unqueried rows of that column, even conditional on the transcript. While the tree has queried fewer than half the rows of a column, its next query there finds the zero with probability at most $2/m$, so zeros found this way number at most $2G/m$ in expectation. Every other found zero costs at least $m/2$ queries in its column, so there are at most $2G/m$ of those.

With at most $G$ queries in the dummy run, the erased-zero probability is therefore
$$
 \Pr[\text{query }X_I[J_I]]\le\frac{4G}{m^2}.
\tag{8}
$$

<a id="5.3"></a>

### 5.3 Predicting the cell address

The index of any query to a bit of $B_{i,s}$ includes $s$, and the tree chooses that index before any answer is returned. If $s=s_i$, the query has already named all $r$ values $P(A_{i,1}),\ldots,P(A_{i,r})$. A tree can therefore reach the planted cell only by predicting $r$ independent hard values, and a direct-product theorem bounds such predictions.

**Lemma 5** (OpenAI ([OpenAI 2026](#cite-OpenAI2026), Lemma 4.1); @Shaltiel2003; @Drucker2012). *Let $P$ be a partial function and $\mu$ a distribution on its domain such that every deterministic algorithm making at most $L$ queries computes $P$ under $\mu$ with probability at most $\beta$. If $U_1,\ldots,U_r$ are independent samples from $\mu$, every algorithm making at most $L$ queries to each $U_h$ outputs $(P(U_1),\ldots,P(U_r))$ with probability at most $\beta^r$. The algorithm may be randomized, interleave its queries adaptively among the $r$ inputs, and receive additional information independent of $(U_1,\ldots,U_r)$.*

*Proof.* Fix the coins and the additional information, leaving a deterministic algorithm. A transcript of positive probability fixes the answers to the queried bits of each input, and every tuple consistent with these answers follows the same query schedule. So the event of obtaining a transcript is a product of constraints on the separate inputs, and the conditional law of $(U_1,\ldots,U_r)$ given it is again a product. For each $h$ let $V_h$ be the largest probability of computing $P(U_h)$ from its current conditional law with its remaining queries. A query to $U_h$ cannot increase $V_h$ in expectation, since making that query and continuing optimally was already available, and it leaves the other factors unchanged. So $\prod_h V_h$ is a supermartingale. At the end the probability of a correct answer vector is at most $\prod_h V_h$, and initially $\prod_h V_h\le\beta^r$. $\square$

Conditioning on the transcript is legitimate here because the transcript constrains each input separately. Conditioning on an event such as "the tree makes few queries to this column" is different, since the tree's later choices depend on earlier answers.<sup class="footnote-ref"><a href="#fn-and" id="fnref-and">1</a></sup>


Since $L<R(P)$ and there are finitely many trees of depth at most $L$, finite minimax ([Yao 1977](#cite-Yao1977)) gives a distribution $\mu$ on the domain of $P$ under which every such tree has success at most $\beta=2/3$. This is the common law of the address inputs. Call a column *heavy* if the tree makes more than $L$ queries to its address inputs on the full dummy run, counting repetitions, and *light* otherwise. There are at most $G/L$ heavy columns on any run, and since $I$ is independent of the run,
$$
 \Pr[I\text{ heavy}]\le\frac{G}{mL}.
$$

For a light column we bound the joint event directly. Fix a column $i$ and a query time $\tau\le G$. The target inclusion is
$$
 \{i\text{ light and the query at time }\tau\text{ is in }B_{i,s_i}\}
 \subseteq\{\text{a capped predictor outputs }s_i\}.
$$
The predictor uses its $r$ unknown inputs as $A_{i,1},\ldots,A_{i,r}$. It samples all zero rows and the other columns' address inputs as on a dummy input, sets all cell bits to zero, and simulates the tree's queries before time $\tau$, querying the unknown inputs only for requested bits of $A_{i,h}$. It stops before the $(L+1)$-st such query in total. If the index the tree would query at time $\tau$ is a bit of some $B_{i,s}$, it outputs $s$ without reading that bit; on any other index, early termination of the tree, or a simulation stopped by the cap, it outputs a fixed string. The tree's query time and the predictor's count of target queries are separate clocks, and the [worked exposition](/library/quartic/exposition/) traces both on an example.

The total cap gives the predictor at most $L$ queries to *each* target input on every branch, and Lemma 5 allows $L$ queries to each input separately, so the predictor succeeds with probability at most $\beta^r$ under $\mu^{\otimes r}$. If $i$ is light at the end of the run, the simulation uses at most $L$ target queries through time $\tau$, so a query to $B_{i,s_i}$ at that time makes the predictor output $s_i$. Correct default guesses can also make the predictor succeed, so only the inclusion holds, and
$$
 \Pr[i\text{ light and query }\tau\text{ is in }B_{i,s_i}]
 \ \le\ \Pr[\text{predictor outputs }s_i]\ \le\ \beta^r.
\tag{9}
$$
For each column there are at most $G$ query times. Averaging over the independent choice of $I$ and adding the chance of a heavy column,
$$
 \Pr[\text{query }B_{I,s_I}]
 \le \frac G{mL}+\frac1m\sum_{i=1}^m G\beta^r
 = \frac G{mL}+G\beta^r .
\tag{10}
$$

<a id="5.4"></a>

### 5.4 The randomized bound

Combining (8) and (10), the gap between the acceptance probabilities on the two distributions is at most
$$
 \frac{4G}{m^2}+\frac G{mL}+G(2/3)^r <\frac13.
\tag{11}
$$
Here $G\le mL/100\le m^2/100$, so the first two terms are at most $1/25$ and $1/100$, and $r=20\ell$ gives $G(2/3)^r\le Gm^{-10}$. Averaging over coins gives (11) for randomized trees, while an algorithm with error at most $1/3$ on both supports would need a gap of at least $1/3$. Hence $R(F_{k,m})>\lfloor mL/100\rfloor$. The heavy-column term sets the scale $mL$; the $r$ address bits only make a lucky guess of a whole address unlikely enough to survive a union bound over the $G$ query times. The constants $20$, $100$ and $1000$ leave ample slack.
<!-- /passage:sec-5 -->

<a id="6"></a>

## 6. The optimal exponent

<!-- passage:sec-6 -->

For sufficiently large $m$, the floor in (3) gives $L\ge m^{1-1/k}/(2\ell^2)$ and $\lfloor mL/100\rfloor\ge mL/200$, so $R(F_{k,m})\ge m^{2-1/k}/(400\ell^2)$, a deliberately loose constant. Now fix $0\le\alpha<4$, choose $k\ge2$ with $k>2/(4-\alpha)$, and hold $k$ fixed as $m$ grows through powers of four. By (1) with $b_k=6$ and $c_k=1/400$,
$$
 \frac{R(F_{k,m})}{(1+Q(F_{k,m}))^\alpha}
 \ \ge\ \frac{1}{400(1+C_k)^\alpha}\,
 \frac{m^{2-1/k-\alpha/2}}{(\log_2 m)^{2+6\alpha}}
 \ \longrightarrow\ \infty.
$$
Thus for each exponent below four some fixed $k$ gives a counterexample, proving optimality of the quartic upper bound. The inequality $k>2/(4-\alpha)$ is strict because the logarithmic factors must be absorbed; for example $k=3$ excludes every $\alpha<10/3$. The order of quantifiers matters: $k$ is chosen first and then $m\to\infty$, and substituting a $k$ that grows with $m$ into (1) would not be justified, since $C_k$ and the threshold depend on $k$.

The two mechanisms of the proof are worth separating from this construction. Complementary comparisons support efficient quantum search even when most comparisons have no stable orientation, provided one candidate wins its comparisons reliably. And a classical algorithm can be charged for a simultaneous prediction that it reveals in the index of its query, before it receives any answer.
<!-- /passage:sec-6 -->

<a id="7"></a>

## 7. Further results in the reconstruction

<!-- passage:sec-7 -->

The full reconstruction proves several results that go beyond OpenAI's paper. AI systems produced them, and no person has reviewed them. Each item says whether a Lean theorem states it or it is written mathematics only.

**A direct proof of the fixed-$k$ Forrelation bound.** The [full reconstruction, §8](/library/quartic/reconstruction/#forr_target) and the Lean development prove (3) for each fixed $k$, with error $1/3$ and an unspecified threshold in $m$; the full quantitative theorem of Bansal and Sinha is not reproved. As in their proof, fair signs are compared with a correlated law obtained by pairing Gaussian vectors with their Walsh transforms. The reconstruction interpolates in the bias of the first block only, and repeated Gaussian integration by parts with a bounded algebraic transform carries the resulting bias factor through the remaining blocks, one Walsh entry of size $m^{-1/2}$ at a time. The mean of $\Phi$ separates the two laws, while a martingale argument adapted from Girish, Tal and Wu ([Girish et al. 2021](#cite-GTW2021)) bounds the change in any shallow adaptive tree. Lean checks this proof.

**Uniform dependence on $k$ and a single growing family.** A Lean theorem states $R(P_{k,4^t})>\frac{2}{18225}\,m^{1-1/k}/(k^2\ln(4km))$ whenever $15k+2\le2t$, and this uniformity is what allows $k$ to grow with $m$. Compare $\log_2R$ with $4\log_2Q$: the classical exponent $2-1/k$ loses $\ell/k$ against $2\ell$, and the factor $2^{10k}$ in the decoder's repetition count adds $40k$ to $4\log_2Q$. Balancing these losses gives $k\approx\sqrt{\ell/40}$. With $k=\lfloor\sqrt{t/20}\rfloor$ for $m=4^t$, $t\ge80$, the [full reconstruction](/library/quartic/reconstruction/#ROOT-GROWING-K) obtains a single family with $R\ge Q^{4-\varepsilon(\ell)}$ and $\varepsilon(\ell)=O(1/\sqrt\ell)$; its explicit rate is vacuous for small $\ell$. Diagonalizing the fixed-$k$ theorem already gives some such family; the addition is the explicit schedule and rate. The inputs are stated in Lean, the combining calculation is written mathematics only.

**Two steps in the proof of Bansal and Sinha.** [Appendix D.3](/library/quartic/reconstruction/#forr_bs_mismatch) of the full reconstruction finds two discrepancies in §5.4 of arXiv:2008.07003v3 (printed p. 38): two successive displayed bounds differ by a logarithmic factor that is unbounded for fixed $k\ge3$, and (5.31) subtracts $\delta^2/(4N)$ where their Theorem 3.1 gives the exceptional probability $4/(N\delta^2)$. The appendix derives from their displayed bounds a corrected estimate with a weaker logarithmic factor, which still exceeds $L$ in (3) for every fixed $k$ and large $m$; so the separation is unaffected, and the proof of (3) above uses neither step. Written mathematics only.

**The Sherstov–Storozhenko–Wu bound for the Walsh promise.** For $0<\eta\le1$ and powers of two $m\ge2^{15k+2}$, [Appendix D.3](/library/quartic/reconstruction/#forr_ssw_comparison) derives $R_{(1-\eta)/2}(P_{k,m})\ge\frac{\eta^2}{162eC^2}\bigl(m/(1+\ln(km))\bigr)^{1-1/k}$, where $C$ is the unspecified absolute constant of their Fourier-growth theorem ([Sherstov et al. 2023](#cite-SSW2023)). The Fourier bound is theirs; its transfer to the Walsh promise is the reconstruction's. Written mathematics only.

**A prefactor in Špalek and Szegedy.** For two-bit parity, which has an exact one-query algorithm, the printed prefactor of Theorem 3.1 of Špalek and Szegedy ([Špalek and Szegedy 2006](#cite-SS2006)) applied to a four-cycle adversary matrix would give $Q_{1/100}\ge2-\sqrt{99}/25>1$. At error $1/3$ there is no contradiction. The corresponding theorem of Høyer, Lee and Špalek ([Høyer et al. 2007](#cite-HLS2007), Theorem 1) has an extra factor $1/2$, which agrees with the witness. No erratum has been confirmed by the authors, and the asymptotic content is unaffected ([Appendix D.4](/library/quartic/reconstruction/#R3-A-PARITY-PREFACTOR); written mathematics only).

The reconstruction also contains alternative arguments for known bounds: Lean proves the sharper erased-zero bound $2G/m^2$, proves Lemma 5 by an induction over sub-distributions, and states the universal quartic bound along three routes with different constants.
<!-- /passage:sec-7 -->

<a id="8"></a>

## 8. Verification and reproducibility

<!-- passage:sec-8 -->

The Lean development is in the [quartic-query-lean repository](https://github.com/wcook04/quartic-query-lean); every link in this paper names one release. The theorem `theorem_1_1_unconditional` states Theorem 1 with no hypotheses, with both bounds of (1) beyond a threshold and the randomized bound in the finite form $R>\lfloor mL/100\rfloor$. A separate theorem, `construction_family_named`, states (1) with $b_k=6$ and $c_k=1/400$ beyond a threshold. The fixed-$k$ bound (3) is `ForrelationLower.bansalSinhaLower` and the uniform bound of Section 7 is `forrelation_lower_uniform_sharp`. The headline theorem and (3) depend only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`, and the headline statement is accepted by Comparator against an independently compiled specification. Lean checks these proofs; whether the Lean statements say what OpenAI's paper says has been compared by AI agents only. The [theorem index](https://github.com/wcook04/quartic-query-lean/blob/v1.0.2/docs/proof_index.md) links each formal statement to its source.
<!-- /passage:sec-8 -->

## References

<!-- passage:sec-references -->

<a id="cite-AA2018"></a>Aaronson, Scott, and Andris Ambainis. 2018. "Forrelation: A Problem That Optimally Separates Quantum from Classical Computing." *SIAM Journal on Computing* 47 (3): 982--1038. <https://doi.org/10.1137/15M1050902>.

<a id="cite-ABK2016"></a>Aaronson, Scott, Shalev Ben-David, and Robin Kothari. 2016. "Separations in Query Complexity Using Cheat Sheets." *Proceedings of the 48th Annual ACM Symposium on Theory of Computing (STOC 2016)*, 863--76. <https://doi.org/10.1145/2897518.2897644>.

<a id="cite-ABKRT2021"></a>Aaronson, Scott, Shalev Ben-David, Robin Kothari, Shravas Rao, and Avishay Tal. 2021. "[Degree vs. approximate degree and quantum implications of Huang's sensitivity theorem]{.nocase}." *Proceedings of the 53rd Annual ACM Symposium on Theory of Computing (STOC 2021)*, 1330--42.

<a id="cite-ABBLSS2017"></a>Ambainis, Andris, Kaspars Balodis, Aleksandrs Belovs, Troy Lee, Miklos Santha, and Juris Smotrovs. 2017. "Separations in Query Complexity Based on Pointer Functions." *Journal of the ACM* 64 (5): 32:1--24.

<a id="cite-AIK2026"></a>Ambainis, Andris, Jānis Iraids, and Martins Kokainis. 2026. *Near-Optimal Separations of Certificate Complexity from Randomized and Quantum Query Complexity*. <https://arxiv.org/abs/2609.11664v3>.

<a id="cite-BansalSinha2021"></a>Bansal, Nikhil, and Makrand Sinha. 2021. "$k$-Forrelation Optimally Separates Quantum and Classical Query Complexity." *Proceedings of the 53rd Annual ACM Symposium on Theory of Computing (STOC 2021)*, 1303--16. <https://doi.org/10.1145/3406325.3451040>.

<a id="cite-BenDavid2015"></a>Ben-David, Shalev. 2015. *A Super-Grover Separation Between Randomized and Quantum Query Complexities*.

<a id="cite-BDK2026"></a>Ben-David, Shalev, and Robin Kothari. 2026. *Randomized Query Complexity Can Beat Certificate Complexity*.

<a id="cite-DH1996"></a>Dürr, Christoph, and Peter Høyer. 1996. *A Quantum Algorithm for Finding the Minimum*.

<a id="cite-GTW2021"></a>Girish, Uma, Avishay Tal, and Kewen Wu. 2021. "Fourier Growth of Parity Decision Trees." *36th Computational Complexity Conference (CCC 2021)*, LIPIcs, vol. 200: 39:1--36. <https://doi.org/10.4230/LIPIcs.CCC.2021.39>.

<a id="cite-GPW2018"></a>Göös, Mika, Toniann Pitassi, and Thomas Watson. 2018. "[Deterministic communication vs. partition number]{.nocase}." *SIAM Journal on Computing* 47 (6): 2435--50. <https://doi.org/10.1137/16M1059369>.

<a id="cite-Grover1996"></a>Grover, Lov K. 1996. "A Fast Quantum Mechanical Algorithm for Database Search." *Proceedings of the 28th Annual ACM Symposium on Theory of Computing (STOC 1996)*, 212--19.

<a id="cite-HLS2007"></a>Høyer, Peter, Troy Lee, and Robert Špalek. 2007. "Negative Weights Make Adversaries Stronger." *Proceedings of the 39th Annual ACM Symposium on Theory of Computing (STOC 2007)*, 526--35.

<a id="cite-Huang2019"></a>Huang, Hao. 2019. "Induced Subgraphs of Hypercubes and a Proof of the Sensitivity Conjecture." *Annals of Mathematics* 190 (3): 949--55. <https://doi.org/10.4007/annals.2019.190.3.6>.

<a id="cite-MPS2023"></a>Mande, Nikhil S., Manaswi Paraashar, and Nitin Saurabh. 2023. "Randomized and Quantum Query Complexities of Finding a King in a Tournament." *43rd IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2023)*, LIPIcs, vol. 284: 30:1--19. <https://doi.org/10.4230/LIPIcs.FSTTCS.2023.30>.

<a id="cite-OpenAI2026"></a>OpenAI. 2026. *A Nearly Quartic Separation Between Randomized and Quantum Query Complexity*. <https://github.com/openai/math/blob/4eaee875/preprints/A-Nearly-Quartic-Separation-Between-Randomized-and-Quantum-Query-Complexity-October-5-2026/quartic-query-separation.pdf>.

<a id="cite-SSW2023"></a>Sherstov, Alexander A., Andrey A. Storozhenko, and Pei Wu. 2023. "An Optimal Separation of Randomized and Quantum Query Complexity." *SIAM Journal on Computing* 52 (2): 525--67. <https://doi.org/10.1137/22M1468943>.

<a id="cite-SS2006"></a>Špalek, Robert, and Mario Szegedy. 2006. "All Quantum Adversary Methods Are Equivalent." *Theory of Computing* 2 (1): 1--18. <https://doi.org/10.4086/toc.2006.v002a001>.

<a id="cite-Tal2020"></a>Tal, Avishay. 2020. "Towards Optimal Separations Between Quantum and Randomized Query Complexities." *Proceedings of the 61st Annual IEEE Symposium on Foundations of Computer Science (FOCS 2020)*, 228--39.

<a id="cite-Yao1977"></a>Yao, Andrew Chi-Chih. 1977. "Probabilistic Computations: Toward a Unified Measure of Complexity." *Proceedings of the 18th Annual Symposium on Foundations of Computer Science (FOCS 1977)*, 222--27.


<!-- lean-links -->
<!-- /lean-links -->
<!-- /passage:sec-references -->

## Notes

<!-- passage:sec-notes -->

<a id="fn-and"></a>**1.** For AND on the equally likely inputs $01,10,11$, one query has optimal success $2/3$. Reading the first bit and stopping only when it is zero succeeds with probability one conditional on using one read. The [worked exposition](/library/quartic/exposition/) explains why this does not contradict the one-query bound. [↩](#fnref-and)
<!-- /passage:sec-notes -->


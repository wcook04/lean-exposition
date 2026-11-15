# Constant-query verification by algebraic encoding

*A specialist reconstruction of the algebraic PCP proof of Amireddy, Behera, Srinivasan, Sudan and Willumsgaard, following Troy Lee's formalization*

## Abstract

<!-- passage:pcp-short-abstract -->
The PCP theorem gives every language in NP a polynomial-time verifier with logarithmic randomness, constantly many proof-bit queries, perfect completeness and soundness error at most one half. We explain the algebraic construction of Amireddy, Behera, Srinivasan, Sudan and Willumsgaard through Troy Lee's formalization. Degree reduction keeps encoded line restrictions polynomial in size; Hadamard words make the required observations available as bit queries. The soundness argument chooses four nearby polynomials and forces them to satisfy the colouring constraints together. Its main difficulty is correction at prescribed certificate points, where average proximity alone gives no control. We derive the rejection-dependent correction bound and its use in the seven-check verifier, taking the underlying low-degree testing theorems as stated inputs. The resource bounds follow the formal variant, including its sampling conventions and query counts.
<!-- /passage:pcp-short-abstract -->

## 1. The theorem and the encoding problem

<!-- passage:pcp-short-theorem -->
**Theorem (PCP).** For every language $L\subseteq\{0,1\}^{*}$ in NP, there are a polynomial-time verifier $V$, natural numbers $a,b,q_0$, and a polynomial $p\in\mathbb N[X]$ with the following properties. On an input $x$ of length $n$, the verifier uses exactly

$$
a\lceil\log_2(n+2)\rceil+b
$$

fair random bits, makes at most $q_0$ proof-bit queries on every run, and reads only addresses below $p(n)$. If $x\in L$, there is one proof accepted for every random seed. If $x\notin L$, every proof is accepted with probability at most $1/2$.

The verifier, implementation, constants and polynomial are fixed for $L$ before the input is chosen. A proof may depend on $x$, but it is fixed before the random seed. Conversely, every language admitting such a verifier lies in NP. Thus, with the usual resource notation,

$$
\mathrm{NP}=\mathrm{PCP}(O(\log n),O(1)).
$$

Arora–Lund–Motwani–Sudan–Szegedy [3] proved the constant-query theorem, building on Arora–Safra [2]. We consider the algebraic proof in the corrected version of [1], as implemented by Lee [5]. The cost of reading a field value is already an obstacle in the usual point-versus-line test: a field value takes several bits, and a line polynomial's coefficient vector takes its degree times as many. Treating either object as one oracle symbol does not prove constant **bit** query complexity.

Proof size constrains the encoding as well. Applying the binary encoding directly to a growing line-coefficient vector can require quasipolynomially many bits. The construction first reduces the degree, then applies the binary encoding to individual field values.

A base-$b$ digit expansion turns a line polynomial of degree strictly below $b^c$ into a degree-$c$ polynomial in $cb$ variables. Here $c$ is fixed while $b$ grows. A Hadamard word then makes a binary observation of a field value accessible in one query. Testing and locally correcting the encoded line recovers the required homogeneous binary observation of its value at the digit-substitution point despite errors. These operations suffice to verify the polynomial constraints. An auxiliary line oracle remains part of the proof, but the verifier's acceptance computation is not recursively re-encoded through repeated PCP composition [1, §1].

Low rejection in the four low-degree tests supplies four polynomials close to the received tables. We fix these witnesses and use a difference check and two certificate checks to force a proper colouring. The certificate checks request values at special points. Section 5 derives the correction bound needed there; Section 6 uses it to constrain the same four witnesses simultaneously.

The [full argument](../long/reasoning-record.md) proves the testing results and explains the machine reductions used here. The [worked exposition](../expository/main.md) follows the construction through finite examples.
<!-- /passage:pcp-short-theorem -->

## 2. Four polynomials and seven checks

<!-- passage:pcp-short-colour-constraints -->
Let $F$ be a field of characteristic two, of cardinality $q$, containing a primitive cube root of unity $\omega$. Represent the three colours by

$$
\mathcal C=\{1,\omega,\omega^2\}.
$$

For $u,v\in\mathcal C$, their difference satisfies $(u-v)^4=u-v$. Hence $u\ne v$ exactly when $(u-v)^3=1$.

Choose a nonempty grid $H^m\subseteq F^m$ large enough to hold the graph's $N$ vertices, adding isolated vertices at unused grid points. Write $h=|H|$. Coordinatewise interpolation gives a colour extension $P$ of degree at most $d_0=m(h-1)$, and a public polynomial $E$ of degree at most $2d_0$ on pairs of grid points. On the grid, $E$ is one on edges of the padded graph and zero elsewhere.

Set

$$
\begin{aligned}
Q_P(X,Y)&=P(X)-P(Y),\\
A_P(X)&=P(X)^3-1,\\
B_P(X,Y)&=E(X,Y)\bigl(Q_P(X,Y)^3-1\bigr).
\end{aligned}
\tag{1}
$$

An honest colouring makes $A_P$ vanish on $H^m$ and $B_P$ vanish on $H^{2m}$. Conversely, these vanishing conditions recover a proper colouring: the first restricts every vertex to the three allowed values, and the second separates the values across each edge. Both are needed. For example, assigning the four elements of $\mathbb F_4$ to $K_4$ satisfies every edge equation, since every nonzero field element has cube one; the vertex assigned zero fails the vertex equation. The degree bounds in (1) are $d_0,3d_0,5d_0$.

To certify vanishing on a grid, put $Z_H(T)=\prod_{u\in H}(T-u)$. Repeated monic division in the separate coordinates shows that a polynomial $A$ vanishes on $H^k$ precisely when [1, Lemma 2.9]

$$
A(X)=\sum_{i=1}^{k} Z_H(X_i)U_i(X).
$$

The remainder has degree below $h$ in every variable; if it vanishes on the grid, interpolation makes it zero. Packing the quotients into

$$
M(X,Y)=\sum_iY_iU_i(X)
$$

gives the two polynomial identities

$$
M(X,0)=0,\qquad M(X,Z_H(X))=A(X).
\tag{2}
$$

Here $Z_H$ is applied coordinatewise. Each nonzero quotient has degree at most $\deg A-h$, so $Y_iU_i$ has degree at most $\deg A$ because $h\ge1$. Thus $M$ has that degree bound too. The converse in (2) holds even for a proposed certificate nonlinear in $Y$: on the grid its two second arguments coincide.
<!-- /passage:pcp-short-colour-constraints -->

<!-- passage:pcp-short-proof-inventory -->
The received proof consists of eight arbitrary binary tables. Their intended honest contents are

| Primary table | Intended polynomial | Point domain | Label degree |
| --- | --- | --- | --- |
| $f_P$ | Colour extension $P$ | $F^m$ | $3$ |
| $f_Q$ | Difference $Q_P(X,Y)$ | $F^{2m}$ | $3$ |
| $f_A$ | Vertex certificate $M_A$ | $F^{2m}$ | $1$ |
| $f_B$ | Edge certificate $M_B$ | $F^{4m}$ | $1$ |

Each primary table has an auxiliary table encoding its restrictions to lines. The descriptions above specify the honest proof; received tables may contain arbitrary bits.

A primary address consists of a point and a label. A label in $\mathcal B_r$ is a squarefree Boolean polynomial of degree at most $r$ in the binary coordinates of a field value; the stored bit is its evaluation (Section 3). If a primary table has point domain $F^k$, its auxiliary table is indexed by an oriented line $(u,v)\in F^k\times F^k$; the row for that line has type

$$
h_{u,v}:F^{cb}\times\mathcal B_1\longrightarrow\mathbb F_2.
$$

Here $b$ is the digit base, $c$ the fixed inner degree, and $\mathcal B_1$ the affine label space. Honest rows encode the digit-transformed line restriction at the inner point; the label selects one bit of that field value. The verifier also computes the public adjacency polynomial $E$ from the graph.

One run accepts only if all seven checks pass: four low-degree checks on these primary/auxiliary pairs, two checks of the grid certificates, and a comparison of the received difference bit with the sum of the two received colour bits. Each branch uses its prescribed independent seed. The certificate corrections use the same received auxiliary tables as the low-degree checks. We will justify these operations before proving their joint soundness.
<!-- /passage:pcp-short-proof-inventory -->

## 3. Why two encodings are needed

<!-- passage:pcp-short-digit-encoding -->
Fix positive integers $b,c$, and consider a univariate polynomial $T(Y)=\sum_{j<b^c}t_jY^j$. Write $j=\sum_{i=0}^{c-1}j_ib^i$, where $0\le j_i<b$, and introduce $cb$ variables $X_{i,s}$. The set-multilinear encoding of [1, Definition 3.1 and Claim 3.2] is

$$
\Psi(T)=\sum_{j<b^c}t_j\prod_{i=0}^{c-1}X_{i,j_i},
\qquad
\Phi(z)_{i,s}=z^{s b^i}.
\tag{3}
$$

Every monomial of $\Psi(T)$ uses one variable from each of $c$ groups, so the polynomial has total degree at most $c$. Substitution recovers the original evaluation:

$$
\Psi(T)(\Phi(z))
=\sum_{j<b^c}t_jz^{\sum_i j_i b^i}=T(z).
\tag{4}
$$

An honest line table consists of these encodings. In the soundness proof, we choose a polynomial $U$ of degree at most $c$ close to the received row; it need not have the set-multilinear form in (3). Nevertheless,

$$
T_U(Y)=U(\Phi(Y)),\qquad \deg T_U\le D:=cb^c.
\tag{5}
$$

Indeed, a monomial of $U$ has at most $c$ variable occurrences, and each substituted variable has degree at most $b^c$. The honest prover encodes polynomials of degree strictly below $b^c$; decoding gives only the bound $D$. The field size must accommodate this larger bound.
<!-- /passage:pcp-short-digit-encoding -->

<!-- passage:pcp-short-hadamard-encoding -->
Fix a linear isomorphism $\rho:F\to\mathbb F_2^t$, where $q=2^t$. Let $\mathcal B_r$ be the binary vector space of squarefree Boolean polynomials in $t$ variables of degree at most $r$. For $r\ge1$, encode $u\in F$ by [1, Definitions 3.5–3.6]

$$
\mathcal H_r(u)(R)=R(\rho(u)),\qquad R\in\mathcal B_r.
\tag{6}
$$

A label $R$ is an address within the row; the stored bit is $R(\rho(u))$. The label degree $r$ is independent of the degree of the field polynomial whose values are encoded. The word has $2^{\sum_{j=0}^{\min(r,t)}\binom tj}$ bits. Distinct field values disagree on exactly half its positions: adding a coordinate label on which the values differ pairs agreeing labels with disagreeing ones. The same argument applies to homogeneous linear labels $L:F\to\mathbb F_2$. Consequently, for field-valued functions $f,g$,

$$
\Delta(\mathcal H_r(f),\mathcal H_r(g))=\tfrac12\Delta(f,g),
\tag{7}
$$

where both distances use the same finite point domain. The encoded distance also averages over a label domain, which may be either all labels or homogeneous linear labels. Throughout, $\Delta$ and all probabilities are uniform finite averages over the indicated domains.

Identify affine binary labels with maps $L:F\to\mathbb F_2$ through $\rho$. Higher-degree labels permit nonlinear field checks. Multiplication in $F$ is bilinear in binary coordinates. If $A\in F[Y]$ has degree at most $r$ and $L$ is such an affine label, squarefree reduction produces a label $\Lambda_{A,L}\in\mathcal B_r$ such that

$$
L(A(u))=\mathcal H_r(u)(\Lambda_{A,L}).
\tag{8}
$$

Cubic labels suffice for the constraints in (1). To take a weighted sum of field values, the verifier uses homogeneous linear labels: their constant term is zero, so they preserve sums. The scalar multiple $\eta u$ is observed by relabelling $L$ as $L\circ(\eta\cdot)$; for $\eta\ne0$ this permutes the homogeneous labels.

A corrupted word can be wrong at every label produced by a special substitution. For any requested label $Q$, use the two-query answer

$$
\operatorname{SC}_w(Q;R)=w(Q+R)-w(R),
\tag{9}
$$

where $R$ is a fresh uniform full label. If $w$ is $\epsilon$-close to a linear functional $\ell$ on labels, (9) differs from $\ell(Q)$ with probability at most $2\epsilon$, for every fixed $Q$: both read positions are individually uniform. Evaluation words are linear functionals on labels, so this observation will justify the derived cubic reads without any assumption that the relabelling in (8) preserves uniformity.

The three label domains have different roles:

| Domain | Form of a label | Role in the proof |
| --- | --- | --- |
| Full $\mathcal B_r$ | Any squarefree polynomial of degree at most $r$ | Fresh masks for requested nonlinear observations; full-table proximity |
| Affine $\mathcal B_1$ | $\alpha+\lambda\cdot z$ | Row consistency bridges full-label decoding to the homogeneous restriction |
| Homogeneous linear | $\lambda\cdot z$ | Sum-preserving comparisons and the half-distance identity |

Full-label proximity does not by itself control the homogeneous restriction. The decoding result below supplies both bounds for the same field value or polynomial.
<!-- /passage:pcp-short-hadamard-encoding -->

## 4. What the low-degree tests supply

<!-- passage:pcp-short-weighted-test -->
The inner polynomial has constant degree $c$. Assume $q>2c$, take a generator $\zeta$ of the full group $F^\times$, and let

$$
a_i=\zeta^i,\qquad
\eta_i=\prod_{j\ne i}\frac{-a_j}{a_i-a_j}
\quad(1\le i\le c+1).
$$

The nodes and weights are nonzero. Lagrange interpolation gives, for every degree-at-most-$c$ polynomial,

$$
f(u)=\sum_{i=1}^{c+1}\eta_i f(u+a_iv).
\tag{10}
$$

We use two precise guarantees of this weighted test. Exact satisfaction for every $u,v$ characterizes total degree at most $c$. If uniform $(u,v)$ violates it with probability $\delta<1/[2(c+2)^2]$, one degree-at-most-$c$ polynomial is within $2\delta$ of $f$. The plurality correction $g$ additionally satisfies the pointwise estimate

$$
\Pr_v\left[\sum_i\eta_i f(x+a_iv)\ne g(x)\right]
\le2(c+1)\delta\quad\text{for every }x.
$$

The [weighted proof](../long/reasoning-record.md#2-the-corrected-short-low-degree-test) derives the pointwise estimate and the three losses $2(c+1)\delta$, $(c+1)\delta$, and $2(c+1)^2\delta$ that force exact satisfaction. It also gives the full-generator argument and the application of Friedl–Sudan [9, Lemma 4]: in characteristic two, $q>2c$ implies the sufficient condition $q/2-1\ge c$. Rubinfeld–Sudan [7, §4] provide the robust-characterization antecedent; Kaufman–Sudan [8, Theorem 2.9] give a general theorem for linear-invariant families with a two-ary independent local formal characterization. The explicit constants here follow Lee's implementation. Appendix A explains why the weights and full generator in corrected [1] matter.
<!-- /passage:pcp-short-weighted-test -->

<!-- passage:pcp-short-binary-decoding -->
The binary row tester conjoins BLR additivity [4], unit preservation, the implemented product checks and consistency on affine labels. Its soundness contract is this: from any received row $w:\mathcal B_r\to\mathbb F_2$, choose one field value with both full-label and homogeneous-label error at most $28$ times row rejection. This choice is made in the soundness proof; the verifier only runs local tests.

The restriction to homogeneous labels requires a separate deduction. In a row with rejection $\epsilon<1/28$, the characteristic-two linearity estimate [6, Theorem 1.2; 1, Theorem B.1] and the unit/product checks supply an evaluation functional with full-label error at most $\epsilon$. Affine consistency costs at most $\epsilon$ for its check and $2\epsilon$ for masking, so the same value has affine error at most $3\epsilon$. Homogeneous labels occupy half of that affine domain, giving error at most $6\epsilon$. If $\epsilon\ge1/28$, choose any value and use $1\le28\epsilon$. The [complete row proof](../long/reasoning-record.md#testing-a-received-hadamard-word) proves evaluation structure and all these estimates.

The implemented tester retains product checks at every degree from two to $r$, sharing read values. Its query bound is $2r+4$, hence ten for cubic labels. The v2 algorithm uses only the top-degree product check and has eight queries. All query bounds here include the implementation's extra checks.

For a received inner table $w:F^{cb}\times\mathcal B_r\to\mathbb F_2$, the binary polynomial tester flips a fair coin between the row test at a uniform inner point and a homogeneous binary observation of (10) at uniform $u,v,L$. If its rejection is $\kappa$, each branch rejects with probability at most $2\kappa$. Row decoding, the weighted theorem and the half-distance identity give one polynomial $U$ of total degree at most $c$ with

$$
\Delta_{\rm full}(w,\mathcal H_r(U)),\quad
\Delta_{\rm hom}(w,\mathcal H_r(U))\le K\kappa,
\qquad K=4(c+2)^2\bigl(112(c+2)+60\bigr).
\tag{11}
$$

Under the field and node assumptions above, every received inner table has one polynomial $U$ of total degree at most $c$ whose full-label and homogeneous-label distances are each at most $K$ times the tester's rejection probability. There is no small-rejection premise: the proof uses the trivial distance bound outside the weighted theorem's small-error regime. The [binary low-degree proof](../long/reasoning-record.md#a-binary-version-of-the-weighted-low-degree-test) gives the branch calculation.
<!-- /passage:pcp-short-binary-decoding -->

<!-- passage:pcp-short-outer-decoding -->
The outer test has a primary table $f(x,R)$ and an auxiliary row $h_{u,v}$ for each oriented line $u+Yv$. Choose uniform $u,v,z$ (including $z=0$), a uniform homogeneous label $L$, an inner correction direction, and independent tester seeds. Require all three checks to pass:

1. The Hadamard test on the primary row $f(u,\cdot)$.
2. The inner binary polynomial test on $h_{u,v}$.
3. Equality between $f(u+zv,L)$ and the inner correction of that same row $h_{u,v}$ at $\Phi(z)$ with label $L$.

The auxiliary row in the second and third checks belongs to the same sampled pair $(u,v)$.

The inner corrector uses (10) without a separate query at its centre (the sampled direction may be zero). At a prescribed inner point $a$, it sums the $c+1$ weighted observations at $a+a_iv$. For a received row of homogeneous error $\tau$, its wrong-answer probability is at most $(c+1)\tau$, averaged over the uniform direction and homogeneous label. Each point and weighted label is uniform, even though the requested centre need not be. This is why a direct query at $\Phi(z)$ can be replaced safely.

Suppose the outer test rejects with probability $\kappa$. By the primary Hadamard bound, choose one field function $g$ with both binary errors at most $28\kappa$. Decode each auxiliary row using (11) and substitute (3) to obtain a line polynomial $T_{u,v}$ of degree at most $D=cb^c$. Replacing the corrected auxiliary answer costs at most $(c+1)K\kappa$, the tested comparison fails on at most $\kappa$, and replacing the primary answer costs at most $28\kappa$. The half-distance identity (7) therefore gives

$$
\Pr_{u,v,z}[T_{u,v}(z)\ne g(u+zv)]
\le J\kappa,
\qquad J=2\bigl((c+1)K+29\bigr).
\tag{12}
$$

The factor two is exactly (7). No polynomial consistency among different auxiliary rows has been assumed.

We import the following point-versus-line contract. Suppose

$$
q\ge10^6D^3,\qquad \theta\le\frac1{4\cdot10^6},
$$

and arbitrary degree-at-most-$D$ line polynomials disagree with a point function on a fraction $\theta$ of uniform triples $(u,v,z)$. Then the point function is within $2\theta$ of one polynomial of total degree at most $D$. The line table includes all oriented pairs, zero directions, and all parameters $z\in F$; consistency between different parametrizations is not an input assumption.

This is Lee's explicit variant of [3, Theorem 45]. Its [bivariate agreement proof](../long/reasoning-record.md#4-bivariate-agreement) follows the method of [2, §5.2] and [3, Appendix A]; the [point-versus-line proof](../long/reasoning-record.md#5-point-versus-line-soundness) supplies the stated constants and zero-slice estimates.

Applying this theorem to (12) and encoding the resulting field distance yields one polynomial $P$ of degree at most $D$ such that

$$
\Delta_{\rm full}(f,\mathcal H_r(P)),\quad
\Delta_{\rm hom}(f,\mathcal H_r(P))
\le S\kappa,
\qquad S=28+J,
\tag{13}
$$

provided $J\kappa\le1/(4\cdot10^6)$. The restricted conclusion is for homogeneous linear labels. The stronger affine-label conclusion stated for the corresponding tester in [1] is not needed here. For a certificate whose full label domain is already degree one, the first bound in (13) also controls its affine labels.
<!-- /passage:pcp-short-outer-decoding -->

## 5. Correcting the nonuniform certificate queries

<!-- passage:pcp-short-outer-correction -->
The points $(x,0)$ and $(x,Z_H(x))$ in (2) occupy special subsets of the certificate's domain. Even a table with tiny average error could be wrong at all these points. The verifier must correct each requested value before using the certificate identities.

A low-degree test averages over the auxiliary anchor as well as its direction. It need not control the rows at one prescribed anchor, so the corrector tests its selected row again.

Fix a target $a$ and choose a uniform homogeneous label $L$. Sample a direction $v$, a nonzero uniform $z\in F^\times$, a separate uniform inner correction direction, and an independent inner-test seed. Test the auxiliary row $h_{a,v}$. Correct that row at $\Phi(z)$ and compare the answer with $f(a+zv,L)$. Reject if the test or comparison fails; otherwise return the correction at $\Phi(0)$. The two corrections use the same inner direction and label. The output is one bit or rejection, with at most $3c+9$ proof-bit reads. Exact primary and auxiliary tables for a polynomial of degree strictly below $b^c$ return $L(P(a))$ for every seed.

Let the primary table be within homogeneous distance $\delta$ of a degree-$D$ polynomial $P$, where $D\ge cb^c$. Denote by $R_a$ the actual rejection probability of this corrector at $a$. Its probability of rejection **or** a wrong returned bit satisfies

$$
\Pr[\text{failure at }a]
\le C R_a+\delta+\frac{D}{2(q-1)},
\qquad C=2+2(c+1)K.
\tag{14}
$$

Decode each auxiliary row by (11), and let $T_v$ be its decoded line polynomial. Inner-test failure forces rejection, so the average decoding error is at most $KR_a$. Put $e=(c+1)KR_a$; each corrected auxiliary answer can be replaced by $L(T_v(\cdot))$ at cost at most $e$.

If $T_v(0)\ne P(a)$, the difference $T_v(Y)-P(a+Yv)$ is a nonzero polynomial of degree at most $D$. Among the $q-1$ nonzero parameters it has at most $D$ roots. Applying the half-distance identity gives

$$
\Pr_{v,L}[L(T_v(0))\ne L(P(a))]
\le \Pr_{v,z,L}[L(T_v(z))\ne L(P(a+zv))]
+\frac{D}{2(q-1)}.
$$

At the sampled point, replacing the auxiliary correction, using the tested comparison, and replacing the primary bit cost at most $e$, $R_a$ and $\delta$. The last bound holds because $a+zv$ is uniform for each nonzero $z$. At the origin, replacing the decoded bit by the actual correction costs another $e$; including rejection costs another $R_a$. The total is $2e+2R_a+\delta+D/[2(q-1)]$, which is (14).

This statement allows an arbitrary auxiliary table. Such a table may cause frequent rejection; (14) says that a corrector which seldom rejects cannot often return the wrong bit. It holds at every target, averaged over the random homogeneous label, and is therefore usable at the nonuniform targets in (2). The [full correction proof](../long/reasoning-record.md#correcting-an-outer-value-at-a-prescribed-point) makes these quantifiers explicit.
<!-- /passage:pcp-short-outer-correction -->

<!-- passage:pcp-short-zero -->
Now suppose $A$ and a proposed certificate $M$ have degree at most $D$, but $A$ fails to vanish on $H^k$. At least one residual in (2) is a nonzero polynomial; after substituting $Z_H$, its degree is at most $Dh$. The polynomial root bound shows that a uniform $x$ violates at least one field identity with probability at least $1-Dh/q$. A random homogeneous label detects a nonzero residual with probability $1/2$, so the ideal binary check rejects with probability at least

$$
\frac{1-Dh/q}{2}.
$$

The actual ZERO check samples one $x,L$ and reads a primary bit $a_{\rm bit}$. With the same $x,L$ and independent remaining seeds, its certificate corrections at $(x,0)$ and $(x,Z_H(x))$ return $b_0,b_Z$ or reject. ZERO accepts precisely when neither call rejects, $b_0=0$, and $b_Z=a_{\rm bit}$. A single nonzero residual suffices for the ideal lower bound; independence of the two detections is unnecessary.

Let its rejection be $\kappa$, and let $\delta_A,\delta_M$ be the homogeneous distances of the primary and certificate tables from their respective polynomial encodings. Each correction's rejection event is contained in ZERO rejection. This bounds its rejection after averaging over the targets requested by ZERO; it need not bound rejection at every fixed target. Coupling the ideal and actual tests and using (14) twice gives

$$
\frac{1-Dh/q}{2}
\le(1+2C)\kappa+\delta_A+2\delta_M+\frac{D}{q-1}.
\tag{15}
$$

Thus small observed rejection forces the decoded polynomial to vanish on the grid, once the error terms are below the left side.

For (1), the primary constraint bit is produced from a cubic-encoded colour or difference row using (8) and the fresh mask in (9). Write $\epsilon_x$ for the full-label error in the received row at $x$. Conditional on this point, replacing the derived read costs at most $2\epsilon_x$, for every requested label. Since ZERO samples $x$ uniformly, the total loss is at most $2\mathbb E_x\epsilon_x\le2\epsilon$, where $\epsilon$ is the full-table error bound supplied by (13). The downstream rejection probability therefore changes by at most $2\epsilon$. In (15) the ideal primary distance is then zero and the rejection term becomes $\kappa+2\epsilon$:

$$
\frac{1-Dh/q}{2}
\le(1+2C)(\kappa+2\epsilon)+2\delta_M+\frac{D}{q-1}.
\tag{16}
$$

The factor $1+2C$ multiplies the derived-read error because that error enters through rejection. The argument averages over the actual fresh randomness; it does not select a favourable fixed mask and treat it as a deterministic oracle. See the [full ZERO analysis](../long/reasoning-record.md#checking-that-a-polynomial-vanishes-on-a-grid).
<!-- /passage:pcp-short-zero -->

## 6. One decoding for all seven checks

<!-- passage:pcp-short-assembly -->
For the eight arbitrary tables introduced in Section 2, the received-bit difference check is

$$
f_Q((x,y),L)=f_P(x,L)+f_P(y,L).
\tag{17}
$$

Fix the received proof. If the whole verifier rejects with probability $\kappa$, each of its seven branches rejects with probability at most $\kappa$, because acceptance is conjunctive.

Assume $q\ge10^6D^3$, $q\ge100Dh$ and $m(h-1)\le D$. When $J\kappa\le1/(4\cdot10^6)$, apply (13) to each of the four low-degree tests and choose polynomials $P,Q,M_A,M_B$ of degree at most $D$, each with the appropriate errors at most $\epsilon=S\kappa$. Fix these choices. In (17), replacing the three received bits by the decoded bits costs at most $3\epsilon$. If $Q$ differed from $P(X)-P(Y)$, their nonzero polynomial difference would have relative support at least $1-D/q$. Equation (7) would make the ideal check reject on at least half that fraction. Hence

$$
\kappa+3\epsilon<\frac{1-D/q}{2}
\tag{18}
$$

forces the polynomial identity $Q=P(X)-P(Y)$.

The decoded vertex and edge constraints now have degree at most $3D$ and $5D$: the public adjacency extension has degree at most $2D$. Use $5D$ as a common bound in (16). If either constraint failed to vanish on its grid, it would imply

$$
\frac{1-5Dh/q}{2}
\le(1+2C)(\kappa+2\epsilon)+2\epsilon+\frac{5D}{q-1}.
\tag{19}
$$

All constants $J,S,C$ depend only on fixed $c$. For a sufficiently small positive constant $g_c$, every $\kappa<g_c$ satisfies the low-degree threshold, (18), and the strict reverse of (19). For example, put

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

The field bound gives $5Dh/q\le1/4$ and $5D/(q-1)\le1/8$. The error depending on $\kappa$ in (19) is below $1/16$, so its right side is below $3/16$ and its left side is at least $3/8$. Thus both constraints vanish, and (1) recovers a proper colouring. Contrapositively, every proof for a non-three-colourable graph is rejected with probability at least $g_c$.

For completeness, start with a proper colouring, its exact interpolants and exact certificates, and the honest encoded line restrictions. If their degrees are below $b^c$, every component test accepts for every seed. This supplies one fixed eight-table proof with perfect completeness. The soundness argument used the same four decoded polynomials throughout; separate existential decodings for each later check would not suffice.
<!-- /passage:pcp-short-assembly -->

## 7. Resources, implementation and the reverse inclusion

<!-- passage:pcp-short-resources -->
Take $c=4$. For a graph on $N$ vertices, let $a\ge2$ be least with $\lceil\log_2N\rceil\le a2^a$, with natural-number ceiling log equal to zero at $N=0,1$. Set

$$
s=2^a,\qquad m=b=h=s,\qquad
t=12a+32,\qquad q=2^t=2^{32}s^{12}.
\tag{21}
$$

The grid contains $s^s=2^{a2^a}\ge N$ points. Also $D=4s^4$ and

$$
10^6D^3=64\cdot10^6s^{12}\le q,
\qquad100Dh\le q.
$$

Since $s\ge4$, the honest degrees satisfy $5s(s-1)<s^4=b^c$. The extension degree $t$ is divisible by four, so the field has the required cube roots. Minimality of $a$ gives

$$
a2^a\le32(\lceil\log_2N\rceil+1).
\tag{22}
$$

Equation (22) bounds the randomness and proof addresses. Field vectors in the query and seed spaces use $O(st)=O(a2^a)$ bits; constant-degree label vectors use $O(t^3)=O(a2^a)$ bits: $t=12a+32=O(a)$, and $a^2/2^a$ is bounded for integers $a\ge2$. There are only a fixed number of such vectors. Thus the seed length is $O(\log N)$ and the table address spaces have size $2^{O(a2^a)}=N^{O(1)}$, with the harmless small-$N$ convention included.

Four corrector parameters were sampled from $F^\times$. For an exact fixed fair-bit sampler, the implementation samples all four from $F$ and accepts immediately if any is zero. Conditional on all being nonzero, the seed distribution is precisely the one analysed above. Rejection is multiplied by $((q-1)/q)^4\ge1/16$. All other random coordinates are encoded bijectively by fixed-length bit strings.

For one unamplified run, the query bounds are

| Check | Bound |
| --- | ---: |
| Colour and difference low-degree tests | $2c+18$ each |
| Two certificate low-degree tests | $2c+14$ each |
| Two derived ZERO tests | $6c+20$ each |
| Difference check | $3$ |

Their sum bounds the run by at most $20c+107=187$ proof-bit reads, including both reads of each fresh derived answer. Some seeds accept without querying. After fair-bit sampling the rejection gap is at least $g_c/16$. Repeating independently a constant number of times against the same fixed proof reduces soundness error to at most $1/2$, preserving logarithmic randomness and constant query complexity. The [exact parameter and gap calculations](../long/reasoning-record.md#parameters-for-every-finite-graph) and [repetition proof](../long/reasoning-record.md#repetition-on-one-fixed-proof) give the numerical bounds. They establish existence, not a practical verifier.
<!-- /passage:pcp-short-resources -->

<!-- passage:pcp-short-complexity -->
The operations behind these queries are polynomial-time computations. The formal implementation constructs the field through a computed irreducible polynomial and obtains generators and cube roots by bounded search. These searches are polynomial in $q$, which is polynomially bounded in the input length. The public adjacency extension, label substitutions, seed codecs and packed proof addresses are computed explicitly. The program producing the queries and verdict is compiled into Mathlib's finite multi-stack machine model with a polynomial cost bound; constant query complexity alone would not establish this runtime statement.

For a fixed NP language, a bounded accepting computation tableau gives a finite constraint system of fixed arity. One-hot coding, Boolean clauses and three-colouring gadgets yield an executable polynomial-time reduction to a graph of polynomial encoded size. Composing this reduction with the amplified verifier preserves constant queries and polynomial proof length. If the reduction has output bound $p(n)$, then

$$
\lceil\log_2(p(n)+2)\rceil
\le (\deg p)\lceil\log_2(n+2)\rceil
+\lceil\log_2(p(1)+2)\rceil.
$$

Padding the random string to the resulting fixed canonical length preserves its prefix distribution. This gives the exact quantifier order and randomness format in the theorem. The long record separates the [machine implementation](../long/reasoning-record.md#the-polynomial-time-implementation), [graph reduction](../long/reasoning-record.md#from-every-np-verifier-to-a-graph), and [transport of the resource bounds](../long/reasoning-record.md#transporting-the-verifier-through-the-reduction).

For the converse, guess the first $p(n)$ proof bits and simulate the verifier on every random string. There are at most $2^b(2(n+2))^a$ such strings, and each simulation takes polynomial time. Perfect completeness gives a prefix for which every run accepts. If a prefix were accepted for a no-instance, its zero extension would be a fixed proof with acceptance probability one, contradicting soundness. Thus this finite witness relation is an NP relation, completing the equality in the theorem.
<!-- /passage:pcp-short-complexity -->

## Formal correspondence and credits

<!-- passage:pcp-short-formal-correspondence -->
Using Lean, Lee proved the [forward PCP theorem][lean-forward] with an implemented verifier in a concrete finite-machine model, and the [reverse inclusion in that model][lean-reverse]. Explicit machine simulations identify the concrete witness class with [the NP class in the unchanged vendored ComplexityLib][lean-reference-np]. Our quantitative statements follow his [encoded-line decoding theorem][lean-line], [local-correction guarantee][lean-correction] and [assembled three-colouring argument][lean-assembly]. They retain the homogeneous-label guarantee, whole-field outer sampling, independent branch seeds and ten-query cubic Hadamard test of that implementation. The separate [source and verification account](../long/reasoning-record.md#source-and-verification-account) records the exact source revision, theorem definitions and validation evidence. The old-test calculation in Appendix A is an ordinary mathematical explanation, not an additional formal theorem.

This account was prepared by Will Cook with AI assistance. The PCP construction follows Amireddy, Behera, Srinivasan, Sudan and Willumsgaard. It combines their set-multilinear form of inverse-Kronecker degree reduction with the established low-degree Hadamard encoding. The formal proof is due to Troy Lee. The corrected paper acknowledges Lee's identification of the earlier low-degree-test error. This explanatory reconstruction claims no new PCP theorem.
<!-- /passage:pcp-short-formal-correspondence -->

## Appendix A. Why the corrected weighted test matters

<!-- passage:pcp-short-old-test-counterexample -->
The weights and full generator are the correction in [1, v2, Fact 2.7 and Lemma 3.3]. The old unit-weight test fails even over arbitrarily large fields. For $q=2^{2k}$, $k\ge2$, take an element $\omega$ of order three and, in dimension $m\ge1$, put $f(x)=x_1^4$. In characteristic two,

$$
f(u)+\sum_{i=1}^3f(u+\omega^iv)
=4u_1^4+v_1^4\sum_{i=1}^3\omega^{4i}=0
$$

for every $u,v$. Yet every polynomial of total degree at most two agrees with $f$ on at most a fraction $4/q$ of $F^m$: fixing the other coordinates leaves a nonzero degree-four difference in $x_1$. Thus enlarging the field cannot repair the earlier test. Corrected [1] credits Lee with identifying the error. This calculation concerns that scalar test; it is not a cheating proof against all checks of the final verifier.
<!-- /passage:pcp-short-old-test-counterexample -->

## References

1. Prashanth Amireddy, Amik Raj Behera, Srikanth Srinivasan, Madhu Sudan and Sophus Valentin Willumsgaard. *A Simple Algebraic Proof of the PCP Theorem*. [arXiv:2608.17429v2](https://arxiv.org/abs/2608.17429v2), 22 October 2026. The earlier test discussed in Appendix A is in [v1](https://arxiv.org/abs/2608.17429v1), Fact 2.7 and Lemma 3.3; the current construction uses v2.
2. Sanjeev Arora and Shmuel Safra. *Probabilistic Checking of Proofs: A New Characterization of NP*. Journal of the ACM **45**(1), 70–122, 1998. [Journal text](https://www.cs.umd.edu/~gasarch/TOPICS/pcp/AS.pdf). The bivariate agreement construction is in §5.2.
3. Sanjeev Arora, Carsten Lund, Rajeev Motwani, Madhu Sudan and Mario Szegedy. *Proof Verification and the Hardness of Approximation Problems*. Journal of the ACM **45**(3), 1998. [Author-hosted manuscript](https://people.seas.harvard.edu/~madhusudan/papers/1992/almss-journ.pdf), especially Theorems 45 and 69 in that manuscript's numbering.
4. Manuel Blum, Michael Luby and Ronitt Rubinfeld. *Self-Testing/Correcting with Applications to Numerical Problems*. Journal of Computer and System Sciences **47**(3), 549–595, 1993. [Author-hosted manuscript](https://people.csail.mit.edu/ronitt/papers/selftestcorrect.pdf).
5. Troy Lee. *Formalization of the PCP theorem*. [Source and mathematical guide](https://github.com/troyjlee/tcs-formalizations/tree/a0ce13ed0fa264f051c1278e039596ce65557fa4/docs/pcp).
6. Mihir Bellare, Don Coppersmith, Johan Håstad, Marcos Kiwi and Madhu Sudan. *Linearity Testing in Characteristic Two*. IEEE Transactions on Information Theory **42**(6), 1781–1795, 1996. [Author-hosted manuscript](https://www.csc.kth.se/tcs/projects/publications/bchks.pdf), Theorem 1.2.
7. Ronitt Rubinfeld and Madhu Sudan. *Robust Characterizations of Polynomials with Applications to Program Testing*. SIAM Journal on Computing **25**(2), 252–271, 1996. [Prepublication manuscript](https://www.cs.princeton.edu/courses/archive/spring04/cos598B/bib/RubinfeldS.pdf), §4, Theorem 5; cited as Theorem 4.1 of the published paper in [1, §3.2].
8. Tali Kaufman and Madhu Sudan. *Algebraic Property Testing: The Role of Invariance*. STOC 2008, 403–412. [Conference manuscript](https://people.csail.mit.edu/madhu/papers/2007/apt-conf.pdf), Theorem 2.9.
9. Katalin Friedl and Madhu Sudan. *Some Improvements to Total Degree Tests*. Proceedings of the Third Israel Symposium on Theory of Computing and Systems, 1995. [Corrected manuscript, arXiv:1307.3975v1](https://arxiv.org/abs/1307.3975v1), Lemma 4.

[lean-forward]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Theorem.lean#L24-L35
[lean-reverse]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/ReverseConcrete.lean#L33-L39
[lean-reference-np]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Complexity/ReferenceNPConverse.lean#L39-L41
[lean-line]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/EncodedLineLowDegreeSoundness.lean#L325-L339
[lean-correction]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/BinaryLocalCorrectionSoundness.lean#L222-L236
[lean-assembly]: https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/PCP/Algebraic/ThreeColorVerifierSoundness.lean#L58-L70

# Result-by-result comparison

Follow the links to the original and adapted statements and any Lean declarations. The AI assessments compare each declaration with the authors’ claim or the part identified in the note.

### Theorem 1.1

[Authors’ statement](../?l=b4441-5170) · [Adapted statement](../adapted/?l=b3193-3922)

**Same mathematical strength.** This statement gives the smooth odd Euler solution with finite maximal time, bounded velocity, vorticity blow-up, the two divergent integrals and both off-origin limits. It makes uniqueness of the maximal velocity and its lifespan explicit.

[`TorusEuler.Paper.theorem_1_1`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.theorem_1_1)

**Lean is weaker.** The existence form carries the singularity and off-origin conclusions. The maximal-velocity uniqueness clause belongs to the other formal statement. Comparator accepted both formal statements in the [recorded check](https://github.com/wcook04/proof-reader/actions/runs/44925234532).

[`TorusEuler.theorem11`](../lean/?m=TorusEuler.MainTheorem&d=TorusEuler.theorem11)

### Remark 1.2

[Authors’ statement](../?l=b5171-5388) · [Adapted statement](../adapted/?l=b6490-6791)

**In the adapted edition.** The revised remark specifies a smooth extension of the field through the terminal time away from the origin. The Euler equations are imposed for the pre-terminal solution.

**Same mathematical strength.** Both statements assert existence of smooth odd divergence-free data $u_0$ on $\mathbb T^3$ and a smooth odd maximal Euler solution $u,p$ on $[0,T_*)$, $0<T_*<\infty$, with uniformly bounded velocity, $|\operatorname{curl}u(t,0)|\to\infty$, and divergent time integrals of the gradient and vorticity $L^\infty$ norms. On every compact set away from the origin, $u$ and $\partial_tu$ converge in every spatial $C^m$ norm. The additional conclusion of Remark 1.2 is that this same velocity extends smoothly in space and time through $T_*$ away from the origin. The formal statement makes maximal-velocity uniqueness explicit. Fields are represented by integer-periodic functions on $\mathbb R^3$, the excluded origin by the integer lattice, and the pressure is normalized to zero mean. The extension is periodic and is not required to solve Euler after $T_*$. The proof uses an auxiliary existence theorem selecting an exponent and a threshold and supplying an extension for all real times away from the lattice. The supplied auxiliary statement file expressly distinguishes this proved existence assertion from the broader auxiliary claim for every threshold satisfying further estimates. The verdict concerns the existential remark, not that broader claim.

[`TorusEuler.Paper.remark_1_2`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.remark_1_2)

### Lemma 1.3

[Authors’ statement](../?l=b34337-34525) · [Adapted statement](../adapted/?l=b39916-40104)

**Lean is stronger.** Let $b\ge1$ be an integer and $K(s)=320b(s+1)$. Assume $\mathcal B(s)>0$ and $\log\mathcal B(s)\ge4K(s+1)^3$ for $s\ge1$, $q_1=1$, $\lambda_0\ge\mathcal B(1)$, $\lambda_j=\lambda_{j-1}^{K(q_j)}$, and $q_{j+1}=\max\{1\le s\le q_j+1:\mathcal B(s)\le\lambda_{j-1}\}$ for $j\ge1$. The formal statement proves $q_j\le q_{j+1}\le q_j+1$, $q_j\to\infty$, and $4\log\lambda_{j+2}\le(\log\lambda_{j-1})^2$ for every $j\ge1$. The last formula is exactly (1.15), since $L_i=4\log\lambda_{i+1}$. The maximum is the greatest admissible integer. In the paper, $\mathcal B$ is also nondecreasing and dominates the fixed-order analytic constants, and $b$ is fixed by the later construction. The formal statement does not assume these two conditions; it proves the same three assertions from $\mathcal B(s)>0$ and the lower bound (1.13) alone. Frequencies are real, while derivative orders and the exponents $K(s)$ are nonnegative integers; the hypotheses force the relevant frequencies to be positive.

[`TorusEuler.Paper.lemma_1_3`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_1_3)

### Lemma 2.1

[Authors’ statement](../?l=b36920-37555) · [Adapted statement](../adapted/?l=b41363-41998)

**Lean is stronger.** Let $J$ be an interval on which relative time derivatives are unique. The formal statement assumes a differentiable spatial linear map $D(t)$ with $\operatorname{tr}D=0$ and symmetric $D'+D^2$, together with $k'=-D^Tk$ and $\mathbf a'=-D\mathbf a+2(k\cdot D\mathbf a)k/|k|^2$. For differentiable $F$ and any primitive $P'=F$, it proves that $u(t,x)=D(t)x+\mathbf a(t)F(k(t)\cdot x)$ is divergence free and satisfies the Euler momentum equation on $\mathbb R^3$ whenever $k\cdot\mathbf a=0$ throughout $J$. The pressure is exactly $-x\cdot(D'+D^2)x/2-p_{\rm w}P(k\cdot x)$. The needed time and spatial differentiability of the velocity and spatial differentiability of the pressure are included. If $k,\mathbf a$ are nonzero and perpendicular at one $t_0\in J$, these properties persist at every $t\in J$, including times before $t_0$.

The paper assumes smooth $D$, a smooth odd one-periodic profile with $F'(0)=1$, and a primitive of zero phase average. The formal statement does not require those additional profile properties or the higher regularity of $D$. It also extends the Euler-identity part to $k=0$, where the coefficient is assigned zero by the convention that division by zero is zero. The persistence part still explicitly requires nonzero initial data. These are precise extensions of the quoted lemma, not a change from periodic Euler dynamics to an affine torus flow: this lemma concerns the local affine model on $\mathbb R^3$.

[`TorusEuler.Paper.lemma_2_1`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_2_1)

### Lemma 2.2

[Authors’ statement](../?l=b39275-39820) · [Adapted statement](../adapted/?l=b44132-44677)

**Lean is stronger.** For nonzero perpendicular paths $k,\mathbf a\in\mathbb R^3$ satisfying $k\prime=-B^Tk$ and $\mathbf a\prime=-B\mathbf a+2(k\cdot B\mathbf a)k/|k|^2$ on a time set $J$, with $\operatorname{tr}B=0$, define $E_1=k/|k|$, $E_2=\mathbf a/|\mathbf a|$, $E_3=E_1\times E_2$, $B_{ij}=E_i\cdot BE_j$, and $\sigma=|k||\mathbf a|$. The formal statement gives an orthonormal frame and precisely the four identities $E_1'=-B_{12}E_2-B_{13}E_3$, $E_2'=B_{12}E_1-B_{32}E_3$, $E_3'=B_{13}E_1+B_{32}E_2$, and $(\log\sigma)'=B_{33}$. The three frame positions correspond in order to the paper’s subscripts $1,2,3$. Nonvanishing and perpendicularity are explicit hypotheses at every time in the set under consideration; a defined normalized triple alone would not guarantee orthonormality.

The paper assumes a smooth background $B$ on an interval. The formal statement does not require any time regularity of $B$ beyond the prescribed derivatives of $k$ and $\mathbf a$, and it permits relative derivatives on an arbitrary time set. On the paper’s interval these are the ordinary interior derivatives and the appropriate one-sided endpoint derivatives. No symmetry assumption on $B'+B^2$ appears. The stronger verdict refers to these weaker background and domain hypotheses with all four conclusions retained. It does not mean that the separate logarithmic derivatives of $|k|$ and $|\mathbf a|$, displayed inside the proof, are also conclusions of this declaration.

[`TorusEuler.Paper.lemma_2_2`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_2_2)

### Lemma 2.3

[Authors’ statement](../?l=b45839-46988) · [Adapted statement](../adapted/?l=b51476-52625)

**Lean is stronger.** Let $B,E_c$ be continuous on compact $I\ni t_0$, with $\operatorname{tr}B=0$. On $I$, let $k_p,\mathbf a_p\ne0$, $k_p\cdot\mathbf a_p=0$, $k_p'=-B^Tk_p$, $\mathbf a_p'=-B\mathbf a_p+2(k_p\cdot B\mathbf a_p)k_p/|k_p|^2$. Physical derivatives are relative to $I$. Put $E_1=k_p/|k_p|$, $E_2=\mathbf a_p/|\mathbf a_p|$, $E_3=E_1\times E_2$, $B_{ij}=E_i\cdot BE_j$, $\sigma_p=|k_p||\mathbf a_p|$, $\sigma=\sigma_p(t_0)$, $\nu=B_{12}(t_0)>0$, $\eta=B_{32}(t_0)>0$, $r=\sqrt{2\sigma\nu}$, $S=\sigma/r$, $\varepsilon=\eta/\nu$, $\tau=r(t-t_0)$. Assume $T\ge2$, $[t_0,t_0+T/r]\subset I$, and $k'=-M^Tk$ on $I$, $k(t_0)=\lambda E_3(t_0)$, $\lambda>0$, where $M=B+\mathbf a_p\otimes k_p+E_c$. On $0\le\tau\le T$, require $B_{12}=\nu$, $B_{32}=\eta$, all other frame entries zero, and $E_c=0$. Define $\zeta=(k\cdot E_1,Sk\cdot E_2,k\cdot E_3)/\lambda$ and $\alpha=(S\mathbf a\cdot E_1,\mathbf a\cdot E_2,S\mathbf a\cdot E_3)$. Then $|k_p||\mathbf a_p|=\sigma$ and $\zeta'=(-(1+1/(2S^2))\zeta_2,-\varepsilon\zeta_3,\varepsilon\zeta_2/(2S^2))$. Every transverse amplitude solving $\mathbf a'=-M\mathbf a+2(k\cdot M\mathbf a)k/|k|^2$ satisfies $\alpha_1'=-\alpha_2+\zeta_1\Pi$, $\alpha_2'=-(1-1/(2S^2))\alpha_1+\varepsilon(\zeta_1\alpha_1+\zeta_2\alpha_2)/(2S^2\zeta_3)+\zeta_2\Pi/S^2$, where $\zeta_3\ne0$ and $\Pi=[2\zeta_2\alpha_1+(\zeta_1+\varepsilon\zeta_3)\alpha_2]/[\zeta_1^2+\zeta_2^2/S^2+\zeta_3^2]$.

For each fixed $\varepsilon,T$ and every tolerance $e>0$, it chooses one $S_0$ before the physical configuration, wave frequency, activation time and evaluated time. Every model wave with $S\ge S_0$ satisfies $|\zeta-(\varepsilon\tau^2/2,-\varepsilon\tau,1)|\le e$ in Euclidean norm, and every entry of its amplitude matrix is within $e$ of the corresponding entry of $-\bigl(\begin{smallmatrix}\varepsilon\tau\sin2\varphi&\cos^2\varphi(1-\varepsilon\tan\varphi)\\1&0\end{smallmatrix}\bigr)$, where $\varphi=\arctan(\varepsilon\tau^2/2)$. These estimates hold throughout $[0,T]$.

The statement additionally includes $\zeta_3\ne0$ beyond that common threshold. It permits continuous background data on a compact physical set containing the active interval, rather than requiring the smooth background on precisely that interval used in the paper. The result concerns a limit with $\varepsilon,T$ fixed; it does not claim a polynomial shear threshold in $T$.

[`TorusEuler.Paper.lemma_2_3`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_2_3)

### Lemma 2.4

[Authors’ statement](../?l=b52505-53272) · [Adapted statement](../adapted/?l=b58287-59054)

**Lean is stronger.** Let $B,E_c$ be continuous on compact $I\ni t_0$, with $\operatorname{tr}B=0$. On $I$, let $k_p,\mathbf a_p\ne0$, $k_p\cdot\mathbf a_p=0$, $k_p'=-B^Tk_p$, $\mathbf a_p'=-B\mathbf a_p+2(k_p\cdot B\mathbf a_p)k_p/|k_p|^2$. Physical derivatives are relative to $I$. Put $E_1=k_p/|k_p|$, $E_2=\mathbf a_p/|\mathbf a_p|$, $E_3=E_1\times E_2$, $B_{ij}=E_i\cdot BE_j$, $\sigma_p=|k_p||\mathbf a_p|$, $\sigma=\sigma_p(t_0)$, $\nu=B_{12}(t_0)>0$, $\eta=B_{32}(t_0)>0$, $r=\sqrt{2\sigma\nu}$, $S=\sigma/r$, $\varepsilon=\eta/\nu$, $\tau=r(t-t_0)$. Assume $T\ge2$, $[t_0,t_0+T/r]\subset I$, and $k'=-M^Tk$ on $I$, $k(t_0)=\lambda E_3(t_0)$, $\lambda>0$, where $M=B+\mathbf a_p\otimes k_p+E_c$. Define $\delta=\sup_I|B_{12}/\nu-1|+\sup_I|B_{32}/\eta-1|+\sup_I\|B\|/r+\sup_I\|E_c\|/\nu$. For sufficiently large integer $C_0$, assume $C_0\varepsilon\le1$ and $C_0T^{C_0}\delta\le\varepsilon$. With $\zeta=(k\cdot E_1,Sk\cdot E_2,k\cdot E_3)/\lambda$ and $\varphi=\arctan(\varepsilon\tau^2/2)$, the formal statement gives $|\zeta-(\tan\varphi,-\varepsilon\tau,1)|$, $||k|^2\cos^2\varphi/\lambda^2-1|\le CT^p\delta\le1/2$, $1/2\le\zeta_3\le3/2$, $|\zeta|\le3T^2$, and $|\sigma_p/\sigma-1|\le2T\delta$. One continuous $\mathcal E$ satisfies $\|\mathcal E\|\le CT^p\delta$ and $\alpha'=[-\bigl(\begin{smallmatrix}\varepsilon\tau\sin2\varphi&\cos^2\varphi(1-\varepsilon\tan\varphi)\\1&0\end{smallmatrix}\bigr)+\mathcal E]\alpha$ for every $\mathbf a'=-M\mathbf a+2(k\cdot M\mathbf a)k/|k|^2$, $k\cdot\mathbf a=0$ on $I$, where $\alpha=(S\mathbf a\cdot E_1,\mathbf a\cdot E_2)$. Absolute $C$ and integers $p,N$ precede $C_0\ge N$ and all data. Bounds concern $[0,T]$; vector norms are Euclidean, pair operator norms use the maximum norm.

The comparison with the printed lemma concerns three specific choices. First, the formal statement permits continuous $B,E_c$ on a compact set containing the active interval. When that set is larger, the error suprema are also taken there and the smallness assumption must be checked there. Second, continuity of the common amplitude error and the bound for $\sigma_p/\sigma$ are conclusions that the paper obtains in its proof but omits from the lemma statement. Third, the formal statement fixes Euclidean operator norms for the physical matrices and the maximum norm on pairs for the amplitude error; the paper leaves its matrix norms unspecified. The real coefficient and natural exponent can be absorbed into the paper’s $CT^C$ notation by enlarging an absolute constant because $T\ge2$.

[`TorusEuler.Paper.lemma_2_4`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_2_4)

### Lemma 2.5

[Authors’ statement](../?l=b59901-60598) · [Adapted statement](../adapted/?l=b65860-66557)

**Same mathematical strength.** For $0<\varepsilon\le1$, let $\varphi=\arctan(\varepsilon\tau^2/2)$ and consider $Y'=\cos^2\varphi(1-\varepsilon\tan\varphi)-\varepsilon\tau\sin(2\varphi)Y-Y^2$, $Y(0)=1$, on $[0,\infty)$. There is a unique solution on that half-line, with $|Y|\le1$ and $Y=(1+e)\cos\varphi-\varepsilon\tau\sin(2\varphi)/4$ for one function $0\le e\le\varepsilon/8$. Its amplitude $a_{\rm ref}=\exp\int_0^\tau Y$ equals $\sqrt{\cos\varphi}\exp\int_0^\tau(1+e)\cos\varphi$. It has its global maximum at the unique zero $\tau_m$ of $Y$, with $2\le\varepsilon\tau_m\le3$, positive $Y$ before and negative $Y$ after, and $\log a_{\rm ref}(\tau_m)\ge\varepsilon^{-1/2}-1$. The formal statement therefore retains all the conclusions of Lemma 2.5. It makes uniqueness on $[0,\infty)$ explicit, matching the paper’s reference to “the solution,” and uses one common deviation $e$ in both representations. The equation, bounds and uniqueness concern only $\tau\ge0$, with a right derivative at zero; negative-time values are unrestricted. The statement does not assert that the perturbed amplitude has its maximum at the reference turning time.

[`TorusEuler.Paper.lemma_2_5`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_2_5)

### Lemma 2.6

[Authors’ statement](../?l=b65832-66700) · [Adapted statement](../adapted/?l=b72061-72929)

**Lean is stronger.** Let $B,E_c$ be continuous on compact $I\supset[t_0,t_0+T/r]$, with $\operatorname{tr}B=0$ and nonzero perpendicular preceding wave data satisfying $k_p\prime=-B^Tk_p$, $\mathbf a_p\prime=-B\mathbf a_p+2(k_p\cdot B\mathbf a_p)k_p/|k_p|^2$. Set $E_1=\widehat{k_p}$, $E_2=\widehat{\mathbf a_p}$ and $E_3=E_1\times E_2$; $B_{ij}=E_i\cdot BE_j$. Physical derivatives are relative to $I$; for interval $I$, endpoint derivatives are one-sided. Put $\sigma=|k_p(t_0)||\mathbf a_p(t_0)|$, $\nu=B_{12}(t_0)>0$, $\eta=B_{32}(t_0)>0$, $r=\sqrt{2\sigma\nu}$, $S=\sigma/r$, $\varepsilon=\eta/\nu$, and $\delta=\sup_I|B_{12}/\nu-1|+\sup_I|B_{32}/\eta-1|+\sup_I\|B\|/r+\sup_I\|E_c\|/\nu$. Assume $T\ge2$ and $C_0\varepsilon\le1$, $C_0T^{C_0}\delta\le\varepsilon$ for sufficiently large integer $C_0$. In physical time, the new wave solves $k'=-M^Tk$, $\mathbf a'=-M\mathbf a+2(k\cdot M\mathbf a)k/|k|^2$, $k\cdot\mathbf a=0$, with $M=B+\mathbf a_p\otimes k_p+E_c$, $k(t_0)=\lambda E_3(t_0)$, $\lambda>0$, and $\mathbf a(t_0)=-E_1(t_0)/S+E_2(t_0)$. Use $\tau=r(t-t_0)$, $\alpha_1=S\mathbf a\cdot E_1$, $\alpha_2=\mathbf a\cdot E_2$, $\varphi=\arctan(\varepsilon\tau^2/2)$, and $a_{\rm ref}=\exp\int_0^\tau Y$ with $Y\prime=\cos^2\varphi(1-\varepsilon\tan\varphi)-\varepsilon\tau\sin(2\varphi)Y-Y^2$, $Y(0)=1$, on $[0,\infty)$. The formal statement gives $\alpha_2>0$, $|\alpha_1/\alpha_2+Y|\le CT^p\delta$, $\alpha_2\le|\mathbf a|\le(1+CT^p\delta)\alpha_2$, and $|\log(|\mathbf a|/a_{\rm ref})|\le\varepsilon$ at every $\tau\in[0,T]$. It also supplies an invertible linear propagator from $k(\tau_1)^\perp$ onto $k(\tau_2)^\perp$ for $0\le\tau_1\le\tau_2\le T$, agreeing with every transverse amplitude solution and satisfying $\|\Phi\|\le252\exp(1)S|\mathbf a(\tau_2)|/|\mathbf a(\tau_1)|$ in the Euclidean operator norm. These retain all conclusions of Lemma 2.6 and specify its propagator constant. The generalization is from smooth $B$ on the physical interval to continuous $B$ on a compact set containing it. For a larger set, the four suprema defining $\delta$ are also taken over that set, so the smallness condition must still be checked there. The absolute factor $C$, integer exponent $p$ and integer threshold for $C_0$ are chosen before the wave data. The paper’s $CT^C$ notation is recovered by enlarging an absolute constant for $T\ge2$.

[`TorusEuler.Paper.lemma_2_6`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_2_6)

### Lemma 2.7

[Authors’ statement](../?l=b70210-70766) · [Adapted statement](../adapted/?l=b76983-77539)

**Lean is stronger.** Let $B,E_c$ be continuous on compact $I\supset[t_0,t_0+T/r]$, with $\operatorname{tr}B=0$ and nonzero perpendicular preceding wave data satisfying $k_p\prime=-B^Tk_p$, $\mathbf a_p\prime=-B\mathbf a_p+2(k_p\cdot B\mathbf a_p)k_p/|k_p|^2$. Set $E_1=\widehat{k_p}$, $E_2=\widehat{\mathbf a_p}$ and $E_3=E_1\times E_2$; $B_{ij}=E_i\cdot BE_j$. Physical derivatives are relative to $I$; for interval $I$, endpoint derivatives are one-sided. Put $\sigma=|k_p(t_0)||\mathbf a_p(t_0)|$, $\nu=B_{12}(t_0)>0$, $\eta=B_{32}(t_0)>0$, $r=\sqrt{2\sigma\nu}$, $S=\sigma/r$, $\varepsilon=\eta/\nu$, and $\delta=\sup_I|B_{12}/\nu-1|+\sup_I|B_{32}/\eta-1|+\sup_I\|B\|/r+\sup_I\|E_c\|/\nu$. Assume $T\ge2$ and $C_0\varepsilon\le1$, $C_0T^{C_0}\delta\le\varepsilon$ for sufficiently large integer $C_0$. In physical time, the new wave solves $k'=-M^Tk$, $\mathbf a'=-M\mathbf a+2(k\cdot M\mathbf a)k/|k|^2$, $k\cdot\mathbf a=0$, with $M=B+\mathbf a_p\otimes k_p+E_c$, $k(t_0)=\lambda E_3(t_0)$, $\lambda>0$, and $\mathbf a(t_0)=-E_1(t_0)/S+E_2(t_0)$. Use $\tau=r(t-t_0)$ and $\varphi=\arctan(\varepsilon\tau^2/2)$. Define the new frame by $E_{1,+}=k/|k|$, $E_{2,+}=\mathbf a/|\mathbf a|$, $E_{3,+}=E_{1,+}\times E_{2,+}$ and its couplings by $\nu_+=E_{1,+}\cdot ME_{2,+}$, $\eta_+=E_{3,+}\cdot ME_{2,+}$. The formal statement gives $\nu_+\ge\varepsilon\nu/2$ on $[0,T]$. For $\sqrt2/\varepsilon\le\tau\le T$, it proves $|\nu_+/\nu-1|\le\varepsilon$ and $|(\eta_+/\nu_+)/\cos\varphi-1|\le1/2$. These are exactly the quantitative conclusions of Lemma 2.7, with the same reference angle. The statement is more general in requiring only continuous $B$ and permitting a larger compact observation set; the error $\delta$ must be measured on that set. It does not identify the reference angle with the actual perturbed wave angle, and its conclusion retains the fixed tolerance $1/2$, rather than the intermediate $O(\varepsilon)$ relative-error claim in the paper’s proof. The universal integer threshold for $C_0$ is chosen before all physical wave data. Here hats denote division by Euclidean length.

[`TorusEuler.Paper.lemma_2_7`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_2_7)

### Proposition 2.8

[Authors’ statement](../?l=b77292-78108) · [Adapted statement](../adapted/?l=b83726-84542)

**Lean is stronger.** Let $B,E_c$ be continuous on compact $I\supset[t_0,t_0+T/r]$, with $\operatorname{tr}B=0$ and nonzero perpendicular preceding wave data satisfying $k_p\prime=-B^Tk_p$, $\mathbf a_p\prime=-B\mathbf a_p+2(k_p\cdot B\mathbf a_p)k_p/|k_p|^2$. Set $E_1=\widehat{k_p}$, $E_2=\widehat{\mathbf a_p}$ and $E_3=E_1\times E_2$; $B_{ij}=E_i\cdot BE_j$. Physical derivatives are relative to $I$; for interval $I$, endpoint derivatives are one-sided. Put $\sigma=|k_p(t_0)||\mathbf a_p(t_0)|$, $\nu=B_{12}(t_0)>0$, $\eta=B_{32}(t_0)>0$, $r=\sqrt{2\sigma\nu}$, $S=\sigma/r$, $\varepsilon=\eta/\nu$, and $\delta=\sup_I|B_{12}/\nu-1|+\sup_I|B_{32}/\eta-1|+\sup_I\|B\|/r+\sup_I\|E_c\|/\nu$. Assume $T\ge2$ and $C_0\varepsilon\le1$, $C_0T^{C_0}\delta\le\varepsilon$ for sufficiently large integer $C_0$. In physical time, the new wave solves $k'=-M^Tk$, $\mathbf a'=-M\mathbf a+2(k\cdot M\mathbf a)k/|k|^2$, $k\cdot\mathbf a=0$, with $M=B+\mathbf a_p\otimes k_p+E_c$, $k(t_0)=\lambda E_3(t_0)$, $\lambda>0$, and $\mathbf a(t_0)=-E_1(t_0)/S+E_2(t_0)$. Use $\tau=r(t-t_0)$ and $\varphi=\arctan(\varepsilon\tau^2/2)$. Here a reference slope means any solution of $Y\prime=\cos^2\varphi(1-\varepsilon\tan\varphi)-\varepsilon\tau\sin2\varphi\,Y-Y^2$, $Y(0)=1$, on $[0,\infty)$. Such a solution is used to characterize the output $\tau_m$; it is not a supplied input to the proposition. Define $E_{1,+}=k/|k|$, $E_{2,+}=\mathbf a/|\mathbf a|$, $E_{3,+}=E_{1,+}\times E_{2,+}$, $\nu_+=E_{1,+}\cdot ME_{2,+}$ and $\eta_+=E_{3,+}\cdot ME_{2,+}$. Assume $0<\varepsilon_+\le\varepsilon/32$ and $H=2/\sqrt{\varepsilon\varepsilon_+}\le T$. The formal statement identifies the unique nonnegative zero $\tau_m$ of every reference slope, with $\tau_m\ge2/\varepsilon$, and supplies a crossing $\eta_+/\nu_+=\varepsilon_+$ in $[\tau_m,H]$. It chooses one attained maximum $A=\max_{[0,T]}|\mathbf a|$. At every crossing in that interval, $\exp(-1)/(4\sqrt{\varepsilon\varepsilon_+})\le|\mathbf a||k|/(\lambda A)\le18\exp(3)/\sqrt{\varepsilon\varepsilon_+}$. On $[0,1]$ it gives $|\mathbf a|\le\exp(3-1/\sqrt\varepsilon)A$. These retain Proposition 2.8 with explicit absolute strength factors and the same early-time factor. Continuous $B$ and a larger compact observation set are permitted, with $\delta$ measured on that set. The proposition does not state uniqueness of a crossing or locate the perturbed amplitude maximum at $\tau_m$. A separate older formal theorem locates a crossing strictly inside the bracket and uses the weaker symmetric lower factor $1/(18\exp(3))$; that is not the exact lower constant of the current formal statement. The universal integer threshold for $C_0$ is chosen before all physical wave data. Here hats denote division by Euclidean length.

[`TorusEuler.Paper.proposition_2_8`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.proposition_2_8)

### Lemma 3.1

[Authors’ statement](../?l=b88218-88505) · [Adapted statement](../adapted/?l=b96732-97112)

**In the adapted edition.** The revised statement specifies periodicity of the primitives, integer derivative orders and uniformity of the constants in the cutoff width.

**Lean is stronger.** The formal theorem proves Lemma 3.1 for one specified family, whereas the paper asserts existence of a suitable family. For every $0<h\le1$, the constructed $F_h$ is smooth, odd and period one; its normalized primitive $P_h$ is smooth, period one and has zero phase mean, with $P_h'=F_h$. There is one $C>0$, chosen before $h$, such that $F_h'(0)=1$, $-Ch\le F_h'\le1$ and $\|F_h\|_\infty\le Ch$. For each integer $j\ge2$, there is $C_j>0$, chosen before $h$ and the phase, such that $\|\partial_s^jF_h\|_\infty\le C_jh^{1-j}$. The exponent uses integer subtraction, so it is negative for $j\ge2$, exactly as in the paper. The specified bump is supported in $[-1/8,1/8]$, inside the interval allowed by the proof. Phase mean means integration over $[0,1]$; the primitive is normalized by subtracting that mean, not by fixing its value at zero. The formula is defined outside the admissible width range, but the theorem asserts these properties only for $0<h\le1$. The stronger verdict concerns the identified family and its uniform estimates; it does not assert spatial periodicity after evaluation at an arbitrary real wave vector.

[`TorusEuler.Paper.lemma_3_1`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_3_1)

### Lemma 4.1

[Authors’ statement](../?l=b93841-94250) · [Adapted statement](../adapted/?l=b103174-103583)

**Same mathematical strength.** Let $0<T\le1$, let $u$ be a smooth divergence-free velocity on $[0,T]\times\mathbb T^3$, and let $X$ be its flow with $X(0,a)=a$. Write $F=D_aX$, $M=(\nabla u)\circ X$, $H^\#=-(M_t+M^2)$, $K=F^TF$ and $\Omega=F^T(M^T-M)F$. Suppose $w\cdot H^\#(t,a)w\le|w|^2$ for every $t,a,w$; symmetry of $H^\#$ and an Euler equation for $u$ are not assumed.

For every label $a$ and every $z\in H^1_0([0,T];\mathbb R^3)$, put $\xi=Fz$. Both statements give $\int H^\#\xi\cdot\xi\le\tfrac12\int|\xi_t|^2$ and $\int(Kz_t\cdot z_t+\Omega z_t\cdot z)\ge\tfrac12\int|\xi_t|^2$. The factor $1/2$, the sign of the $\Omega$ term and the test class agree.

The formal statement uses periodic lifts to $\mathbb R^3$ for the torus and represents $z$ by $z(t)=\int_0^t v(s)\,ds$, with $v\in L^2(0,T;\mathbb R^3)$ and $\int_0^T v=0$. This is exactly the space of Sobolev paths with both endpoints zero; it does not restrict the test paths to smooth ones. It writes $\xi_t=M\xi+Fv$, an almost-everywhere identity sufficient for these integrals. The bound on $H^\#$ is one-sided, not an absolute matrix-norm bound.

[`TorusEuler.Paper.lemma_4_1`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_4_1)

### Theorem 4.2

[Authors’ statement](../?l=b95322-95900) · [Adapted statement](../adapted/?l=b105480-106058)

**Lean is stronger.** On $I=[0,T]$, $0<T\le1$, let $U$ be smooth, unit-periodic and divergence free, $X$ its flow from time zero, $F=D_aX$, $M=(DU)\circ X$, $K=F^TF$, $\Omega=F^T(M^T-M)F$, and $H^\#=-(M_t+M^2)\le I$ as quadratic forms. Assume $\|F^{-1}\|_\infty\le D\ge1$, $\|M\|_\infty\le L$, $\|K\|_\infty\le K_0$, $\|D_aK\|_\infty\le K_1$, $\|\Omega\|_\infty\le\Omega_0$, $\|D_a\Omega\|_\infty\le\Omega_1$, with nonnegative bounds.

For $L_{\rm src}\in C(I;C^{0,1/2}(\mathbb T^3))$, solve $Kv-J(\Omega v)+L_{\rm src}=c+G_\phi$, $z_t=v$, $z(0)=z(T)=0$, where $Jw(t)=\int_0^tw(s)\,ds$. The fields $z,v,c$ are weakly divergence free; $z\in C^1_tC^{0,1/2}$, $v,G_\phi\in C_tC^{0,1/2}$, and $G_\phi=\nabla_a\phi$ for a periodic potential at each time. The formal theorem gives existence for every such source and uniqueness of $z,v,c,G_\phi$ on $I$. It does not assert uniqueness of the scalar potential: adding an arbitrary function of time leaves the equations unchanged. The potential has no time-regularity requirement in this part of the statement. The fields on the torus are represented by unit-periodic lifts.

There are absolute $C\ge0$ and an integer $p\ge0$ such that $A=C(D+L+K_0+K_1+\Omega_0+\Omega_1)^p$ gives $\|v\|_{C_tC^{0,1/2}}\le A\|L_{\rm src}\|_{C_tC^{0,1/2}}$ and $\|(\mathbb PK(t))^{-1}\mathbb P\|\le A$ uniformly on $I$. Both norms are operator estimates: the velocity bound includes the factor $\|L_{\rm src}\|$, while the fixed-time inverse is already an operator norm. The fixed-time map inverted is $w\mapsto\mathbb P(K(t)w)$ on the solenoidal half-Hölder subspace, and its inverse is composed with $\mathbb P$ to accept arbitrary inputs. Constants $C,p$ are chosen before the parent and source. The paper uses full $C^{1,1/2}$ coefficient norms, whereas the formal theorem needs only coefficient and first label-derivative suprema; this accounts for the stronger quantitative verdict. The half-Hölder norm is the maximum of the supremum norm and seminorm. The exponent $p$ is existential in this numbered theorem; a separate inverse theorem supplies the explicit exponent $1164$.

For smooth periodic Eulerian $f$, take $g=F^T(f\circ X)$ and $L_{\rm src}=-Jg$. The formal statement constructs smooth $z$ and a smooth periodic label pressure $\mathsf q$ of spatial mean zero, with $Kv_t+\nabla_a\mathsf q=g-2F^TF_t v$. Then $b=(Fv)\circ X^{-1}$ and $q=\mathsf q\circ X^{-1}$ are smooth, $\operatorname{div}b=0$, and $b_t+U\cdot\nabla b+b\cdot\nabla U+\nabla q=f$, with $b(0)=c$. The smooth label pressure is reconstructed; the formal statement does not identify it with the time derivative of the initially arbitrary potential $\phi$. No Euler equation for the parent is assumed.

[`TorusEuler.Paper.theorem_4_2`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.theorem_4_2)

### Proposition 5.1

[Authors’ statement](../?l=b105919-106506) · [Adapted statement](../adapted/?l=b117440-118051)

**In the adapted edition.** The transport estimate now explicitly assumes spatial smoothness of the field and a nonnegative amplitude bound.

**Lean is stronger.** Let $0<T\le1$, $\mathsf D\ge2$ and $\lambda\ge1$. The parent $U$ is a smooth odd divergence-free field on $[0,T]\times\mathbb T^3$, with Fourier support $|\xi|\le2\mathsf D$ and flow $X$. The bounds $\|\nabla U\|_\infty,\|D_aX\|_\infty,\|(D_aX)^{-1}\|_\infty\le\mathsf D$ hold. For a smooth periodic pressure $p_U$, set $R_U=U_t+U\cdot\nabla U+\nabla p_U$; require $R_U$ odd, supported in $|\xi|\le4\mathsf D$, $\|R_U\|_\infty\le\lambda^{-5/2}$, and $D^2p_U-\nabla R_U\le I$ as quadratic forms. The formal statement imposes these conditions directly. The paper selects the zero-mean Poisson pressure; the formal statement permits any pressure meeting the displayed conditions, without separately requiring $\operatorname{div}R_U=0$.

Choose $k_*\ne0$ and $0\le t_0<T$ with $|\kappa(t_0,0)|=\lambda$, where $\kappa=(D_aX)^{-T}k_*$. For each of $(D_aX)^{\pm1}$, $M=(\nabla U)\circ X$, $\kappa/\lambda$, $\lambda^2/|\kappa|^2$ and $P_\kappa=\kappa\otimes\kappa/|\kappa|^2$, the formal statement bounds its $m$th label derivative by $C_m\mathsf D^{C(m+1)}$, uniformly in time and label. It also gives $|f\circ X|_m\le C_m A_f\mathsf D^{Cm}$ whenever all spatial derivatives of $f$ satisfy $|f|_m\le C'_m A_f\mathsf D^m$, with $A_f\ge0$ and an arbitrary real normed target space.

For every $0<\ell_*\le\mathsf D^{-C}$, summing the derivatives with weights $\ell_*^m$ gives $\|c\|_{[n]}\le C_n\mathsf D^C$ and $\|f\circ X\|_{[n]}\le C_n A_f$. Here the formal derivative norm is the operator norm of the full multilinear derivative, whereas the paper sums coordinate derivatives; finite-dimensional comparison only changes the order-dependent constants. One integer $C$ and the coefficient constants are chosen before the parent and the derivative order. The composition constants may depend on the prescribed sequence $C'_m$, as the paper permits. The transported covector is nonzero, so the displayed divisions are ordinary divisions. The stronger verdict concerns the larger parent-pressure class; it does not assert a better power of $\lambda$.

[`TorusEuler.Paper.proposition_5_1`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.proposition_5_1)

### Proposition 5.2

[Authors’ statement](../?l=b110085-110359) · [Adapted statement](../adapted/?l=b121833-122107)

**Lean is stronger.** Let $0<T\le1$, $\mathsf D\ge2$ and $\lambda\ge1$. The parent $U$ is a smooth odd divergence-free field on $[0,T]\times\mathbb T^3$, with Fourier support $|\xi|\le2\mathsf D$ and flow $X$. The bounds $\|\nabla U\|_\infty,\|D_aX\|_\infty,\|(D_aX)^{-1}\|_\infty\le\mathsf D$ hold. For a smooth periodic pressure $p_U$, set $R_U=U_t+U\cdot\nabla U+\nabla p_U$; require $R_U$ odd, supported in $|\xi|\le4\mathsf D$, $\|R_U\|_\infty\le\lambda^{-5/2}$, and $D^2p_U-\nabla R_U\le I$ as quadratic forms. The formal statement imposes these conditions directly. The paper selects the zero-mean Poisson pressure; the formal statement permits any pressure meeting the displayed conditions, without separately requiring $\operatorname{div}R_U=0$.

Let $F=D_aX$, $M=(\nabla U)\circ X$ and $\mathbf d=F^{-T}\nabla_a$. For smooth periodic phase-independent fields $\bar f,B,\bar q$, suppose $B_t+MB+\mathbf d\bar q=\bar f$ and $B=Fz_t$, where the smooth periodic displacement $z$ satisfies $z(0)=z(T)=0$ and $\operatorname{div}_a z_t=0$. Volume preservation makes the last condition equivalent to $\mathbf d\cdot B=0$. No vanishing of the mean correction before activation is required.

For a sufficiently large fixed integer $a$ and $\ell_*=\mathsf D^{-a}$, the formal statement gives $\|B\|_{[n]}\le C_n\mathsf D^C\|\bar f\|_{[n+1]}$ at every nonnegative integer order $n$. These are unweighted suprema on the entire interval $[0,T]$, summed over label derivatives with weights $\ell_*^{|\alpha|}$; phase derivatives vanish. The statement estimates every solution satisfying these conditions. It does not assert existence or choose the additive function of time in $\bar q$.

The derivative loss is exactly one, as in (5.12). Once $a$ is fixed, one integer exponent $C$ is chosen before the parent and before $n$; only $C_n$ varies with order. The formal statement enlarges the allowed parent-pressure class described above. Its explicit endpoint and divergence requirements express the paper's mean equation, rather than additional initial-value restrictions.

[`TorusEuler.Paper.proposition_5_2`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.proposition_5_2)

### Lemma 5.3

[Authors’ statement](../?l=b114386-114676) · [Adapted statement](../adapted/?l=b126223-126513)

**Different formulation.** Let $0<T\le1$, $\mathsf D\ge2$ and $\lambda\ge1$. The parent $U$ is a smooth odd divergence-free field on $[0,T]\times\mathbb T^3$, with Fourier support $|\xi|\le2\mathsf D$ and flow $X$. The bounds $\|\nabla U\|_\infty,\|D_aX\|_\infty,\|(D_aX)^{-1}\|_\infty\le\mathsf D$ hold. For a smooth periodic pressure $p_U$, set $R_U=U_t+U\cdot\nabla U+\nabla p_U$; require $R_U$ odd, supported in $|\xi|\le4\mathsf D$, $\|R_U\|_\infty\le\lambda^{-5/2}$, and $D^2p_U-\nabla R_U\le I$ as quadratic forms. The formal statement imposes these conditions directly. The paper selects the zero-mean Poisson pressure; the formal statement permits any pressure meeting the displayed conditions, without separately requiring $\operatorname{div}R_U=0$.

Write $F=D_aX$, $M=(\nabla U)\circ X$ and $\kappa=F^{-T}k_*$, where $k_*\ne0$. Choose $0\le t_0<T$ with $|\kappa(t_0,0)|=\lambda$. At the origin take a nonzero transverse solution $\mathbf a$ of $\mathbf a_t=-M\mathbf a+2\kappa(\kappa\cdot M\mathbf a)/|\kappa|^2$. Put $\gamma(t)=\lambda^{3/4}|\mathbf a(t,0)|$. For every transverse homogeneous solution $\mathbf b$ and $t_0\le t'\le t\le T$, assume $|\mathbf b(t)|/\gamma(t)\le\mathsf D|\mathbf b(t')|/\gamma(t')$, and assume $\kappa\cdot M\mathbf a\ge\mathsf D^{-1}|\kappa||\mathbf a|$ at the origin. The formal normalization is $0<\gamma\le1$; the paper additionally requires $\max\gamma=1$. Fix $\ell_*=\mathsf D^{-a}$ for a sufficiently large integer $a$, and $h=\lambda^{-1/2}$.

For a profile $f(t,a,s)$, the norm $\|f\|_{[n]}$ sums $\ell_*^{|\alpha|}h^j\sup|\partial_a^\alpha\partial_s^j f|$ over $|\alpha|+j\le n$ on $[0,T]$. The weighted norm $\|f\|_{[n],\gamma}$ uses $[t_0,T]$ and divides by $\gamma(t)$; it differentiates only labels and phase. Each multi-index is counted once. The profiles are smooth on the closed time slab, one-periodic in $s$, and satisfy $f(t,a+n,s+k_*\cdot n)=f(t,a,s)$ for $n\in\mathbb Z^3$. Their stipulated zero values outside the time slab do not assert smoothness across its endpoints.

Use the particular fixed smooth radial envelope $g$, equal to one on $|a|\le\ell_*$ and zero for $|a|\ge2\ell_*$. Extend the seed from the origin by solving its linear equation with $\mathbf a(t_0,a)=(I-P_{\kappa(t_0,a)})\mathbf a(t_0,0)$. For $|a|\le2\ell_*$ the formal statement gives $|\mathbf a(t,a)|\le2|\mathbf a(t,0)|$ and the strict inequality $\kappa\cdot M\mathbf a>0$ on $[t_0,T]$. For a transverse solution $V_t=-(I-2P_\kappa)MV+(I-P_\kappa)f$, whose initial value and source vanish outside the repeated envelope support, it gives $\|V\|_{[n],\gamma}\le C_n\mathsf D^C(\gamma(t_0)^{-1}\|V(t_0)\|_{[n]}+\|f\|_{[n],\gamma})$.

For the transverse momentum equation $V_t+MV+\kappa\partial_s\mathsf p=f$, the formal estimate is $\|V\|_{[n],\gamma}+\lambda\|\mathsf p\|_{[n],\gamma}\le C_n\mathsf D^C\|f\|_{[n],\gamma}$. It assumes a full-interval solution with $V(0)=0$, $V\perp\kappa$, and zero phase means of $V,f,\mathsf p$; the source vanishes before $t_0$ and outside the envelope. For $A_1=g\mathbf aF_h$ and its zero-mean wave pressure it gives the same left-hand side bounded by $C_n\mathsf D^C\lambda^{-5/4}$.

The numerical powers, initial-value term and pressure factor agree with (5.19)–(5.22). The scope changes in both directions: part (i) of the numbered formal statement takes profiles smooth on $[0,T]$, while the paper permits data given only on $[t_0,T]$; a smooth extension is needed to apply that statement to such data. The parent pressure and the central normalization are less restrictive as described above. Part (ii) is an estimate conditional on a solution; its existence and uniqueness are separate results. The constants are chosen before the parent and derivative order, after fixing $a$.

[`TorusEuler.Paper.lemma_5_3`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_5_3)

### Proposition 5.4

[Authors’ statement](../?l=b124798-126025) · [Adapted statement](../adapted/?l=b137223-138450)

**Lean is stronger.** Let $0<T\le1$, $\mathsf D\ge2$ and $\lambda\ge1$. The parent $U$ is a smooth odd divergence-free field on $[0,T]\times\mathbb T^3$, with Fourier support $|\xi|\le2\mathsf D$ and flow $X$. The bounds $\|\nabla U\|_\infty,\|D_aX\|_\infty,\|(D_aX)^{-1}\|_\infty\le\mathsf D$ hold. For a smooth periodic pressure $p_U$, set $R_U=U_t+U\cdot\nabla U+\nabla p_U$; require $R_U$ odd, supported in $|\xi|\le4\mathsf D$, $\|R_U\|_\infty\le\lambda^{-5/2}$, and $D^2p_U-\nabla R_U\le I$ as quadratic forms. The formal statement imposes these conditions directly. The paper selects the zero-mean Poisson pressure; the formal statement permits any pressure meeting the displayed conditions, without separately requiring $\operatorname{div}R_U=0$.

Write $F=D_aX$, $M=(\nabla U)\circ X$ and $\kappa=F^{-T}k_*$, where $k_*\ne0$. Choose $0\le t_0<T$ with $|\kappa(t_0,0)|=\lambda$. At the origin take a nonzero transverse solution $\mathbf a$ of $\mathbf a_t=-M\mathbf a+2\kappa(\kappa\cdot M\mathbf a)/|\kappa|^2$. Put $\gamma(t)=\lambda^{3/4}|\mathbf a(t,0)|$. For every transverse homogeneous solution $\mathbf b$ and $t_0\le t'\le t\le T$, assume $|\mathbf b(t)|/\gamma(t)\le\mathsf D|\mathbf b(t')|/\gamma(t')$, and assume $\kappa\cdot M\mathbf a\ge\mathsf D^{-1}|\kappa||\mathbf a|$ at the origin. The formal normalization is $0<\gamma\le1$; the paper additionally requires $\max\gamma=1$. Fix $\ell_*=\mathsf D^{-a}$ for a sufficiently large integer $a$, and $h=\lambda^{-1/2}$.

Let $g$ be the fixed smooth radial envelope, equal to one on $|a|\le\ell_*$ and zero for $|a|\ge2\ell_*$, and let $\widetilde\chi$ be a smooth time cutoff with $0\le\widetilde\chi\le1$, vanishing for $t<t_0$. Here $F_h$ is the fixed smooth one-periodic zero-mean phase profile of Section 3. The seed is the transverse linear solution with initial value $(I-P_{\kappa(t_0,a)})\mathbf a(t_0,0)$. For each integer $P\ge2$, the formal statement supplies this seed and a smooth finite expansion with $A_1=g\mathbf aF_h$, $V_1=\widetilde\chi A_1$, $C_1=B_1=\bar q_1=0$, $C_{p+1}=C[V_p]$, and the mean and transverse equations (5.11), (5.27) and (5.28). Mean pressures have zero spatial mean; transverse pressures have zero phase mean. For $p\ge2$, $V_p(0)=0$, while $B_p=Fz_{p,t}$ with $\operatorname{div}_a z_{p,t}=0$ and $z_p(0)=z_p(T)=0$. The level-two mean source includes $-R_U\circ X$.

The recursive equations can be stated without referring to another result. Write $Y_i=V_i+C_i$, $Z_i=Y_i+B_i$ and $S=\widetilde\chi'A_1$. For $2\le p\le P$, define

$H_p=(\partial_t+M)C_p+\mathbf d\mathsf p_{p-1}-\mathbf1_{p=2}C[S]+\sum_{i+j=p}(Z_i\cdot\mathbf d)Z_j+\sum_{i+j=p+1,\,i\ge2}(C_i\cdot\kappa)\partial_sY_j$,

where all summation indices are positive integers. Set $\bar f_p=-\langle H_p\rangle_s-\mathbf1_{p=2}R_U\circ X$, $f_p=-(H_p-\langle H_p\rangle_s)$ and $f_p^S=-\sum_{i=2}^p(B_i\cdot\kappa)\partial_sY_{p+1-i}$. The mean equation is $B_{p,t}+MB_p+\mathbf d\bar q_p=\bar f_p$ with $B_p$ and $\bar q_p$ independent of phase. The transverse equation is $V_{p,t}+MV_p+\kappa\partial_s\mathsf p_p=f_p+f_p^S$, with $\kappa\cdot V_p=0$, zero phase mean and $V_p(0)=0$. The new mean is therefore fixed before the current transverse source is determined. The subtraction at level two removes the differentiated cutoff from the leading curl correction. Its remaining contribution to the full equation is $R_{\widetilde\chi}=S+C[S]$.

With $V_{P+1}=B_{P+1}=0$, the remainder is

$R_P=(\partial_t+M)C_{P+1}+\mathbf d\mathsf p_P+\sum_{1\le i,j\le P+1,\,i+j\ge P+1}(Z_i\cdot\mathbf d)Z_j+\sum_{1\le i,j\le P+1,\,i+j\ge P+2}(Z_i\cdot\kappa)\partial_sY_j$.

These are finite sums; there is no passage to an infinite expansion. The stored correction of $V_p$ carries the paper index $C_{p+1}$. At unused index zero, natural-number predecessor is zero, so the bare reindexing gives $C_0=C_1$; the expansion separately imposes $C_1=0$.

Write $W=\sum_{p=1}^P(V_p+C_{p+1}+B_p)$, $\mathsf P=\sum_{p=1}^P(\mathsf p_p+\bar q_p)$ and $\widetilde{\mathbf d}=\mathbf d+\kappa\partial_s$, with $\mathbf d=F^{-T}\nabla_a$. The conclusion is $\widetilde{\mathbf d}\cdot W=0$ and $W_t+MW+(W\cdot\widetilde{\mathbf d})W+\widetilde{\mathbf d}\mathsf P+R_U\circ X=R_P+R_{\widetilde\chi}$. Here $R_P$ is the finite remainder (5.30), and $R_{\widetilde\chi}=S+C[S]$ with $S=\widetilde\chi'A_1$. The oscillatory part, and the oscillatory sources at levels $2\le p\le P$, vanish outside the repeated envelope. Oscillatory velocities, their pressures and all retained divergence corrections vanish before activation. The means need not vanish there.

The final convention is $V_{P+1}=B_{P+1}=0$, hence $Y_{P+1}=Z_{P+1}=C_{P+1}$. Outside the envelope $R_P$ is phase-independent; this does not say it vanishes. Uniqueness concerns $V_p,B_p,\mathsf p_p,\bar q_p$ for $1\le p\le P$ and $C_p$ for $1\le p\le P+1$, not unused entries of an infinite family. Profiles represent periodic physical fields by the relation $f(t,a+n,s+k_*\cdot n)=f(t,a,s)$; smoothness is on $[0,T]$. The identities and support conclusions match the paper. The formal statement explicitly asserts existence and uniqueness and allows the broader pressure and seed normalization above; the radius threshold is chosen independently of the parent and depth.

[`TorusEuler.Paper.proposition_5_4`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.proposition_5_4)

### Lemma 5.5

[Authors’ statement](../?l=b128740-129419) · [Adapted statement](../adapted/?l=b140621-141300)

**Different formulation.** Let $0<T\le1$, $\mathsf D\ge2$ and $\lambda\ge1$. The parent $U$ is a smooth odd divergence-free field on $[0,T]\times\mathbb T^3$, with Fourier support $|\xi|\le2\mathsf D$ and flow $X$. The bounds $\|\nabla U\|_\infty,\|D_aX\|_\infty,\|(D_aX)^{-1}\|_\infty\le\mathsf D$ hold. For a smooth periodic pressure $p_U$, set $R_U=U_t+U\cdot\nabla U+\nabla p_U$; require $R_U$ odd, supported in $|\xi|\le4\mathsf D$, $\|R_U\|_\infty\le\lambda^{-5/2}$, and $D^2p_U-\nabla R_U\le I$ as quadratic forms. The formal statement imposes these conditions directly. The paper selects the zero-mean Poisson pressure; the formal statement permits any pressure meeting the displayed conditions, without separately requiring $\operatorname{div}R_U=0$.

Write $F=D_aX$, $M=(\nabla U)\circ X$ and $\kappa=F^{-T}k_*$, where $k_*\ne0$. Choose $0\le t_0<T$ with $|\kappa(t_0,0)|=\lambda$. At the origin take a nonzero transverse solution $\mathbf a$ of $\mathbf a_t=-M\mathbf a+2\kappa(\kappa\cdot M\mathbf a)/|\kappa|^2$. Put $\gamma(t)=\lambda^{3/4}|\mathbf a(t,0)|$. For every transverse homogeneous solution $\mathbf b$ and $t_0\le t'\le t\le T$, assume $|\mathbf b(t)|/\gamma(t)\le\mathsf D|\mathbf b(t')|/\gamma(t')$, and assume $\kappa\cdot M\mathbf a\ge\mathsf D^{-1}|\kappa||\mathbf a|$ at the origin. The formal normalization is $0<\gamma\le1$; the paper additionally requires $\max\gamma=1$. Fix $\ell_*=\mathsf D^{-a}$ for a sufficiently large integer $a$, and $h=\lambda^{-1/2}$.

For a profile $f(t,a,s)$, the norm $\|f\|_{[n]}$ sums $\ell_*^{|\alpha|}h^j\sup|\partial_a^\alpha\partial_s^j f|$ over $|\alpha|+j\le n$ on $[0,T]$. The weighted norm $\|f\|_{[n],\gamma}$ uses $[t_0,T]$ and divides by $\gamma(t)$; it differentiates only labels and phase. Each multi-index is counted once. The profiles are smooth on the closed time slab, one-periodic in $s$, and satisfy $f(t,a+n,s+k_*\cdot n)=f(t,a,s)$ for $n\in\mathbb Z^3$. Their stipulated zero values outside the time slab do not assert smoothness across its endpoints.

Set $\mathbf d=(D_aX)^{-T}\nabla_a$ and $C[V]=\mathbf d\times Q[V]$, where $Q[V]=-\partial_s^{-1}(\kappa\times V/|\kappa|^2)$ and $\partial_s^{-1}$ takes the zero-mean periodic primitive. For $V\perp\kappa$ on $[t_0,T]$ with zero phase mean, the formal statement gives $\|C[V]\|_{[n],\gamma}\le C_n\mathsf D^C\lambda^{-1}\|V\|_{[n+1],\gamma}$. If $V_t+MV+\kappa\partial_s\mathsf p=f$ and the pressure and source have zero phase mean, it also gives $\|(\partial_t+M)C[V]+\mathbf d\mathsf p\|_{[n],\gamma}\le C_n\mathsf D^C\lambda^{-1}(\|V\|_{[n+1],\gamma}+\|f\|_{[n+1],\gamma})$.

The gain $\lambda^{-1}$ and the loss of one label-or-phase derivative agree exactly with (5.31)–(5.32). The numbered formal statement requires smooth profiles on the whole interval $[0,T]$ and zero phase means of $V$ and $f$ there. The differential equation, transversality and pressure normalization are required only on $[t_0,T]$. Thus an arbitrary field given on the active interval is not an input until an appropriate extension has been supplied. This restriction accompanies the weaker pressure and seed-normalization assumptions above, which explains the verdict different.

For the leading field $A_1=g\mathbf aF_h$, the formal statement itself supplies smooth profiles on $[0,T]$ that agree with $A_1$ and its pressure on the active interval within the centered label cell; elsewhere they obey the stated coupled translation law. They satisfy the homogeneous equation throughout the active interval. The source term then vanishes in the second estimate. One exponent $C$ works at every derivative order after the envelope exponent is fixed, and all constants are chosen before the parent. Nonvanishing of $\kappa$ and positivity of $\gamma$ make every division used in these conclusions ordinary division.

[`TorusEuler.Paper.lemma_5_5`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_5_5)

### Theorem 5.6

[Authors’ statement](../?l=b131772-132886) · [Adapted statement](../adapted/?l=b143989-145103)

**Lean is stronger.** Let $0<T\le1$, $\mathsf D\ge2$ and $\lambda\ge1$. The parent $U$ is a smooth odd divergence-free field on $[0,T]\times\mathbb T^3$, with Fourier support $|\xi|\le2\mathsf D$ and flow $X$. The bounds $\|\nabla U\|_\infty,\|D_aX\|_\infty,\|(D_aX)^{-1}\|_\infty\le\mathsf D$ hold. For a smooth periodic pressure $p_U$, set $R_U=U_t+U\cdot\nabla U+\nabla p_U$; require $R_U$ odd, supported in $|\xi|\le4\mathsf D$, $\|R_U\|_\infty\le\lambda^{-5/2}$, and $D^2p_U-\nabla R_U\le I$ as quadratic forms. The formal statement imposes these conditions directly. The paper selects the zero-mean Poisson pressure; the formal statement permits any pressure meeting the displayed conditions, without separately requiring $\operatorname{div}R_U=0$.

Write $F=D_aX$, $M=(\nabla U)\circ X$ and $\kappa=F^{-T}k_*$, where $k_*\ne0$. Choose $0\le t_0<T$ with $|\kappa(t_0,0)|=\lambda$. At the origin take a nonzero transverse solution $\mathbf a$ of $\mathbf a_t=-M\mathbf a+2\kappa(\kappa\cdot M\mathbf a)/|\kappa|^2$. Put $\gamma(t)=\lambda^{3/4}|\mathbf a(t,0)|$. For every transverse homogeneous solution $\mathbf b$ and $t_0\le t'\le t\le T$, assume $|\mathbf b(t)|/\gamma(t)\le\mathsf D|\mathbf b(t')|/\gamma(t')$, and assume $\kappa\cdot M\mathbf a\ge\mathsf D^{-1}|\kappa||\mathbf a|$ at the origin. The formal normalization is $0<\gamma\le1$; the paper additionally requires $\max\gamma=1$. Fix $\ell_*=\mathsf D^{-a}$ for a sufficiently large integer $a$, and $h=\lambda^{-1/2}$.

For a profile $f(t,a,s)$, the norm $\|f\|_{[n]}$ sums $\ell_*^{|\alpha|}h^j\sup|\partial_a^\alpha\partial_s^j f|$ over $|\alpha|+j\le n$ on $[0,T]$. The weighted norm $\|f\|_{[n],\gamma}$ uses $[t_0,T]$ and divides by $\gamma(t)$; it differentiates only labels and phase. Each multi-index is counted once. The profiles are smooth on the closed time slab, one-periodic in $s$, and satisfy $f(t,a+n,s+k_*\cdot n)=f(t,a,s)$ for $n\in\mathbb Z^3$. Their stipulated zero values outside the time slab do not assert smoothness across its endpoints.

The finite expansion is selected as follows. Extend the seed to all labels by its transverse equation with $\mathbf a(t_0,a)=(I-P_{\kappa(t_0,a)})\mathbf a(t_0,0)$. Use the fixed smooth radial envelope $g$, equal to one on $|a|\le\ell_*$ and zero on $|a|\ge2\ell_*$, and the fixed one-periodic zero-mean phase profile $F_h$ of Section 3. The time cutoff $\widetilde\chi$ is smooth on $[0,T]$, lies in $[0,1]$, and is zero for $t<t_0$. This permits $\widetilde\chi\equiv1$ when $t_0=0$. On the centered label cell set $A_1=g\mathbf aF_h$, $V_1=\widetilde\chi A_1$ and $\mathsf p_1=\widetilde\chi\mathsf p[A_1]$, where $\mathsf p[A_1]$ has zero phase mean and $A_{1,t}+MA_1+\kappa\partial_s\mathsf p[A_1]=0$. Set $B_1=\bar q_1=C_1=0$ and $C_{p+1}=C[V_p]$. Here $C[V]=\mathbf d\times(-\kappa\times\partial_s^{-1}V/|\kappa|^2)$, $\mathbf d=F^{-T}\nabla_a$, and $\partial_s^{-1}$ is the zero-mean phase primitive. Higher transverse velocities have zero phase mean, are perpendicular to $\kappa$ and satisfy $V_p(0)=0$. The means have $B_p=Fz_{p,t}$, $\operatorname{div}_a z_{p,t}=0$ and $z_p(0)=z_p(T)=0$. Use the recursive sources in (5.27)–(5.28), including $-R_U\circ X$ at mean level two. Mean pressures have zero spatial mean and transverse pressures zero phase mean. The terminal convention is $V_{P+1}=B_{P+1}=0$. All profiles are smooth on $[0,T]$, one-periodic in phase, and satisfy $f(t,a+n,s+k_*\cdot n)=f(t,a,s)$ for $n\in\mathbb Z^3$.

The recursive equations can be stated without referring to another result. Write $Y_i=V_i+C_i$, $Z_i=Y_i+B_i$ and $S=\widetilde\chi'A_1$. For $2\le p\le P$, define

$H_p=(\partial_t+M)C_p+\mathbf d\mathsf p_{p-1}-\mathbf1_{p=2}C[S]+\sum_{i+j=p}(Z_i\cdot\mathbf d)Z_j+\sum_{i+j=p+1,\,i\ge2}(C_i\cdot\kappa)\partial_sY_j$,

where all summation indices are positive integers. Set $\bar f_p=-\langle H_p\rangle_s-\mathbf1_{p=2}R_U\circ X$, $f_p=-(H_p-\langle H_p\rangle_s)$ and $f_p^S=-\sum_{i=2}^p(B_i\cdot\kappa)\partial_sY_{p+1-i}$. The mean equation is $B_{p,t}+MB_p+\mathbf d\bar q_p=\bar f_p$ with $B_p$ and $\bar q_p$ independent of phase. The transverse equation is $V_{p,t}+MV_p+\kappa\partial_s\mathsf p_p=f_p+f_p^S$, with $\kappa\cdot V_p=0$, zero phase mean and $V_p(0)=0$. The new mean is therefore fixed before the current transverse source is determined. The subtraction at level two removes the differentiated cutoff from the leading curl correction. Its remaining contribution to the full equation is $R_{\widetilde\chi}=S+C[S]$.

With $V_{P+1}=B_{P+1}=0$, the remainder is

$R_P=(\partial_t+M)C_{P+1}+\mathbf d\mathsf p_P+\sum_{1\le i,j\le P+1,\,i+j\ge P+1}(Z_i\cdot\mathbf d)Z_j+\sum_{1\le i,j\le P+1,\,i+j\ge P+2}(Z_i\cdot\kappa)\partial_sY_j$.

These are finite sums; there is no passage to an infinite expansion. The stored correction of $V_p$ carries the paper index $C_{p+1}$. At unused index zero, natural-number predecessor is zero, so the bare reindexing gives $C_0=C_1$; the expansion separately imposes $C_1=0$.

For an expansion of finite depth $P\ge2$ obtained by the mean and transverse equations, assume $\mathsf D^C\lambda^{-1/12}\le1$. The formal statement gives, for $2\le p\le P$, $\|V_p\|_{[n],\gamma}+\|f_p+f_p^S\|_{[n],\gamma}+\lambda\|\mathsf p_p\|_{[n],\gamma}\le C_{n,p}\mathsf D^C\lambda^{-5/4-2(p-1)/3}$ and $\|B_p\|_{[n]}+\|\bar f_p\|_{[n]}\le C_{n,p}\mathsf D^C\lambda^{-5/2-2(p-2)/3}$. It also bounds $\|C_{p+1}\|_{[n],\gamma}$ by $C_{n,p}\mathsf D^C\lambda^{-9/4-2(p-1)/3}$ for $1\le p\le P$. At level one the oscillation and pressure bound holds with no source term.

For $W=\sum_{p=1}^P(V_p+C_{p+1}+B_p)$ and $W_{\rm osc}=W-\langle W\rangle_s$, the conclusion includes $\|W_{\rm osc}\|_{[m],\gamma}\le C_{m,P}\mathsf D^C\lambda^{-5/4}$ and $\|\sum_{p=2}^PB_p\|_{[m]}+\|\sum_{p=2}^P\bar f_p\|_{[m]}\le C_{m,P}\mathsf D^C\lambda^{-5/2}$. The remainder in the momentum identity satisfies $\|R_P\|_{[m]}\le C_{m,P}\lambda^{-5/4-2P/3}$, with no extra power of $\mathsf D$.

These are the powers and index ranges of (5.34)–(5.38). The same expansion satisfies every derivative order. The formal statement quantifies the level constants $C_{n,p}$ independently of the terminal depth $P$, while the sum and remainder constants may depend on $P$. The integer exponent $C$ is fixed before the parent, level, depth and derivative order, after choosing the envelope exponent $a$; that same $C$ occurs in the smallness assumption. The stronger verdict records the larger pressure and seed-normalization class. The statement concerns finite expansions; it neither asserts convergence of an infinite expansion at fixed frequency nor supplies a bound on the growth of $C_{n,p}$ with $n$ or $p$.

[`TorusEuler.Paper.theorem_5_6`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.theorem_5_6)

### Lemma 5.7

[Authors’ statement](../?l=b140709-141500) · [Adapted statement](../adapted/?l=b153563-154354)

**Lean is stronger.** Let $0<T\le1$, $\mathsf D\ge2$ and $\lambda\ge1$. The parent $U$ is a smooth odd divergence-free field on $[0,T]\times\mathbb T^3$, with Fourier support $|\xi|\le2\mathsf D$ and flow $X$. The bounds $\|\nabla U\|_\infty,\|D_aX\|_\infty,\|(D_aX)^{-1}\|_\infty\le\mathsf D$ hold. For a smooth periodic pressure $p_U$, set $R_U=U_t+U\cdot\nabla U+\nabla p_U$; require $R_U$ odd, supported in $|\xi|\le4\mathsf D$, $\|R_U\|_\infty\le\lambda^{-5/2}$, and $D^2p_U-\nabla R_U\le I$ as quadratic forms. The formal statement imposes these conditions directly. The paper selects the zero-mean Poisson pressure; the formal statement permits any pressure meeting the displayed conditions, without separately requiring $\operatorname{div}R_U=0$.

Write $F=D_aX$, $M=(\nabla U)\circ X$ and $\kappa=F^{-T}k_*$, where $k_*\ne0$. Choose $0\le t_0<T$ with $|\kappa(t_0,0)|=\lambda$. At the origin take a nonzero transverse solution $\mathbf a$ of $\mathbf a_t=-M\mathbf a+2\kappa(\kappa\cdot M\mathbf a)/|\kappa|^2$. Put $\gamma(t)=\lambda^{3/4}|\mathbf a(t,0)|$. For every transverse homogeneous solution $\mathbf b$ and $t_0\le t'\le t\le T$, assume $|\mathbf b(t)|/\gamma(t)\le\mathsf D|\mathbf b(t')|/\gamma(t')$, and assume $\kappa\cdot M\mathbf a\ge\mathsf D^{-1}|\kappa||\mathbf a|$ at the origin. The formal normalization is $0<\gamma\le1$; the paper additionally requires $\max\gamma=1$. Fix $\ell_*=\mathsf D^{-a}$ for a sufficiently large integer $a$, and $h=\lambda^{-1/2}$.

For a profile $f(t,a,s)$, the norm $\|f\|_{[n]}$ sums $\ell_*^{|\alpha|}h^j\sup|\partial_a^\alpha\partial_s^j f|$ over $|\alpha|+j\le n$ on $[0,T]$. The weighted norm $\|f\|_{[n],\gamma}$ uses $[t_0,T]$ and divides by $\gamma(t)$; it differentiates only labels and phase. Each multi-index is counted once. The profiles are smooth on the closed time slab, one-periodic in $s$, and satisfy $f(t,a+n,s+k_*\cdot n)=f(t,a,s)$ for $n\in\mathbb Z^3$. Their stipulated zero values outside the time slab do not assert smoothness across its endpoints.

Let $g_0$ be such a profile with values in a real normed space, independent of phase outside the repeated support of the envelope. Define its physical field by $g_0^\natural(t,x)=g_0(t,a,k_*\cdot a)$ with $a=X(t,\cdot)^{-1}(x)$. The transformation rule of the profile ensures periodicity in $x$ even when $k_*\notin\mathbb Z^3$. For $t\in[t_0,T]$, the formal statement bounds the sum of its order-$m$ spatial derivative suprema by $C_m(\mathsf D^C\lambda^{3/2})^m\gamma(t)\|g_0\|_{[m],\gamma}$ and gives $\|g_0^\natural(t)\|_{C^{m,1/2}}\le C_m(\mathsf D^C\lambda^{3/2})^{m+1}\gamma(t)\|g_0\|_{[m+1],\gamma}$, including membership in $C^{m,1/2}$.

The same bounds hold on $[0,T]$ with the unweighted norm and $\gamma$ replaced by one. If $g_0$ is independent of phase everywhere, the factor $\lambda^{3/2}$ per derivative disappears. The formal spatial derivative sum in the conclusion ranges over all ordered coordinate sequences of length $m$; the paper's sum ranges over multi-indices. Their multiplicities are bounded in terms of $m$ and absorbed into $C_m$. This physical derivative sum is distinct from the finite profile norm on the right, which counts each multi-index once.

The paper's smooth continuation across cell faces is represented by the globally defined profile and its transformation law. The formal statement also allows arbitrary real normed target spaces, asserts the Hölder regularity explicitly, and uses the broader parent and seed hypotheses above. The envelope exponent is fixed first, followed by $C$ and the sequence $C_m$, before the parent and target space. The integer $C$ is independent of derivative order and no expansion depth enters this estimate.

[`TorusEuler.Paper.lemma_5_7`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_5_7)

### Lemma 5.8

[Authors’ statement](../?l=b142791-143611) · [Adapted statement](../adapted/?l=b155993-156813)

**Lean is stronger.** Let $0<T\le1$, $\mathsf D\ge2$ and $\lambda\ge1$. The parent $U$ is a smooth odd divergence-free field on $[0,T]\times\mathbb T^3$, with Fourier support $|\xi|\le2\mathsf D$ and flow $X$. The bounds $\|\nabla U\|_\infty,\|D_aX\|_\infty,\|(D_aX)^{-1}\|_\infty\le\mathsf D$ hold. For a smooth periodic pressure $p_U$, set $R_U=U_t+U\cdot\nabla U+\nabla p_U$; require $R_U$ odd, supported in $|\xi|\le4\mathsf D$, $\|R_U\|_\infty\le\lambda^{-5/2}$, and $D^2p_U-\nabla R_U\le I$ as quadratic forms. The formal statement imposes these conditions directly. The paper selects the zero-mean Poisson pressure; the formal statement permits any pressure meeting the displayed conditions, without separately requiring $\operatorname{div}R_U=0$.

Write $F=D_aX$, $M=(\nabla U)\circ X$ and $\kappa=F^{-T}k_*$, where $k_*\ne0$. Choose $0\le t_0<T$ with $|\kappa(t_0,0)|=\lambda$. At the origin take a nonzero transverse solution $\mathbf a$ of $\mathbf a_t=-M\mathbf a+2\kappa(\kappa\cdot M\mathbf a)/|\kappa|^2$. Put $\gamma(t)=\lambda^{3/4}|\mathbf a(t,0)|$. For every transverse homogeneous solution $\mathbf b$ and $t_0\le t'\le t\le T$, assume $|\mathbf b(t)|/\gamma(t)\le\mathsf D|\mathbf b(t')|/\gamma(t')$, and assume $\kappa\cdot M\mathbf a\ge\mathsf D^{-1}|\kappa||\mathbf a|$ at the origin. The formal normalization is $0<\gamma\le1$; the paper additionally requires $\max\gamma=1$. Fix $\ell_*=\mathsf D^{-a}$ for a sufficiently large integer $a$, and $h=\lambda^{-1/2}$.

The finite expansion is selected as follows. Extend the seed to all labels by its transverse equation with $\mathbf a(t_0,a)=(I-P_{\kappa(t_0,a)})\mathbf a(t_0,0)$. Use the fixed smooth radial envelope $g$, equal to one on $|a|\le\ell_*$ and zero on $|a|\ge2\ell_*$, and the fixed one-periodic zero-mean phase profile $F_h$ of Section 3. The time cutoff $\widetilde\chi$ is smooth on $[0,T]$, lies in $[0,1]$, and is zero for $t<t_0$. This permits $\widetilde\chi\equiv1$ when $t_0=0$. On the centered label cell set $A_1=g\mathbf aF_h$, $V_1=\widetilde\chi A_1$ and $\mathsf p_1=\widetilde\chi\mathsf p[A_1]$, where $\mathsf p[A_1]$ has zero phase mean and $A_{1,t}+MA_1+\kappa\partial_s\mathsf p[A_1]=0$. Set $B_1=\bar q_1=C_1=0$ and $C_{p+1}=C[V_p]$. Here $C[V]=\mathbf d\times(-\kappa\times\partial_s^{-1}V/|\kappa|^2)$, $\mathbf d=F^{-T}\nabla_a$, and $\partial_s^{-1}$ is the zero-mean phase primitive. Higher transverse velocities have zero phase mean, are perpendicular to $\kappa$ and satisfy $V_p(0)=0$. The means have $B_p=Fz_{p,t}$, $\operatorname{div}_a z_{p,t}=0$ and $z_p(0)=z_p(T)=0$. Use the recursive sources in (5.27)–(5.28), including $-R_U\circ X$ at mean level two. Mean pressures have zero spatial mean and transverse pressures zero phase mean. The terminal convention is $V_{P+1}=B_{P+1}=0$. All profiles are smooth on $[0,T]$, one-periodic in phase, and satisfy $f(t,a+n,s+k_*\cdot n)=f(t,a,s)$ for $n\in\mathbb Z^3$.

The recursive equations can be stated without referring to another result. Write $Y_i=V_i+C_i$, $Z_i=Y_i+B_i$ and $S=\widetilde\chi'A_1$. For $2\le p\le P$, define

$H_p=(\partial_t+M)C_p+\mathbf d\mathsf p_{p-1}-\mathbf1_{p=2}C[S]+\sum_{i+j=p}(Z_i\cdot\mathbf d)Z_j+\sum_{i+j=p+1,\,i\ge2}(C_i\cdot\kappa)\partial_sY_j$,

where all summation indices are positive integers. Set $\bar f_p=-\langle H_p\rangle_s-\mathbf1_{p=2}R_U\circ X$, $f_p=-(H_p-\langle H_p\rangle_s)$ and $f_p^S=-\sum_{i=2}^p(B_i\cdot\kappa)\partial_sY_{p+1-i}$. The mean equation is $B_{p,t}+MB_p+\mathbf d\bar q_p=\bar f_p$ with $B_p$ and $\bar q_p$ independent of phase. The transverse equation is $V_{p,t}+MV_p+\kappa\partial_s\mathsf p_p=f_p+f_p^S$, with $\kappa\cdot V_p=0$, zero phase mean and $V_p(0)=0$. The new mean is therefore fixed before the current transverse source is determined. The subtraction at level two removes the differentiated cutoff from the leading curl correction. Its remaining contribution to the full equation is $R_{\widetilde\chi}=S+C[S]$.

With $V_{P+1}=B_{P+1}=0$, the remainder is

$R_P=(\partial_t+M)C_{P+1}+\mathbf d\mathsf p_P+\sum_{1\le i,j\le P+1,\,i+j\ge P+1}(Z_i\cdot\mathbf d)Z_j+\sum_{1\le i,j\le P+1,\,i+j\ge P+2}(Z_i\cdot\kappa)\partial_sY_j$.

These are finite sums; there is no passage to an infinite expansion. The stored correction of $V_p$ carries the paper index $C_{p+1}$. At unused index zero, natural-number predecessor is zero, so the bare reindexing gives $C_0=C_1$; the expansion separately imposes $C_1=0$.

Let $P\ge2$ and take the resulting finite expansion. Set $W=\sum_{p=1}^P(V_p+C_{p+1}+B_p)$, $\mathsf P=\sum_{p=1}^P(\mathsf p_p+\bar q_p)$, $V=U+W^\natural$ and $\Pi=p_U+\mathsf P^\natural$. The notation $f^\natural(t,x)$ means $f(t,a,k_*\cdot a)$ at $a=X(t,\cdot)^{-1}(x)$. Choose $C_{\rm step}=\Gamma_P\mathsf D^b$ sufficiently large and assume $C_{\rm step}\lambda^{-1/12}\le1$. The exponent $b$ is independent of $P$, whereas $\Gamma_P$ may depend on $P$ and the fixed profiles.

The formal statement says that $V$ is smooth, periodic, odd and divergence free on $[0,T]\times\mathbb T^3$, and that $\Pi$ is smooth and periodic there. Its exact momentum residual is $R_V=R_P^\natural+R_{\widetilde\chi}^\natural$, where $R_P$ is the remainder of the finite expansion and $R_{\widetilde\chi}=\widetilde\chi'(A_1+C[A_1])$ is the activation error. The parent residual has already been canceled in this identity.

With $\bar W=\sum_{p=2}^PB_p$ and $W_{\rm osc}=W-\bar W$, the bounds are $\|W_{\rm osc}^\natural\|_{C_tL^\infty}\le C_{0,P}\mathsf D^b\lambda^{-5/4}$, $\|W_{\rm osc}^\natural\|_{C_tC^{m,1/2}}\le C_{m,P}\mathsf D^{b(m+2)}\lambda^{3(m+1)/2-5/4}$ and $\|\bar W^\natural\|_{C_tC^{m,1/2}}\le C_{m,P}\mathsf D^{b(m+2)}\lambda^{-5/2}$. The residual satisfies $\|R_V\|_{C_tC^{1,1/2}}\le C_{\rm step}\lambda^2(\lambda^{-2P/3}+\|\widetilde\chi'\gamma\|_{\infty,[t_0,T]})$. All three time norms of fields use $[0,T]$; only the last cutoff supremum uses $[t_0,T]$.

The powers, parity, divergence assertion and activation factor agree with (5.46)–(5.48). Pointwise bounds uniform in time represent the displayed time suprema; Hölder regularity is also asserted. The formal statement permits the larger pressure and seed class specified above. After fixing $a$, it chooses thresholds $b_0,\Gamma_{0,P}$ and constants $C_{m,P}$ before the parent, then allows every $b\ge b_0$ and $\Gamma_P\ge\Gamma_{0,P}$ satisfying the corresponding smallness assumption. These constants do not change when $b$ or $\Gamma_P$ is enlarged. No vanishing of the mean correction before activation is concluded.

[`TorusEuler.Paper.lemma_5_8`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_5_8)

### Lemma 5.9

[Authors’ statement](../?l=b145788-146157) · [Adapted statement](../adapted/?l=b158740-159142)

**In the adapted edition.** The pressure Hessian bound explicitly uses the order on quadratic forms.

**Lean is stronger.** Let $0<T\le1$, $\mathsf D\ge2$ and $\lambda\ge1$. The parent $U$ is a smooth odd divergence-free field on $[0,T]\times\mathbb T^3$, with Fourier support $|\xi|\le2\mathsf D$ and flow $X$. The bounds $\|\nabla U\|_\infty,\|D_aX\|_\infty,\|(D_aX)^{-1}\|_\infty\le\mathsf D$ hold. For a smooth periodic pressure $p_U$, set $R_U=U_t+U\cdot\nabla U+\nabla p_U$; require $R_U$ odd, supported in $|\xi|\le4\mathsf D$, $\|R_U\|_\infty\le\lambda^{-5/2}$, and $D^2p_U-\nabla R_U\le I$ as quadratic forms. The formal statement imposes these conditions directly. The paper selects the zero-mean Poisson pressure; the formal statement permits any pressure meeting the displayed conditions, without separately requiring $\operatorname{div}R_U=0$.

Write $F=D_aX$, $M=(\nabla U)\circ X$ and $\kappa=F^{-T}k_*$, where $k_*\ne0$. Choose $0\le t_0<T$ with $|\kappa(t_0,0)|=\lambda$. At the origin take a nonzero transverse solution $\mathbf a$ of $\mathbf a_t=-M\mathbf a+2\kappa(\kappa\cdot M\mathbf a)/|\kappa|^2$. Put $\gamma(t)=\lambda^{3/4}|\mathbf a(t,0)|$. For every transverse homogeneous solution $\mathbf b$ and $t_0\le t'\le t\le T$, assume $|\mathbf b(t)|/\gamma(t)\le\mathsf D|\mathbf b(t')|/\gamma(t')$, and assume $\kappa\cdot M\mathbf a\ge\mathsf D^{-1}|\kappa||\mathbf a|$ at the origin. The formal normalization is $0<\gamma\le1$; the paper additionally requires $\max\gamma=1$. Fix $\ell_*=\mathsf D^{-a}$ for a sufficiently large integer $a$, and $h=\lambda^{-1/2}$.

The finite expansion is selected as follows. Extend the seed to all labels by its transverse equation with $\mathbf a(t_0,a)=(I-P_{\kappa(t_0,a)})\mathbf a(t_0,0)$. Use the fixed smooth radial envelope $g$, equal to one on $|a|\le\ell_*$ and zero on $|a|\ge2\ell_*$, and the fixed one-periodic zero-mean phase profile $F_h$ of Section 3. The time cutoff $\widetilde\chi$ is smooth on $[0,T]$, lies in $[0,1]$, and is zero for $t<t_0$. This permits $\widetilde\chi\equiv1$ when $t_0=0$. On the centered label cell set $A_1=g\mathbf aF_h$, $V_1=\widetilde\chi A_1$ and $\mathsf p_1=\widetilde\chi\mathsf p[A_1]$, where $\mathsf p[A_1]$ has zero phase mean and $A_{1,t}+MA_1+\kappa\partial_s\mathsf p[A_1]=0$. Set $B_1=\bar q_1=C_1=0$ and $C_{p+1}=C[V_p]$. Here $C[V]=\mathbf d\times(-\kappa\times\partial_s^{-1}V/|\kappa|^2)$, $\mathbf d=F^{-T}\nabla_a$, and $\partial_s^{-1}$ is the zero-mean phase primitive. Higher transverse velocities have zero phase mean, are perpendicular to $\kappa$ and satisfy $V_p(0)=0$. The means have $B_p=Fz_{p,t}$, $\operatorname{div}_a z_{p,t}=0$ and $z_p(0)=z_p(T)=0$. Use the recursive sources in (5.27)–(5.28), including $-R_U\circ X$ at mean level two. Mean pressures have zero spatial mean and transverse pressures zero phase mean. The terminal convention is $V_{P+1}=B_{P+1}=0$. All profiles are smooth on $[0,T]$, one-periodic in phase, and satisfy $f(t,a+n,s+k_*\cdot n)=f(t,a,s)$ for $n\in\mathbb Z^3$.

The recursive equations can be stated without referring to another result. Write $Y_i=V_i+C_i$, $Z_i=Y_i+B_i$ and $S=\widetilde\chi'A_1$. For $2\le p\le P$, define

$H_p=(\partial_t+M)C_p+\mathbf d\mathsf p_{p-1}-\mathbf1_{p=2}C[S]+\sum_{i+j=p}(Z_i\cdot\mathbf d)Z_j+\sum_{i+j=p+1,\,i\ge2}(C_i\cdot\kappa)\partial_sY_j$,

where all summation indices are positive integers. Set $\bar f_p=-\langle H_p\rangle_s-\mathbf1_{p=2}R_U\circ X$, $f_p=-(H_p-\langle H_p\rangle_s)$ and $f_p^S=-\sum_{i=2}^p(B_i\cdot\kappa)\partial_sY_{p+1-i}$. The mean equation is $B_{p,t}+MB_p+\mathbf d\bar q_p=\bar f_p$ with $B_p$ and $\bar q_p$ independent of phase. The transverse equation is $V_{p,t}+MV_p+\kappa\partial_s\mathsf p_p=f_p+f_p^S$, with $\kappa\cdot V_p=0$, zero phase mean and $V_p(0)=0$. The new mean is therefore fixed before the current transverse source is determined. The subtraction at level two removes the differentiated cutoff from the leading curl correction. Its remaining contribution to the full equation is $R_{\widetilde\chi}=S+C[S]$.

With $V_{P+1}=B_{P+1}=0$, the remainder is

$R_P=(\partial_t+M)C_{P+1}+\mathbf d\mathsf p_P+\sum_{1\le i,j\le P+1,\,i+j\ge P+1}(Z_i\cdot\mathbf d)Z_j+\sum_{1\le i,j\le P+1,\,i+j\ge P+2}(Z_i\cdot\kappa)\partial_sY_j$.

These are finite sums; there is no passage to an infinite expansion. The stored correction of $V_p$ carries the paper index $C_{p+1}$. At unused index zero, natural-number predecessor is zero, so the bare reindexing gives $C_0=C_1$; the expansion separately imposes $C_1=0$.

Let $P\ge2$ and take the resulting finite expansion. Set $W=\sum_{p=1}^P(V_p+C_{p+1}+B_p)$, $\mathsf P=\sum_{p=1}^P(\mathsf p_p+\bar q_p)$, $V=U+W^\natural$ and $\Pi=p_U+\mathsf P^\natural$. The notation $f^\natural(t,x)$ means $f(t,a,k_*\cdot a)$ at $a=X(t,\cdot)^{-1}(x)$. Choose $C_{\rm step}=\Gamma_P\mathsf D^b$ sufficiently large and assume $C_{\rm step}\lambda^{-1/12}\le1$. The exponent $b$ is independent of $P$, whereas $\Gamma_P$ may depend on $P$ and the fixed profiles.

For every $t\in[0,T]$, $x\in\mathbb T^3$ and $w\in\mathbb R^3$, the formal pressure conclusion is $w\cdot D_x^2\mathsf P^\natural(t,x)w\le C_{\rm step}\lambda^{-1/4}|w|^2$. This is the upper quadratic-form estimate (5.49) for the added pressure. It gives no matching lower bound and is not an estimate of the absolute Hessian norm.

For $t\in[t_0,T]$, it also gives $\|\nabla V(t,0)-\nabla U(t,0)-\widetilde\chi(t)\mathbf a(t,0)\otimes\kappa(t,0)\|\le\lambda^{-1/3}$. The tensor $\mathbf a\otimes\kappa$ acts on $w$ as $(\kappa\cdot w)\mathbf a$, and the error is measured in operator norm. Defining the displayed difference to be $E_c(t)$ gives precisely (5.50); no separate unknown error field is needed.

Both conclusions retain their different time intervals. The formal statement has the larger parent-pressure class and requires only $0<\gamma\le1$, without an attained peak. For each sufficiently large fixed envelope exponent, its thresholds for $b$ and $\Gamma_P$ are chosen before the parent and expansion. The same conclusion holds after increasing those constants if the stronger smallness condition still holds. The pressure estimate is for the finite approximate solution; it is not itself the upper bound for the normalized pressure after Fourier truncation.

[`TorusEuler.Paper.lemma_5_9`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_5_9)

### Lemma 5.10

[Authors’ statement](../?l=b151324-151615) · [Adapted statement](../adapted/?l=b164527-164818)

**Lean is stronger.** Let $0<T\le1$, $\mathsf D\ge2$ and $\lambda\ge1$. The parent $U$ is a smooth odd divergence-free field on $[0,T]\times\mathbb T^3$, with Fourier support $|\xi|\le2\mathsf D$ and flow $X$. The bounds $\|\nabla U\|_\infty,\|D_aX\|_\infty,\|(D_aX)^{-1}\|_\infty\le\mathsf D$ hold. For a smooth periodic pressure $p_U$, set $R_U=U_t+U\cdot\nabla U+\nabla p_U$; require $R_U$ odd, supported in $|\xi|\le4\mathsf D$, $\|R_U\|_\infty\le\lambda^{-5/2}$, and $D^2p_U-\nabla R_U\le I$ as quadratic forms. The formal statement imposes these conditions directly. The paper selects the zero-mean Poisson pressure; the formal statement permits any pressure meeting the displayed conditions, without separately requiring $\operatorname{div}R_U=0$.

Write $F=D_aX$, $M=(\nabla U)\circ X$ and $\kappa=F^{-T}k_*$, where $k_*\ne0$. Choose $0\le t_0<T$ with $|\kappa(t_0,0)|=\lambda$. At the origin take a nonzero transverse solution $\mathbf a$ of $\mathbf a_t=-M\mathbf a+2\kappa(\kappa\cdot M\mathbf a)/|\kappa|^2$. Put $\gamma(t)=\lambda^{3/4}|\mathbf a(t,0)|$. For every transverse homogeneous solution $\mathbf b$ and $t_0\le t'\le t\le T$, assume $|\mathbf b(t)|/\gamma(t)\le\mathsf D|\mathbf b(t')|/\gamma(t')$, and assume $\kappa\cdot M\mathbf a\ge\mathsf D^{-1}|\kappa||\mathbf a|$ at the origin. The formal normalization is $0<\gamma\le1$; the paper additionally requires $\max\gamma=1$. Fix $\ell_*=\mathsf D^{-a}$ for a sufficiently large integer $a$, and $h=\lambda^{-1/2}$.

The finite expansion is selected as follows. Extend the seed to all labels by its transverse equation with $\mathbf a(t_0,a)=(I-P_{\kappa(t_0,a)})\mathbf a(t_0,0)$. Use the fixed smooth radial envelope $g$, equal to one on $|a|\le\ell_*$ and zero on $|a|\ge2\ell_*$, and the fixed one-periodic zero-mean phase profile $F_h$ of Section 3. The time cutoff $\widetilde\chi$ is smooth on $[0,T]$, lies in $[0,1]$, and is zero for $t<t_0$. This permits $\widetilde\chi\equiv1$ when $t_0=0$. On the centered label cell set $A_1=g\mathbf aF_h$, $V_1=\widetilde\chi A_1$ and $\mathsf p_1=\widetilde\chi\mathsf p[A_1]$, where $\mathsf p[A_1]$ has zero phase mean and $A_{1,t}+MA_1+\kappa\partial_s\mathsf p[A_1]=0$. Set $B_1=\bar q_1=C_1=0$ and $C_{p+1}=C[V_p]$. Here $C[V]=\mathbf d\times(-\kappa\times\partial_s^{-1}V/|\kappa|^2)$, $\mathbf d=F^{-T}\nabla_a$, and $\partial_s^{-1}$ is the zero-mean phase primitive. Higher transverse velocities have zero phase mean, are perpendicular to $\kappa$ and satisfy $V_p(0)=0$. The means have $B_p=Fz_{p,t}$, $\operatorname{div}_a z_{p,t}=0$ and $z_p(0)=z_p(T)=0$. Use the recursive sources in (5.27)–(5.28), including $-R_U\circ X$ at mean level two. Mean pressures have zero spatial mean and transverse pressures zero phase mean. The terminal convention is $V_{P+1}=B_{P+1}=0$. All profiles are smooth on $[0,T]$, one-periodic in phase, and satisfy $f(t,a+n,s+k_*\cdot n)=f(t,a,s)$ for $n\in\mathbb Z^3$.

The recursive equations can be stated without referring to another result. Write $Y_i=V_i+C_i$, $Z_i=Y_i+B_i$ and $S=\widetilde\chi'A_1$. For $2\le p\le P$, define

$H_p=(\partial_t+M)C_p+\mathbf d\mathsf p_{p-1}-\mathbf1_{p=2}C[S]+\sum_{i+j=p}(Z_i\cdot\mathbf d)Z_j+\sum_{i+j=p+1,\,i\ge2}(C_i\cdot\kappa)\partial_sY_j$,

where all summation indices are positive integers. Set $\bar f_p=-\langle H_p\rangle_s-\mathbf1_{p=2}R_U\circ X$, $f_p=-(H_p-\langle H_p\rangle_s)$ and $f_p^S=-\sum_{i=2}^p(B_i\cdot\kappa)\partial_sY_{p+1-i}$. The mean equation is $B_{p,t}+MB_p+\mathbf d\bar q_p=\bar f_p$ with $B_p$ and $\bar q_p$ independent of phase. The transverse equation is $V_{p,t}+MV_p+\kappa\partial_s\mathsf p_p=f_p+f_p^S$, with $\kappa\cdot V_p=0$, zero phase mean and $V_p(0)=0$. The new mean is therefore fixed before the current transverse source is determined. The subtraction at level two removes the differentiated cutoff from the leading curl correction. Its remaining contribution to the full equation is $R_{\widetilde\chi}=S+C[S]$.

With $V_{P+1}=B_{P+1}=0$, the remainder is

$R_P=(\partial_t+M)C_{P+1}+\mathbf d\mathsf p_P+\sum_{1\le i,j\le P+1,\,i+j\ge P+1}(Z_i\cdot\mathbf d)Z_j+\sum_{1\le i,j\le P+1,\,i+j\ge P+2}(Z_i\cdot\kappa)\partial_sY_j$.

These are finite sums; there is no passage to an infinite expansion. The stored correction of $V_p$ carries the paper index $C_{p+1}$. At unused index zero, natural-number predecessor is zero, so the bare reindexing gives $C_0=C_1$; the expansion separately imposes $C_1=0$.

Let $P\ge2$ and take the resulting finite expansion. Set $W=\sum_{p=1}^P(V_p+C_{p+1}+B_p)$, $\mathsf P=\sum_{p=1}^P(\mathsf p_p+\bar q_p)$, $V=U+W^\natural$ and $\Pi=p_U+\mathsf P^\natural$. The notation $f^\natural(t,x)$ means $f(t,a,k_*\cdot a)$ at $a=X(t,\cdot)^{-1}(x)$. Choose $C_{\rm step}=\Gamma_P\mathsf D^b$ sufficiently large and assume $C_{\rm step}\lambda^{-1/12}\le1$. The exponent $b$ is independent of $P$, whereas $\Gamma_P$ may depend on $P$ and the fixed profiles.

Let $v$ be a smooth periodic divergence-free perturbation on $[0,T]\times\mathbb T^3$ with $\sup_{t,x}\|D_x^jv(t,x)\|\le\lambda^{-5/2}$ for each integer $0\le j\le2$. The formal statement supplies a flow $Y$ of $V+v$ and proves $\sup_{t,a}\|D_aY(t,a)\|\le C_{\rm step}\lambda^{1/4}$ and the same bound for the derivative of the inverse flow. It also asserts these bounds for every flow solving the stated initial-value problem on $[0,T]$.

The paper assumes the single norm bound $\|v\|_{C_tC^2}\le\lambda^{-5/2}$. The formal hypotheses bound each of the three derivative orders separately in operator norm; the paper's norm bound implies these inequalities. In addition, the formal statement allows the broader parent-pressure class and a nonzero central seed whose peak need not reach $\lambda^{-3/4}$. These are enlargements of the admitted data, while the two bounds in (5.53) are retained.

The inverse derivative means the derivative of the transition from time $t$ back to time zero. At the particle position $Y(t,a)$ it is $(D_aY(t,a))^{-1}$; the bounds over all positions are equivalent because the flow is bijective. The formal fields are periodic lifts to $\mathbb R^3$, and their flows commute with integer translations. Smoothness and the flow conclusions concern the closed interval $[0,T]$, not an unspecified continuation beyond it. All thresholds are fixed before the parent and perturbation.

[`TorusEuler.Paper.lemma_5_10`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_5_10)

### Proposition 5.11

[Authors’ statement](../?l=b155361-156485) · [Adapted statement](../adapted/?l=b168820-169944)

**Lean is stronger.** Let $0<T\le1$, $\mathsf D\ge2$ and $\lambda\ge1$. The parent $U$ is a smooth odd divergence-free field on $[0,T]\times\mathbb T^3$, with Fourier support $|\xi|\le2\mathsf D$ and flow $X$. The bounds $\|\nabla U\|_\infty,\|D_aX\|_\infty,\|(D_aX)^{-1}\|_\infty\le\mathsf D$ hold. For a smooth periodic pressure $p_U$, set $R_U=U_t+U\cdot\nabla U+\nabla p_U$; require $R_U$ odd, supported in $|\xi|\le4\mathsf D$, $\|R_U\|_\infty\le\lambda^{-5/2}$, and $D^2p_U-\nabla R_U\le I$ as quadratic forms. The formal statement imposes these conditions directly. The paper selects the zero-mean Poisson pressure; the formal statement permits any pressure meeting the displayed conditions, without separately requiring $\operatorname{div}R_U=0$.

Write $F=D_aX$, $M=(\nabla U)\circ X$ and $\kappa=F^{-T}k_*$, where $k_*\ne0$. Choose $0\le t_0<T$ with $|\kappa(t_0,0)|=\lambda$. At the origin take a nonzero transverse solution $\mathbf a$ of $\mathbf a_t=-M\mathbf a+2\kappa(\kappa\cdot M\mathbf a)/|\kappa|^2$. Put $\gamma(t)=\lambda^{3/4}|\mathbf a(t,0)|$. For every transverse homogeneous solution $\mathbf b$ and $t_0\le t'\le t\le T$, assume $|\mathbf b(t)|/\gamma(t)\le\mathsf D|\mathbf b(t')|/\gamma(t')$, and assume $\kappa\cdot M\mathbf a\ge\mathsf D^{-1}|\kappa||\mathbf a|$ at the origin. The formal normalization is $0<\gamma\le1$; the paper additionally requires $\max\gamma=1$. Fix $\ell_*=\mathsf D^{-a}$ for a sufficiently large integer $a$, and $h=\lambda^{-1/2}$.

The finite expansion is selected as follows. Extend the seed to all labels by its transverse equation with $\mathbf a(t_0,a)=(I-P_{\kappa(t_0,a)})\mathbf a(t_0,0)$. Use the fixed smooth radial envelope $g$, equal to one on $|a|\le\ell_*$ and zero on $|a|\ge2\ell_*$, and the fixed one-periodic zero-mean phase profile $F_h$ of Section 3. The time cutoff $\widetilde\chi$ is smooth on $[0,T]$, lies in $[0,1]$, and is zero for $t<t_0$. This permits $\widetilde\chi\equiv1$ when $t_0=0$. On the centered label cell set $A_1=g\mathbf aF_h$, $V_1=\widetilde\chi A_1$ and $\mathsf p_1=\widetilde\chi\mathsf p[A_1]$, where $\mathsf p[A_1]$ has zero phase mean and $A_{1,t}+MA_1+\kappa\partial_s\mathsf p[A_1]=0$. Set $B_1=\bar q_1=C_1=0$ and $C_{p+1}=C[V_p]$. Here $C[V]=\mathbf d\times(-\kappa\times\partial_s^{-1}V/|\kappa|^2)$, $\mathbf d=F^{-T}\nabla_a$, and $\partial_s^{-1}$ is the zero-mean phase primitive. Higher transverse velocities have zero phase mean, are perpendicular to $\kappa$ and satisfy $V_p(0)=0$. The means have $B_p=Fz_{p,t}$, $\operatorname{div}_a z_{p,t}=0$ and $z_p(0)=z_p(T)=0$. Use the recursive sources in (5.27)–(5.28), including $-R_U\circ X$ at mean level two. Mean pressures have zero spatial mean and transverse pressures zero phase mean. The terminal convention is $V_{P+1}=B_{P+1}=0$. All profiles are smooth on $[0,T]$, one-periodic in phase, and satisfy $f(t,a+n,s+k_*\cdot n)=f(t,a,s)$ for $n\in\mathbb Z^3$.

Let $P\ge2$ and take the resulting finite expansion. Set $W=\sum_{p=1}^P(V_p+C_{p+1}+B_p)$, $\mathsf P=\sum_{p=1}^P(\mathsf p_p+\bar q_p)$, $V=U+W^\natural$ and $\Pi=p_U+\mathsf P^\natural$. The notation $f^\natural(t,x)$ means $f(t,a,k_*\cdot a)$ at $a=X(t,\cdot)^{-1}(x)$. Choose $C_{\rm step}=\Gamma_P\mathsf D^b$ sufficiently large and assume $C_{\rm step}\lambda^{-1/12}\le1$. The exponent $b$ is independent of $P$, whereas $\Gamma_P$ may depend on $P$ and the fixed profiles.

Fix a smooth radial multiplier $\psi$ with $0\le\psi\le1$, $\psi=1$ on $|\xi|\le1$ and $\psi=0$ for $|\xi|>2$. For $\Lambda\ge1$, let $u=S_\Lambda V$, where the multiplier on $e^{2\pi i\xi\cdot x}$ is $\psi(\xi/\Lambda)$, and let $p$ be the periodic zero-mean solution of $\Delta p=-\operatorname{tr}((\nabla u)^2)$. The formal statement supplies such $u,p$. It proves $u$ smooth, odd and divergence free, with Fourier support $|\xi|\le2\Lambda$, and proves its momentum residual $R_u=u_t+u\cdot\nabla u+\nabla p$ odd and divergence free, with support $|\xi|\le4\Lambda$.

Put $\varepsilon_\Lambda=\Lambda^{2-P}(1+\|V\|_{C_tC^{P,1/2}})^2$. The conclusions are $\|u-V\|_{C_tC^{2,1/2}}\le C_{2,P}\varepsilon_\Lambda$ and $\|R_u\|_{C_tC^{1,1/2}}+\|D^2(p-\Pi)\|_{C_tC^{0,1/2}}\le C\|R_V\|_{C_tC^{1,1/2}}+C_{2,P}\varepsilon_\Lambda$. They imply the stated upper quadratic-form bound $D^2(p-p_U)\le(C_{\rm step}\lambda^{-1/4}+C\|R_V\|_{C_tC^{1,1/2}}+C_{2,P}\varepsilon_\Lambda)I$. All time suprema are over $[0,T]$.

The exponent $2-P$ is an integer, so it is negative when $P>2$; it is not subtraction truncated at zero. The formal estimate for the sum permits the two terms to be evaluated at independent times. This represents the sum of two time suprema in (5.56), not a weaker bound at one common time. The multiplier is fixed before its constants are chosen, and those constants precede the parent, depth and cutoff frequency. The larger parent-pressure and seed classes remain admissible, but the new pressure $p$ is normalized by the Poisson equation exactly as in the paper. Existence is explicit; uniqueness of this normalized pressure follows from the periodic Poisson problem rather than an additional uniqueness clause in this numbered statement.

[`TorusEuler.Paper.proposition_5_11`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.proposition_5_11)

### Lemma 6.1

[Authors’ statement](../?l=b161088-161298) · [Adapted statement](../adapted/?l=b174633-174843)

**Same mathematical strength.** Let $U_0(x)=\sin(2\pi x_2)(e_1+\rho e_3)$ and $B_\rho=2\pi(e_1+\rho e_3)\otimes e_2$. Assume $0<\rho\le1$, $\lambda\ge1$, $T>0$ and $T\|B_\rho\|\le1/8$. The frequency restriction is the standing assumption of §5.1. The formal statement first asserts existence of central paths $\kappa,\mathbf a$ on $[0,T]$ satisfying $\kappa_t=-B_\rho^T\kappa$ and $\mathbf a_t=-(I-2P_\kappa)B_\rho\mathbf a$, where $P_\kappa$ is orthogonal projection onto $\mathbb R\kappa$. They remain nonzero and perpendicular, start with $\kappa(0)=\lambda e_1$ and $\mathbf a(0)=c e_2$ for some $c>0$, and attain $\max_{[0,T]}|\mathbf a|=\lambda^{-3/4}$.

For every such pair, put $\gamma(t)=\lambda^{3/4}|\mathbf a(t)|$ and $\nu(t)=(\kappa/|\kappa|)\cdot B_\rho(\mathbf a/|\mathbf a|)$. For every $\mathsf D\ge2$, every transverse solution $\mathbf b_t=-(I-2P_\kappa)B_\rho\mathbf b$, and every $0\le t'\le t\le T$, it proves $|\mathbf b(t)|/\gamma(t)\le\mathsf D|\mathbf b(t')|/\gamma(t')$ and $\nu(t)\ge\mathsf D^{-1}$. It also proves $\lambda^{1/4}/2\le|\kappa(0)||\mathbf a(0)|\le\lambda^{1/4}$. These are precisely the two conditions (5.5) and the initial-strength interval of Lemma 6.1. Positivity of the seed makes the divisions ordinary positive divisions. The matrix norm is the Euclidean operator norm; for this rank-one matrix it equals the Frobenius norm.

The formal object records only the data at the origin, which are exactly what this lemma estimates. It does not by itself construct the spatially localized perturbation or attach the time cutoff. The paths are defined on all real times, with the equations required on $[0,T]$ and derivatives taken within that interval. Explicit existence accompanies the universal estimate; it formalizes the first-wave construction preceding the lemma rather than replacing the assertion about every normalized first wave.

[`TorusEuler.Paper.lemma_6_1`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_6_1)

### Theorem 7.1

[Authors’ statement](../?l=b168661-169000) · [Adapted statement](../adapted/?l=b183551-183890)

**Different formulation.** The formal theorem constructs a single sequence of approximate velocities with the principal bounds of Theorem 7.1 and also identifies the expansion and truncation used at each step. Its parameter quantifiers and some identifications of the central wave differ from the paper's contextual description.

First fix a smooth radial Fourier symbol $\psi$ with $0\le\psi\le1$, equal to one on the unit ball and zero outside the ball of radius two. For every integer $a_0\ge0$, the formal theorem chooses integers $b\ge1$, $a\ge a_0$ and a majorant $F$ of the fixed-order constants. These choices precede the threshold function $\mathcal B$. Every positive nondecreasing $\mathcal B$ satisfying $F(s)\le\mathcal B(s)$ and $\log\mathcal B(s)\ge4K(s+1)^3$ for $s\ge1$, with $K(s)=320b(s+1)$, then admits a threshold $N_1$. For every real $N\ge N_1$ it constructs the sequence with $\lambda_0=N$, $q_1=1$, $\lambda_j=\lambda_{j-1}^{K(q_j)}$ and $q_{j+1}=\max\{1\le s\le q_j+1:\mathcal B(s)\le\lambda_{j-1}\}$. Thus the envelope exponent can be chosen above any prescribed lower bound; the statement does not assert that every sufficiently large $a$ works. The strength constant is fixed explicitly as $C=18e^3$.

The spatial domain is $\mathbb T^3=\mathbb R^3/\mathbb Z^3$, represented by periodic functions on $\mathbb R^3$. Write $L_j=4\log\lambda_{j+1}$, $\varepsilon_j=L_{j+1}^{-2}$, $\tau_j=\lambda_{j-1}^{-1/8}L_{j+1}^3$ and $S_j=t_j+2\tau_j$ for $j\ge1$, with $S_0=1$. The velocities are jointly smooth on $[0,S_j]\times\mathbb T^3$, odd, divergence free and supported in Fourier frequencies $|k|\le2\lambda_j^5$. The initial field is $U_0(x)=\sin(2\pi x_2)(e_1+\varepsilon_1e_3)$. The flow $X_j$ is the actual label flow of $U_j$ from time zero; $\pi_j$ is its zero-mean pressure; and $R_j=\partial_tU_j+(U_j\cdot\nabla)U_j+\nabla\pi_j$ is its momentum residual. Throughout each slab the theorem gives $\|U_j\|_\infty\le\lambda_j$, $\|(D_aX_j)^{\pm1}\|_\infty\le\lambda_j$, $\|R_j\|_\infty\le\lambda_{j+1}^{-3}$ and $D^2\pi_j\le(\sum_{i<j}\lambda_i^{-1})I$. Matrix inequalities are quadratic-form inequalities and matrix norms are operator norms.

For $j\ge1$, the central gradient is split as $\nabla U_j(t,0)=\nabla U_{j-1}(t,0)+\widetilde\chi_j(t)\mathbf a_j(t)\otimes\kappa_j(t)+E_{c,j}(t)$ on $[t_j,S_j]$, with $\|E_{c,j}\|\le\lambda_j^{-1/4}$. With $E_1=\kappa_j/|\kappa_j|$, $E_2=\mathbf a_j/|\mathbf a_j|$ and $E_3=E_1\times E_2$, the couplings are $\nu_j=E_1\cdot\nabla U_{j-1}(t,0)E_2$ and $\eta_j=E_3\cdot\nabla U_{j-1}(t,0)E_2$. At $t_{j+1}$ they satisfy $\eta_j/\nu_j=\varepsilon_j$, $\pi\le\nu_j\le4\pi$ and $C^{-1}\lambda_j^{1/4}\le|\mathbf a_j||\kappa_j|\le C\lambda_j^{1/4}L_{j+1}^2$. Also $0\le t_{j+1}-t_j\le\tau_j$, and the cutoff equals one from $t_{j+1}$ to $S_j$. The activation times satisfy $0=t_1=t_2<t_3<\cdots\to T_\infty>0$, with $T_\infty<S_j$ for every $j$.

Two comparison guarantees are retained for the central waves. For each wave $j\ge2$, put $\Theta_j=r_j(S_j-t_j)$, where $r_j=\sqrt{2\sigma_{j-1}(t_j)\nu_{j-1}(t_j)}$, and let $\delta_j$ denote its formal comparison error. The construction carries an integer $C_0\ge240$ such that $C_0\varepsilon_{j-1}\le1$ and $C_0\Theta_j^{C_0}\delta_j\le\varepsilon_{j-1}$ for every $j\ge2$. Separately, for every fixed integer $C$, all sufficiently late waves satisfy these inequalities with $C$ in place of $C_0$. There is also a common constant $K$ with $\Theta_j\le K L_{j+1}^4$ for all $j\ge2$. Thus the eventual clause does not mean that the comparison is unavailable at earlier stages for the carried constant. In the exported quantifiers, the construction, including its carried constant, is chosen after $N$. Here $\delta_j$ is the comparison error (2.6) of wave $j$, with suprema over $[t_j,S_j]$.

The oscillation $O_j$ is identified with the oscillatory part of the finite localized expansion, evaluated using the inverse parent flow. The expansion has depth $6K_{j+1}$ and envelope radius $\lambda_{j-1}^{-9a}$, and the child velocity is its parent-plus-increment after Fourier cutoff at $\lambda_j^5$. The support of $O_j(t)$ lies within distance $\lambda_{j-1}^{-1}$ of the integer lattice, which represents the single origin on the torus. For each $t\in[0,S_j]$ the formal conditions give $\|O_j(t)\|_\infty\le\lambda_j^{-1}$ and $\|U_j(t)-U_{j-1}(t)-O_j(t)\|_{C^{m,1/2}}\le\lambda_j^{-1}$ for integers $0\le m\le q_j$. For $j\ge2$, $O_j$ vanishes on $[0,t_j]$. The Hölder bounds are expressed at each time, with a separate finiteness requirement. That spatial norm is the sum over orders through $m$ of the supremum and half-Hölder seminorm of the full derivative tensor, so the bound is stated at each time rather than as a $C([0,S_j];C^{m,1/2})$ norm. Smooth step data are also supplied; the pointwise formulation alone is not evidence that time continuity fails.

Two contextual equalities remain missing from the exported conditions. The localized seed at the origin is identified with $\mathbf a_j$, but the transported covector $(D_aX_{j-1})^{-T}k_*$ is not identified with $\kappa_j$. Moreover, the first wave's initial covector $\lambda_1e_1$, initial amplitude direction $e_2$ and attained normalization $\max|\mathbf a_1|=\lambda_1^{-3/4}$ are not recorded; its initial first coupling $\nu_1(0)=2\pi$ is recorded. Later waves do carry their prescribed initial directions and normalization through the selected crossing data. These omissions, together with the precise envelope-exponent quantifier, prevent an unqualified assertion that the two statements are identical.

[`TorusEuler.Paper.theorem_7_1`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.theorem_7_1)

### Proposition 8.1

[Authors’ statement](../?l=b184468-184935) · [Adapted statement](../adapted/?l=b200196-200668)

**In the adapted edition.** The compact time interval explicitly has a nonnegative endpoint.

**Different formulation.** For the common construction of Theorem 7.1, the formal statement produces a smooth odd periodic Euler solution on $[0,T_\infty)$ with mean-zero pressure. The initial data converge in every $C^{m,1/2}$, and convergence in that spatial norm is uniform on every $[0,S]$ with $S<T_\infty$. It then says that any maximal solution of finite lifespan from the same datum lasts at least to $T_\infty$ and agrees with this limit. The paper instead starts with the maximal solution supplied by general existence theory, whose lifespan may still be infinite at this point. Thus the preterminal existence and convergence conclusions are present, but general maximal-solution existence is not asserted by this declaration. Corollary 8.3 subsequently proves finite maximality for the constructed solution. Fields are period-one functions on $\mathbb R^3$; the spatial Hölder norm is $\sum_{i\le m}(\sup|D^if|+[D^if]_{1/2})$, with $D^if$ the full $i$th derivative tensor.

[`TorusEuler.Paper.proposition_8_1`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.proposition_8_1)

### Proposition 8.2

[Authors’ statement](../?l=b186220-186374) · [Adapted statement](../adapted/?l=b201999-202153)

**Lean is stronger.** For the smooth Euler limit of the common construction, the formal statement gives both printed conclusions: one finite bound for the velocity throughout $[0,T_\infty)$ and the full limit $|\operatorname{curl}u(t,0)|\to\infty$. It additionally supplies fixed real constants $c>0,C$ and an index $J$ such that, for every $j\ge J$ and every $t\in[t_j,t_{j+1})$, $|\operatorname{curl}u(t,0)|\ge c\lambda_{j-1}^{1/8}-C\lambda_{j-1}^{1/32}-C$. This bound is for the limiting solution, whereas (8.2) bounds the approximation and uses the older-gradient term $\lambda_{j-2}^9$. The constants are independent of the late index and time. The velocity norm is the essential supremum on the unit cell. The stronger interval estimate, together with crossing-duration bounds, supplies the direct integral argument in the formal Corollary 8.3; a divergent pointwise limit alone would not suffice.

[`TorusEuler.Paper.proposition_8_2`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.proposition_8_2)

### Corollary 8.3

[Authors’ statement](../?l=b189054-189169) · [Adapted statement](../adapted/?l=b205187-205302)

**In the adapted edition.** The edition adds a direct integration argument after the proof using the periodic Beale–Kato–Majda criterion. It combines the lower curl bound with a lower bound on the length of each late crossing interval.

**Different formulation.** The final conclusions agree: $T_*=T_\infty>0$, the constructed Euler solution has no smooth continuation, and both integrals in (1.2) are infinite. The formal conclusion also identifies the same lifespan for every maximal solution of finite lifespan from the same datum. The explicit implication has a different preceding input: its version of Proposition 8.2 includes a uniform lower bound $c\lambda_{j-1}^{1/8}-C\lambda_{j-1}^{1/32}-C$ on every sufficiently late activation interval. The proof combines that bound with lower estimates for the crossing durations. The paper instead invokes the periodic Beale–Kato–Majda criterion after identifying the maximal time. The quantitative input is established earlier in the formal construction; it is not an unproved extra condition on the final example. This declaration proves the construction-specific corollary without proving the general continuation criterion. The integrals are nonnegative Lebesgue integrals over $[0,T_\infty)$, with essential suprema over one spatial period and operator norm for the gradient.

[`TorusEuler.Paper.corollary_8_3`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.corollary_8_3)

### Proposition 8.4

[Authors’ statement](../?l=b189856-190037) · [Adapted statement](../adapted/?l=b205989-206170)

**Same mathematical strength.** For the Euler limit of the common construction, the formal statement gives both limits in Proposition 8.4. For every compact $K$ avoiding the torus origin and every integer $m\ge0$, $u(t)$ and $\partial_tu(t)$ converge uniformly with all spatial derivatives through order $m$ as $t\uparrow T_\infty$. The torus is represented by periodic functions on $\mathbb R^3$, so a compact observation set avoids every integer lattice point. For each field, compact set and order, the limit is represented by a $C^m$ function on an open neighbourhood of that set. The time derivative is taken within $[0,T_\infty)$, including a right derivative at zero. These are local spatial limits of the velocity and its first time derivative. The statement does not assert that every construction admits one jointly smooth extension through the terminal time; the auxiliary note proves that stronger conclusion after a suitable choice of the construction.

[`TorusEuler.Paper.proposition_8_4`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.proposition_8_4)

### Theorem A.1

[Authors’ statement](../?l=b192595-193093) · [Adapted statement](../adapted/?l=b213329-213827)

**Lean is stronger.** On $I=[0,1]$ and $\mathbb T^3=\mathbb R^3/\mathbb Z^3$, let $K(t,a)$ be symmetric and $\Omega(t,a)$ skew-symmetric. Assume $K\ge\kappa I$ for $\kappa>0$ and $\int_0^1(Kz_t\cdot z_t+\Omega z_t\cdot z)\,dt\ge\mu\int_0^1|z_t|^2\,dt$ for every label $a$ and $z\in H^1_0(I;\mathbb R^3)$, with $\mu>0$. The formal numbered statement retains both symmetry assumptions.

For every $L\in C(I;C^{0,1/2})$ it supplies unique divergence-free $z\in C^1(I;C^{0,1/2})$ and time-independent divergence-free $c\in C^{0,1/2}$, and a unique gradient $\nabla\phi\in C(I;C^{0,1/2})$, such that $Kz_t-\int_0^t\Omega(s)z_t(s)\,ds+L=c+\nabla\phi$ and $z(0)=z(1)=0$. Uniqueness is on $I$ and concerns the gradient, not the scalar potential up to an additive function of time. Smooth $K,\Omega,L$ give smooth $z,c,\nabla\phi$ on the closed slab.

The regularity hypothesis is weaker than the paper's $C(I;C^{1,1/2})$: the formal statement assumes continuity in $C^{0,1/2}$, spatial differentiability, and uniform bounds $K_0,K_1,\Omega_0,\Omega_1$ on the coefficients and their first spatial derivatives. With $Q=2+\kappa^{-1}+\mu^{-1}+K_0+K_1+\Omega_0+\Omega_1$, it gives $\sup_{t\in I}\|z_t(t)\|_{C^{0,1/2}}\le CQ^p\sup_{t\in I}\|L(t)\|_{C^{0,1/2}}$, for a single constant $C$ and nonnegative integer $p$ chosen before the data. The paper's hypotheses imply these bounds, with a change of absolute constant.

The formal $C^{0,1/2}$ norm is the maximum of the supremum norm and the half-Hölder seminorm; this is equivalent to their sum. Sobolev test paths are represented by the primitives of zero-mean $L^2$ velocities, which is exactly $H^1_0$. Divergence-free Hölder fields are understood weakly. Neither representation reduces the paper's solution or test class.

[`TorusEuler.Paper.theorem_A_1`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.theorem_A_1)

### Lemma A.2

[Authors’ statement](../?l=b194285-195191) · [Adapted statement](../adapted/?l=b215424-216330)

**Lean is stronger.** There are two settings: $H=\mathbb R^3$ with $\mathcal R=\mathbb P$, the spatial Leray projection; or $H=L^2(0,1;\mathbb R^3)$ with $\mathcal R=\mathbb P\mathcal Q$, where $\mathcal Qw=w-\int_0^1w(t)\,dt$. Let $B(a)$ be a field of bounded linear operators on $H$, with a supplied bound $L_B\ge0$ such that $\|B(a)-B(b)\|\le L_Bd(a,b)$. Suppose $\langle B(a)w,w\rangle\ge\mu\|w\|^2$ for $\mu>0$ and every label, for all $w$ in the first setting and all zero-time-mean $w$ in the second. Symmetry of $B$ is not required.

The formal statement gives a bounded invertible map $v\mapsto\mathcal R(Bv)$ on the projected space $\mathcal RC^{0,1/2}(\mathbb T^3;H)$ and the estimate $\|v\|_{C^{0,1/2}}\le C(2+\mu^{-1}+\|B\|_\infty+L_B)^p\|\mathcal RBv\|_{C^{0,1/2}}$. One $C$ and nonnegative integer $p$ serve both settings. The range condition includes spatial divergence freedom and, in the path setting, zero time mean; the inverse is not asserted on all Hölder fields.

For every integer $k\ge1$ such that $B\in C^{k,1/2}$, the same map is invertible on the corresponding projected $C^{k,1/2}$ space, with equivalence of the norms of $v$ and $\mathcal RBv$. The constants in this higher-order comparison may depend on $k$ and the coefficient and coercivity controls; the statement does not give an order-independent higher norm bound.

The paper assumes $B\in C^{1,1/2}$ already for the base inverse. The formal statement only needs the displayed Lipschitz bound there, while retaining the paper's higher regularity assumptions for the higher-order conclusions. A bounded first spatial derivative supplies a Lipschitz constant, so the paper's estimate follows after enlarging the absolute constant. Spatial fields are functions on the flat unit torus; $L^2$ paths identify functions equal almost everywhere, so including or excluding the time endpoints does not alter the path space.

[`TorusEuler.Paper.lemma_A_2`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_A_2)

### Lemma B.1

[Authors’ statement](../?l=b203508-204329) · [Adapted statement](../adapted/?l=b225363-226248)

**In the adapted edition.** The derivative commutation is stated for smooth fields and a cutoff scale fixed in time.

**Different formulation.** Let $S_\Lambda$ act on $\mathbb T^3=\mathbb R^3/\mathbb Z^3$ by the Fourier multiplier $\psi(\xi/\Lambda)$. The paper assumes a smooth radial symbol, $0\le\psi\le1$, equal to one on the unit ball and supported in the radius-two ball, and $\Lambda\ge1$. The formal statement permits even symbols and every $\Lambda>0$. It chooses the operator constant and the sequences of Bernstein and tail constants after $\psi$ but before the frequency, target spaces and fields.

For continuous fields with frequencies at most $4\Lambda$, it proves $\sum_{|\beta|=m}\|\partial^\beta f\|_\infty\le C_m\Lambda^m\|f\|_\infty$, with every multi-index counted once and any real normed target, including incomplete targets. The frequency hypothesis means that every continuous real linear scalar measurement has no Fourier coefficients outside that band. For continuous complex Banach-valued fields and continuous real velocities, it proves $\|(I-S_\Lambda)f\|_{C^{s,1/2}}\le C_M\Lambda^{s-M}\|f\|_{C^{M,1/2}}$ for $0\le s\le M$, with the asserted output regularity. The exponent is an integer difference: $s<M$ gives a reciprocal power, not exponent zero.

Its essential-supremum operator bound uses almost-everywhere strongly measurable, essentially bounded inputs in complex Banach spaces. Its real-velocity branch assumes continuity; a separate theorem proves the measurable real-velocity estimate. The separate real normed-space estimate uses the real part of the scalar spectral kernel, with the ordinary multiplier interpretation for even symbols and complete targets. That separate result is not an additional clause of the numbered statement.

Spatial commutation is explicit at every complex order and at first real coordinate order. One time derivative commutes on a smooth nondegenerate closed slab, with derivatives taken within the slab at its endpoints. Higher real orders require repeated application. Parity, divergence preservation for smooth real velocities and output support $|\xi|\le2\Lambda$ are also included. The Hölder norms are sums over orders of the supremum and half-Hölder seminorm of the full derivative tensor. The comparison therefore records broader symbol and scale ranges alongside differently organized target and derivative scopes, rather than claiming literal identity of the full statements.

[`TorusEuler.Paper.lemma_B_1`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_B_1)

### Lemma D.1

[Authors’ statement](../?l=b209031-209781) · [Adapted statement](../adapted/?l=b231765-232549)

**In the adapted edition.** The revised statement makes the integer derivative order and label and phase smoothness explicit.

**Lean is stronger.** Let $I$ be a specified time set, $\ell_*,h>0$, and $\gamma:I\to(0,\infty)$. For fields $f(t,a,s)$ smooth in $(a,s)\in\mathbb R^3\times\mathbb R$, put $\|f\|_{[n]}=\sum_{|\beta|+j\le n}\ell_*^{|\beta|}h^j\sup_{t,a,s}|\partial_a^\beta\partial_s^jf|$ and $\|f\|_{[n],\gamma}=\|f/\gamma\|_{[n]}$. Each mixed multi-index occurs once. The boundedness hypotheses refer to the derivative families entering the following right sides, before a real-valued supremum is used as a norm.

If the derivatives of $f/\gamma$ through order $n+1$ are uniformly bounded, the formal statement proves $\sum_i\|\partial_{a_i}f\|_{[n],\gamma}\le3\ell_*^{-1}\|f\|_{[n+1],\gamma}$ and $\|\partial_sf\|_{[n],\gamma}\le h^{-1}\|f\|_{[n+1],\gamma}$. If the derivatives of $f$ and $g/\gamma$ through order $n$ are bounded, it proves $\|B(f,g)\|_{[n],\gamma}\le C_n\|B\|\|f\|_{[n]}\|g\|_{[n],\gamma}$ for any continuous bilinear map $B$ between real normed spaces. These estimates do not require phase periodicity.

For a period-one real Banach-valued field whose normalized derivatives through order $n$ are bounded, phase averaging is contractive and subtracting the phase average costs at most two. For zero phase mean, the primitive $\int_0^sf-\int_0^1\int_0^rf$ also costs at most two. Each output has bounded derivative families. No time differentiability is assumed, and positivity of $\gamma$ alone does not imply boundedness after normalization.

For phase-independent fields and $\gamma=1$, the product estimate also holds in the spatial half-Hölder finite norms. Each half-Hölder contribution is the maximum of the uniform norm and seminorm, equivalent within a factor two to their sum. The formal statement thus supplies the estimates of Lemma D.1 with explicit derivative and primitive constants and a general bilinear product. Its constants are independent of the fields, scales and time weight.

[`TorusEuler.Paper.lemma_D_1`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_D_1)

### Lemma D.2

[Authors’ statement](../?l=b210879-210966) · [Adapted statement](../adapted/?l=b233647-233758)

**In the adapted edition.** The revised statement explicitly assumes a derivative scale of at least one.

**Different formulation.** For smooth phase-independent coefficients and $\mathsf D\ge1$, the formal statement retains polynomial derivative bounds under products and inversion, with output constants chosen before the time domain, parent parameter and fields. It extends matrix products to bounded bilinear actions and inversion to complete real normed algebras, requiring pointwise invertibility. Its exponents are nonnegative integers: input exponents $q,r$ give product exponent $2\max(q,r)$, and inverse growth exponent $e$ gives inverse exponent $3\max(q,e)$. In part (c), $0<\ell_*\le\mathsf D^{-q}$ implies $\|c\|_{[n]}\le C_n\mathsf D^q$ and $\ell_*^m|c|_m\le C_m\mathsf D^{2q}\ell_*$ for $m\ge1$. The paper retains its specified real exponent $C$ in this part. Replacing it by $\lceil C\rceil$ changes both the allowed radius and the concluding powers. For $C=1/2$ and $\mathsf D=4$, the paper's radius bound is $1/2$, whereas the rounded condition is $1/4$. Rounding is adequate when the construction can choose a smaller radius, but it does not prove the literal clause at the original fixed exponent.

[`TorusEuler.Paper.lemma_D_2`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_D_2)

### Lemma D.3

[Authors’ statement](../?l=b212500-213780) · [Adapted statement](../adapted/?l=b235292-236615)

**In the adapted edition.** The zero-order estimate is a hypothesis on every admissible solution with its own forcing and prescribed data.

**Lean is stronger.** Assume a finite coefficient equation $\mathcal Lv=\mathcal L_0v+\sum_\nu T_\nu(c_\nu v)=f$, a zero-order estimate for every admissible unknown with its own forcing, principal commutation and product-rule identities, commuting coefficient and forcing derivatives, and nonnegative operator bounds. For a conclusion at order $n$, the formal statement needs the weighted coefficient bounds (D.7) only for $1\le m\le n$. It then proves $\|v\|_{[n]}\le C_nC_{\rm low}\|f\|_{[n]}$, preserving one factor of the zero-order bound. The spaces are arbitrary real seminormed vector spaces and the derivatives form an arbitrary finite ordered family. Thus constraints, equations modulo gradients and prescribed data must be represented in the chosen solution and forcing spaces and their derivative maps. The weighted spatial-and-phase norms, or the half-Hölder norms, are applications after these choices. The constant is selected before the spaces, maps and coefficients, but may depend on the number of derivative directions, which is fixed in the paper. It does not depend on the values of the derivative maps: those are introduced after the constant. The result estimates existing solutions; it asserts no existence or invertibility of a general equation.

[`TorusEuler.Paper.lemma_D_3`](../lean/?m=TorusEuler.Paper.Spine&d=TorusEuler.Paper.lemma_D_3)

### Auxiliary note · Theorem 1.1

[Authors’ statement](../?l=b231757-232158) · [Adapted statement](../adapted/?l=b257642-258043)

**Lean statement only.** This proposition ranges over admissible cutoffs and threshold functions meeting both the spatial and time-derivative bounds. It describes the wider smooth space-time extension claim, with no proof attached to this declaration.

[`TorusEuler.Paper.Aux.Statement.theorem_1_1`](../lean/?m=TorusEuler.Paper.Auxiliary.Statements&d=TorusEuler.Paper.Aux.Statement.theorem_1_1)

**Lean is weaker.** The checked theorem chooses a monotone threshold function and a lower bound on the initial frequency, giving smooth extension away from the origin for a selected construction at each sufficiently large initial frequency. Its witness also supplies both increment estimates used by the checked auxiliary lemmas.

[`TorusEuler.auxiliaryTerminalSmoothness`](../lean/?m=TorusEuler.AuxiliaryTerminalSmoothness&d=TorusEuler.auxiliaryTerminalSmoothness)

### Auxiliary note · Lemma 1.2

[Authors’ statement](../?l=b233476-233771) · [Adapted statement](../adapted/?l=b258920-259314)

**In the adapted edition.** The revised statement chooses the starting index after fixing the derivative orders and the construction. It specifies one-sided time derivatives at the endpoints.

**Lean statement only.** The open statement allows every admissible cutoff and every construction with the listed stage and threshold hypotheses. It fixes the two derivative orders before choosing a starting index for the mixed-increment estimate.

[`TorusEuler.Paper.Aux.Statement.lemma_1_2`](../lean/?m=TorusEuler.Paper.Auxiliary.Statements&d=TorusEuler.Paper.Aux.Statement.lemma_1_2)

**Lean is weaker.** The checked lemma extracts mixed-increment bounds and time continuity from the construction and threshold chosen by `TorusEuler.auxiliaryTerminalSmoothness`. The estimate holds for each sufficiently large initial frequency with the selected schedule.

[`TorusEuler.auxiliaryLemma12`](../lean/?m=TorusEuler.PaperAuxiliaryStatements&d=TorusEuler.auxiliaryLemma12)

### Auxiliary note · Lemma 1.3

[Authors’ statement](../?l=b234101-234471) · [Adapted statement](../adapted/?l=b259732-260102)

**Lean statement only.** The open statement allows every admissible cutoff and every construction with the listed stage and threshold hypotheses. It chooses the exponent and starting index for the velocity and residual bounds after fixing the time-derivative order.

[`TorusEuler.Paper.Aux.Statement.lemma_1_3`](../lean/?m=TorusEuler.Paper.Auxiliary.Statements&d=TorusEuler.Paper.Aux.Statement.lemma_1_3)

**Lean is weaker.** The checked lemma uses the same construction and chosen threshold as the checked mixed-increment lemma. It extracts the endpoint derivative bounds from `TorusEuler.auxiliaryTerminalSmoothness` and proves continuity in the spatial supremum norm.

[`TorusEuler.auxiliaryLemma13`](../lean/?m=TorusEuler.PaperAuxiliaryStatements&d=TorusEuler.auxiliaryLemma13)

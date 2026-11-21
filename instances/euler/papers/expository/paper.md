
<!-- passage:front -->
# Reading the formal statements as mathematics

The paper is *Finite-Time Singularity Formation for the Three-Dimensional Euler Equations*, by Levent Alpöge, Tristan Buckmaster and Matei P. Coiculescu; the formal statements are theirs, at commit `fd3a158`. A definition specifies an object or a condition; an existence theorem supplies an object satisfying it. A step used inside a proof is not automatically a conclusion of the theorem it is linked to. Each card states its own hypotheses and conclusion.
<!-- /passage:front -->

## What a comparison means

<!-- passage:sec-what-a-comparison-means -->

**Same**: the quoted assertion agrees after the stated translation. **Stronger**: the formal statement has fewer hypotheses, more conclusions or a sharper bound, and the card names the difference. **Weaker**: the converse. **Different**: neither direction fits, for example when a definition or a final estimate is linked to a sentence about a construction or an intermediate identity. A judgment concerns the quoted assertion only; a shared name or number is not evidence of equivalence.
<!-- /passage:sec-what-a-comparison-means -->

## The torus and the time interval

<!-- passage:sec-the-torus-and-the-time-interval -->

The torus is $\mathbb T^3=\mathbb R^3/\mathbb Z^3$. Fields are integer-periodic functions on $\mathbb R^3$ or, in the endpoint spaces, functions on the quotient. Integrals and essential suprema use the unit cube $[-1/2,1/2]^3$, of volume one. Avoiding the torus origin means avoiding every point of $\mathbb Z^3$ on the covering space. The lift uses the Euclidean distance and the endpoint quotient the maximum of the three circle distances; their Hölder seminorms are equivalent, not equal.

Functions have values at every real time, but Euler, smoothness and uniqueness are asserted only on the stated interval. A classical solution is jointly smooth on $[0,T_*)\times\mathbb R^3$ with $0<T_*<\infty$; maximality excludes a smooth Euler extension agreeing in velocity on a longer interval. The approximate stages live on closed intervals $[0,S_j]$, and their activation times tend to $T_\infty<S_j$. Derivatives at an included endpoint are one-sided.
<!-- /passage:sec-the-torus-and-the-time-interval -->

## Norms and default values

<!-- passage:sec-norms-and-default-values -->

Vectors have the Euclidean norm and matrices its operator norm; $D_xu$ has entries $\partial_ju_i$. The $L^\infty$ quantities in Theorem 1.1 are essential suprema in $[0,\infty]$, and a nonnegative time integral may equal $\infty$. The endpoint $C^{0,1/2}$ norm is $\max(\|f\|_\infty,[f]_{1/2})$; the $C^{m,1/2}$ norm used for convergence sums the supremum and half-Hölder seminorm of the derivatives through order $m$; Appendix D sums weighted coordinate derivatives. These conventions are not interchangeable inside an estimate, and a supremum in time of a spatial norm is not a space-time norm.

Some operations have default values. Division by zero gives zero, so $v/|v|$ is a unit vector only when $v\ne0$. The square root of a negative number is zero; $\log0=0$ and $\log(-x)=\log x$. A real supremum of an unbounded set is zero; an integral of a nonintegrable function is zero. Derivative orders and schedule exponents are nonnegative integers, and subtraction of such indices stops at zero. None of these defaults supplies a missing hypothesis: each card says where positivity, regularity and integrability enter.
<!-- /passage:sec-norms-and-default-values -->

## The wave and its frame

<!-- passage:sec-the-wave-and-its-frame -->

For nonzero perpendicular $k_p,\mathbf a_p$ the frame is $E_1=k_p/|k_p|$, $E_2=\mathbf a_p/|\mathbf a_p|$, $E_3=E_1\times E_2$. At $t_0$ freeze $\sigma=|k_p||\mathbf a_p|$, $\nu=E_1\cdot BE_2>0$ and $\eta=E_3\cdot BE_2>0$, with $B$ the older gradient; put $\varepsilon=\eta/\nu$, $r=\sqrt{2\sigma\nu}$, $S=\sigma/r$ and $\tau=r(t-t_0)$. The reference angle $\arctan(\varepsilon\tau^2/2)$ is not the actual wave direction, and the reference zero need not locate the actual amplitude maximum. Amplitude normalization specifies an attained maximum, not only an upper bound.

A profile $f(t,a,s)$ has independent label and phase variables; physical evaluation substitutes $a=X(t,\cdot)^{-1}(x)$ and $s=k_*\cdot a$, and a physical force becomes $f(t,X(t,a))$ in labels. The hierarchy separates exact algebraic cancellation, solvability of the mean and transverse equations, and quantitative bounds; its stability assumption controls every transverse homogeneous solution, not only the selected wave.
<!-- /passage:sec-the-wave-and-its-frame -->

## The endpoint problem

<!-- passage:sec-the-endpoint-problem -->

Put $F=D_aX$, $M=(D_xU)\circ X$, $K=F^TF$, $\Omega=F^T(M^T-M)F$ and $H^\#=-(M_t+M^2)$. The hypothesis $H^\#\le I$ bounds a quadratic form from above and allows large negative eigenvalues. The unknowns satisfy $Kv-\int_0^t\Omega v+L=c+\nabla_a\phi$, $v=z_t$, $z(0)=z(T)=0$, $\operatorname{div}_az=0$, with $c$ independent of time and divergence free. Uniqueness concerns $z$, $v$, $c$ and the pressure gradient; the potential is fixed only by its zero mean. The velocity bound keeps the source norm, $\|v\|\le A\|L\|$. The formal theorem allows weaker coefficient regularity than the paper but keeps ellipticity and displacement coercivity.
<!-- /passage:sec-the-endpoint-problem -->

## The sequence and the terminal time

<!-- passage:sec-the-sequence-and-the-terminal-time -->

The indices follow the paper: $\lambda_0=N$, $q_1=1$, $L_j=4\log\lambda_{j+1}$, $\varepsilon_j=L_{j+1}^{-2}$; the maximum rule picks the greatest admissible order. Constants chosen before the data are uniform in those data. The real cutoff uses the real part of a spectral kernel, and its identification with the multiplier uses an even symbol, as the paper's radial symbol is. Appendix D's weighted estimates need bounds for $f/\gamma$; positivity of $\gamma$ alone does not give them. Local limits of $u$ and $\partial_tu$ are distinct from a smooth extension through the terminal time; the auxiliary theorem supplies such an extension away from the origin and imposes no Euler equation after the terminal time.
<!-- /passage:sec-the-sequence-and-the-terminal-time -->



<!-- passage:front -->
# Reading the formal statements as mathematics

The references below are to the paper of Levent Alpöge, Tristan Buckmaster and Matei P. Coiculescu. A definition specifies a mathematical object or a condition; an existence theorem supplies an object satisfying it. Each comparison keeps that distinction explicit.
<!-- /passage:front -->

## The torus and periodic fields

<!-- passage:sec-the-torus-and-periodic-fields -->

The torus is $\mathbb T^3=\mathbb R^3/\mathbb Z^3$. Velocity and pressure are represented by functions on $\mathbb R^3$ satisfying $f(x+n)=f(x)$ for every integer vector $n$. Integrals and essential suprema use $[-1/2,1/2]^3$; its boundary has zero volume. The punctured torus is represented by $\mathbb R^3\setminus\mathbb Z^3$, since every lattice point represents the same origin. Some endpoint spaces instead use functions directly on the quotient. These are two representations of the same spatial domain.
<!-- /passage:sec-the-torus-and-periodic-fields -->

## Velocity, pressure and norms

<!-- passage:sec-velocity-pressure-and-norms -->

Velocity is vector valued and pressure scalar valued. Their underlying functions are defined at all real times; the hypotheses specify where they are smooth and satisfy the equations. Pressure has zero spatial mean. The gradient acts by $D_xu\,v$, consistent with $(\nabla u)_{ij}=\partial_j u_i$; its pointwise norm is the Euclidean operator norm. The $L^\infty$ quantity is an essential supremum in $[0,\infty]$. For smooth periodic fields it equals the ordinary supremum. Derivative expressions are assigned zero when differentiability fails; smoothness hypotheses are therefore part of the mathematical content.
<!-- /passage:sec-velocity-pressure-and-norms -->

## Classical solutions and maximality

<!-- passage:sec-classical-solutions-and-maximality -->

A classical solution is jointly smooth on $[0,T)\times\mathbb R^3$, periodic, and satisfies Euler pointwise, with $T>0$ finite. At zero the time derivative is taken from the right. Maximality excludes a smooth periodic Euler solution on any longer interval agreeing in velocity before $T$. Two classical solutions from the same data agree on their common interval. For maximal solutions, the formal version of Theorem 1.1 also asserts equality of the lifespans. Equality outside the solution intervals is neither required nor meaningful as a uniqueness assertion.
<!-- /passage:sec-classical-solutions-and-maximality -->

## The singular time and spatial limits

<!-- passage:sec-the-singular-time-and-spatial-limits -->

Theorem 1.1 uses one endpoint $T_*$ for maximality, central vorticity divergence and both infinite nonnegative time integrals in (1.2). It also bounds velocity uniformly before $T_*$. For every compact set away from the lattice and every $m$, the spatial derivatives through $m$ of $u$ and $\partial_tu$ converge uniformly to derivatives of local $C^m$ fields. This is a spatial limit. Remark 1.2 separately gives a smooth space-time extension away from the origin, without imposing Euler after $T_*$. The accumulation time of the approximate sequence is identified with the maximal lifespan by a later result, not by convergence alone.
<!-- /passage:sec-the-singular-time-and-spatial-limits -->

## The profile

<!-- passage:sec-the-profile -->

For $0<h\le1$, $F_h$ is smooth, odd and one-periodic; $P_h$ is its mean-zero periodic primitive. The normalization $F_h'(0)=1$ preserves the central gradient, while $|F_h|\le Ch$ makes the velocity small. Constants are chosen before the width and phase. In $|F_h^{(j)}|\le C_jh^{1-j}$, $1-j$ is an integer and may be negative. The family is defined outside the admissible width range as well, but the profile theorem imposes its conclusions only within that range. It asserts no smooth dependence on $h$.
<!-- /passage:sec-the-profile -->

## Localized profiles

<!-- passage:sec-localized-profiles -->

A profile $f(t,a,s)$ has independent time, particle-label and unit-period phase variables. With $A=X(t,\cdot)^{-1}$, its physical evaluation is $f(t,A(x),k_*\cdot A(x))$. The leading profile is $g(a)\mathbf a(t,a)F_h(s)$. A zero collar at the label cell's boundary permits smooth periodic extension with arbitrary real $k_*$. The divergence correction is the slow curl of $Q[V]=-\partial_s^{-1}(\kappa\times V/|\kappa|^2)$, where $\kappa$ is the transported covector. Its phase primitive has zero phase mean. The completed field is divergence free under transversality and compatibility with the same flow.
<!-- /passage:sec-localized-profiles -->

## The wave and its frame

<!-- passage:sec-the-wave-and-its-frame -->

For a preceding wave, nonzero transverse vectors $k_p,\mathbf a_p$ give $E_1=k_p/|k_p|$, $E_2=\mathbf a_p/|\mathbf a_p|$, $E_3=E_1\times E_2$ and strength $\sigma_p=|k_p||\mathbf a_p|$. Their nonvanishing and orthogonality make this an orthonormal frame. Division by zero is assigned zero in the formulas, so normalization alone does not guarantee a unit vector. At activation $t_0$, put $\sigma=\sigma_p(t_0)$. For positive coupling $\nu$, put $r=\sqrt{2\sigma\nu}$ and $S=\sigma/r$. For the new amplitude, $\alpha_1=S E_1\cdot\mathbf a$ and $\alpha_2=E_2\cdot\mathbf a$; some comparison estimates use $(U,V)=(-\alpha_1,\alpha_2)$, turning the paper’s initial pair $(-1,1)$ into $(1,1)$. Pairs can carry a maximum norm; statements using Euclidean operator norms are identified separately.
<!-- /passage:sec-the-wave-and-its-frame -->

## The endpoint unknowns

<!-- passage:sec-the-endpoint-unknowns -->

On $I=[0,T]$, with $0<T\le1$, let $X$ be the flow of a smooth periodic divergence-free parent velocity $U$, $F=D_aX$ and $M=(D_xU)\circ X$. For a given continuous source $L$ in $C^{0,1/2}$, the unknowns in (4.9) are $z$, $v=z_t$, a time-independent divergence-free field $c$, and a pressure gradient $G=\nabla_a\phi$, with $z(0)=z(T)=0$. They satisfy $Kv-\int_0^t\Omega v+L=c+G$, where $K=F^TF$ and $\Omega=F^T(M^T-M)F$. The spatial space is $C^{0,1/2}$, normed by the maximum of the supremum and Hölder seminorm; divergence is imposed weakly there. The physical variables are $\xi=Fz$ and $b=(Fv)\circ X^{-1}$. Under $-(M_t+M^2)\le I$, the endpoint theorem gives existence and uniqueness in these classes. Uniqueness concerns the pressure gradient, since the potential admits time-dependent constants. For the smooth force source, $c=b(0)$.
<!-- /passage:sec-the-endpoint-unknowns -->

## The inductive sequence

<!-- passage:sec-the-inductive-sequence -->

The indices agree with the paper: $\lambda_0=N$, $q_1=1$, and $L_j=4\log\lambda_{j+1}$, so $\varepsilon_j=L_{j+1}^{-2}$. Frequency separation uses nonnegative integer powers; negative powers in analytic estimates have their stated integer or real meaning. The maximum rule selects the greatest admissible order. The sequence consists of actual velocities, residuals, flows, oscillations and corrections satisfying stage estimates. Its existence must be distinguished from a list of those estimates. Spatial convergence uses the sum of supremum and one-half Hölder seminorms of derivatives through the stated order; activation times tend to a common finite endpoint.
<!-- /passage:sec-the-inductive-sequence -->


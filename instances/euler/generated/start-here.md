# How the construction reaches a singular time

Alpöge, Buckmaster and Coiculescu construct smooth periodic initial data for the unforced three-dimensional Euler equations. The velocity stays bounded, while the vorticity at the origin tends to infinity at a finite time. The proof has two connected tasks: amplify a succession of localized waves, and control the corrections needed to make their limit solve Euler. Each finite stage remains an approximate solution.

The route starts with the target, then follows the construction to its limiting solution. The order is explanatory: the parameter schedule appears when it becomes necessary to repeat the construction indefinitely.

## Step 1. Fix what must be proved

Theorem 1.1 concerns a smooth, odd, divergence-free initial velocity on $\mathbb T^3$. Its maximal classical solution has a finite lifespan $[0,T_*)$, bounded velocity and $|\operatorname{curl}u(t,0)|\to\infty$. Both the gradient and vorticity $L^\infty$ norms have divergent time integrals. Away from the origin, the velocity and its first time derivative have limits in every spatial $C^m$ norm.

## Steps 2–6. Make each wave prepare the next

A Craik–Criminale wave has velocity $\mathbf a(t)F(k(t)\cdot x)$, with $\mathbf a\perp k$. Its central gradient is $\mathbf a\otimes k$ when $F'(0)=1$. The preceding wave supplies a shear that amplifies the next wave; the reference equation quantifies this growth. Lemma 2.6 transfers that estimate to the perturbed wave and bounds the evolution of every transverse amplitude, which will also be needed for the corrections.

Large amplitude alone does not make the process repeatable. Proposition 2.8 finds a time when the new wave has the positive couplings and smaller coupling ratio required by its successor, while retaining a large shear. It bounds the wave while it is being switched on by an exponentially small fraction of its attained maximum. The crossing is compared with the reference amplitude maximum; the proposition does not identify the actual amplitude maximum with that time.

Lemma 3.1 chooses a profile with $F_h'(0)=1$ and $-Ch\le F_h'\le1$. When the wave pressure coefficient is positive, these bounds preserve the central gradient while controlling the positive part of the added pressure Hessian. The wave is then localized in particle labels and completed by a curl to preserve incompressibility (§3).

## Steps 7–9. Choose the initial correction through an endpoint problem

The phase average of the error requires a velocity correction that may extend over the torus. Its initial value is free to change. The construction chooses that initial value so that the first-order change in each particle's final position vanishes.

For the parent flow $X$, write $M=(\nabla U)\circ X$ and $H^\#=-(M_t+M^2)$. On an interval of length at most one, the upper quadratic-form bound $H^\#\le I$ gives coercivity for displacements vanishing at both endpoints (Lemma 4.1). Large negative eigenvalues are allowed. Theorem 4.2 turns this into an inverse for the linearized endpoint problem, with a bound proportional to the source norm. Lemma 5.3 controls the separate oscillatory equation using the transverse evolution bound. These two inverses solve different parts of the error.

## Steps 10–15. Build a finite correction and preserve the hypotheses

At each level, solve for the phase mean first, then for the transverse oscillation, and retain its divergence correction. The order matters because the new mean transports the leading wave's phase. Proposition 5.4 gives an exact identity for the remaining error; Theorem 5.6 bounds that error at a chosen finite depth, with the frequency selected to absorb the constants that depend on the depth.

Lemma 5.8 produces an approximate velocity with two residual terms: the finite expansion remainder and the time cutoff error. Lemma 5.9 controls the added pressure Hessian from above and the error in the central gradient. Lemma 5.10 controls the deformation of the new flow, including after a small perturbation. That separate estimate supplies a hypothesis needed at the next step.

Finally, Proposition 5.11 truncates the velocity in Fourier frequency and estimates the resulting third error. Expansion depth, early wave amplitude and Fourier cutoff control the three errors respectively. The residual remains nonzero at a finite stage. Only the oscillatory part has shrinking support and vanishes before activation; the mean corrections and Fourier tails need not.

## Steps 16–20. Use one sequence to obtain a smooth Euler solution

Lemma 1.3 lets the controlled derivative order $q_j$ tend to infinity slowly enough to absorb the constants required at each stage. Lemma 6.1 starts the construction from a stationary periodic shear. Theorem 7.1 then produces one sequence $U_j$ for all derivative orders, with activation times tending to $T_\infty>0$ and each stage defined beyond that time.

The key estimate (7.4) separates the localized oscillatory increment $O_j$ from $U_j-U_{j-1}-O_j$. The velocity increments are summable in the uniform norm. On any fixed interval ending before $T_\infty$, all sufficiently late $O_j$ vanish, and the remaining increments are summable in every fixed spatial derivative norm. Proposition 8.1 passes to the limit in the nonlinear equation as the residual tends to zero. This is where the construction obtains an exact unforced Euler solution.

## Steps 21–23. Establish the terminal conclusions separately

Proposition 8.2 proves vorticity growth throughout every sufficiently late activation interval. Projecting along the newest wave vector removes that wave's leading curl and reveals the preceding wave's contribution. This gives a full limit to infinity as $t\uparrow T_\infty$, while the velocity stays bounded.

Corollary 8.3 identifies $T_*=T_\infty$ and proves divergence of both time integrals. Divergence of the vorticity itself would not suffice to prove divergence of its integral. The paper invokes the periodic Beale–Kato–Majda criterion. The formal proof replaces it with an argument specific to the construction: it integrates the quantitative vorticity bound from Proposition 8.2 over the late activation intervals, whose lengths the crossing data bound from below.

For Proposition 8.4, shrinking supports give local spatial limits away from the origin. The first time derivative also requires control of the nonlocal pressure. A spatial cutoff separates the locally controlled term from a distant term whose pressure kernel is smooth. Smooth extension in space and time through the terminal time is the additional conclusion of Remark 1.2.

## Reading the comparisons

Each formal statement has been compared with the paper through the full definitions it uses. Theorem 1.1 has the same formal content as the paper, including the torus representation, the norms, maximality and the local limits away from the origin. Where an intermediate result is stronger, the formal version usually weakens a hypothesis, for example by admitting any parent pressure whose residual meets the required bounds. Where it differs, its card names the hypothesis or identification that changes. A stronger verdict for an intermediate estimate does not enlarge Theorem 1.1.

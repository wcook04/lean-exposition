# Independent review: v1 low-degree test counterexample

**Verdict: accept**, for the exact scalar test in v1 Fact 2.7 and Lemma 3.3, not a counterexample to the corrected v2 test, the entire PCP theorem, or the pinned Lean theorem. This is an ordinary mathematical argument, not a Lean verification or a claim of novelty.

Let k ≥ 2, q = 2^(2k), c = 2, and choose ζ ∈ Fq of order 3, possible because 3 divides q−1. For any dimension m′ ≥ 1 set f(x₁,…,x_m′) = x₁⁴. For all u,v ∈ Fq^m′, Frobenius in characteristic two gives

    f(u) + Σᵢ₌₁³ f(u + ζⁱv)
      = 4u₁⁴ + v₁⁴ Σᵢ₌₁³ ζ⁴ⁱ
      = 0,

because 4 = 0 in Fq, ζ⁴ = ζ, and 1 + ζ + ζ² = 0. Thus the test rejects with probability zero, even pointwise for every u,v. Yet f is not a degree-≤2 polynomial function: restricting any purported representation to the first coordinate would give a polynomial X⁴−g(X) of degree 4 with q > 4 distinct roots and leading coefficient 1. This also excludes individual degree ≤2 representations, since restriction leaves degree ≤2 in X₁. More strongly, the restriction argument plus the root bound shows every degree-≤2 m′-variate function agrees with f on at most 4/q of inputs (condition on the other coordinates); hence distance ≥ 1−4/q. For arbitrarily large k, q exceeds 8C for any fixed positive constant C, so v1 Lemma 3.3's q > Cc³ condition holds. Choosing any δ with 0 < δ < 1/[2(c+2)²] and 2δ < 1−4/q contradicts its claimed soundness. No dependence on m′ is needed; any imposed positive dimension, including an encoding dimension cm₁, can be used.

**Source comparison.** The v1 source `work/pcp-sources/core/source-v1/main.tex:478–507` (PDF Fact 2.7) asserts the all-one coefficients characterize degree ≤c for order c+1 and proves the forward moment identities only. The example satisfies that stated sum but violates the claimed converse. Lines 715–747 (PDF Lemma 3.3) give the exact unit-weight test, power-of-two/order/field-size hypotheses, and its 2δ soundness conclusion. The local correction identity for honest low-degree polynomials at lines 510–520 is a one-way statement; this example does not refute it. The tested f alone does not supply a cheating oracle for every check of the full binary verifier.

The v2 `source-v2/preliminaries.tex:124–134` (Fact 2.7) assumes q > 2c, uses a generator of Fq× and Lagrange weights, and `source-v2/technical_tools.tex:59–83` (Lemma 3.3) uses the resulting weighted test. For c = 2 and q ≥ 16, its generator has order q−1 > 3 and its test is different; the v1 vanishing-sum calculation therefore does not apply. In fact, the weighted residual for f(X)=X⁴ at u=0, v=1 is nonzero: the error of degree-2 interpolation at 0 is a nonzero product of the three nodes times their nonzero sum ζ+ζ²+ζ³; that sum could vanish only if ζ had order 3. The q > 2c hypothesis is met by this family, but it does not turn the old test into the new one.

The v2 acknowledgments explicitly thank Troy Lee for pointing out a mistake in the earlier Lemma 3.3 (`paper-v2.txt`, Acknowledgments); this acknowledges the earlier error without identifying this particular family or establishing attribution of this example. The repository README independently says its pinned proof formalizes the revised generator/Lagrange-weighted test. No inference is made here about the correctness of the whole v2 argument or about prior discovery of this family.

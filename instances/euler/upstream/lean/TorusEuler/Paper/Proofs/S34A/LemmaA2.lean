import TorusEuler.Paper.Proofs.S34A.Library.FreezingHigher

/-! Conditional proof of **Lemma A.2** of the latest manuscript (package S34A). -/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

set_option maxHeartbeats 20000000 in
/-- Proof of **Lemma A.2** (`cc:holder:freezing`,
sections/appA_mean_regularity.tex:71–90), following the TeX proof at
sections/appA_mean_regularity.tex:92–196, which cites no numbered result (only
Lax–Milgram, Evans §6.2.1). The row's own content carries the TeX steps:

* base clause, both cases: `paperLemmaA2_spatial` (`H = ℝ³`, `R = P`) and
  `paperLemmaA2_mixed` (`H = L²(I;ℝ³)`, `R = P Q`) give the isomorphism `R B` of the
  fixed space with the bound (A.5), exponent `p = 145`; they follow the frozen-symbol
  bound (A.6), the localization (A.7), interpolation and the continuation
  `B_s = (1-s) I + s B` (appA:92–182 and, for `k = 0`, :192–195). One constant
  `C = max Cs Cm` serves both cases.
* higher-order clause, `k = n + 1 ≥ 1`: the commutator induction (appA:183–195) is
  `paperLemmaA2_{spatial,mixed}_holder_restriction` (the class `R C^{k,1/2}` is mapped
  into itself and every datum there has a unique preimage there),
  `…_holder_boundedForward` and `…_holder_boundedInverse` (norm bounds); the inverse
  of the bounded-inverse lemma equals `e` because both compress `B`. The glue
  `Lib.S34A.freezingConclusion_higher` assembles the `↔` and the two-sided bound. -/
theorem Proof.lemma_A_2 : Statement.lemma_A_2 := by
  obtain ⟨Cs, hCs, hs⟩ := paperLemmaA2_spatial
  obtain ⟨Cm, hCm, hm⟩ := paperLemmaA2_mixed
  refine ⟨max Cs Cm, 145, le_max_of_le_left hCs, ?_, ?_⟩
  · intro B μ Lip hμ hLip hL hc
    obtain ⟨e, he, hb⟩ := hs B hμ hLip hL hc
    refine ⟨e, he, fun v => (hb v).trans ?_, ?_⟩
    · gcongr
      exact le_max_left _ _
    · intro k hk hB
      obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
      obtain ⟨hfwd, huniq⟩ := paperLemmaA2_spatial_holder_restriction hμ B hc n hB
      obtain ⟨Cf, hCf, hf⟩ := paperLemmaA2_spatial_holder_boundedForward B (n + 1) hB
      obtain ⟨e', he', Ci, -, hi⟩ := paperLemmaA2_spatial_holder_boundedInverse hμ B hc n hB
      have hee : e' = e := ContinuousLinearEquiv.coe_injective (he'.trans he.symm)
      subst hee
      exact Lib.S34A.freezingConclusion_higher _ _ B e' he' (n + 1) hfwd huniq Cf hCf hf
        Ci hi
  · intro B μ Lip hμ hLip hL hc
    obtain ⟨e, he, hb⟩ := hm B hμ hLip hL hc
    refine ⟨e, he, fun v => (hb v).trans ?_, ?_⟩
    · gcongr
      exact le_max_right _ _
    · intro k hk hB
      obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
      obtain ⟨hfwd, huniq⟩ := paperLemmaA2_mixed_holder_restriction hμ B hc n hB
      obtain ⟨Cf, hCf, hf⟩ := paperLemmaA2_mixed_holder_boundedForward B (n + 1) hB
      obtain ⟨e', he', Ci, -, hi⟩ := paperLemmaA2_mixed_holder_boundedInverse hμ B hc n hB
      have hee : e' = e := ContinuousLinearEquiv.coe_injective (he'.trans he.symm)
      subst hee
      exact Lib.S34A.freezingConclusion_higher _ _ B e' he' (n + 1) hfwd huniq Cf hCf hf
        Ci hi

end TorusEuler.Paper

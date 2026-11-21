import TorusEuler.Paper.S5.Statements

/-!
# Proof of the display (5.59) (package S5c)

The product growth inequality (5.59) (`cc:holder:product-growth`), displayed in the proof
of Proposition 5.11 at `sections/08_exact_wave.tex:424-428` and cited by the proof of
Proposition 8.1. The display cites no numbered result; it is proved by the library lemma
`spatialHolderHalf_bilinear` (glue by decision D3: Leibniz' rule and the algebra inequality
of `C^{0,1/2}`).
-/

namespace TorusEuler.Paper

/-- Proof of **Display (5.59)** (`cc:holder:product-growth`), following
`sections/08_exact_wave.tex:424-428`: "By Leibniz' rule and the algebra inequality for
the norm of `C^{0,1/2}`, for every integer `m ≥ 0`, `‖fg‖_{C^{m,1/2}} ≤ C_m ‖f‖ ‖g‖`".
Both steps are the library lemma `spatialHolderHalf_bilinear` (a library lemma, glue, decision D3: no content row),
which gives the bound with the constant `3(m+1)2^m ‖B‖` for any continuous bilinear
product `B`; the constant of the statement is `C_m = 3(m+1)2^m`. The display cites no
numbered result, so the proof has no hypotheses. -/
theorem Proof.Text.eq_5_59 : Statement.Text.eq_5_59 := by
  intro m
  refine ⟨3 * (m + 1) * (2 : ℝ) ^ m, by positivity, ?_⟩
  intro E F G _ _ _ _ _ _ B f g hf hg
  obtain ⟨h1, h2⟩ := spatialHolderHalf_bilinear B hf hg
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  ring

end TorusEuler.Paper

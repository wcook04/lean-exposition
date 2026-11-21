import TorusEuler.Paper.S2.Statements

/-! # Proof of Lemma 2.2

The conditional proof `TorusEuler.Paper.Proof.lemma_2_2` of
`TorusEuler.Paper.Statement.lemma_2_2` (`cc:lem:frame`,
`sections/02_affine.tex:65-104`). Lemma 2.2 cites no numbered result. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper

open MovingWaveVector

/-- Proof of **Lemma 2.2** (`cc:lem:frame`) following `sections/02_affine.tex:79-104`.
The row cites no numbered result, so there are no hypotheses; the proof uses the row's
own content lemma `hasDerivWithinAt_movingFrame`.

* The frame `E₁ = k/|k|`, `E₂ = a/|a|`, `E₃ = E₁ × E₂` is orthonormal because `k ⊥ a`
  (`orthonormal_movingFrame`; "this orthonormal frame", `:68`).
* The derivative of a normalized vector (`:81-86`) with `k' = -Bᵀk` gives `E₁'` and
  `(log|k|)' = -B₁₁` (`:87-91`); with `p_w|k| = 2|a|B₁₂` it gives `E₂'` and
  `(log|a|)' = -B₂₂` (`:92-97`); the product rule for `E₁ × E₂` gives `E₃'` (`:98-101`);
  and `tr B = 0` gives `(log σ)' = B₃₃` (`:102-103`). Together these are (2.2), the
  conclusion of `hasDerivWithinAt_movingFrame`, applied at each `t ∈ J` with the wave
  equations (2.1) for `D = B` (`WaveOn`). -/
theorem Proof.lemma_2_2 : Statement.lemma_2_2 := by
  intro J B k a htr hWave hData t ht E ν η
  obtain ⟨hk, ha, hp⟩ := hData t ht
  refine ⟨orthonormal_movingFrame hk ha hp, ?_⟩
  simpa only [E, ν, η, frame, entry, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
    hasDerivWithinAt_movingFrame ht (B t) (htr t ht) hk ha hp (hWave.1 t ht)
      (by simpa only [affineWavePressureCoeff] using hWave.2 t ht)

end TorusEuler.Paper

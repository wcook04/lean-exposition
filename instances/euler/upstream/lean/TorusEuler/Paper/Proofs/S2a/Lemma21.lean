import TorusEuler.Paper.S2.Statements
import TorusEuler.AffinePropagation

/-! # Proof of Lemma 2.1

The conditional proof `TorusEuler.Paper.Proof.lemma_2_1` of
`TorusEuler.Paper.Statement.lemma_2_1` (`cc:lem:wave`,
`sections/02_affine.tex:9-51`). Lemma 2.1 cites no numbered result. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper

/-- Proof of **Lemma 2.1** (`cc:lem:wave`) following `sections/02_affine.tex:24-51`.
The row cites no numbered result, so there are no hypotheses; the proof uses the row's
own content lemmas.

* Euler part (`:25-42`): the transport identities for `k·x` and `w = aF(k·x)`, the
  cancellation of the self-advection by `k·a = 0`, the identification of
  `(D' + D²)x` and `(a' + Da)F = p_w kF` as minus the pressure gradients, and
  `div u = tr D + (k·a)F' = 0`, are `affineWave_solvesEulerOn` (with the wave equations
  (2.1) as `WaveOn`); the differentiability conjuncts of the statement are
  `hasDerivWithinAt_affineWaveVelocity` (in `t`), `hasFDerivAt_affineWaveVelocity` (in
  `x`) and `hasGradientAt_affineWavePressure` (the pressure).
* Persistence (`:43-50`): `(k·a)' = 0` by the choice of `p_w`, and the linear equations
  for `k` and `a` with invertible fundamental matrices keep both vectors nonzero; this is
  `affineWave_propagation`. -/
theorem Proof.lemma_2_1 : Statement.lemma_2_1 := by
  intro J hJ hDiff F P hF hP D D' k a hD hS htr hWave
  have ha (t : ℝ) (ht : t ∈ J) : HasDerivWithinAt a
      (-(D t (a t)) + affineWavePressureCoeff (D t) (k t) (a t) • k t) J t := hWave.2 t ht
  refine ⟨fun hperp t ht x => ?_, fun t₀ ht₀ => affineWave_propagation hJ ht₀
    (HasDerivWithinAt.continuousOn hD) hWave.1
    (by simpa only [affineWavePressureCoeff] using ha)⟩
  have hE := affineWave_solvesEulerOn hDiff hF hP hD hS htr hWave.1 ha hperp t ht x
  have hFx := (hF ⟪k t, x⟫_ℝ).hasDerivAt
  exact ⟨(hasDerivWithinAt_affineWaveVelocity (hD t ht) (hWave.1 t ht) (ha t ht)
      hFx).differentiableWithinAt,
    (hasFDerivAt_affineWaveVelocity hFx).differentiableAt,
    (hasGradientAt_affineWavePressure (hS t ht) _ _ _ (hP _)).differentiableAt, hE.1, hE.2⟩

end TorusEuler.Paper
